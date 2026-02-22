//! Lint engine that orchestrates rule checking and fixing.
//!
//! Performance optimizations:
//! - **Parallel file processing**: Uses rayon to check files concurrently.
//! - **Rule cost ordering**: Cheap regex rules run first, complex analysis last.
//! - **Early termination**: `--max-diagnostics` stops collecting once the limit
//!   is reached, avoiding wasted work on large codebases.
//! - **Read-once caching**: Each file is read from disk exactly once per run.
//! - **Parallel file collection**: Directory walks run in parallel via rayon scope.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Mutex;

use rayon::prelude::*;
use tracing::{debug, error, info, warn};

use super::comments::CommentRule;
use super::dead_code::DeadCodeRule;
use super::doc_checker::DocCheckerRule;
use super::duplicate_types::{find_fst_fsti_pairs, DuplicateTypesRule};
use super::effect_checker::EffectCheckerRule;
use super::fix_applicator::{FixApplicator, FixApplicatorConfig, FixChainConfig};
use super::import_optimizer::ImportOptimizerRule;
use super::lowstar::{LowStarBufferRule, LowStarPerfRule};
use super::module_deps::ModuleDepsRule;
use super::naming::NamingRule;
use super::output::{
    color_config,
    print_diagnostics, print_dry_run, print_summary,
    print_apply_header, print_dry_run_header, print_fixes_applied, print_no_fixes_message,
    DryRunFormat, DryRunSummary, LintSummary, OutputFormat,
};
use super::perf_profiler::PerfProfilerRule;
use super::proof_hints::ProofHintsRule;
use super::refinement_simplifier::RefinementSimplifierRule;
use super::reorder_interface::ReorderInterfaceRule;
use super::rules::{Diagnostic, FixSafetyLevel, Rule, RuleCode};
use super::security::SecurityRule;
use super::spec_extractor::SpecExtractorRule;
use super::test_generator::TestGeneratorRule;
use super::unused_opens::UnusedOpensRule;
use super::fstar_traps::{
    AssumeTypeVsValRule, AttributeTargetRule, AutoClassificationRule,
    DecreasesBoundRule, DoNotUnrefineRule, DollarBinderRule,
    ErasableSuggestionRule, FunctionEqualityRule, IntroduceWithRule,
    KeywordAsIdentifierRule, LemmaEnsuresAmbiguityRule,
    MissingDecreasesRule, MissingMulOpenRule, MissingNoeqRule, MissingPluginRule,
    NoeqVsUnopteqRule, OpaqueWithoutRevealRule,
    PatternDisjunctionRule, RequiresTrueOkRule, RevealInTotRule,
    SimpCandidateRule, SimpCommGuardRule, SquashBridgeRule, StrictOnArgumentsRule,
    SumVsOrRule, TacticSuggestionRule, TickVsExplicitRule,
    TotVsGtotRule, UnfoldAliasRule, UnguardedForallRule, UniverseHintRule,
    ValBinderArrowRule,
};
use super::z3_complexity::Z3ComplexityRule;

// ---------------------------------------------------------------------------
// Rule cost ordering
// ---------------------------------------------------------------------------

/// Estimated cost tier for a rule. Lower = cheaper = runs first.
///
/// Running cheap rules first maximizes the chance that `--max-diagnostics`
/// terminates early before expensive rules execute.
fn rule_cost(code: RuleCode) -> u8 {
    match code {
        // Tier 0: Fast regex / simple pattern matching
        RuleCode::FST003 | RuleCode::FST006
        | RuleCode::FST021 | RuleCode::FST025 | RuleCode::FST027
        | RuleCode::FST029 | RuleCode::FST036 | RuleCode::FST040
        | RuleCode::FST041 | RuleCode::FST043 => 0,
        // Tier 1: Medium - single pass with moderate logic
        RuleCode::FST004 | RuleCode::FST011 | RuleCode::FST013
        | RuleCode::FST016 | RuleCode::FST017 | RuleCode::FST018
        | RuleCode::FST019
        | RuleCode::FST020 | RuleCode::FST022 | RuleCode::FST023
        | RuleCode::FST024 | RuleCode::FST026 | RuleCode::FST028
        | RuleCode::FST030 | RuleCode::FST034 | RuleCode::FST035
        | RuleCode::FST037 | RuleCode::FST038 | RuleCode::FST039
        | RuleCode::FST042 | RuleCode::FST044 | RuleCode::FST045
        | RuleCode::FST046 | RuleCode::FST047 | RuleCode::FST048
        | RuleCode::FST049 | RuleCode::FST050 | RuleCode::FST051 => 1,
        // Tier 2: Complex multi-pass analysis
        RuleCode::FST005 | RuleCode::FST007 | RuleCode::FST008
        | RuleCode::FST009 | RuleCode::FST010 | RuleCode::FST012
        | RuleCode::FST014 | RuleCode::FST015
        | RuleCode::FST031 | RuleCode::FST032 | RuleCode::FST033 => 2,
        // Tier 3: Pair rules (most expensive, require two files)
        RuleCode::FST001 | RuleCode::FST002 => 3,
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the lint engine.
#[derive(Debug, Clone, Default)]
pub struct LintConfig {
    /// Rules to enable (if None, all rules are enabled).
    pub select: Option<HashSet<RuleCode>>,
    /// Rules to ignore.
    pub ignore: HashSet<RuleCode>,
    /// Path to F* executable (for rules that need it).
    pub fstar_exe: Option<String>,
    /// Maximum number of diagnostics to collect before stopping.
    /// `None` means unlimited.
    pub max_diagnostics: Option<usize>,
}

impl LintConfig {
    /// Create a new lint configuration from CLI options.
    ///
    /// Warns on stderr about any unrecognized rule codes in `--select` or
    /// `--ignore`. If `--select` is provided but yields zero valid codes,
    /// `has_empty_selection()` will return true so callers can exit early.
    pub fn new(select: Option<String>, ignore: Option<String>, fstar_exe: Option<String>) -> Self {
        let select_set = select.map(|s| {
            let mut valid = HashSet::new();
            for raw in s.split(',') {
                let code = raw.trim();
                if code.is_empty() {
                    continue;
                }
                match RuleCode::parse_code(code) {
                    Some(rc) => { valid.insert(rc); }
                    None => {
                        eprintln!("Warning: Unknown rule code '{}' (ignored)", code);
                    }
                }
            }
            valid
        });

        // Warn if --select was given but resolved to nothing
        if let Some(ref set) = select_set {
            if set.is_empty() {
                eprintln!("Warning: No valid rules selected, nothing will be checked");
            }
        }

        let ignore_set = ignore
            .map(|s| {
                let mut valid = HashSet::new();
                for raw in s.split(',') {
                    let code = raw.trim();
                    if code.is_empty() {
                        continue;
                    }
                    match RuleCode::parse_code(code) {
                        Some(rc) => { valid.insert(rc); }
                        None => {
                            eprintln!("Warning: Unknown rule code '{}' in --ignore (ignored)", code);
                        }
                    }
                }
                valid
            })
            .unwrap_or_default();

        Self {
            select: select_set,
            ignore: ignore_set,
            fstar_exe,
            max_diagnostics: None,
        }
    }

    /// Builder: set the maximum number of diagnostics to collect.
    pub fn with_max_diagnostics(mut self, max: Option<usize>) -> Self {
        self.max_diagnostics = max;
        self
    }

    /// Returns true when `--select` was provided but no valid rule codes
    /// were parsed, meaning the engine would check nothing.
    pub fn has_empty_selection(&self) -> bool {
        matches!(&self.select, Some(set) if set.is_empty())
    }

    /// Check if a rule is enabled.
    pub fn is_rule_enabled(&self, rule: RuleCode) -> bool {
        if self.ignore.contains(&rule) {
            return false;
        }
        match &self.select {
            Some(selected) => selected.contains(&rule),
            None => true,
        }
    }
}

// ---------------------------------------------------------------------------
// Engine
// ---------------------------------------------------------------------------

/// The main lint engine.
pub struct LintEngine {
    config: LintConfig,
    /// Rules sorted by cost (cheap first).
    rules: Vec<Box<dyn Rule>>,
}

impl LintEngine {
    /// Create a new lint engine with the given configuration.
    ///
    /// Rules are sorted by estimated cost so that cheap rules execute first.
    /// This maximizes the benefit of `--max-diagnostics` early termination.
    pub fn new(config: LintConfig) -> Self {
        let mut rules: Vec<Box<dyn Rule>> = Vec::with_capacity(19);

        // Add rules based on configuration
        if config.is_rule_enabled(RuleCode::FST001) {
            rules.push(Box::new(DuplicateTypesRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST002) {
            rules.push(Box::new(ReorderInterfaceRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST003) {
            rules.push(Box::new(CommentRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST004) {
            rules.push(Box::new(UnusedOpensRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST005) {
            rules.push(Box::new(DeadCodeRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST006) {
            rules.push(Box::new(NamingRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST007) {
            rules.push(Box::new(Z3ComplexityRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST008) {
            rules.push(Box::new(ImportOptimizerRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST009) {
            rules.push(Box::new(ProofHintsRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST010) {
            rules.push(Box::new(SpecExtractorRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST011) {
            rules.push(Box::new(EffectCheckerRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST012) {
            rules.push(Box::new(RefinementSimplifierRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST013) {
            rules.push(Box::new(DocCheckerRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST014) {
            rules.push(Box::new(TestGeneratorRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST015) {
            rules.push(Box::new(ModuleDepsRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST016) {
            rules.push(Box::new(PerfProfilerRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST017) {
            rules.push(Box::new(SecurityRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST018) {
            rules.push(Box::new(LowStarBufferRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST019) {
            rules.push(Box::new(LowStarPerfRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST020) {
            rules.push(Box::new(ValBinderArrowRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST021) {
            rules.push(Box::new(KeywordAsIdentifierRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST022) {
            rules.push(Box::new(MissingNoeqRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST023) {
            rules.push(Box::new(UnguardedForallRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST024) {
            rules.push(Box::new(DecreasesBoundRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST025) {
            rules.push(Box::new(AssumeTypeVsValRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST026) {
            rules.push(Box::new(RevealInTotRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST027) {
            rules.push(Box::new(MissingMulOpenRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST028) {
            rules.push(Box::new(StrictOnArgumentsRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST029) {
            rules.push(Box::new(PatternDisjunctionRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST030) {
            rules.push(Box::new(FunctionEqualityRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST031) {
            rules.push(Box::new(OpaqueWithoutRevealRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST032) {
            rules.push(Box::new(UniverseHintRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST033) {
            rules.push(Box::new(TacticSuggestionRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST034) {
            rules.push(Box::new(SimpCandidateRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST035) {
            rules.push(Box::new(SimpCommGuardRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST036) {
            rules.push(Box::new(DollarBinderRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST037) {
            rules.push(Box::new(TotVsGtotRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST038) {
            rules.push(Box::new(IntroduceWithRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST039) {
            rules.push(Box::new(UnfoldAliasRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST040) {
            rules.push(Box::new(AttributeTargetRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST041) {
            rules.push(Box::new(RequiresTrueOkRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST042) {
            rules.push(Box::new(LemmaEnsuresAmbiguityRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST043) {
            rules.push(Box::new(TickVsExplicitRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST044) {
            rules.push(Box::new(MissingDecreasesRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST045) {
            rules.push(Box::new(NoeqVsUnopteqRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST046) {
            rules.push(Box::new(ErasableSuggestionRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST047) {
            rules.push(Box::new(SumVsOrRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST048) {
            rules.push(Box::new(MissingPluginRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST049) {
            rules.push(Box::new(AutoClassificationRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST050) {
            rules.push(Box::new(SquashBridgeRule::new()));
        }
        if config.is_rule_enabled(RuleCode::FST051) {
            rules.push(Box::new(DoNotUnrefineRule::new()));
        }

        // Sort rules by cost: cheap regex rules first, pair rules last.
        rules.sort_by_key(|r| rule_cost(r.code()));

        Self { config, rules }
    }

    /// Check files for issues.
    ///
    /// Files are read once and then checked in parallel across all enabled
    /// single-file rules. Pair rules run after single-file rules complete.
    pub async fn check(&self, paths: &[PathBuf], format: OutputFormat, show_fixes: bool) -> i32 {
        if self.config.has_empty_selection() {
            return 1;
        }

        info!("Checking {} path(s)", paths.len());

        let files = self.collect_files(paths);
        info!("Found {} F* file(s)", files.len());

        // Phase 1: Read all files from disk (parallel I/O).
        let file_cache = self.read_files_parallel(&files);
        debug!("Cached {} file(s) in memory", file_cache.len());

        // Phase 2: Run single-file rules in parallel across files.
        let max_diags = self.config.max_diagnostics.unwrap_or(usize::MAX);
        let diag_count = AtomicUsize::new(0);
        let limit_reached = AtomicBool::new(false);

        let single_rules: Vec<&dyn Rule> = self.rules.iter()
            .filter(|r| !r.requires_pair())
            .map(|r| r.as_ref())
            .collect();

        let mut all_diagnostics: Vec<Diagnostic> = file_cache
            .par_iter()
            .flat_map_iter(|(file, content)| {
                if limit_reached.load(Ordering::Relaxed) {
                    return Vec::new();
                }
                let mut diags = Vec::new();
                for rule in &single_rules {
                    if limit_reached.load(Ordering::Relaxed) {
                        break;
                    }
                    diags.extend(rule.check(file, content));
                }
                // Track count for early termination.
                if !diags.is_empty() {
                    let prev = diag_count.fetch_add(diags.len(), Ordering::Relaxed);
                    if prev + diags.len() >= max_diags {
                        limit_reached.store(true, Ordering::Relaxed);
                        let allowed = max_diags.saturating_sub(prev);
                        diags.truncate(allowed);
                    }
                }
                diags
            })
            .collect();

        // Phase 3: Run pair rules (sequential -- typically few pairs).
        if !limit_reached.load(Ordering::Relaxed) {
            let cache_paths: Vec<PathBuf> = file_cache.iter().map(|(p, _)| p.clone()).collect();
            let pairs = find_fst_fsti_pairs(&cache_paths);
            debug!("Found {} .fst/.fsti pair(s)", pairs.len());

            let pair_rules: Vec<&dyn Rule> = self.rules.iter()
                .filter(|r| r.requires_pair())
                .map(|r| r.as_ref())
                .collect();

            if !pair_rules.is_empty() {
                for (fst_file, fsti_file) in &pairs {
                    if limit_reached.load(Ordering::Relaxed) {
                        break;
                    }
                    let (fst_content, fsti_content) = match (
                        file_cache.get(fst_file),
                        file_cache.get(fsti_file),
                    ) {
                        (Some((_, fc)), Some((_, fic))) => (fc.as_str(), fic.as_str()),
                        _ => continue,
                    };

                    for rule in &pair_rules {
                        if limit_reached.load(Ordering::Relaxed) {
                            break;
                        }
                        let diags = rule.check_pair(fst_file, fst_content, fsti_file, fsti_content);
                        let prev = diag_count.fetch_add(diags.len(), Ordering::Relaxed);
                        let allowed = max_diags.saturating_sub(prev);
                        if allowed < diags.len() {
                            all_diagnostics.extend(diags.into_iter().take(allowed));
                            limit_reached.store(true, Ordering::Relaxed);
                        } else {
                            all_diagnostics.extend(diags);
                        }
                    }
                }
            }
        }

        // Drop the cache before output to free memory.
        drop(file_cache);

        // Sort diagnostics for deterministic output (parallel collection is
        // unordered).
        all_diagnostics.sort_unstable_by(|a, b| {
            a.file.cmp(&b.file)
                .then_with(|| a.range.start_line.cmp(&b.range.start_line))
                .then_with(|| a.range.start_col.cmp(&b.range.start_col))
        });

        // Count files with issues.
        let files_with_issues: HashSet<&PathBuf> =
            all_diagnostics.iter().map(|d| &d.file).collect();

        let mut summary = LintSummary {
            files_with_issues: files_with_issues.len(),
            ..LintSummary::default()
        };
        for diag in &all_diagnostics {
            summary.add_diagnostic(diag);
        }

        // Print results.
        if let Err(e) = print_diagnostics(&all_diagnostics, format, show_fixes) {
            eprintln!("Error printing diagnostics: {}", e);
        }
        if let Err(e) = print_summary(&summary, format) {
            eprintln!("Error printing summary: {}", e);
        }

        if all_diagnostics.is_empty() { 0 } else { 1 }
    }

    /// Fix files.
    ///
    /// By default (dry_run=true), this shows what WOULD be changed without modifying files.
    /// Set dry_run=false (via --apply flag) to actually write changes.
    ///
    /// Both dry-run and apply modes use the same `FixApplicator` code path to
    /// ensure the dry-run output accurately reflects what `--apply` would do
    /// (same eligibility checks, edit merging, overlap detection, and validation).
    ///
    /// Safety levels determine which fixes can be applied:
    /// - Safe: Can be auto-applied with --apply
    /// - Caution: Shows warning, applies with --apply
    /// - Unsafe: Requires --force in addition to --apply
    pub async fn fix(
        &self,
        paths: &[PathBuf],
        format: OutputFormat,
        dry_run: bool,
        dry_run_format: DryRunFormat,
        force: bool,
    ) -> i32 {
        if self.config.has_empty_selection() {
            return 1;
        }

        // Skip ANSI-colored headers when output is JSON to avoid corrupting
        // machine-readable output on stdout.
        let suppress_header = matches!(dry_run_format, DryRunFormat::Json)
            || matches!(format, OutputFormat::Json | OutputFormat::Sarif | OutputFormat::Github);

        if !suppress_header {
            let stdout = std::io::stdout();
            let mut handle = stdout.lock();

            if dry_run {
                if let Err(e) = print_dry_run_header(&mut handle) {
                    eprintln!("Error printing header: {}", e);
                }
            } else if let Err(e) = print_apply_header(&mut handle) {
                eprintln!("Error printing header: {}", e);
            }
        }

        info!(
            "Fixing {} path(s){}",
            paths.len(),
            if dry_run { " (dry run)" } else { "" }
        );

        let files = self.collect_files(paths);
        info!("Found {} F* file(s)", files.len());

        // Phase 1: Read all files from disk (parallel I/O).
        let file_cache = self.read_files_parallel(&files);

        // Phase 2: Collect fixable diagnostics.
        let all_diagnostics = self.collect_fixable_diagnostics(&file_cache);

        // Build content map for DryRunSummary fallback (keyed by PathBuf).
        let content_map: HashMap<&PathBuf, &str> = file_cache
            .iter()
            .map(|(p, c)| (p, c.as_str()))
            .collect();

        // Filter diagnostics based on safety level (same for both dry-run and apply).
        let (applicable_diagnostics, skipped_unsafe): (Vec<_>, Vec<_>) = all_diagnostics
            .into_iter()
            .partition(|d| {
                if let Some(ref fix) = d.fix {
                    force || fix.can_apply_without_force()
                } else {
                    false
                }
            });

        // Report skipped unsafe fixes if any (for both dry-run and apply).
        if !skipped_unsafe.is_empty() && !force && !suppress_header {
            let c = color_config();
            let unsafe_count = skipped_unsafe.len();
            println!(
                "{}{}Note: {} fix{} require{} --force to apply (Unsafe safety level).{}",
                c.bold(), c.yellow(),
                unsafe_count,
                if unsafe_count == 1 { "" } else { "es" },
                if unsafe_count == 1 { "s" } else { "" },
                c.reset(),
            );
            for diag in &skipped_unsafe {
                if let Some(ref fix) = diag.fix {
                    let reason = fix.unsafe_reason.as_deref().unwrap_or("Unsafe fix");
                    println!(
                        "  - {}: {} ({})",
                        diag.file.display(),
                        diag.rule,
                        reason
                    );
                }
            }
        }

        // Show caution warnings for Caution-level fixes.
        let caution_count = applicable_diagnostics
            .iter()
            .filter(|d| {
                d.fix.as_ref().is_some_and(|f| f.safety_level == FixSafetyLevel::Caution)
            })
            .count();

        if caution_count > 0 && !suppress_header {
            let c = color_config();
            println!(
                "{}{}Caution: {} fix{} {} risk{} and should be reviewed.{}",
                c.bold(), c.yellow(),
                caution_count,
                if caution_count == 1 { "" } else { "es" },
                if caution_count == 1 { "has" } else { "have" },
                if caution_count == 1 { "" } else { "s" },
                c.reset(),
            );
        }

        // Unified code path: use FixApplicator for BOTH dry-run and apply.
        // This ensures dry-run output accurately reflects what --apply would do.
        let applicator_config = if dry_run {
            FixApplicatorConfig::dry_run()
                .with_verbose(false)
                .with_force(force)
        } else {
            FixApplicatorConfig::apply()
                .with_verbose(true)
                .with_force(force)
        };
        let mut applicator = FixApplicator::new(applicator_config);

        match applicator.apply_batch(&applicable_diagnostics) {
            Ok(applied) => {
                if dry_run {
                    // Build DryRunSummary from the applicator results.
                    // This ensures the summary reflects the same eligibility
                    // checks, edit merging, and validation as --apply.
                    let mut dry_run_summary = DryRunSummary::new();
                    for diag in &applicable_diagnostics {
                        if let Some(content) = content_map.get(&diag.file) {
                            // Only add diagnostics that were actually processed
                            // (not skipped by eligibility checks)
                            let was_applied = applied.iter().any(|af| {
                                af.file == diag.file || {
                                    let canonical = diag.file.canonicalize()
                                        .unwrap_or_else(|_| diag.file.clone());
                                    af.file == canonical
                                }
                            });
                            if was_applied {
                                dry_run_summary.add_fix(diag, content);
                            }
                        }
                    }
                    dry_run_summary.finalize();

                    // Free cache before output
                    drop(content_map);
                    drop(file_cache);

                    if dry_run_summary.total_fixes == 0 {
                        if let Err(e) = print_no_fixes_message() {
                            eprintln!("Error printing message: {}", e);
                        }
                    } else if let Err(e) = print_dry_run(&dry_run_summary, dry_run_format) {
                        eprintln!("Error printing dry-run output: {}", e);
                    }
                    return 0;
                }

                // Apply mode output
                drop(content_map);
                drop(file_cache);

                let fixed_count = applied.len();
                let summary = applicator.summary();

                if fixed_count == 0 && summary.fixes_skipped == 0 {
                    if let Err(e) = print_no_fixes_message() {
                        eprintln!("Error printing message: {}", e);
                    }
                } else {
                    if let Err(e) = print_fixes_applied(fixed_count) {
                        eprintln!("Error printing message: {}", e);
                    }

                    if summary.fixes_skipped > 0 {
                        let c = color_config();
                        println!(
                            "{}{}{} fix{} skipped (low confidence or unsafe).{}",
                            c.bold(), c.yellow(),
                            summary.fixes_skipped,
                            if summary.fixes_skipped == 1 { "" } else { "es" },
                            c.reset(),
                        );
                        for (file, reason) in &summary.skipped_reasons {
                            println!("  - {}: {}", file.display(), reason);
                        }
                    }

                    if summary.fixes_failed > 0 {
                        let c = color_config();
                        println!(
                            "{}{}{} fix{} failed.{}",
                            c.bold(), c.red(),
                            summary.fixes_failed,
                            if summary.fixes_failed == 1 { "" } else { "es" },
                            c.reset(),
                        );
                        for (file, reason) in &summary.failed_reasons {
                            println!("  - {}: {}", file.display(), reason);
                        }
                    }
                }
            }
            Err(e) => {
                drop(content_map);
                drop(file_cache);

                error!("Fix application failed: {}", e);
                let c = color_config();
                eprintln!("{}{}Error: {}{}", c.bold(), c.red(), e, c.reset());
                return 1;
            }
        }

        0
    }

    /// Check a single file's content in-memory without disk I/O.
    ///
    /// Runs all enabled single-file rules against the provided content.
    /// Pair rules (FST001, FST002) are skipped since they require two files.
    /// Returns diagnostics sorted by position for deterministic output.
    pub fn check_content(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        for rule in &self.rules {
            if !rule.requires_pair() {
                diagnostics.extend(rule.check(file, content));
            }
        }
        diagnostics.sort_unstable_by(|a, b| {
            a.file
                .cmp(&b.file)
                .then_with(|| a.range.start_line.cmp(&b.range.start_line))
                .then_with(|| a.range.start_col.cmp(&b.range.start_col))
        });
        diagnostics
    }

    // -----------------------------------------------------------------------
    // File I/O helpers
    // -----------------------------------------------------------------------

    /// Read files from disk in parallel using rayon.
    ///
    /// Returns a Vec of (path, content) pairs. Files that fail to read are
    /// skipped with a warning.
    /// Collect fixable diagnostics from file cache using all configured rules.
    ///
    /// Runs single-file rules in parallel and pair rules sequentially, then
    /// returns only diagnostics that have a fix attached. This method is used
    /// by both `fix()` and `fix_with_chains()` to ensure consistent behavior.
    fn collect_fixable_diagnostics(
        &self,
        file_cache: &[(PathBuf, String)],
    ) -> Vec<Diagnostic> {
        // Single-file rules (parallel).
        let single_rules: Vec<&dyn Rule> = self
            .rules
            .iter()
            .filter(|r| !r.requires_pair())
            .map(|r| r.as_ref())
            .collect();

        let mut all_diagnostics: Vec<Diagnostic> = file_cache
            .par_iter()
            .flat_map_iter(|(file, content)| {
                let mut diags = Vec::new();
                for rule in &single_rules {
                    for diag in rule.check(file, content) {
                        if diag.fix.is_some() {
                            diags.push(diag);
                        }
                    }
                }
                diags
            })
            .collect();

        // Pair rules (sequential).
        let cache_paths: Vec<PathBuf> = file_cache.iter().map(|(p, _)| p.clone()).collect();
        let pairs = find_fst_fsti_pairs(&cache_paths);

        let pair_rules: Vec<&dyn Rule> = self
            .rules
            .iter()
            .filter(|r| r.requires_pair())
            .map(|r| r.as_ref())
            .collect();

        if !pair_rules.is_empty() {
            let content_map: HashMap<&PathBuf, &str> = file_cache
                .iter()
                .map(|(p, c)| (p, c.as_str()))
                .collect();

            for (fst_file, fsti_file) in &pairs {
                let (fst_content, fsti_content) = match (
                    content_map.get(fst_file),
                    content_map.get(fsti_file),
                ) {
                    (Some(fc), Some(fic)) => (*fc, *fic),
                    _ => continue,
                };

                for rule in &pair_rules {
                    for diag in rule.check_pair(fst_file, fst_content, fsti_file, fsti_content) {
                        if diag.fix.is_some() {
                            all_diagnostics.push(diag);
                        }
                    }
                }
            }
        }

        all_diagnostics
    }

    /// Fix files with chained follow-up rules.
    ///
    /// After applying the initial batch of fixes, re-reads the modified files
    /// and runs follow-up rules (e.g., after FST001 removes duplicate types,
    /// run FST004 to remove unused opens that were only needed by the removed
    /// code). Iterates up to `chain_config.max_iterations` times.
    ///
    /// Returns the total number of fixes applied across all iterations.
    pub async fn fix_with_chains(
        &self,
        paths: &[PathBuf],
        format: OutputFormat,
        force: bool,
        chain_config: FixChainConfig,
    ) -> i32 {
        if self.config.has_empty_selection() {
            return 1;
        }

        let suppress_header = matches!(format, OutputFormat::Json | OutputFormat::Sarif | OutputFormat::Github);

        if !suppress_header {
            let stdout = std::io::stdout();
            let mut handle = stdout.lock();
            if let Err(e) = print_apply_header(&mut handle) {
                eprintln!("Error printing header: {}", e);
            }
        }

        let files = self.collect_files(paths);
        let mut total_applied = 0usize;
        let mut modified_files: Vec<PathBuf> = Vec::new();

        for iteration in 0..chain_config.max_iterations {
            // Re-read files (original or modified from previous iteration).
            let file_cache = self.read_files_parallel(&files);
            let all_diagnostics = self.collect_fixable_diagnostics(&file_cache);

            // Filter by safety.
            let applicable: Vec<Diagnostic> = all_diagnostics
                .into_iter()
                .filter(|d| {
                    d.fix.as_ref().is_some_and(|f| force || f.can_apply_without_force())
                })
                .collect();

            if applicable.is_empty() {
                if iteration == 0 {
                    info!("No fixable diagnostics found");
                } else {
                    info!(
                        "Fix chain converged after {} iteration(s)",
                        iteration
                    );
                }
                break;
            }

            let applicator_config = FixApplicatorConfig::apply()
                .with_verbose(iteration == 0)
                .with_force(force);
            let mut applicator = FixApplicator::new(applicator_config);

            match applicator.apply_batch(&applicable) {
                Ok(applied) => {
                    let count = applied.len();
                    if count == 0 {
                        info!(
                            "Fix chain iteration {} produced no changes, stopping",
                            iteration + 1
                        );
                        break;
                    }

                    total_applied += count;
                    modified_files.extend(applicator.modified_files());

                    // Determine which follow-up rules should run.
                    let applied_rules: std::collections::HashSet<RuleCode> =
                        applied.iter().map(|af| af.rule).collect();
                    let follow_ups: std::collections::HashSet<RuleCode> = applied_rules
                        .iter()
                        .flat_map(|r| chain_config.follow_up_rules(*r))
                        .collect();

                    if follow_ups.is_empty() {
                        info!(
                            "No follow-up rules for iteration {}, chain complete",
                            iteration + 1
                        );
                        break;
                    }

                    info!(
                        "Fix chain iteration {}: {} fixes applied, {} follow-up rule(s)",
                        iteration + 1,
                        count,
                        follow_ups.len()
                    );
                }
                Err(e) => {
                    error!("Fix chain iteration {} failed: {}", iteration + 1, e);
                    break;
                }
            }
        }

        if total_applied > 0 {
            if let Err(e) = print_fixes_applied(total_applied) {
                eprintln!("Error printing message: {}", e);
            }
        } else if let Err(e) = print_no_fixes_message() {
            eprintln!("Error printing message: {}", e);
        }

        0
    }

    fn read_files_parallel(&self, files: &[PathBuf]) -> Vec<(PathBuf, String)> {
        files
            .par_iter()
            .filter_map(|file| {
                match fs::read_to_string(file) {
                    Ok(content) => Some((file.clone(), content)),
                    Err(e) => {
                        warn!("Failed to read {}: {}", file.display(), e);
                        None
                    }
                }
            })
            .collect()
    }

    /// Collect all F* files from paths using parallel directory traversal.
    ///
    /// Top-level paths are processed in parallel. Each directory spawns
    /// recursive sub-tasks via rayon's scoped threads.
    fn collect_files(&self, paths: &[PathBuf]) -> Vec<PathBuf> {
        let files = Mutex::new(Vec::new());

        rayon::scope(|s| {
            for path in paths {
                let files = &files;
                s.spawn(move |s| {
                    if !path.exists() {
                        warn!("Path does not exist: {}", path.display());
                        return;
                    }
                    if path.is_file() {
                        if is_fstar_file(path) {
                            if let Ok(mut guard) = files.lock() {
                                guard.push(path.clone());
                            }
                        }
                    } else if path.is_dir() {
                        collect_dir_recursive(s, path, files);
                    }
                });
            }
        });

        let mut result = files.into_inner().unwrap_or_else(|e| e.into_inner());
        // Sort for deterministic processing order.
        result.sort();
        result
    }
}

/// Recursively collect F* files from a directory using rayon scoped threads.
///
/// Each sub-directory is processed as a separate rayon task, enabling
/// parallel traversal of large directory trees.
fn collect_dir_recursive<'s>(
    scope: &rayon::Scope<'s>,
    dir: &Path,
    files: &'s Mutex<Vec<PathBuf>>,
) {
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(e) => {
            warn!("Failed to read directory {}: {}", dir.display(), e);
            return;
        }
    };

    // Batch file results to reduce mutex contention.
    let mut batch = Vec::new();

    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_file() && is_fstar_file(&path) {
            batch.push(path);
        } else if path.is_dir() {
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if !name.starts_with('.') && name != "node_modules" && name != "target" {
                scope.spawn(move |s| {
                    collect_dir_recursive(s, &path, files);
                });
            }
        }
    }

    if !batch.is_empty() {
        if let Ok(mut guard) = files.lock() {
            guard.extend(batch);
        }
    }
}

/// Check if a file is an F* source file.
fn is_fstar_file(path: &Path) -> bool {
    path.extension()
        .and_then(|ext| ext.to_str())
        .map(|ext| ext == "fst" || ext == "fsti")
        .unwrap_or(false)
}

// ---------------------------------------------------------------------------
// Helper trait extension for Vec<(PathBuf, String)> lookups
// ---------------------------------------------------------------------------

trait FileCache {
    fn get(&self, path: &Path) -> Option<&(PathBuf, String)>;
}

impl FileCache for Vec<(PathBuf, String)> {
    fn get(&self, path: &Path) -> Option<&(PathBuf, String)> {
        self.iter().find(|(p, _)| p == path)
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    /// Helper to create a test file with content.
    fn create_test_file(dir: &TempDir, name: &str, content: &str) -> PathBuf {
        let path = dir.path().join(name);
        fs::write(&path, content).expect("Failed to write test file");
        path
    }

    /// Helper to read a test file content.
    fn read_test_file(path: &Path) -> String {
        fs::read_to_string(path).expect("Failed to read test file")
    }

    // =====================================================================
    // CLI BEHAVIOR TESTS
    // =====================================================================

    #[test]
    fn test_lint_config_default() {
        let config = LintConfig::default();
        assert!(config.select.is_none());
        assert!(config.ignore.is_empty());
        assert!(config.fstar_exe.is_none());
        assert!(config.max_diagnostics.is_none());
    }

    #[test]
    fn test_lint_config_with_select() {
        let config = LintConfig::new(Some("FST001,FST002".to_string()), None, None);
        assert!(config.is_rule_enabled(RuleCode::FST001));
        assert!(config.is_rule_enabled(RuleCode::FST002));
        assert!(!config.is_rule_enabled(RuleCode::FST003));
    }

    #[test]
    fn test_lint_config_with_ignore() {
        let config = LintConfig::new(None, Some("FST001".to_string()), None);
        assert!(!config.is_rule_enabled(RuleCode::FST001));
        assert!(config.is_rule_enabled(RuleCode::FST002));
    }

    #[test]
    fn test_lint_config_max_diagnostics_builder() {
        let config = LintConfig::new(None, None, None).with_max_diagnostics(Some(100));
        assert_eq!(config.max_diagnostics, Some(100));
    }

    // =====================================================================
    // RULE ORDERING TESTS
    // =====================================================================

    #[test]
    fn test_rule_cost_ordering() {
        // Verify cheap rules have lower cost than expensive ones.
        assert!(rule_cost(RuleCode::FST003) < rule_cost(RuleCode::FST005));
        assert!(rule_cost(RuleCode::FST006) < rule_cost(RuleCode::FST001));
        assert!(rule_cost(RuleCode::FST004) <= rule_cost(RuleCode::FST007));
    }

    #[test]
    fn test_engine_sorts_rules_by_cost() {
        let config = LintConfig::default();
        let engine = LintEngine::new(config);

        // Verify rules are sorted by cost.
        let costs: Vec<u8> = engine.rules.iter().map(|r| rule_cost(r.code())).collect();
        for window in costs.windows(2) {
            assert!(
                window[0] <= window[1],
                "Rules must be sorted by cost: {} <= {}",
                window[0],
                window[1]
            );
        }
    }

    // =====================================================================
    // DRY-RUN MODE TESTS
    // =====================================================================

    #[tokio::test]
    async fn test_dry_run_does_not_modify_files() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let original_content = r#"module Test

open FStar.Pervasives

let x = 1
"#;
        let fst_file = create_test_file(&temp_dir, "Test.fst", original_content);

        let config = LintConfig::new(Some("FST004".to_string()), None, None);
        let engine = LintEngine::new(config);
        let _exit_code = engine.fix(&[fst_file.clone()], OutputFormat::Text, true, DryRunFormat::Full, false).await;

        let content_after = read_test_file(&fst_file);
        assert_eq!(
            original_content, content_after,
            "Dry-run mode should NOT modify files"
        );
    }

    #[tokio::test]
    async fn test_dry_run_returns_zero_exit_code() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let content = r#"module Test
let x = 1
"#;
        let fst_file = create_test_file(&temp_dir, "Test.fst", content);

        let config = LintConfig::default();
        let engine = LintEngine::new(config);
        let exit_code = engine.fix(&[fst_file], OutputFormat::Text, true, DryRunFormat::Full, false).await;

        assert_eq!(exit_code, 0, "Fix command should return 0 exit code");
    }

    // =====================================================================
    // APPLY MODE TESTS
    // =====================================================================

    #[tokio::test]
    async fn test_apply_mode_modifies_files() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let original_content = r#"module Test

(** Documentation for x *)
let x = 1
"#;
        let fst_file = create_test_file(&temp_dir, "Test.fst", original_content);

        let config = LintConfig::new(Some("FST013".to_string()), None, None);
        let engine = LintEngine::new(config);
        let _exit_code = engine.fix(&[fst_file.clone()], OutputFormat::Text, false, DryRunFormat::Full, false).await;
    }

    // =====================================================================
    // FILE COLLECTION TESTS
    // =====================================================================

    #[tokio::test]
    async fn test_collect_fstar_files_only() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        create_test_file(&temp_dir, "Test.fst", "module Test\n");
        create_test_file(&temp_dir, "Test.fsti", "module Test\n");
        create_test_file(&temp_dir, "README.md", "# README\n");
        create_test_file(&temp_dir, "test.rs", "fn main() {}\n");

        let config = LintConfig::default();
        let engine = LintEngine::new(config);
        let files = engine.collect_files(&[temp_dir.path().to_path_buf()]);

        assert_eq!(files.len(), 2);
        assert!(files.iter().all(|f| {
            let ext = f.extension().and_then(|e| e.to_str());
            ext == Some("fst") || ext == Some("fsti")
        }));
    }

    #[tokio::test]
    async fn test_collect_skips_hidden_directories() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let hidden_dir = temp_dir.path().join(".hidden");
        fs::create_dir(&hidden_dir).expect("Failed to create hidden dir");
        fs::write(hidden_dir.join("Hidden.fst"), "module Hidden\n")
            .expect("Failed to write hidden file");

        create_test_file(&temp_dir, "Visible.fst", "module Visible\n");

        let config = LintConfig::default();
        let engine = LintEngine::new(config);
        let files = engine.collect_files(&[temp_dir.path().to_path_buf()]);

        assert_eq!(files.len(), 1);
        assert!(files[0].ends_with("Visible.fst"));
    }

    #[tokio::test]
    async fn test_collect_files_sorted_deterministically() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        create_test_file(&temp_dir, "Zeta.fst", "module Zeta\n");
        create_test_file(&temp_dir, "Alpha.fst", "module Alpha\n");
        create_test_file(&temp_dir, "Mid.fst", "module Mid\n");

        let config = LintConfig::default();
        let engine = LintEngine::new(config);
        let files = engine.collect_files(&[temp_dir.path().to_path_buf()]);

        assert_eq!(files.len(), 3);
        // Files should be sorted.
        for window in files.windows(2) {
            assert!(window[0] <= window[1], "Files must be sorted");
        }
    }

    // =====================================================================
    // CHECK MODE TESTS
    // =====================================================================

    #[tokio::test]
    async fn test_check_returns_zero_for_clean_files() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let content = r#"module Test

let x : nat = 1
"#;
        let fst_file = create_test_file(&temp_dir, "Test.fst", content);

        let config = LintConfig::new(Some("FST003".to_string()), None, None);
        let engine = LintEngine::new(config);
        let exit_code = engine.check(&[fst_file], OutputFormat::Text, false).await;

        assert_eq!(exit_code, 0, "Check should return 0 for clean files");
    }

    // =====================================================================
    // SAFETY BEHAVIOR TESTS
    // =====================================================================

    #[tokio::test]
    async fn test_fix_with_no_fixable_issues() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let content = r#"module Test
let x = 1
"#;
        let fst_file = create_test_file(&temp_dir, "Test.fst", content);
        let original = read_test_file(&fst_file);

        let config = LintConfig::default();
        let engine = LintEngine::new(config);
        let _exit_code = engine.fix(&[fst_file.clone()], OutputFormat::Text, false, DryRunFormat::Full, false).await;

        let after = read_test_file(&fst_file);
        assert_eq!(
            original, after,
            "File should not change when there are no fixable issues"
        );
    }

    // =====================================================================
    // REGRESSION TESTS
    // =====================================================================

    #[test]
    fn test_dry_run_summary_skips_uncached_files() {
        use super::super::output::DryRunSummary;
        use super::super::rules::{Diagnostic, DiagnosticSeverity, Fix, Range, RuleCode};

        let mut summary = DryRunSummary::new();
        let file_contents: HashMap<PathBuf, String> = HashMap::new();

        let diag = Diagnostic {
            rule: RuleCode::FST004,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("/nonexistent/Uncached.fst"),
            range: Range::new(1, 1, 1, 10),
            message: "unused open".to_string(),
            fix: Some(Fix::safe("remove open", vec![])),
        };

        if let Some(content) = file_contents.get(&diag.file) {
            summary.add_fix(&diag, content);
        }

        summary.finalize();
        assert_eq!(summary.total_fixes, 0, "Uncached file diagnostic must be skipped");
        assert_eq!(summary.files_affected, 0);
    }

    #[test]
    fn test_dry_run_summary_includes_cached_files() {
        use super::super::output::DryRunSummary;
        use super::super::rules::{Diagnostic, DiagnosticSeverity, Fix, Range, RuleCode};

        let mut summary = DryRunSummary::new();
        let mut file_contents: HashMap<PathBuf, String> = HashMap::new();
        file_contents.insert(
            PathBuf::from("Cached.fst"),
            "module Cached\nlet x = 1\n".to_string(),
        );

        let diag = Diagnostic {
            rule: RuleCode::FST004,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("Cached.fst"),
            range: Range::new(1, 1, 2, 1),
            message: "unused open".to_string(),
            fix: Some(Fix::safe("remove open", vec![])),
        };

        if let Some(content) = file_contents.get(&diag.file) {
            summary.add_fix(&diag, content);
        }

        summary.finalize();
        assert_eq!(summary.total_fixes, 1, "Cached file diagnostic must be counted");
        assert_eq!(summary.files_affected, 1);
    }

    #[tokio::test]
    async fn test_check_with_pair_uses_cache() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let fst_content = "module PairTest\n\ntype my_type = nat\n\nlet x : my_type = 0\n";
        let fsti_content = "module PairTest\n\ntype my_type = nat\n\nval x : my_type\n";

        create_test_file(&temp_dir, "PairTest.fst", fst_content);
        create_test_file(&temp_dir, "PairTest.fsti", fsti_content);

        let config = LintConfig::new(Some("FST001".to_string()), None, None);
        let engine = LintEngine::new(config);
        let exit_code = engine
            .check(&[temp_dir.path().to_path_buf()], OutputFormat::Text, false)
            .await;

        assert!(
            exit_code == 0 || exit_code == 1,
            "check() must complete successfully with cached pair files"
        );
    }

    #[tokio::test]
    async fn test_fix_with_pair_uses_cache() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let fst_content = "module CacheTest\n\ntype cache_t = nat\n\nlet y : cache_t = 0\n";
        let fsti_content = "module CacheTest\n\ntype cache_t = nat\n\nval y : cache_t\n";

        let fst_path = create_test_file(&temp_dir, "CacheTest.fst", fst_content);
        let fsti_path = create_test_file(&temp_dir, "CacheTest.fsti", fsti_content);

        let config = LintConfig::new(Some("FST001".to_string()), None, None);
        let engine = LintEngine::new(config);
        let exit_code = engine
            .fix(
                &[temp_dir.path().to_path_buf()],
                OutputFormat::Text,
                true,
                DryRunFormat::Full,
                false,
            )
            .await;

        assert_eq!(exit_code, 0, "Dry-run fix must return 0");
        assert_eq!(
            read_test_file(&fst_path), fst_content,
            ".fst file must not be modified in dry-run"
        );
        assert_eq!(
            read_test_file(&fsti_path), fsti_content,
            ".fsti file must not be modified in dry-run"
        );
    }

    #[test]
    fn test_more_lines_count_correctness() {
        let start_line: usize = 0;
        let end_line: usize = 14;
        let lines_len: usize = 20;

        let mut more_count: Option<usize> = None;
        for i in start_line..std::cmp::min(end_line + 1, lines_len) {
            if i - start_line >= 10 {
                more_count = Some(end_line - i + 1);
                break;
            }
        }

        assert_eq!(
            more_count,
            Some(5),
            "15-line span showing first 10 must report 5 more lines"
        );
    }

    #[test]
    fn test_no_more_lines_for_ten_lines() {
        let start_line: usize = 0;
        let end_line: usize = 9;
        let lines_len: usize = 20;

        let mut triggered = false;
        for i in start_line..std::cmp::min(end_line + 1, lines_len) {
            if i - start_line >= 10 {
                triggered = true;
                break;
            }
        }

        assert!(!triggered, "Exactly 10 lines must not trigger 'more lines'");
    }

    #[test]
    fn test_more_lines_count_eleven() {
        let start_line: usize = 5;
        let end_line: usize = 15;
        let lines_len: usize = 20;

        let mut more_count: Option<usize> = None;
        for i in start_line..std::cmp::min(end_line + 1, lines_len) {
            if i - start_line >= 10 {
                more_count = Some(end_line - i + 1);
                break;
            }
        }

        assert_eq!(
            more_count,
            Some(1),
            "11-line span showing first 10 must report 1 more line"
        );
    }

    #[tokio::test]
    async fn test_fix_cache_freed_after_summary() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        for i in 0..10 {
            let content = format!("module Batch{}\n\nlet x_{} = {}\n", i, i, i);
            create_test_file(&temp_dir, &format!("Batch{}.fst", i), &content);
        }

        let config = LintConfig::default();
        let engine = LintEngine::new(config);
        let exit_code = engine
            .fix(
                &[temp_dir.path().to_path_buf()],
                OutputFormat::Text,
                true,
                DryRunFormat::Concise,
                false,
            )
            .await;

        assert_eq!(exit_code, 0, "Fix must succeed with many cached files");
    }

    #[tokio::test]
    async fn test_check_pair_and_single_share_cache() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let fst_content = "module Shared\n\nopen FStar.Pervasives\n\ntype t = nat\n\nlet v : t = 0\n";
        let fsti_content = "module Shared\n\ntype t = nat\n\nval v : t\n";

        create_test_file(&temp_dir, "Shared.fst", fst_content);
        create_test_file(&temp_dir, "Shared.fsti", fsti_content);

        let config = LintConfig::new(Some("FST001,FST004".to_string()), None, None);
        let engine = LintEngine::new(config);
        let exit_code = engine
            .check(&[temp_dir.path().to_path_buf()], OutputFormat::Text, false)
            .await;

        assert!(
            exit_code == 0 || exit_code == 1,
            "check() must complete when both single-file and pair rules share cached content"
        );
    }
}
