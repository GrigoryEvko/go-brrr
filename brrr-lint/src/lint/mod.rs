//! F* linting infrastructure.

mod comments;
mod dead_code;
mod doc_checker;
mod duplicate_types;
mod effect_checker;
mod engine;
pub mod file_safety;
mod fstar_traps;
pub mod fix_applicator;
pub mod fix_validator;
mod import_optimizer;
mod lowstar;
pub mod lsp;
mod module_deps;
mod naming;
mod output;
pub mod parser;
mod perf_profiler;
mod proof_hints;
mod refinement_simplifier;
mod reorder_interface;
pub mod revert;
mod rules;
mod security;
pub(crate) mod shared_patterns;
mod spec_extractor;
mod test_generator;
mod unused_opens;
mod z3_complexity;

pub use comments::CommentRule;
pub use dead_code::DeadCodeRule;
pub use doc_checker::DocCheckerRule;
pub use duplicate_types::DuplicateTypesRule;
pub use effect_checker::{Effect, EffectCheckerRule};
pub use engine::{LintConfig, LintEngine};
pub use fstar_traps::{
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
pub use import_optimizer::ImportOptimizerRule;
pub use module_deps::{
    ModuleDepsRule, ModuleDeps, DependencyGraph, GraphNode, LayerViolation,
    ModuleLayer, classify_layer, extract_dependencies, detect_self_dependency,
    resolve_module_path, build_module_file_map,
};
pub use naming::NamingRule;
pub use output::{
    ColorMode, init_color,
    DryRunFormat, DryRunSummary, FixPreview, OutputFormat,
    print_apply_header, print_dry_run, print_dry_run_header,
    print_fixes_applied, print_no_fixes_message,
};
pub use parser::{
    parse_fstar_file, BlockType, DeclarationBlock, EffectSignature,
    extract_module_construct_info, extract_effect_signature,
    is_standalone_modifier, detect_visibility_modifiers,
    MachineIntType, LowStarBufferType, is_lowstar_module, extract_module_aliases,
};
pub use perf_profiler::PerfProfilerRule;
pub use proof_hints::ProofHintsRule;
pub use refinement_simplifier::RefinementSimplifierRule;
pub use reorder_interface::ReorderInterfaceRule;
pub use rules::{
    print_rules, DeadCodeSafetyLevel, Diagnostic, DiagnosticSeverity, Edit, Fix, FixConfidence,
    Range, Rule, RuleCode,
};
pub use lowstar::{LowStarBufferRule, LowStarPerfRule};
pub use security::SecurityRule;
pub use spec_extractor::SpecExtractorRule;
pub use test_generator::TestGeneratorRule;
pub use unused_opens::UnusedOpensRule;
pub use z3_complexity::Z3ComplexityRule;

// Fix validation exports
pub use fix_validator::{
    content_hash, count_declarations, find_undefined_references, validate_expected_removals,
    validate_fix, validate_fstar_syntax, validate_line_deletion, validate_no_removals,
    validate_whitespace_only_fix, DeclarationChanges, FixValidation,
};

// Fix applicator exports
pub use fix_applicator::{
    AppliedFix, CommitError, ConsoleProgressReporter, FixApplicator, FixApplicatorConfig,
    FixChainConfig, FixError, FixSummary, InteractiveChoice, InteractivePrompt,
    MultiFileFixGroup, ProgressReporter, RollbackError, StdinInteractivePrompt,
    determine_confidence,
};

// Revert exports
pub use revert::{
    format_size, print_backup_details, print_revert_result, print_timestamp_list,
    print_timestamp_list_with_points, print_cleanup_summary, print_backup_summary_line,
    cleanup_old_backups, parse_duration_str, gather_backup_summary,
    BackupEntry, BackupMetadata, BackupDirectoryMetadata, BackupSummaryInfo,
    CleanupSummary, RevertConfig, RevertEngine, RevertError, RevertPoint,
    RevertResult_, TimestampSummary,
    load_metadata, save_metadata, record_backup_in_metadata,
};
