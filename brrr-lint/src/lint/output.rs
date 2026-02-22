//! Output formatting for lint diagnostics.
//!
//! Provides multiple output formats for the F* linter:
//! - **Text**: Human-readable with optional color, width-aware wrapping
//! - **Concise**: One-line-per-diagnostic for editors/scripts
//! - **JSON**: Machine-readable with full fix info
//! - **SARIF 2.1.0**: Static Analysis Results Interchange Format
//! - **GitHub**: `::warning` / `::error` annotation format for GitHub Actions
//!
//! Color support respects `NO_COLOR`, `FORCE_COLOR`, and terminal detection.
//! Diff-style fix previews use box-drawing characters for clean output.

use super::rules::{Diagnostic, DiagnosticSeverity, Fix, FixConfidence, RuleCode};
use clap::ValueEnum;
use serde::Serialize;
use std::collections::HashMap;
use std::io::{self, IsTerminal, Write};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Truncate a string to at most `max_bytes` bytes without splitting a
/// multi-byte UTF-8 character. Returns a sub-slice that is always valid UTF-8
/// and whose length in bytes is <= `max_bytes`.
fn safe_truncate(s: &str, max_bytes: usize) -> &str {
    if s.len() <= max_bytes {
        return s;
    }
    let mut end = max_bytes;
    while end > 0 && !s.is_char_boundary(end) {
        end -= 1;
    }
    &s[..end]
}

// ============================================================================
// TERMINAL WIDTH
// ============================================================================

/// Detect the terminal width from the environment.
///
/// Checks `COLUMNS` env var first, then falls back to 80.
/// This avoids pulling in external crates for a simple query.
fn terminal_width() -> usize {
    if let Ok(cols) = std::env::var("COLUMNS") {
        if let Ok(w) = cols.parse::<usize>() {
            if w > 0 {
                return w;
            }
        }
    }
    80
}

/// Wrap a string to fit within `width` columns.
///
/// Breaks on whitespace boundaries when possible. Lines that contain no
/// whitespace are hard-broken at `width`. Each continuation line is prefixed
/// with `indent`.
fn wrap_text(text: &str, width: usize, indent: &str) -> String {
    if text.len() <= width {
        return text.to_string();
    }

    let effective_width = width.saturating_sub(indent.len());
    if effective_width == 0 {
        return text.to_string();
    }

    let mut result = String::with_capacity(text.len() + text.len() / width * indent.len());
    let mut first_line = true;

    for line in text.lines() {
        if !first_line {
            result.push('\n');
        }
        first_line = false;

        let line_width = if result.is_empty() { width } else { effective_width };
        if line.len() <= line_width {
            if !result.is_empty() && result.ends_with('\n') {
                result.push_str(indent);
            }
            result.push_str(line);
            continue;
        }

        let mut remaining = line;
        let mut first_chunk = true;
        while !remaining.is_empty() {
            let chunk_width = if first_chunk { width } else { effective_width };
            if !first_chunk {
                result.push('\n');
                result.push_str(indent);
            }
            first_chunk = false;

            if remaining.len() <= chunk_width {
                result.push_str(remaining);
                break;
            }

            // Find last whitespace before chunk_width.
            // Clamp chunk_width to a char boundary to avoid panics on
            // multi-byte UTF-8 characters.
            let mut safe_width = chunk_width;
            while safe_width > 0 && !remaining.is_char_boundary(safe_width) {
                safe_width -= 1;
            }
            let break_at = remaining[..safe_width]
                .rfind(char::is_whitespace)
                .map(|pos| pos + 1)
                .unwrap_or(safe_width);

            result.push_str(&remaining[..break_at]);
            remaining = remaining[break_at..].trim_start();
        }
    }

    result
}

// ============================================================================
// COLOR CONFIGURATION
// ============================================================================

/// Controls when ANSI color codes are emitted.
#[derive(Debug, Clone, Copy, ValueEnum, Default)]
pub enum ColorMode {
    /// Detect automatically: enable color when stdout is a terminal,
    /// `NO_COLOR` is not set, and `FORCE_COLOR` is not overriding.
    #[default]
    Auto,
    /// Always emit ANSI color codes, even when piped.
    Always,
    /// Never emit ANSI color codes.
    Never,
}

/// Holds the resolved color-enabled flag and provides accessor methods
/// that return either the real ANSI escape sequence or an empty string.
#[derive(Debug, Clone, Copy)]
pub struct ColorConfig {
    enabled: bool,
}

impl ColorConfig {
    /// Resolve a `ColorMode` into a concrete on/off decision.
    ///
    /// Precedence (highest to lowest):
    /// 1. `ColorMode::Always` / `ColorMode::Never` (explicit CLI flag)
    /// 2. `FORCE_COLOR` env var (non-empty = force on)
    /// 3. `NO_COLOR` env var (any value = force off)
    /// 4. TTY detection via `isatty(stdout)`
    pub fn from_mode(mode: ColorMode) -> Self {
        let enabled = match mode {
            ColorMode::Always => true,
            ColorMode::Never => false,
            ColorMode::Auto => {
                // FORCE_COLOR overrides everything in auto mode
                if let Ok(val) = std::env::var("FORCE_COLOR") {
                    if !val.is_empty() && val != "0" {
                        return Self { enabled: true };
                    }
                }
                // NO_COLOR disables when present (any value, even empty)
                if std::env::var_os("NO_COLOR").is_some() {
                    return Self { enabled: false };
                }
                io::stdout().is_terminal()
            }
        };
        Self { enabled }
    }

    /// Shorthand for `from_mode(ColorMode::Auto)`.
    pub fn auto() -> Self {
        Self::from_mode(ColorMode::Auto)
    }

    /// Whether color output is enabled.
    #[allow(dead_code)]
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    // -- style modifiers --
    pub fn reset(&self) -> &'static str { if self.enabled { "\x1b[0m" } else { "" } }
    pub fn bold(&self) -> &'static str { if self.enabled { "\x1b[1m" } else { "" } }
    pub fn dim(&self) -> &'static str { if self.enabled { "\x1b[2m" } else { "" } }
    #[allow(dead_code)]
    pub fn underline(&self) -> &'static str { if self.enabled { "\x1b[4m" } else { "" } }

    // -- standard foreground --
    pub fn red(&self) -> &'static str { if self.enabled { "\x1b[31m" } else { "" } }
    pub fn green(&self) -> &'static str { if self.enabled { "\x1b[32m" } else { "" } }
    pub fn yellow(&self) -> &'static str { if self.enabled { "\x1b[33m" } else { "" } }
    #[allow(dead_code)]
    pub fn blue(&self) -> &'static str { if self.enabled { "\x1b[34m" } else { "" } }
    pub fn cyan(&self) -> &'static str { if self.enabled { "\x1b[36m" } else { "" } }
    pub fn gray(&self) -> &'static str { if self.enabled { "\x1b[90m" } else { "" } }

    // -- bright foreground --
    pub fn bright_red(&self) -> &'static str { if self.enabled { "\x1b[91m" } else { "" } }
    pub fn bright_green(&self) -> &'static str { if self.enabled { "\x1b[92m" } else { "" } }
    pub fn bright_yellow(&self) -> &'static str { if self.enabled { "\x1b[93m" } else { "" } }
    pub fn bright_cyan(&self) -> &'static str { if self.enabled { "\x1b[96m" } else { "" } }
}

/// Process-wide color configuration, initialized once at startup.
static COLOR: OnceLock<ColorConfig> = OnceLock::new();

/// Set the global color mode. Call this once from `main` before any output.
/// Subsequent calls are ignored (first write wins).
pub fn init_color(mode: ColorMode) {
    let _ = COLOR.set(ColorConfig::from_mode(mode));
}

/// Return the active `ColorConfig`, falling back to auto-detection if
/// `init_color` was never called.
pub fn color_config() -> &'static ColorConfig {
    COLOR.get_or_init(ColorConfig::auto)
}

// ============================================================================
// OUTPUT FORMAT ENUM
// ============================================================================

/// Output format for lint results.
#[derive(Debug, Clone, Copy, ValueEnum, Default)]
pub enum OutputFormat {
    /// Human-readable text output with color and width-aware wrapping.
    #[default]
    Text,
    /// Concise one-line-per-diagnostic format.
    Concise,
    /// Grouped by rule code with counts and example locations.
    /// Designed for LLM/hook contexts where per-diagnostic noise is wasteful.
    Grouped,
    /// JSON output with full fix info for machine consumption.
    Json,
    /// GitHub Actions annotation format (`::warning`, `::error`).
    Github,
    /// SARIF 2.1.0 (Static Analysis Results Interchange Format).
    Sarif,
}

/// Dry-run output format for showing what changes would be made.
#[derive(Debug, Clone, Copy, ValueEnum, Default)]
pub enum DryRunFormat {
    /// Concise: Just list files and fix counts per rule.
    Concise,
    /// Full: Show all changes with unified diff-style output (default).
    #[default]
    Full,
    /// JSON: Machine-readable output for tooling integration.
    Json,
}

// ============================================================================
// SUMMARY STATISTICS
// ============================================================================

/// Summary statistics for a lint run.
#[derive(Debug, Default)]
pub struct LintSummary {
    #[allow(dead_code)]
    pub files_checked: usize,
    #[allow(dead_code)]
    pub files_with_issues: usize,
    pub total_diagnostics: usize,
    pub fixable_diagnostics: usize,
    pub errors: usize,
    pub warnings: usize,
    pub infos: usize,
    pub hints: usize,
    pub by_rule: HashMap<RuleCode, usize>,
}

impl LintSummary {
    pub fn add_diagnostic(&mut self, diag: &Diagnostic) {
        self.total_diagnostics += 1;
        if diag.fix.is_some() {
            self.fixable_diagnostics += 1;
        }
        match diag.severity {
            DiagnosticSeverity::Error => self.errors += 1,
            DiagnosticSeverity::Warning => self.warnings += 1,
            DiagnosticSeverity::Info => self.infos += 1,
            DiagnosticSeverity::Hint => self.hints += 1,
        }
        *self.by_rule.entry(diag.rule).or_insert(0) += 1;
    }
}

// ============================================================================
// RULE METADATA (why / how-to-fix)
// ============================================================================

/// Return a short explanation of *why* this rule exists.
fn rule_why(code: RuleCode) -> &'static str {
    match code {
        RuleCode::FST001 => "Duplicate type definitions cause maintenance confusion and potential inconsistencies between .fst and .fsti files.",
        RuleCode::FST002 => "Interface/implementation mismatches cause F* Error 233 and subtle type-checking failures.",
        RuleCode::FST003 => "Comment syntax issues can silently change parsing behavior: (*) is unit, (-*) is magic wand.",
        RuleCode::FST004 => "Unused opens slow compilation and obscure actual dependencies.",
        RuleCode::FST005 => "Dead code increases maintenance burden and may indicate logical errors.",
        RuleCode::FST006 => "Inconsistent naming makes code harder to read and breaks ecosystem conventions.",
        RuleCode::FST007 => "Z3 complexity patterns cause exponential slowdowns in verification.",
        RuleCode::FST008 => "Broad/circular imports increase build times and coupling between modules.",
        RuleCode::FST009 => "Missing proof hints force Z3 to search harder, slowing verification.",
        RuleCode::FST010 => "Missing interface files prevent separate compilation and encapsulation.",
        RuleCode::FST011 => "Effects like admit/magic bypass the verifier, weakening guarantees.",
        RuleCode::FST012 => "Redundant refinements add noise and may confuse the SMT solver.",
        RuleCode::FST013 => "Missing documentation on public APIs makes the codebase harder to use.",
        RuleCode::FST014 => "Test suggestions help ensure boundary conditions are covered.",
        RuleCode::FST015 => "Excessive module dependencies increase compilation time and fragility.",
        RuleCode::FST016 => "High fuel/rlimit values indicate fragile proofs that may break under changes.",
        RuleCode::FST017 => "Hardcoded secrets and timing-dependent branches compromise cryptographic code.",
        RuleCode::FST018 => "Unmatched push/pop frames and missing liveness predicates cause memory safety issues in extracted C.",
        RuleCode::FST019 => "LowStar performance anti-patterns slow verification of memory-safe C code.",
    }
}

/// Return a short instruction on how to fix the issue.
fn rule_how_to_fix(code: RuleCode) -> &'static str {
    match code {
        RuleCode::FST001 => "Remove the duplicate type definition from the .fst file; keep it only in .fsti.",
        RuleCode::FST002 => "Align declaration order, qualifiers, and signatures between .fst and .fsti files.",
        RuleCode::FST003 => "Ensure all comments are properly opened and closed. Replace (*) with (* *) if a comment is intended.",
        RuleCode::FST004 => "Remove the unused `open` statement or replace with a selective import.",
        RuleCode::FST005 => "Remove unused bindings, or prefix with _ if intentionally unused.",
        RuleCode::FST006 => "Rename to follow F* conventions: snake_case for values, CamelCase for types/constructors.",
        RuleCode::FST007 => "Add SMTPat triggers to quantifiers, reduce z3rlimit, add decreases clauses.",
        RuleCode::FST008 => "Replace broad `open` with selective imports; break circular dependencies.",
        RuleCode::FST009 => "Add the suggested lemma call or SMTPat annotation before the proof obligation.",
        RuleCode::FST010 => "Create a .fsti file with `val` declarations for public definitions.",
        RuleCode::FST011 => "Replace admit() with a real proof; use Ghost effect instead of ML where possible.",
        RuleCode::FST012 => "Simplify the refinement type or promote to a more specific base type.",
        RuleCode::FST013 => "Add a doc-comment (** ... *) above the public declaration.",
        RuleCode::FST014 => "Add the suggested test cases to verify boundary conditions.",
        RuleCode::FST015 => "Reduce module dependencies by splitting large modules or using interfaces.",
        RuleCode::FST016 => "Reduce fuel/ifuel/z3rlimit; add intermediate assertions to guide the solver.",
        RuleCode::FST017 => "Move secrets to configuration; use constant-time comparison functions.",
        RuleCode::FST018 => "Add matching pop_frame for push_frame; add live/modifies predicates.",
        RuleCode::FST019 => "Factor modifies clauses; reduce ST.get calls; add inline_for_extraction.",
    }
}

// ============================================================================
// DRY-RUN OUTPUT FORMATTING
// ============================================================================

/// Box drawing characters for beautiful terminal UI.
mod box_chars {
    // Heavy box drawing (for headers)
    pub const H_DOUBLE_TOP_LEFT: &str = "\u{2554}";     // ╔
    pub const H_DOUBLE_TOP_RIGHT: &str = "\u{2557}";    // ╗
    pub const H_DOUBLE_BOTTOM_LEFT: &str = "\u{255a}";  // ╚
    pub const H_DOUBLE_BOTTOM_RIGHT: &str = "\u{255d}"; // ╝
    pub const H_DOUBLE_HORIZONTAL: &str = "\u{2550}";   // ═
    pub const H_DOUBLE_VERTICAL: &str = "\u{2551}";     // ║

    // Light box drawing (for content)
    pub const TOP_LEFT: &str = "\u{256d}";      // ╭
    pub const TOP_RIGHT: &str = "\u{256e}";     // ╮
    pub const BOTTOM_LEFT: &str = "\u{2570}";   // ╰
    pub const BOTTOM_RIGHT: &str = "\u{256f}";  // ╯
    pub const HORIZONTAL: &str = "\u{2500}";    // ─
    pub const VERTICAL: &str = "\u{2502}";      // │
    pub const VERTICAL_RIGHT: &str = "\u{251c}"; // ├
    pub const VERTICAL_LEFT: &str = "\u{2524}"; // ┤

    // Diff indicators
    pub const CHECK: &str = "\u{2713}";         // ✓
    pub const CROSS: &str = "\u{2717}";         // ✗
    pub const WARNING: &str = "\u{26a0}";       // ⚠
    pub const INFO: &str = "\u{2139}";          // ℹ
}

/// Summary statistics for dry-run output.
#[derive(Debug, Default)]
pub struct DryRunSummary {
    /// Total files that would be affected.
    pub files_affected: usize,
    /// Total fixes that would be applied.
    pub total_fixes: usize,
    /// Fixes that are safe to auto-apply (high confidence).
    pub safe_fixes: usize,
    /// Fixes that require manual review (medium/low confidence).
    pub review_required: usize,
    /// Fixes by rule code.
    pub by_rule: HashMap<RuleCode, usize>,
    /// Fixes by file.
    pub by_file: HashMap<PathBuf, Vec<FixPreview>>,
    /// Lines that would be removed.
    pub lines_removed: usize,
    /// Lines that would be added.
    pub lines_added: usize,
}

/// A preview of a single fix that would be applied.
#[derive(Debug, Clone)]
pub struct FixPreview {
    /// The rule that produced this fix.
    pub rule: RuleCode,
    /// Human-readable message about what the fix does.
    pub message: String,
    /// Lines affected (start, end) - 1-indexed.
    pub line_range: (usize, usize),
    /// Content that would be removed (if any).
    pub removed_content: Option<String>,
    /// Content that would be added (if any).
    pub new_content: Option<String>,
    /// Confidence level of the fix.
    pub confidence: FixConfidence,
    /// Whether the fix is safe to auto-apply.
    pub is_safe: bool,
    /// Reason if unsafe.
    pub unsafe_reason: Option<String>,
}

impl DryRunSummary {
    /// Create a new dry-run summary.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a diagnostic with fix to the summary.
    pub fn add_fix(&mut self, diag: &Diagnostic, original_content: &str) {
        if let Some(fix) = &diag.fix {
            self.total_fixes += 1;

            if fix.is_safe() && fix.confidence == FixConfidence::High {
                self.safe_fixes += 1;
            } else {
                self.review_required += 1;
            }

            *self.by_rule.entry(diag.rule).or_insert(0) += 1;

            let preview = create_fix_preview(diag, fix, original_content);

            if let Some(removed) = &preview.removed_content {
                self.lines_removed += removed.lines().count();
            }
            if let Some(added) = &preview.new_content {
                self.lines_added += added.lines().count();
            }

            self.by_file
                .entry(diag.file.clone())
                .or_default()
                .push(preview);
        }
    }

    /// Finalize the summary (calculate derived values).
    pub fn finalize(&mut self) {
        self.files_affected = self.by_file.len();
    }
}

/// Create a fix preview from a diagnostic.
///
/// Uses the first edit's range (not the diagnostic range) to extract removed
/// content, because the edit range describes exactly which lines will be
/// replaced while the diagnostic range may cover a broader context.
fn create_fix_preview(diag: &Diagnostic, fix: &Fix, original_content: &str) -> FixPreview {
    let lines: Vec<&str> = original_content.lines().collect();

    let (edit_start_line, edit_end_line) = if !fix.edits.is_empty() {
        (fix.edits[0].range.start_line, fix.edits[0].range.end_line)
    } else {
        (diag.range.start_line, diag.range.end_line)
    };

    let start_line = edit_start_line.saturating_sub(1);
    let end_line = edit_end_line.saturating_sub(1);

    let removed_content = if start_line < lines.len() {
        let end = std::cmp::min(end_line + 1, lines.len());
        Some(lines[start_line..end].join("\n"))
    } else {
        None
    };

    let new_content = if !fix.edits.is_empty() {
        let text = &fix.edits[0].new_text;
        if text.is_empty() {
            None
        } else {
            Some(text.clone())
        }
    } else {
        None
    };

    FixPreview {
        rule: diag.rule,
        message: fix.message.clone(),
        line_range: (diag.range.start_line, diag.range.end_line),
        removed_content,
        new_content,
        confidence: fix.confidence,
        is_safe: fix.is_safe(),
        unsafe_reason: fix.unsafe_reason.clone(),
    }
}

// ============================================================================
// DRY-RUN FORMATTERS
// ============================================================================

/// Print the dry-run header banner.
pub fn print_dry_run_header<W: Write>(w: &mut W) -> io::Result<()> {
    use box_chars::*;
    let c = color_config();
    let bold = c.bold();
    let bright_yellow = c.bright_yellow();
    let yellow = c.yellow();
    let reset = c.reset();

    let message = " DRY RUN - No files will be modified. Use --apply to write changes ";
    let width = message.len() + 2;

    writeln!(w)?;
    writeln!(
        w,
        "{bold}{bright_yellow}{H_DOUBLE_TOP_LEFT}{}{H_DOUBLE_TOP_RIGHT}{reset}",
        H_DOUBLE_HORIZONTAL.repeat(width)
    )?;
    writeln!(
        w,
        "{bold}{bright_yellow}{H_DOUBLE_VERTICAL}{reset} {bold}{yellow}{message}{reset} {bold}{bright_yellow}{H_DOUBLE_VERTICAL}{reset}"
    )?;
    writeln!(
        w,
        "{bold}{bright_yellow}{H_DOUBLE_BOTTOM_LEFT}{}{H_DOUBLE_BOTTOM_RIGHT}{reset}",
        H_DOUBLE_HORIZONTAL.repeat(width)
    )?;
    writeln!(w)?;

    Ok(())
}

/// Print the apply mode header banner (when actually writing changes).
pub fn print_apply_header<W: Write>(w: &mut W) -> io::Result<()> {
    use box_chars::*;
    let c = color_config();
    let bold = c.bold();
    let bright_red = c.bright_red();
    let red = c.red();
    let reset = c.reset();

    let message = " APPLYING CHANGES - Files will be modified! ";
    let width = message.len() + 2;

    writeln!(w)?;
    writeln!(
        w,
        "{bold}{bright_red}{H_DOUBLE_TOP_LEFT}{}{H_DOUBLE_TOP_RIGHT}{reset}",
        H_DOUBLE_HORIZONTAL.repeat(width)
    )?;
    writeln!(
        w,
        "{bold}{bright_red}{H_DOUBLE_VERTICAL}{reset} {bold}{red}{message}{reset} {bold}{bright_red}{H_DOUBLE_VERTICAL}{reset}"
    )?;
    writeln!(
        w,
        "{bold}{bright_red}{H_DOUBLE_BOTTOM_LEFT}{}{H_DOUBLE_BOTTOM_RIGHT}{reset}",
        H_DOUBLE_HORIZONTAL.repeat(width)
    )?;
    writeln!(w)?;

    Ok(())
}

/// Print a single fix preview in full diff-style format.
pub fn print_fix_preview_full<W: Write>(
    w: &mut W,
    file: &Path,
    preview: &FixPreview,
) -> io::Result<()> {
    use box_chars::*;
    let c = color_config();
    let bold = c.bold();
    let dim = c.dim();
    let red = c.red();
    let green = c.green();
    let yellow = c.yellow();
    let cyan = c.cyan();
    let bright_cyan = c.bright_cyan();
    let reset = c.reset();

    let rule_line = format!("{}: {}", preview.rule, preview.rule.name());
    let tw = terminal_width();
    let max_width = tw.clamp(40, 100);
    let content_width = max_width.saturating_sub(6); // 2 indent + 2 border + 2 padding

    // File header
    writeln!(w, "{bold}{cyan}File: {}{reset}", file.display())?;

    // Fix box header
    writeln!(
        w,
        "  {dim}{TOP_LEFT}{}{TOP_RIGHT}{reset}",
        HORIZONTAL.repeat(max_width - 4)
    )?;

    // Rule info
    writeln!(
        w,
        "  {dim}{VERTICAL}{reset} {bright_cyan}{rule_line}{reset}"
    )?;

    // Line range
    let line_info = format!("Lines {}-{}", preview.line_range.0, preview.line_range.1);
    writeln!(
        w,
        "  {dim}{VERTICAL}{reset} {dim}{line_info}{reset}"
    )?;

    // Confidence indicator
    let confidence_str = match preview.confidence {
        FixConfidence::High => format!("{green}{CHECK} HIGH confidence{reset}"),
        FixConfidence::Medium => format!("{yellow}{WARNING} MEDIUM confidence{reset}"),
        FixConfidence::Low => format!("{red}{CROSS} LOW confidence{reset}"),
    };
    writeln!(w, "  {dim}{VERTICAL}{reset} {confidence_str}")?;

    // Safety indicator
    if preview.is_safe {
        writeln!(
            w,
            "  {dim}{VERTICAL}{reset} {green}Safe to auto-apply{reset}"
        )?;
    } else {
        writeln!(
            w,
            "  {dim}{VERTICAL}{reset} {red}Requires review{reset}"
        )?;
        if let Some(reason) = &preview.unsafe_reason {
            writeln!(
                w,
                "  {dim}{VERTICAL}{reset}   {dim}Reason: {reason}{reset}"
            )?;
        }
    }

    // Separator
    writeln!(
        w,
        "  {dim}{VERTICAL_RIGHT}{}{VERTICAL_LEFT}{reset}",
        HORIZONTAL.repeat(max_width - 4)
    )?;

    // Show removed content (diff style)
    if let Some(removed) = &preview.removed_content {
        writeln!(w, "  {dim}{VERTICAL}{reset}")?;
        for (i, line) in removed.lines().take(15).enumerate() {
            let line_num = preview.line_range.0 + i;
            let display_line = if line.len() > content_width {
                format!("{}...", safe_truncate(line, content_width.saturating_sub(3)))
            } else {
                line.to_string()
            };
            writeln!(
                w,
                "  {dim}{VERTICAL}{reset} {red}-{line_num:>4} {VERTICAL}{reset} {red}{display_line}{reset}"
            )?;
        }
        let total_lines = removed.lines().count();
        if total_lines > 15 {
            writeln!(
                w,
                "  {dim}{VERTICAL}{reset} {red}  ... ({} more lines){reset}",
                total_lines - 15
            )?;
        }
    }

    // Show added content (diff style)
    if let Some(added) = &preview.new_content {
        writeln!(w, "  {dim}{VERTICAL}{reset}")?;
        for (i, line) in added.lines().take(15).enumerate() {
            let line_num = preview.line_range.0 + i;
            let display_line = if line.len() > content_width {
                format!("{}...", safe_truncate(line, content_width.saturating_sub(3)))
            } else {
                line.to_string()
            };
            writeln!(
                w,
                "  {dim}{VERTICAL}{reset} {green}+{line_num:>4} {VERTICAL}{reset} {green}{display_line}{reset}"
            )?;
        }
        let total_lines = added.lines().count();
        if total_lines > 15 {
            writeln!(
                w,
                "  {dim}{VERTICAL}{reset} {green}  ... ({} more lines){reset}",
                total_lines - 15
            )?;
        }
    } else if preview.removed_content.is_some() {
        writeln!(w, "  {dim}{VERTICAL}{reset}")?;
        writeln!(
            w,
            "  {dim}{VERTICAL}{reset} {yellow}{INFO} Lines will be deleted (no replacement){reset}"
        )?;
    }

    // Box footer
    writeln!(
        w,
        "  {dim}{BOTTOM_LEFT}{}{BOTTOM_RIGHT}{reset}",
        HORIZONTAL.repeat(max_width - 4)
    )?;
    writeln!(w)?;

    Ok(())
}

/// Print a single fix in concise format.
pub fn print_fix_preview_concise<W: Write>(
    w: &mut W,
    file: &Path,
    preview: &FixPreview,
) -> io::Result<()> {
    let c = color_config();
    let red = c.red();
    let green = c.green();
    let yellow = c.yellow();
    let reset = c.reset();

    let confidence_marker = match preview.confidence {
        FixConfidence::High => format!("{green}[H]{reset}"),
        FixConfidence::Medium => format!("{yellow}[M]{reset}"),
        FixConfidence::Low => format!("{red}[L]{reset}"),
    };

    let safe_marker = if preview.is_safe {
        format!("{green}*{reset}")
    } else {
        format!("{red}!{reset}")
    };

    writeln!(
        w,
        "{safe_marker} {}:{}-{} {} {confidence_marker} {}",
        file.display(),
        preview.line_range.0,
        preview.line_range.1,
        preview.rule,
        preview.message
    )?;

    Ok(())
}

/// Print the dry-run summary.
///
/// Uses a fixed box width of 60 display columns. All inner content lines are
/// padded to exactly `width - 2` visible characters so that the left and right
/// box borders align consistently.
pub fn print_dry_run_summary<W: Write>(w: &mut W, summary: &DryRunSummary) -> io::Result<()> {
    use box_chars::*;
    let c = color_config();
    let bold = c.bold();
    let dim = c.dim();
    let red = c.red();
    let green = c.green();
    let yellow = c.yellow();
    let cyan = c.cyan();
    let reset = c.reset();

    let width: usize = 60;
    let inner: usize = width - 2;

    /// Pad `visible_text` with trailing spaces so its total visible length
    /// equals `target`.
    fn pad_to(visible_text: &str, target: usize) -> String {
        let len = visible_text.len();
        if len >= target {
            visible_text.to_string()
        } else {
            format!("{}{}", visible_text, " ".repeat(target - len))
        }
    }

    writeln!(w)?;
    writeln!(
        w,
        "{bold}{TOP_LEFT}{}{TOP_RIGHT}{reset}",
        HORIZONTAL.repeat(inner)
    )?;
    let header = pad_to(" Summary", inner);
    writeln!(
        w,
        "{bold}{VERTICAL}{header}{VERTICAL}{reset}"
    )?;
    writeln!(
        w,
        "{VERTICAL_RIGHT}{}{VERTICAL_LEFT}",
        HORIZONTAL.repeat(inner)
    )?;

    let stat_lines: Vec<(String, &str, &str)> = vec![
        (format!(" Files affected:    {:>6}", summary.files_affected), bold, cyan),
        (format!(" Total fixes:       {:>6}", summary.total_fixes), bold, ""),
        (format!(" Safe to apply:     {:>6}", summary.safe_fixes), bold, green),
        (format!(" Requires review:   {:>6}", summary.review_required), bold, yellow),
        (format!(" Lines removed:     {:>6}", summary.lines_removed), "", red),
        (format!(" Lines added:       {:>6}", summary.lines_added), "", green),
    ];

    for (text, weight, color) in &stat_lines {
        let padded = pad_to(text, inner);
        writeln!(
            w,
            "{dim}{VERTICAL}{reset}{weight}{color}{padded}{reset}{dim}{VERTICAL}{reset}"
        )?;
    }

    if !summary.by_rule.is_empty() {
        writeln!(
            w,
            "{VERTICAL_RIGHT}{}{VERTICAL_LEFT}",
            HORIZONTAL.repeat(inner)
        )?;
        let section_header = pad_to(" Fixes by rule:", inner);
        writeln!(
            w,
            "{dim}{VERTICAL}{reset} {dim}{section_header}{reset}{dim}{VERTICAL}{reset}"
        )?;

        let mut rules: Vec<_> = summary.by_rule.iter().collect();
        rules.sort_by(|a, b| b.1.cmp(a.1));

        for (rule, count) in rules.iter().take(10) {
            let rule_line = format!("   {:<8} {:<20} {:>5}", rule, rule.name(), count);
            let padded = pad_to(&rule_line, inner);
            writeln!(
                w,
                "{dim}{VERTICAL}{reset}{cyan}{padded}{reset}{dim}{VERTICAL}{reset}"
            )?;
        }
        if rules.len() > 10 {
            let more_line = format!("   ... and {} more rules", rules.len() - 10);
            let padded = pad_to(&more_line, inner);
            writeln!(
                w,
                "{dim}{VERTICAL}{reset}{dim}{padded}{reset}{dim}{VERTICAL}{reset}"
            )?;
        }
    }

    writeln!(
        w,
        "{BOTTOM_LEFT}{}{BOTTOM_RIGHT}",
        HORIZONTAL.repeat(inner)
    )?;

    Ok(())
}

/// Print instructions for applying changes.
pub fn print_apply_instructions<W: Write>(w: &mut W, command_hint: &str) -> io::Result<()> {
    let c = color_config();
    let bold = c.bold();
    let bright_green = c.bright_green();
    let reset = c.reset();

    writeln!(w)?;
    writeln!(
        w,
        "{bold}To apply these changes, run:{reset}"
    )?;
    writeln!(
        w,
        "  {bright_green}{command_hint}{reset}"
    )?;
    writeln!(w)?;

    Ok(())
}

/// Print all dry-run output in full format.
pub fn print_dry_run_full(summary: &DryRunSummary) -> io::Result<()> {
    let stdout = io::stdout();
    let mut handle = stdout.lock();

    print_dry_run_header(&mut handle)?;

    for (file, previews) in &summary.by_file {
        for preview in previews {
            print_fix_preview_full(&mut handle, file, preview)?;
        }
    }

    print_dry_run_summary(&mut handle, summary)?;
    print_apply_instructions(&mut handle, "fstar-lsp fix <path> --apply")?;

    Ok(())
}

/// Print all dry-run output in concise format.
pub fn print_dry_run_concise(summary: &DryRunSummary) -> io::Result<()> {
    let c = color_config();
    let bold = c.bold();
    let dim = c.dim();
    let green = c.green();
    let yellow = c.yellow();
    let cyan = c.cyan();
    let bright_green = c.bright_green();
    let reset = c.reset();

    let stdout = io::stdout();
    let mut handle = stdout.lock();

    writeln!(handle)?;
    writeln!(
        handle,
        "{bold}{yellow}DRY RUN{reset} - No files will be modified"
    )?;
    writeln!(handle)?;

    for (file, previews) in &summary.by_file {
        for preview in previews {
            print_fix_preview_concise(&mut handle, file, preview)?;
        }
    }

    writeln!(handle)?;
    writeln!(
        handle,
        "{dim}Legend: * = safe to apply, ! = requires review, [H/M/L] = confidence{reset}"
    )?;
    writeln!(handle)?;
    writeln!(
        handle,
        "Files: {cyan}{}{reset}  Fixes: {}  Safe: {green}{}{reset}  Review: {yellow}{}{reset}",
        summary.files_affected,
        summary.total_fixes,
        summary.safe_fixes,
        summary.review_required
    )?;
    writeln!(handle)?;
    writeln!(
        handle,
        "Run {bright_green}fstar-lsp fix <path> --apply{reset} to write changes"
    )?;

    Ok(())
}

/// JSON structure for dry-run output.
#[derive(Serialize)]
struct JsonDryRunOutput {
    dry_run: bool,
    summary: JsonDryRunSummary,
    fixes: Vec<JsonFixPreview>,
}

#[derive(Serialize)]
struct JsonDryRunSummary {
    files_affected: usize,
    total_fixes: usize,
    safe_fixes: usize,
    review_required: usize,
    lines_removed: usize,
    lines_added: usize,
    by_rule: HashMap<String, usize>,
}

#[derive(Serialize)]
struct JsonFixPreview {
    file: String,
    rule: String,
    rule_name: String,
    message: String,
    start_line: usize,
    end_line: usize,
    confidence: String,
    is_safe: bool,
    unsafe_reason: Option<String>,
    removed_content: Option<String>,
    new_content: Option<String>,
}

/// Print all dry-run output in JSON format.
pub fn print_dry_run_json(summary: &DryRunSummary) -> io::Result<()> {
    let stdout = io::stdout();
    let mut handle = stdout.lock();

    let by_rule: HashMap<String, usize> = summary
        .by_rule
        .iter()
        .map(|(k, v)| (k.to_string(), *v))
        .collect();

    let fixes: Vec<JsonFixPreview> = summary
        .by_file
        .iter()
        .flat_map(|(file, previews)| {
            let file_str = file.display().to_string();
            previews.iter().map(move |p| JsonFixPreview {
                file: file_str.clone(),
                rule: p.rule.to_string(),
                rule_name: p.rule.name().to_string(),
                message: p.message.clone(),
                start_line: p.line_range.0,
                end_line: p.line_range.1,
                confidence: p.confidence.to_string(),
                is_safe: p.is_safe,
                unsafe_reason: p.unsafe_reason.clone(),
                removed_content: p.removed_content.clone(),
                new_content: p.new_content.clone(),
            })
        })
        .collect();

    let output = JsonDryRunOutput {
        dry_run: true,
        summary: JsonDryRunSummary {
            files_affected: summary.files_affected,
            total_fixes: summary.total_fixes,
            safe_fixes: summary.safe_fixes,
            review_required: summary.review_required,
            lines_removed: summary.lines_removed,
            lines_added: summary.lines_added,
            by_rule,
        },
        fixes,
    };

    serde_json::to_writer_pretty(&mut handle, &output)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
    writeln!(handle)?;

    Ok(())
}

/// Print dry-run output in the specified format.
pub fn print_dry_run(summary: &DryRunSummary, format: DryRunFormat) -> io::Result<()> {
    match format {
        DryRunFormat::Full => print_dry_run_full(summary),
        DryRunFormat::Concise => print_dry_run_concise(summary),
        DryRunFormat::Json => print_dry_run_json(summary),
    }
}

/// Print "no fixable issues" message.
pub fn print_no_fixes_message() -> io::Result<()> {
    let c = color_config();
    let green = c.green();
    let reset = c.reset();

    let stdout = io::stdout();
    let mut handle = stdout.lock();

    writeln!(handle)?;
    writeln!(
        handle,
        "{green}{} No fixable issues found.{reset}",
        box_chars::CHECK
    )?;
    writeln!(handle)?;

    Ok(())
}

/// Print completion message after applying fixes.
pub fn print_fixes_applied(count: usize) -> io::Result<()> {
    let c = color_config();
    let bold = c.bold();
    let green = c.green();
    let reset = c.reset();

    let stdout = io::stdout();
    let mut handle = stdout.lock();

    writeln!(handle)?;
    writeln!(
        handle,
        "{bold}{green}{} {} file{} fixed.{reset}",
        box_chars::CHECK,
        count,
        if count == 1 { "" } else { "s" }
    )?;
    writeln!(handle)?;

    Ok(())
}

// ============================================================================
// DIAGNOSTIC OUTPUT DISPATCH
// ============================================================================

/// Print diagnostics to stdout in the specified format.
pub fn print_diagnostics(
    diagnostics: &[Diagnostic],
    format: OutputFormat,
    show_fixes: bool,
) -> io::Result<()> {
    let stdout = io::stdout();
    let mut handle = stdout.lock();

    match format {
        OutputFormat::Text => print_text(&mut handle, diagnostics, show_fixes),
        OutputFormat::Concise => print_concise(&mut handle, diagnostics),
        OutputFormat::Grouped => print_grouped(&mut handle, diagnostics),
        OutputFormat::Json => print_json(&mut handle, diagnostics),
        OutputFormat::Github => print_github(&mut handle, diagnostics),
        OutputFormat::Sarif => print_sarif(&mut handle, diagnostics),
    }
}

/// Print summary statistics.
pub fn print_summary(summary: &LintSummary, format: OutputFormat) -> io::Result<()> {
    let stdout = io::stdout();
    let mut handle = stdout.lock();

    match format {
        OutputFormat::Text | OutputFormat::Concise => {
            print_text_summary(&mut handle, summary)
        }
        OutputFormat::Grouped => {
            // Grouped format includes its own inline summary
            Ok(())
        }
        OutputFormat::Json | OutputFormat::Github | OutputFormat::Sarif => {
            // These formats embed their own summary
            Ok(())
        }
    }
}

// ============================================================================
// TEXT FORMAT (human-readable, width-aware)
// ============================================================================

/// Print text format (ruff-style) with width-aware wrapping.
fn print_text<W: Write>(w: &mut W, diagnostics: &[Diagnostic], show_fixes: bool) -> io::Result<()> {
    let c = color_config();
    let bold = c.bold();
    let dim = c.dim();
    let reset = c.reset();
    let tw = terminal_width();

    for diag in diagnostics {
        let severity_color = match diag.severity {
            DiagnosticSeverity::Error => c.red(),
            DiagnosticSeverity::Warning => c.yellow(),
            DiagnosticSeverity::Info => c.cyan(),
            DiagnosticSeverity::Hint => c.gray(),
        };

        // Location prefix: path:line:col:
        let location = format!(
            "{}:{}:{}",
            diag.file.display(),
            diag.range.start_line,
            diag.range.start_col
        );

        let fixable_marker = if diag.fix.is_some() { " [*]" } else { "" };

        // Main diagnostic line
        writeln!(
            w,
            "{bold}{location}{reset}: {severity_color}{}{reset} {}{fixable_marker}",
            diag.rule,
            diag.message,
        )?;

        // Why/how-to-fix hints (always shown for errors, hidden for hints)
        if matches!(diag.severity, DiagnosticSeverity::Error | DiagnosticSeverity::Warning) {
            let why = rule_why(diag.rule);
            let wrapped_why = wrap_text(why, tw.saturating_sub(6), "      ");
            writeln!(w, "  {dim}why: {wrapped_why}{reset}")?;

            let how = rule_how_to_fix(diag.rule);
            let wrapped_how = wrap_text(how, tw.saturating_sub(6), "      ");
            writeln!(w, "  {dim}fix: {wrapped_how}{reset}")?;
        }

        // Show fix details if requested
        if show_fixes {
            if let Some(fix) = &diag.fix {
                writeln!(w, "  {severity_color}fix: {}{reset}", fix.message)?;
                for edit in &fix.edits {
                    if edit.new_text.is_empty() {
                        writeln!(
                            w,
                            "    {severity_color}|- Delete lines {}-{}{reset}",
                            edit.range.start_line, edit.range.end_line
                        )?;
                    } else {
                        let preview: String = edit
                            .new_text
                            .lines()
                            .take(3)
                            .collect::<Vec<_>>()
                            .join(" | ");
                        let max_preview = tw.saturating_sub(8).min(60);
                        let truncated = if preview.len() > max_preview {
                            format!("{}...", safe_truncate(&preview, max_preview.saturating_sub(3)))
                        } else {
                            preview
                        };
                        writeln!(w, "    {severity_color}|+ {truncated}{reset}")?;
                    }
                }
            }
        }
    }

    Ok(())
}

/// Print text summary with per-rule breakdown.
fn print_text_summary<W: Write>(w: &mut W, summary: &LintSummary) -> io::Result<()> {
    let c = color_config();
    let bold = c.bold();
    let dim = c.dim();
    let red = c.red();
    let yellow = c.yellow();
    let green = c.green();
    let cyan = c.cyan();
    let reset = c.reset();

    writeln!(w)?;
    if summary.total_diagnostics == 0 {
        writeln!(w, "{green}All checks passed!{reset}")?;
        return Ok(());
    }

    // Header line
    write!(
        w,
        "{bold}Found {} issue{}",
        summary.total_diagnostics,
        if summary.total_diagnostics == 1 { "" } else { "s" }
    )?;

    if summary.fixable_diagnostics > 0 {
        write!(w, " ({} fixable)", summary.fixable_diagnostics)?;
    }
    writeln!(w, "{reset}")?;

    // Severity breakdown
    let mut parts = Vec::new();
    if summary.errors > 0 {
        parts.push(format!("{red}{} error{}{reset}", summary.errors, if summary.errors == 1 { "" } else { "s" }));
    }
    if summary.warnings > 0 {
        parts.push(format!("{yellow}{} warning{}{reset}", summary.warnings, if summary.warnings == 1 { "" } else { "s" }));
    }
    if summary.infos > 0 {
        parts.push(format!("{cyan}{} info{reset}", summary.infos));
    }
    if summary.hints > 0 {
        parts.push(format!("{dim}{} hint{}{reset}", summary.hints, if summary.hints == 1 { "" } else { "s" }));
    }
    if !parts.is_empty() {
        writeln!(w, "  {}", parts.join(", "))?;
    }

    // Per-rule breakdown (if more than one rule triggered)
    if summary.by_rule.len() > 1 {
        writeln!(w)?;
        let mut rules: Vec<_> = summary.by_rule.iter().collect();
        rules.sort_by(|a, b| b.1.cmp(a.1));
        for (rule, count) in &rules {
            writeln!(
                w,
                "  {dim}{:<8}{reset} {:<24} {:>4}",
                rule, rule.name(), count
            )?;
        }
    }

    Ok(())
}

// ============================================================================
// CONCISE FORMAT
// ============================================================================

/// Print concise format (one line per diagnostic).
fn print_concise<W: Write>(w: &mut W, diagnostics: &[Diagnostic]) -> io::Result<()> {
    for diag in diagnostics {
        writeln!(
            w,
            "{}:{}:{}: {} {}",
            diag.file.display(),
            diag.range.start_line,
            diag.range.start_col,
            diag.rule,
            diag.message
        )?;
    }
    Ok(())
}

// ============================================================================
// GROUPED FORMAT (token-efficient for LLM hooks)
// ============================================================================

/// Extract a short label from a diagnostic message.
///
/// For repetitive rules (e.g. FST013 "Public val `foo` is missing documentation..."),
/// strips the variable part to yield a common description like "missing docs".
fn abbreviate_message(msg: &str) -> &str {
    // FST013 pattern: "Public val `X` is missing documentation..."
    if let Some(pos) = msg.find("is missing documentation") {
        return &msg[pos..pos + 24]; // "is missing documentation"
    }
    // FST006 pattern: often "X should use snake_case" or similar
    if let Some(pos) = msg.find("should use") {
        let end = msg[pos..].find('.').map(|i| pos + i).unwrap_or(msg.len());
        return safe_truncate(&msg[pos..end], 50);
    }
    // Generic: first 50 chars
    safe_truncate(msg, 50)
}

/// Extract a short identifier from a diagnostic message (e.g. the `name` from
/// "Public val `name` is missing...").
fn extract_name(msg: &str) -> Option<&str> {
    let start = msg.find('`')? + 1;
    let end = start + msg[start..].find('`')?;
    Some(&msg[start..end])
}

/// Majority severity label for a group of diagnostics.
fn majority_severity(diags: &[&Diagnostic]) -> &'static str {
    let (mut e, mut w, mut i, mut h) = (0u32, 0u32, 0u32, 0u32);
    for d in diags {
        match d.severity {
            DiagnosticSeverity::Error => e += 1,
            DiagnosticSeverity::Warning => w += 1,
            DiagnosticSeverity::Info => i += 1,
            DiagnosticSeverity::Hint => h += 1,
        }
    }
    if e >= w && e >= i && e >= h { "error" }
    else if w >= i && w >= h { "warning" }
    else if i >= h { "info" }
    else { "hint" }
}

/// Print grouped format: one block per rule, counts + example locations.
///
/// Optimized for minimal token usage in LLM hook contexts.
fn print_grouped<W: Write>(w: &mut W, diagnostics: &[Diagnostic]) -> io::Result<()> {
    use std::collections::BTreeMap;

    if diagnostics.is_empty() {
        return Ok(());
    }

    // Group by rule code.
    let mut groups: BTreeMap<RuleCode, Vec<&Diagnostic>> = BTreeMap::new();
    for d in diagnostics {
        groups.entry(d.rule).or_default().push(d);
    }

    // Sort by count descending.
    let mut sorted: Vec<_> = groups.into_iter().collect();
    sorted.sort_by(|a, b| b.1.len().cmp(&a.1.len()));

    // Collect the file path from the first diagnostic (for the hint line).
    let file_hint = diagnostics[0].file.display().to_string();
    let total = diagnostics.len();
    let num_rules = sorted.len();

    for (rule, diags) in &sorted {
        let count = diags.len();
        let sev = majority_severity(diags);
        let sev_s = if count == 1 { "" } else { "s" };

        // Header: "FST013 doc-checker x35 warnings"
        write!(w, "{} {} x{} {}{}", rule, rule.name(), count, sev, sev_s)?;

        // For small groups (<=3), append abbreviated common description.
        if count <= 3 {
            writeln!(w)?;
            for d in diags.iter() {
                writeln!(w, "  :{} {}", d.range.start_line, safe_truncate(&d.message, 72))?;
            }
        } else {
            // Append common description on header line.
            let abbrev = abbreviate_message(&diags[0].message);
            writeln!(w, ": {}", abbrev)?;

            // Show first 2 names/locations, then "+N more".
            let mut parts: Vec<String> = Vec::new();
            for d in diags.iter().take(2) {
                if let Some(name) = extract_name(&d.message) {
                    parts.push(format!(":{} {}", d.range.start_line, name));
                } else {
                    parts.push(format!(":{}", d.range.start_line));
                }
            }
            let remaining = count - 2;
            write!(w, "  {}", parts.join(", "))?;
            writeln!(w, " +{} more", remaining)?;
        }
    }

    // Footer: compact summary with drill-down hint.
    let first_rule = &sorted[0].0;
    writeln!(
        w,
        "{} issues, {} rules. brrr-lint check --select {} {}",
        total, num_rules, first_rule, file_hint
    )?;

    Ok(())
}

// ============================================================================
// JSON FORMAT (with full fix info)
// ============================================================================

/// JSON diagnostic for serialization -- includes full fix details.
#[derive(Serialize)]
struct JsonDiagnostic {
    code: String,
    code_name: String,
    message: String,
    severity: String,
    file: String,
    location: JsonLocation,
    why: String,
    how_to_fix: String,
    fixable: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    fix: Option<JsonFix>,
}

#[derive(Serialize)]
struct JsonLocation {
    start_line: usize,
    start_column: usize,
    end_line: usize,
    end_column: usize,
}

#[derive(Serialize)]
struct JsonFix {
    message: String,
    confidence: String,
    safety_level: String,
    is_safe: bool,
    can_auto_apply: bool,
    requires_force: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    unsafe_reason: Option<String>,
    edits: Vec<JsonEdit>,
}

#[derive(Serialize)]
struct JsonEdit {
    file: String,
    start_line: usize,
    start_column: usize,
    end_line: usize,
    end_column: usize,
    new_text: String,
}

/// Full JSON output envelope with diagnostics and summary.
#[derive(Serialize)]
struct JsonOutput {
    version: &'static str,
    diagnostics: Vec<JsonDiagnostic>,
    summary: JsonSummary,
}

#[derive(Serialize)]
struct JsonSummary {
    total: usize,
    fixable: usize,
    errors: usize,
    warnings: usize,
    infos: usize,
    hints: usize,
    by_rule: HashMap<String, usize>,
}

/// Print JSON format with full fix info.
fn print_json<W: Write>(w: &mut W, diagnostics: &[Diagnostic]) -> io::Result<()> {
    let mut by_rule: HashMap<String, usize> = HashMap::new();
    let mut errors = 0usize;
    let mut warnings = 0usize;
    let mut infos = 0usize;
    let mut hints = 0usize;
    let mut fixable = 0usize;

    let json_diags: Vec<JsonDiagnostic> = diagnostics
        .iter()
        .map(|d| {
            match d.severity {
                DiagnosticSeverity::Error => errors += 1,
                DiagnosticSeverity::Warning => warnings += 1,
                DiagnosticSeverity::Info => infos += 1,
                DiagnosticSeverity::Hint => hints += 1,
            }
            *by_rule.entry(d.rule.to_string()).or_insert(0) += 1;
            if d.fix.is_some() {
                fixable += 1;
            }

            JsonDiagnostic {
                code: d.rule.to_string(),
                code_name: d.rule.name().to_string(),
                message: d.message.clone(),
                severity: d.severity.to_string(),
                file: d.file.display().to_string(),
                location: JsonLocation {
                    start_line: d.range.start_line,
                    start_column: d.range.start_col,
                    end_line: d.range.end_line,
                    end_column: d.range.end_col,
                },
                why: rule_why(d.rule).to_string(),
                how_to_fix: rule_how_to_fix(d.rule).to_string(),
                fixable: d.fix.is_some(),
                fix: d.fix.as_ref().map(|f| JsonFix {
                    message: f.message.clone(),
                    confidence: f.confidence.to_string(),
                    safety_level: f.safety_level.to_string(),
                    is_safe: f.is_safe(),
                    can_auto_apply: f.can_auto_apply(),
                    requires_force: f.requires_force(),
                    unsafe_reason: f.unsafe_reason.clone(),
                    edits: f.edits.iter().map(|e| JsonEdit {
                        file: e.file.display().to_string(),
                        start_line: e.range.start_line,
                        start_column: e.range.start_col,
                        end_line: e.range.end_line,
                        end_column: e.range.end_col,
                        new_text: e.new_text.clone(),
                    }).collect(),
                }),
            }
        })
        .collect();

    let output = JsonOutput {
        version: "1",
        diagnostics: json_diags,
        summary: JsonSummary {
            total: diagnostics.len(),
            fixable,
            errors,
            warnings,
            infos,
            hints,
            by_rule,
        },
    };

    serde_json::to_writer_pretty(&mut *w, &output)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
    writeln!(w)?;
    Ok(())
}

// ============================================================================
// GITHUB ACTIONS FORMAT
// ============================================================================

/// Escape a string for GitHub Actions annotation messages.
///
/// GitHub Actions requires `%`, `\n`, and `\r` to be percent-encoded.
fn github_escape(s: &str) -> String {
    s.replace('%', "%25")
     .replace('\n', "%0A")
     .replace('\r', "%0D")
}

/// Print GitHub Actions annotation format.
///
/// Format: `::warning file=F,line=L,col=C,endLine=EL,endColumn=EC,title=RULE::MESSAGE`
fn print_github<W: Write>(w: &mut W, diagnostics: &[Diagnostic]) -> io::Result<()> {
    for diag in diagnostics {
        let level = match diag.severity {
            DiagnosticSeverity::Error => "error",
            DiagnosticSeverity::Warning => "warning",
            DiagnosticSeverity::Info | DiagnosticSeverity::Hint => "notice",
        };

        let title = format!("{} ({})", diag.rule, diag.rule.name());
        let message = github_escape(&diag.message);

        writeln!(
            w,
            "::{level} file={},line={},col={},endLine={},endColumn={},title={title}::{message}",
            diag.file.display(),
            diag.range.start_line,
            diag.range.start_col,
            diag.range.end_line,
            diag.range.end_col,
        )?;
    }
    Ok(())
}

// ============================================================================
// SARIF 2.1.0 FORMAT
// ============================================================================

/// Top-level SARIF log.
#[derive(Serialize)]
struct SarifLog {
    #[serde(rename = "$schema")]
    schema: &'static str,
    version: &'static str,
    runs: Vec<SarifRun>,
}

#[derive(Serialize)]
struct SarifRun {
    tool: SarifTool,
    results: Vec<SarifResult>,
}

#[derive(Serialize)]
struct SarifTool {
    driver: SarifToolDriver,
}

#[derive(Serialize)]
struct SarifToolDriver {
    name: &'static str,
    version: String,
    #[serde(rename = "informationUri")]
    information_uri: &'static str,
    rules: Vec<SarifRule>,
}

#[derive(Serialize)]
struct SarifRule {
    id: String,
    name: String,
    #[serde(rename = "shortDescription")]
    short_description: SarifMessage,
    #[serde(rename = "fullDescription")]
    full_description: SarifMessage,
    #[serde(rename = "helpUri")]
    help_uri: String,
    help: SarifMessage,
    properties: SarifRuleProperties,
}

#[derive(Serialize)]
struct SarifRuleProperties {
    tags: Vec<String>,
}

#[derive(Serialize)]
struct SarifResult {
    #[serde(rename = "ruleId")]
    rule_id: String,
    #[serde(rename = "ruleIndex")]
    rule_index: usize,
    level: &'static str,
    message: SarifMessage,
    locations: Vec<SarifLocation>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    fixes: Vec<SarifFix>,
}

#[derive(Serialize)]
struct SarifMessage {
    text: String,
}

#[derive(Serialize)]
struct SarifLocation {
    #[serde(rename = "physicalLocation")]
    physical_location: SarifPhysicalLocation,
}

#[derive(Serialize)]
struct SarifPhysicalLocation {
    #[serde(rename = "artifactLocation")]
    artifact_location: SarifArtifactLocation,
    region: SarifRegion,
}

#[derive(Serialize)]
struct SarifArtifactLocation {
    uri: String,
}

#[derive(Serialize)]
struct SarifRegion {
    #[serde(rename = "startLine")]
    start_line: usize,
    #[serde(rename = "startColumn")]
    start_column: usize,
    #[serde(rename = "endLine")]
    end_line: usize,
    #[serde(rename = "endColumn")]
    end_column: usize,
}

#[derive(Serialize)]
struct SarifFix {
    description: SarifMessage,
    #[serde(rename = "artifactChanges")]
    artifact_changes: Vec<SarifArtifactChange>,
}

#[derive(Serialize)]
struct SarifArtifactChange {
    #[serde(rename = "artifactLocation")]
    artifact_location: SarifArtifactLocation,
    replacements: Vec<SarifReplacement>,
}

#[derive(Serialize)]
struct SarifReplacement {
    #[serde(rename = "deletedRegion")]
    deleted_region: SarifRegion,
    #[serde(rename = "insertedContent")]
    inserted_content: SarifInsertedContent,
}

#[derive(Serialize)]
struct SarifInsertedContent {
    text: String,
}

/// Map DiagnosticSeverity to SARIF level string.
fn sarif_level(severity: DiagnosticSeverity) -> &'static str {
    match severity {
        DiagnosticSeverity::Error => "error",
        DiagnosticSeverity::Warning => "warning",
        DiagnosticSeverity::Info => "note",
        DiagnosticSeverity::Hint => "note",
    }
}

/// Print SARIF 2.1.0 format.
fn print_sarif<W: Write>(w: &mut W, diagnostics: &[Diagnostic]) -> io::Result<()> {
    // Collect unique rules referenced by these diagnostics
    let mut seen_rules: Vec<RuleCode> = Vec::new();
    let mut rule_index_map: HashMap<RuleCode, usize> = HashMap::new();

    for diag in diagnostics {
        if let std::collections::hash_map::Entry::Vacant(e) = rule_index_map.entry(diag.rule) {
            e.insert(seen_rules.len());
            seen_rules.push(diag.rule);
        }
    }

    let sarif_rules: Vec<SarifRule> = seen_rules
        .iter()
        .map(|&code| SarifRule {
            id: code.to_string(),
            name: code.name().to_string(),
            short_description: SarifMessage {
                text: code.name().to_string(),
            },
            full_description: SarifMessage {
                text: code.description().to_string(),
            },
            help_uri: format!(
                "https://github.com/grigorye/brrr-lint/blob/main/docs/rules/{}.md",
                code.as_str()
            ),
            help: SarifMessage {
                text: format!(
                    "Why: {}\nFix: {}",
                    rule_why(code),
                    rule_how_to_fix(code)
                ),
            },
            properties: SarifRuleProperties {
                tags: vec!["fstar".to_string(), "verification".to_string()],
            },
        })
        .collect();

    let sarif_results: Vec<SarifResult> = diagnostics
        .iter()
        .map(|d| {
            let fixes = if let Some(fix) = &d.fix {
                fix.edits
                    .iter()
                    .map(|edit| SarifFix {
                        description: SarifMessage {
                            text: fix.message.clone(),
                        },
                        artifact_changes: vec![SarifArtifactChange {
                            artifact_location: SarifArtifactLocation {
                                uri: edit.file.display().to_string(),
                            },
                            replacements: vec![SarifReplacement {
                                deleted_region: SarifRegion {
                                    start_line: edit.range.start_line,
                                    start_column: edit.range.start_col,
                                    end_line: edit.range.end_line,
                                    end_column: edit.range.end_col,
                                },
                                inserted_content: SarifInsertedContent {
                                    text: edit.new_text.clone(),
                                },
                            }],
                        }],
                    })
                    .collect()
            } else {
                Vec::new()
            };

            SarifResult {
                rule_id: d.rule.to_string(),
                rule_index: rule_index_map[&d.rule],
                level: sarif_level(d.severity),
                message: SarifMessage {
                    text: d.message.clone(),
                },
                locations: vec![SarifLocation {
                    physical_location: SarifPhysicalLocation {
                        artifact_location: SarifArtifactLocation {
                            uri: d.file.display().to_string(),
                        },
                        region: SarifRegion {
                            start_line: d.range.start_line,
                            start_column: d.range.start_col,
                            end_line: d.range.end_line,
                            end_column: d.range.end_col,
                        },
                    },
                }],
                fixes,
            }
        })
        .collect();

    let log = SarifLog {
        schema: "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/main/sarif-2.1/schema/sarif-schema-2.1.0.json",
        version: "2.1.0",
        runs: vec![SarifRun {
            tool: SarifTool {
                driver: SarifToolDriver {
                    name: "brrr-lint",
                    version: env!("CARGO_PKG_VERSION").to_string(),
                    information_uri: "https://github.com/grigorye/brrr-lint",
                    rules: sarif_rules,
                },
            },
            results: sarif_results,
        }],
    };

    serde_json::to_writer_pretty(&mut *w, &log)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
    writeln!(w)?;
    Ok(())
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::rules::{Edit, Range};

    // ---- helpers ----

    fn make_diag(
        rule: RuleCode,
        severity: DiagnosticSeverity,
        message: &str,
        fix: Option<Fix>,
    ) -> Diagnostic {
        Diagnostic {
            rule,
            severity,
            file: PathBuf::from("test.fst"),
            range: Range::new(10, 1, 15, 1),
            message: message.to_string(),
            fix,
        }
    }

    fn make_diag_with_fix() -> Diagnostic {
        Diagnostic {
            rule: RuleCode::FST001,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("test.fst"),
            range: Range::new(5, 1, 10, 1),
            message: "Duplicate type definition".to_string(),
            fix: Some(Fix::safe("Remove duplicate", vec![Edit {
                file: PathBuf::from("test.fst"),
                range: Range::new(5, 1, 10, 1),
                new_text: "".to_string(),
            }])),
        }
    }

    fn create_test_preview(
        rule: RuleCode,
        line_range: (usize, usize),
        confidence: FixConfidence,
        is_safe: bool,
    ) -> FixPreview {
        FixPreview {
            rule,
            message: format!("Test fix for {:?}", rule),
            line_range,
            removed_content: Some("old code".to_string()),
            new_content: Some("new code".to_string()),
            confidence,
            is_safe,
            unsafe_reason: if !is_safe {
                Some("Test reason".to_string())
            } else {
                None
            },
        }
    }

    // ---- safe_truncate ----

    #[test]
    fn test_safe_truncate_ascii() {
        assert_eq!(safe_truncate("hello", 3), "hel");
        assert_eq!(safe_truncate("hello", 10), "hello");
        assert_eq!(safe_truncate("", 5), "");
    }

    #[test]
    fn test_safe_truncate_multibyte() {
        // Each character is 3 bytes in UTF-8
        let s = "\u{2713}\u{2717}\u{26a0}"; // 9 bytes total
        assert_eq!(safe_truncate(s, 3).len(), 3); // exactly one char
        assert_eq!(safe_truncate(s, 4).len(), 3); // can't split, stays at 3
        assert_eq!(safe_truncate(s, 6).len(), 6); // two chars
    }

    // ---- wrap_text ----

    #[test]
    fn test_wrap_text_short() {
        assert_eq!(wrap_text("short", 80, "  "), "short");
    }

    #[test]
    fn test_wrap_text_wraps_at_whitespace() {
        let result = wrap_text("hello world foo bar", 12, "  ");
        assert!(result.contains('\n'));
        // Every line should be <= 12 chars (first) or <= 10 (continuation)
        for (i, line) in result.lines().enumerate() {
            if i == 0 {
                assert!(line.len() <= 12, "first line too long: {:?}", line);
            }
        }
    }

    // ---- terminal_width ----

    #[test]
    fn test_terminal_width_default() {
        // When COLUMNS is not set, should return 80
        // (We can't reliably test env var mutation in parallel tests,
        // so just verify the function returns a sane value.)
        let w = terminal_width();
        assert!(w >= 10);
    }

    // ---- ColorConfig ----

    #[test]
    fn test_color_config_never() {
        let cc = ColorConfig::from_mode(ColorMode::Never);
        assert!(!cc.is_enabled());
        assert_eq!(cc.red(), "");
        assert_eq!(cc.reset(), "");
    }

    #[test]
    fn test_color_config_always() {
        let cc = ColorConfig::from_mode(ColorMode::Always);
        assert!(cc.is_enabled());
        assert_eq!(cc.red(), "\x1b[31m");
        assert_eq!(cc.reset(), "\x1b[0m");
        assert_eq!(cc.bold(), "\x1b[1m");
        assert_eq!(cc.underline(), "\x1b[4m");
    }

    // ---- LintSummary ----

    #[test]
    fn test_lint_summary_add_diagnostic() {
        let mut s = LintSummary::default();
        s.add_diagnostic(&make_diag(RuleCode::FST001, DiagnosticSeverity::Error, "err", None));
        s.add_diagnostic(&make_diag(RuleCode::FST001, DiagnosticSeverity::Warning, "warn", None));
        s.add_diagnostic(&make_diag(RuleCode::FST004, DiagnosticSeverity::Info, "info", None));
        s.add_diagnostic(&make_diag(RuleCode::FST004, DiagnosticSeverity::Hint, "hint", None));
        s.add_diagnostic(&make_diag_with_fix());

        assert_eq!(s.total_diagnostics, 5);
        assert_eq!(s.errors, 1);
        assert_eq!(s.warnings, 2); // 1 from make_diag + 1 from make_diag_with_fix
        assert_eq!(s.infos, 1);
        assert_eq!(s.hints, 1);
        assert_eq!(s.fixable_diagnostics, 1);
        assert_eq!(s.by_rule[&RuleCode::FST001], 3);
        assert_eq!(s.by_rule[&RuleCode::FST004], 2);
    }

    // ---- Text format ----

    #[test]
    fn test_text_output_error() {
        let diag = make_diag(RuleCode::FST011, DiagnosticSeverity::Error, "admit() found", None);
        let mut buf = Vec::new();
        print_text(&mut buf, &[diag], false).unwrap();
        let out = String::from_utf8(buf).unwrap();

        assert!(out.contains("test.fst:10:1"));
        assert!(out.contains("FST011"));
        assert!(out.contains("admit() found"));
        assert!(out.contains("why:"));
        assert!(out.contains("fix:"));
    }

    #[test]
    fn test_text_output_with_fix() {
        let diag = make_diag_with_fix();
        let mut buf = Vec::new();
        print_text(&mut buf, &[diag], true).unwrap();
        let out = String::from_utf8(buf).unwrap();

        assert!(out.contains("FST001"));
        assert!(out.contains("fix:"));
        assert!(out.contains("Delete lines"));
    }

    #[test]
    fn test_text_output_hint_no_why() {
        let diag = make_diag(RuleCode::FST009, DiagnosticSeverity::Hint, "try lemma_x", None);
        let mut buf = Vec::new();
        print_text(&mut buf, &[diag], false).unwrap();
        let out = String::from_utf8(buf).unwrap();

        assert!(out.contains("FST009"));
        // Hints should NOT have why/fix lines
        assert!(!out.contains("why:"));
    }

    // ---- Text summary ----

    #[test]
    fn test_text_summary_no_issues() {
        let mut buf = Vec::new();
        let summary = LintSummary::default();
        print_text_summary(&mut buf, &summary).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.contains("All checks passed"));
    }

    #[test]
    fn test_text_summary_with_issues() {
        let mut summary = LintSummary::default();
        summary.total_diagnostics = 5;
        summary.errors = 2;
        summary.warnings = 3;
        summary.fixable_diagnostics = 1;
        summary.by_rule.insert(RuleCode::FST001, 3);
        summary.by_rule.insert(RuleCode::FST004, 2);

        let mut buf = Vec::new();
        print_text_summary(&mut buf, &summary).unwrap();
        let out = String::from_utf8(buf).unwrap();

        assert!(out.contains("Found 5 issues"));
        assert!(out.contains("1 fixable"));
        assert!(out.contains("FST001"));
        assert!(out.contains("FST004"));
    }

    // ---- Concise format ----

    #[test]
    fn test_concise_output() {
        let diags = vec![
            make_diag(RuleCode::FST001, DiagnosticSeverity::Warning, "dup type", None),
            make_diag(RuleCode::FST004, DiagnosticSeverity::Warning, "unused open", None),
        ];
        let mut buf = Vec::new();
        print_concise(&mut buf, &diags).unwrap();
        let out = String::from_utf8(buf).unwrap();

        assert_eq!(out.lines().count(), 2);
        assert!(out.contains("test.fst:10:1: FST001 dup type"));
        assert!(out.contains("test.fst:10:1: FST004 unused open"));
    }

    // ---- JSON format ----

    #[test]
    fn test_json_output_valid() {
        let diag = make_diag_with_fix();
        let mut buf = Vec::new();
        print_json(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        // Must be valid JSON
        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert_eq!(parsed["version"], "1");
        assert!(parsed["diagnostics"].is_array());
        assert!(parsed["summary"].is_object());
    }

    #[test]
    fn test_json_output_has_fix_info() {
        let diag = make_diag_with_fix();
        let mut buf = Vec::new();
        print_json(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        let d = &parsed["diagnostics"][0];

        assert_eq!(d["code"], "FST001");
        assert_eq!(d["code_name"], "duplicate-types");
        assert_eq!(d["fixable"], true);
        assert!(d["why"].is_string());
        assert!(d["how_to_fix"].is_string());

        // Fix details
        let fix = &d["fix"];
        assert_eq!(fix["is_safe"], true);
        assert_eq!(fix["can_auto_apply"], true);
        assert_eq!(fix["confidence"], "high");
        assert_eq!(fix["safety_level"], "safe");
        assert!(fix["edits"].is_array());
        assert_eq!(fix["edits"].as_array().unwrap().len(), 1);
    }

    #[test]
    fn test_json_output_no_fix() {
        let diag = make_diag(RuleCode::FST003, DiagnosticSeverity::Warning, "unclosed comment", None);
        let mut buf = Vec::new();
        print_json(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        let d = &parsed["diagnostics"][0];

        assert_eq!(d["fixable"], false);
        assert!(d["fix"].is_null());
    }

    #[test]
    fn test_json_summary_counts() {
        let diags = vec![
            make_diag(RuleCode::FST001, DiagnosticSeverity::Error, "e1", None),
            make_diag(RuleCode::FST001, DiagnosticSeverity::Warning, "w1", None),
            make_diag(RuleCode::FST004, DiagnosticSeverity::Info, "i1", None),
        ];
        let mut buf = Vec::new();
        print_json(&mut buf, &diags).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        let s = &parsed["summary"];
        assert_eq!(s["total"], 3);
        assert_eq!(s["errors"], 1);
        assert_eq!(s["warnings"], 1);
        assert_eq!(s["infos"], 1);
        assert_eq!(s["hints"], 0);
        assert_eq!(s["by_rule"]["FST001"], 2);
        assert_eq!(s["by_rule"]["FST004"], 1);
    }

    // ---- GitHub Actions format ----

    #[test]
    fn test_github_escape() {
        assert_eq!(github_escape("hello\nworld"), "hello%0Aworld");
        assert_eq!(github_escape("50%"), "50%25");
        assert_eq!(github_escape("a\rb"), "a%0Db");
    }

    #[test]
    fn test_github_output_format() {
        let diag = make_diag(RuleCode::FST011, DiagnosticSeverity::Error, "admit() used", None);
        let mut buf = Vec::new();
        print_github(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        assert!(out.starts_with("::error "));
        assert!(out.contains("file=test.fst"));
        assert!(out.contains("line=10"));
        assert!(out.contains("col=1"));
        assert!(out.contains("endLine=15"));
        assert!(out.contains("endColumn=1"));
        assert!(out.contains("title=FST011 (effect-checker)"));
        assert!(out.contains("::admit() used"));
    }

    #[test]
    fn test_github_warning_level() {
        let diag = make_diag(RuleCode::FST004, DiagnosticSeverity::Warning, "unused", None);
        let mut buf = Vec::new();
        print_github(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.starts_with("::warning "));
    }

    #[test]
    fn test_github_notice_level() {
        let diag = make_diag(RuleCode::FST009, DiagnosticSeverity::Info, "hint", None);
        let mut buf = Vec::new();
        print_github(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.starts_with("::notice "));
    }

    #[test]
    fn test_github_multiline_message() {
        let diag = make_diag(
            RuleCode::FST001,
            DiagnosticSeverity::Warning,
            "line1\nline2\nline3",
            None,
        );
        let mut buf = Vec::new();
        print_github(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        // Message newlines must be escaped
        assert!(out.contains("line1%0Aline2%0Aline3"));
        // Output itself must be a single line
        assert_eq!(out.trim().lines().count(), 1);
    }

    // ---- SARIF 2.1.0 format ----

    #[test]
    fn test_sarif_output_valid_json() {
        let diag = make_diag(RuleCode::FST001, DiagnosticSeverity::Warning, "dup type", None);
        let mut buf = Vec::new();
        print_sarif(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert!(parsed.is_object());
    }

    #[test]
    fn test_sarif_schema_and_version() {
        let diag = make_diag(RuleCode::FST001, DiagnosticSeverity::Warning, "test", None);
        let mut buf = Vec::new();
        print_sarif(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert_eq!(parsed["version"], "2.1.0");
        assert!(parsed["$schema"].as_str().unwrap().contains("sarif-schema-2.1.0"));
    }

    #[test]
    fn test_sarif_tool_info() {
        let diag = make_diag(RuleCode::FST001, DiagnosticSeverity::Warning, "test", None);
        let mut buf = Vec::new();
        print_sarif(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        let driver = &parsed["runs"][0]["tool"]["driver"];
        assert_eq!(driver["name"], "brrr-lint");
        assert!(driver["version"].is_string());
        assert!(driver["rules"].is_array());
    }

    #[test]
    fn test_sarif_results_structure() {
        let diags = vec![
            make_diag(RuleCode::FST001, DiagnosticSeverity::Error, "error msg", None),
            make_diag(RuleCode::FST004, DiagnosticSeverity::Warning, "warn msg", None),
        ];
        let mut buf = Vec::new();
        print_sarif(&mut buf, &diags).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        let results = parsed["runs"][0]["results"].as_array().unwrap();
        assert_eq!(results.len(), 2);

        // First result
        assert_eq!(results[0]["ruleId"], "FST001");
        assert_eq!(results[0]["level"], "error");
        assert_eq!(results[0]["ruleIndex"], 0);

        // Second result
        assert_eq!(results[1]["ruleId"], "FST004");
        assert_eq!(results[1]["level"], "warning");
        assert_eq!(results[1]["ruleIndex"], 1);
    }

    #[test]
    fn test_sarif_rules_deduplication() {
        let diags = vec![
            make_diag(RuleCode::FST001, DiagnosticSeverity::Warning, "a", None),
            make_diag(RuleCode::FST001, DiagnosticSeverity::Warning, "b", None),
            make_diag(RuleCode::FST004, DiagnosticSeverity::Warning, "c", None),
        ];
        let mut buf = Vec::new();
        print_sarif(&mut buf, &diags).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        let rules = parsed["runs"][0]["tool"]["driver"]["rules"].as_array().unwrap();
        // Only 2 unique rules, even though 3 diagnostics
        assert_eq!(rules.len(), 2);
    }

    #[test]
    fn test_sarif_location() {
        let diag = make_diag(RuleCode::FST001, DiagnosticSeverity::Warning, "test", None);
        let mut buf = Vec::new();
        print_sarif(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        let loc = &parsed["runs"][0]["results"][0]["locations"][0]["physicalLocation"];
        assert_eq!(loc["artifactLocation"]["uri"], "test.fst");
        assert_eq!(loc["region"]["startLine"], 10);
        assert_eq!(loc["region"]["startColumn"], 1);
        assert_eq!(loc["region"]["endLine"], 15);
        assert_eq!(loc["region"]["endColumn"], 1);
    }

    #[test]
    fn test_sarif_with_fix() {
        let diag = make_diag_with_fix();
        let mut buf = Vec::new();
        print_sarif(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        let fixes = parsed["runs"][0]["results"][0]["fixes"].as_array().unwrap();
        assert_eq!(fixes.len(), 1);

        let fix = &fixes[0];
        assert!(fix["description"]["text"].is_string());
        let changes = fix["artifactChanges"].as_array().unwrap();
        assert_eq!(changes.len(), 1);
        let replacement = &changes[0]["replacements"][0];
        assert_eq!(replacement["deletedRegion"]["startLine"], 5);
        assert_eq!(replacement["insertedContent"]["text"], "");
    }

    #[test]
    fn test_sarif_without_fix() {
        let diag = make_diag(RuleCode::FST003, DiagnosticSeverity::Warning, "test", None);
        let mut buf = Vec::new();
        print_sarif(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        // fixes array should be empty (and skipped via skip_serializing_if)
        let result = &parsed["runs"][0]["results"][0];
        // Either missing key or empty array
        let fixes = result.get("fixes");
        assert!(fixes.is_none() || fixes.unwrap().as_array().unwrap().is_empty());
    }

    #[test]
    fn test_sarif_rule_help() {
        let diag = make_diag(RuleCode::FST011, DiagnosticSeverity::Error, "admit", None);
        let mut buf = Vec::new();
        print_sarif(&mut buf, &[diag]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        let rule = &parsed["runs"][0]["tool"]["driver"]["rules"][0];
        let help = rule["help"]["text"].as_str().unwrap();
        assert!(help.contains("Why:"));
        assert!(help.contains("Fix:"));
    }

    // ---- Dry-run output ----

    #[test]
    fn test_dry_run_summary_new() {
        let summary = DryRunSummary::new();
        assert_eq!(summary.files_affected, 0);
        assert_eq!(summary.total_fixes, 0);
        assert_eq!(summary.safe_fixes, 0);
        assert_eq!(summary.review_required, 0);
    }

    #[test]
    fn test_dry_run_summary_add_fix() {
        let mut summary = DryRunSummary::new();

        let diag = Diagnostic {
            rule: RuleCode::FST001,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("test.fst"),
            range: Range::new(1, 1, 5, 1),
            message: "Test diagnostic".to_string(),
            fix: Some(Fix::safe("Test fix", vec![])),
        };

        let content = "line1\nline2\nline3\nline4\nline5";
        summary.add_fix(&diag, content);
        summary.finalize();

        assert_eq!(summary.total_fixes, 1);
        assert_eq!(summary.safe_fixes, 1);
        assert_eq!(summary.review_required, 0);
        assert_eq!(summary.files_affected, 1);
        assert!(summary.by_rule.contains_key(&RuleCode::FST001));
    }

    #[test]
    fn test_dry_run_summary_counts_unsafe_as_review() {
        let mut summary = DryRunSummary::new();

        let diag = Diagnostic {
            rule: RuleCode::FST005,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("test.fst"),
            range: Range::new(1, 1, 5, 1),
            message: "Test diagnostic".to_string(),
            fix: Some(Fix::new("Test fix", vec![]).with_confidence(FixConfidence::Medium)),
        };

        let content = "line1\nline2\nline3\nline4\nline5";
        summary.add_fix(&diag, content);
        summary.finalize();

        assert_eq!(summary.total_fixes, 1);
        assert_eq!(summary.safe_fixes, 0);
        assert_eq!(summary.review_required, 1);
    }

    #[test]
    fn test_dry_run_header_output() {
        let mut output = Vec::new();
        print_dry_run_header(&mut output).expect("Failed to write header");
        let result = String::from_utf8(output).expect("Invalid UTF-8");

        assert!(result.contains("DRY RUN"));
        assert!(result.contains("No files will be modified"));
        assert!(result.contains("\u{2554}")); // ╔
        assert!(result.contains("\u{2557}")); // ╗
    }

    #[test]
    fn test_apply_header_output() {
        let mut output = Vec::new();
        print_apply_header(&mut output).expect("Failed to write header");
        let result = String::from_utf8(output).expect("Invalid UTF-8");

        assert!(result.contains("APPLYING CHANGES"));
        assert!(result.contains("Files will be modified"));
    }

    #[test]
    fn test_fix_preview_full_output() {
        let mut output = Vec::new();
        let file = PathBuf::from("/test/path/file.fst");
        let preview = create_test_preview(RuleCode::FST001, (10, 15), FixConfidence::High, true);

        print_fix_preview_full(&mut output, &file, &preview).expect("Failed to write preview");
        let result = String::from_utf8(output).expect("Invalid UTF-8");

        assert!(result.contains("file.fst"));
        assert!(result.contains("FST001"));
        assert!(result.contains("10"));
        assert!(result.contains("15"));
        assert!(result.contains("HIGH"));
    }

    #[test]
    fn test_fix_preview_concise_output() {
        let mut output = Vec::new();
        let file = PathBuf::from("/test/path/file.fst");
        let preview = create_test_preview(RuleCode::FST004, (5, 5), FixConfidence::High, true);

        print_fix_preview_concise(&mut output, &file, &preview).expect("Failed to write preview");
        let result = String::from_utf8(output).expect("Invalid UTF-8");

        assert_eq!(result.lines().count(), 1);
        assert!(result.contains("file.fst"));
        assert!(result.contains("FST004"));
        assert!(result.contains("*"));
        assert!(result.contains("[H]"));
    }

    #[test]
    fn test_fix_preview_concise_unsafe() {
        let mut output = Vec::new();
        let file = PathBuf::from("/test/path/file.fst");
        let preview = create_test_preview(RuleCode::FST005, (5, 5), FixConfidence::Low, false);

        print_fix_preview_concise(&mut output, &file, &preview).expect("Failed to write preview");
        let result = String::from_utf8(output).expect("Invalid UTF-8");

        assert!(result.contains("!"));
        assert!(result.contains("[L]"));
    }

    #[test]
    fn test_dry_run_summary_output() {
        let mut summary = DryRunSummary::new();
        summary.files_affected = 5;
        summary.total_fixes = 10;
        summary.safe_fixes = 7;
        summary.review_required = 3;
        summary.lines_removed = 50;
        summary.lines_added = 30;
        summary.by_rule.insert(RuleCode::FST001, 4);
        summary.by_rule.insert(RuleCode::FST004, 6);

        let mut output = Vec::new();
        print_dry_run_summary(&mut output, &summary).expect("Failed to write summary");
        let result = String::from_utf8(output).expect("Invalid UTF-8");

        assert!(result.contains("5"));
        assert!(result.contains("10"));
        assert!(result.contains("7"));
        assert!(result.contains("3"));
        assert!(result.contains("50"));
        assert!(result.contains("30"));
        assert!(result.contains("FST001"));
        assert!(result.contains("FST004"));
    }

    #[test]
    fn test_apply_instructions_output() {
        let mut output = Vec::new();
        print_apply_instructions(&mut output, "fstar-lsp fix src/ --apply")
            .expect("Failed to write instructions");
        let result = String::from_utf8(output).expect("Invalid UTF-8");

        assert!(result.contains("fstar-lsp fix src/ --apply"));
        assert!(result.contains("To apply these changes"));
    }

    #[test]
    fn test_dry_run_format_enum() {
        let _concise = DryRunFormat::Concise;
        let _full = DryRunFormat::Full;
        let _json = DryRunFormat::Json;

        let default: DryRunFormat = Default::default();
        assert!(matches!(default, DryRunFormat::Full));
    }

    #[test]
    fn test_fix_preview_with_no_new_content() {
        let preview = FixPreview {
            rule: RuleCode::FST001,
            message: "Delete duplicate type".to_string(),
            line_range: (10, 15),
            removed_content: Some("type old = int".to_string()),
            new_content: None,
            confidence: FixConfidence::High,
            is_safe: true,
            unsafe_reason: None,
        };

        let mut output = Vec::new();
        let file = PathBuf::from("test.fst");
        print_fix_preview_full(&mut output, &file, &preview).expect("Failed to write preview");
        let result = String::from_utf8(output).expect("Invalid UTF-8");

        assert!(result.contains("deleted"));
    }

    #[test]
    fn test_create_fix_preview_helper() {
        let diag = Diagnostic {
            rule: RuleCode::FST001,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("test.fst"),
            range: Range::new(5, 1, 10, 1),
            message: "Duplicate type".to_string(),
            fix: Some(Fix::safe("Remove duplicate", vec![Edit {
                file: PathBuf::from("test.fst"),
                range: Range::new(5, 1, 10, 1),
                new_text: "".to_string(),
            }])),
        };

        let content = "line1\nline2\nline3\nline4\ntype x = int\ntype x = int\nline7\nline8\nline9\nline10";
        let preview = create_fix_preview(&diag, diag.fix.as_ref().unwrap(), content);

        assert_eq!(preview.rule, RuleCode::FST001);
        assert_eq!(preview.line_range, (5, 10));
        assert!(preview.removed_content.is_some());
        assert!(preview.new_content.is_none());
    }

    #[test]
    fn test_lines_counting() {
        let mut summary = DryRunSummary::new();

        let diag = Diagnostic {
            rule: RuleCode::FST001,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("test.fst"),
            range: Range::new(1, 1, 3, 1),
            message: "Test".to_string(),
            fix: Some(Fix::safe("Fix", vec![Edit {
                file: PathBuf::from("test.fst"),
                range: Range::new(1, 1, 3, 1),
                new_text: "new line 1\nnew line 2".to_string(),
            }])),
        };

        let content = "line1\nline2\nline3";
        summary.add_fix(&diag, content);

        assert_eq!(summary.lines_removed, 3);
        assert_eq!(summary.lines_added, 2);
    }

    // ---- rule_why / rule_how_to_fix ----

    #[test]
    fn test_rule_why_all_codes() {
        for code in RuleCode::all() {
            let why = rule_why(*code);
            assert!(!why.is_empty(), "rule_why({:?}) returned empty string", code);
        }
    }

    #[test]
    fn test_rule_how_to_fix_all_codes() {
        for code in RuleCode::all() {
            let how = rule_how_to_fix(*code);
            assert!(!how.is_empty(), "rule_how_to_fix({:?}) returned empty string", code);
        }
    }

    // ---- OutputFormat enum ----

    #[test]
    fn test_output_format_default() {
        let default: OutputFormat = Default::default();
        assert!(matches!(default, OutputFormat::Text));
    }

    #[test]
    fn test_output_format_all_variants() {
        let _text = OutputFormat::Text;
        let _concise = OutputFormat::Concise;
        let _json = OutputFormat::Json;
        let _github = OutputFormat::Github;
        let _sarif = OutputFormat::Sarif;
    }

    // ---- Empty diagnostics ----

    #[test]
    fn test_json_empty_diagnostics() {
        let mut buf = Vec::new();
        print_json(&mut buf, &[]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert_eq!(parsed["diagnostics"].as_array().unwrap().len(), 0);
        assert_eq!(parsed["summary"]["total"], 0);
    }

    #[test]
    fn test_sarif_empty_diagnostics() {
        let mut buf = Vec::new();
        print_sarif(&mut buf, &[]).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert_eq!(parsed["runs"][0]["results"].as_array().unwrap().len(), 0);
        assert_eq!(parsed["runs"][0]["tool"]["driver"]["rules"].as_array().unwrap().len(), 0);
    }

    #[test]
    fn test_github_empty_diagnostics() {
        let mut buf = Vec::new();
        print_github(&mut buf, &[]).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.is_empty());
    }

    #[test]
    fn test_concise_empty_diagnostics() {
        let mut buf = Vec::new();
        print_concise(&mut buf, &[]).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.is_empty());
    }

    #[test]
    fn test_text_empty_diagnostics() {
        let mut buf = Vec::new();
        print_text(&mut buf, &[], false).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.is_empty());
    }

    // ---- Multiple diagnostics in JSON ----

    #[test]
    fn test_json_multiple_diagnostics_with_mixed_fixes() {
        let diags = vec![
            make_diag_with_fix(),
            make_diag(RuleCode::FST007, DiagnosticSeverity::Warning, "quantifier without trigger", None),
            Diagnostic {
                rule: RuleCode::FST005,
                severity: DiagnosticSeverity::Warning,
                file: PathBuf::from("other.fst"),
                range: Range::new(1, 1, 1, 10),
                message: "Dead code".to_string(),
                fix: Some(Fix::unsafe_fix(
                    "Remove dead binding",
                    vec![Edit {
                        file: PathBuf::from("other.fst"),
                        range: Range::new(1, 1, 1, 10),
                        new_text: "".to_string(),
                    }],
                    FixConfidence::Low,
                    "May be used via SMTPat",
                )),
            },
        ];

        let mut buf = Vec::new();
        print_json(&mut buf, &diags).unwrap();
        let out = String::from_utf8(buf).unwrap();

        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert_eq!(parsed["diagnostics"].as_array().unwrap().len(), 3);
        assert_eq!(parsed["summary"]["fixable"], 2);

        // Check unsafe fix details
        let unsafe_fix = &parsed["diagnostics"][2]["fix"];
        assert_eq!(unsafe_fix["is_safe"], false);
        assert_eq!(unsafe_fix["requires_force"], true);
        assert_eq!(unsafe_fix["confidence"], "low");
        assert_eq!(unsafe_fix["unsafe_reason"], "May be used via SMTPat");
    }
}
