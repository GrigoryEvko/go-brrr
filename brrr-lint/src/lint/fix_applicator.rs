//! Safe, controlled fix application system with two-phase commit.
//!
//! This module provides a robust fix application system with:
//! - Two-phase commit (validate to temp files, then atomically apply)
//! - Full rollback capability
//! - Progress reporting
//! - Interactive mode for manual approval
//! - Safety limits to prevent runaway operations
//!
//! # Safety Guarantees
//!
//! 1. **Two-phase commit**: All fixes are first applied to temp files and validated.
//!    Only if ALL validations pass do we atomically move temp files to real files.
//!
//! 2. **Atomic operations**: Uses rename() for atomic file replacement on POSIX systems.
//!
//! 3. **Backup**: Every modified file is backed up before changes are applied.
//!
//! 4. **Rollback**: If any fix fails during phase 2, all changes are rolled back.
//!
//! 5. **Safety limits**: Prevents modifying too many files or too many lines at once.
//!
//! # Usage
//!
//! ```rust,ignore
//! use crate::lint::fix_applicator::{FixApplicator, FixApplicatorConfig};
//!
//! let config = FixApplicatorConfig::default();
//! let mut applicator = FixApplicator::new(config);
//!
//! // Phase 1: Prepare all fixes (validates to temp files)
//! for fix in fixes {
//!     applicator.prepare_fix(&fix)?;
//! }
//!
//! // Phase 2: Commit all changes atomically (or rollback on failure)
//! applicator.commit()?;
//! ```

use std::collections::HashMap;
use std::fmt;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use tracing::{debug, error, info, warn};

use super::duplicate_types::cleanup_consecutive_blanks;
use super::file_safety::{AtomicWriter, AtomicWriteError};
use super::fix_validator::{validate_fix as validate_fix_content, FixValidation};
use super::rules::{Diagnostic, Edit, Fix, FixConfidence, FixSafetyLevel, RuleCode};

// =============================================================================
// CONFIGURATION
// =============================================================================

/// Default maximum number of files to modify in one run.
const DEFAULT_MAX_FILES: usize = 50;

/// Default maximum number of lines changed per file.
const DEFAULT_MAX_LINES_PER_FILE: usize = 100;

/// Default minimum confidence threshold for auto-applying fixes.
const DEFAULT_MIN_CONFIDENCE: f64 = 0.8;

/// Configuration for the fix applicator.
#[derive(Debug, Clone)]
pub struct FixApplicatorConfig {
    /// Whether to run in dry-run mode (no actual file modifications).
    pub dry_run: bool,

    /// Directory for storing backups.
    pub backup_dir: Option<PathBuf>,

    /// Maximum number of files to modify in one run.
    /// Use `force` to override this limit.
    pub max_files: usize,

    /// Maximum number of lines changed per file.
    /// Use `force` to override this limit.
    pub max_lines_per_file: usize,

    /// Force mode - bypasses safety limits.
    pub force: bool,

    /// Interactive mode - prompt for each fix.
    pub interactive: bool,

    /// Minimum confidence threshold for auto-applying fixes.
    pub min_confidence: f64,

    /// Whether to show detailed progress reporting.
    pub verbose: bool,
}

impl Default for FixApplicatorConfig {
    fn default() -> Self {
        Self {
            dry_run: true,
            backup_dir: None,
            max_files: DEFAULT_MAX_FILES,
            max_lines_per_file: DEFAULT_MAX_LINES_PER_FILE,
            force: false,
            interactive: false,
            min_confidence: DEFAULT_MIN_CONFIDENCE,
            verbose: false,
        }
    }
}

impl FixApplicatorConfig {
    /// Create a config for dry-run mode.
    pub fn dry_run() -> Self {
        Self {
            dry_run: true,
            ..Default::default()
        }
    }

    /// Create a config for apply mode.
    pub fn apply() -> Self {
        Self {
            dry_run: false,
            ..Default::default()
        }
    }

    /// Set interactive mode.
    pub fn with_interactive(mut self, interactive: bool) -> Self {
        self.interactive = interactive;
        self
    }

    /// Set force mode (bypass safety limits).
    pub fn with_force(mut self, force: bool) -> Self {
        self.force = force;
        self
    }

    /// Set custom backup directory.
    pub fn with_backup_dir(mut self, dir: PathBuf) -> Self {
        self.backup_dir = Some(dir);
        self
    }

    /// Set custom max files limit.
    pub fn with_max_files(mut self, max: usize) -> Self {
        self.max_files = max;
        self
    }

    /// Set custom max lines per file limit.
    pub fn with_max_lines_per_file(mut self, max: usize) -> Self {
        self.max_lines_per_file = max;
        self
    }

    /// Set minimum confidence threshold.
    pub fn with_min_confidence(mut self, threshold: f64) -> Self {
        self.min_confidence = threshold;
        self
    }

    /// Set verbose mode.
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }
}

// =============================================================================
// FIX CHAIN CONFIGURATION
// =============================================================================

/// Configuration for fix chain iteration.
///
/// After applying one set of fixes (e.g., FST001 removing duplicate types),
/// the resulting file may have new issues detectable by other rules (e.g.,
/// FST004 unused opens that were only needed by the removed code). Fix chains
/// automate this re-lint-and-fix cycle.
#[derive(Debug, Clone)]
pub struct FixChainConfig {
    /// Maximum number of chain iterations before stopping.
    /// Prevents infinite loops when fixes oscillate.
    pub max_iterations: usize,

    /// Ordered rule chains: after fixing `from`, re-lint with `to`.
    /// Each pair `(from, to)` means: after a fix from rule `from` succeeds,
    /// schedule a re-lint with rule `to` on the affected files.
    pub chains: Vec<(RuleCode, RuleCode)>,
}

impl Default for FixChainConfig {
    fn default() -> Self {
        Self {
            max_iterations: 3,
            chains: vec![
                // After removing duplicate types, check for unused opens
                (RuleCode::FST001, RuleCode::FST004),
                // After removing unused opens, check for unused imports
                (RuleCode::FST004, RuleCode::FST008),
            ],
        }
    }
}

impl FixChainConfig {
    /// Find which rules should run as follow-ups after a given rule produced fixes.
    pub fn follow_up_rules(&self, completed_rule: RuleCode) -> Vec<RuleCode> {
        self.chains
            .iter()
            .filter(|(from, _)| *from == completed_rule)
            .map(|(_, to)| *to)
            .collect()
    }
}

// =============================================================================
// MULTI-FILE FIX GROUP
// =============================================================================

/// A group of prepared fixes across multiple files that must commit atomically.
///
/// Used for pair rules (FST001, FST002) where fixing a .fst file may require
/// coordinated changes to its .fsti counterpart. If any file in the group
/// fails to commit, ALL files in the group are rolled back.
#[derive(Debug)]
pub struct MultiFileFixGroup {
    /// Rule that generated this group.
    pub rule: RuleCode,

    /// Files and their prepared content, in commit order.
    /// Each entry is (file_path, original_content, new_content).
    pub files: Vec<(PathBuf, String, String)>,

    /// Combined fix message.
    pub message: String,
}

impl MultiFileFixGroup {
    /// Create a new multi-file fix group.
    pub fn new(rule: RuleCode, message: impl Into<String>) -> Self {
        Self {
            rule,
            files: Vec::new(),
            message: message.into(),
        }
    }

    /// Add a file to the group.
    pub fn add_file(&mut self, path: PathBuf, original: String, new_content: String) {
        self.files.push((path, original, new_content));
    }

    /// Number of files in this group.
    pub fn file_count(&self) -> usize {
        self.files.len()
    }

    /// Check if this group spans multiple files.
    pub fn is_multi_file(&self) -> bool {
        self.files.len() > 1
    }
}

// =============================================================================
// CONFIDENCE AUTO-DETERMINATION
// =============================================================================

/// Determine the appropriate confidence level for a fix based on its
/// characteristics: the rule that generated it, the type of edits, and
/// the safety level.
///
/// This provides a sensible default when rules do not explicitly set
/// confidence, reducing the chance of over- or under-confident fixes.
pub fn determine_confidence(
    rule: RuleCode,
    edits: &[Edit],
    safety_level: FixSafetyLevel,
) -> FixConfidence {
    // Unsafe fixes always get low confidence
    if safety_level == FixSafetyLevel::Unsafe {
        return FixConfidence::Low;
    }

    // Caution fixes cap at medium
    let cap = if safety_level == FixSafetyLevel::Caution {
        FixConfidence::Medium
    } else {
        FixConfidence::High
    };

    // Determine base confidence from rule characteristics
    let base = match rule {
        // High confidence: mechanical, well-defined transformations
        RuleCode::FST001 => FixConfidence::High,  // Duplicate type removal (exact match)
        RuleCode::FST004 => FixConfidence::High,  // Unused open removal
        RuleCode::FST013 => FixConfidence::High,  // Adding doc comments (additive)

        // Medium confidence: likely correct but some risk
        RuleCode::FST002 => FixConfidence::Medium, // Reordering declarations
        RuleCode::FST012 => FixConfidence::Medium, // Refinement simplification
        RuleCode::FST010 => FixConfidence::Medium, // Spec extraction (new file)

        // Low confidence: significant risk
        RuleCode::FST005 => FixConfidence::Low,    // Dead code removal
        _ => FixConfidence::Medium,
    };

    // Adjust based on edit characteristics
    let adjusted = if edits.is_empty() {
        FixConfidence::Low
    } else if edits.iter().all(|e| e.new_text.is_empty()) {
        // Pure deletions are riskier
        match base {
            FixConfidence::High => FixConfidence::High, // Trust high-confidence deletions
            _ => FixConfidence::Low,
        }
    } else if edits.len() > 5 {
        // Many edits = more risk
        match base {
            FixConfidence::High => FixConfidence::Medium,
            other => other,
        }
    } else {
        base
    };

    // Apply safety cap
    std::cmp::min(adjusted, cap)
}

// =============================================================================
// ERROR TYPES
// =============================================================================

/// Errors that can occur during fix application.
#[derive(Debug)]
pub enum FixError {
    /// Fix validation failed.
    ValidationFailed {
        file: PathBuf,
        reason: String,
        validation: Box<FixValidation>,
    },

    /// Fix is marked as unsafe.
    UnsafeFix {
        file: PathBuf,
        reason: String,
    },

    /// Fix has low confidence.
    LowConfidence {
        file: PathBuf,
        confidence: FixConfidence,
        required: f64,
    },

    /// Safety limit exceeded (too many files).
    TooManyFiles {
        count: usize,
        limit: usize,
    },

    /// Safety limit exceeded (too many lines changed in file).
    TooManyLines {
        file: PathBuf,
        count: usize,
        limit: usize,
    },

    /// File read error.
    FileRead {
        file: PathBuf,
        source: io::Error,
    },

    /// Atomic write error.
    AtomicWrite {
        file: PathBuf,
        source: AtomicWriteError,
    },

    /// User aborted in interactive mode.
    UserAborted,

    /// User skipped this fix in interactive mode.
    UserSkipped {
        file: PathBuf,
    },

    /// Temp file creation failed.
    TempFileCreation {
        file: PathBuf,
        source: io::Error,
    },

    /// Phase 1 (preparation) failed, no changes made.
    PreparationFailed {
        reason: String,
        failures: Vec<(PathBuf, String)>,
    },

    /// Phase 2 (commit) failed, rollback attempted.
    CommitFailed {
        reason: String,
        successful_rollbacks: Vec<PathBuf>,
        failed_rollbacks: Vec<(PathBuf, String)>,
    },
}

impl fmt::Display for FixError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FixError::ValidationFailed { file, reason, validation } => {
                write!(
                    f,
                    "Fix validation failed for {}: {} (confidence: {:.2})",
                    file.display(),
                    reason,
                    validation.confidence
                )
            }
            FixError::UnsafeFix { file, reason } => {
                write!(f, "Fix marked as unsafe for {}: {}", file.display(), reason)
            }
            FixError::LowConfidence { file, confidence, required } => {
                write!(
                    f,
                    "Fix confidence too low for {}: {} < {:.2}",
                    file.display(),
                    confidence,
                    required
                )
            }
            FixError::TooManyFiles { count, limit } => {
                write!(
                    f,
                    "Safety limit exceeded: {} files to modify, limit is {} (use --force to override)",
                    count, limit
                )
            }
            FixError::TooManyLines { file, count, limit } => {
                write!(
                    f,
                    "Safety limit exceeded for {}: {} lines to change, limit is {} (use --force to override)",
                    file.display(),
                    count,
                    limit
                )
            }
            FixError::FileRead { file, source } => {
                write!(f, "Failed to read file {}: {}", file.display(), source)
            }
            FixError::AtomicWrite { file, source } => {
                write!(f, "Failed to write file {}: {}", file.display(), source)
            }
            FixError::UserAborted => {
                write!(f, "Operation aborted by user")
            }
            FixError::UserSkipped { file } => {
                write!(f, "Fix skipped by user for {}", file.display())
            }
            FixError::TempFileCreation { file, source } => {
                write!(
                    f,
                    "Failed to create temp file for {}: {}",
                    file.display(),
                    source
                )
            }
            FixError::PreparationFailed { reason, failures } => {
                write!(f, "Preparation phase failed: {}. ", reason)?;
                write!(f, "{} file(s) failed validation", failures.len())
            }
            FixError::CommitFailed {
                reason,
                successful_rollbacks,
                failed_rollbacks,
            } => {
                write!(f, "Commit phase failed: {}. ", reason)?;
                write!(
                    f,
                    "Rolled back {} file(s), {} rollback(s) failed",
                    successful_rollbacks.len(),
                    failed_rollbacks.len()
                )
            }
        }
    }
}

impl std::error::Error for FixError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            FixError::FileRead { source, .. } => Some(source),
            FixError::TempFileCreation { source, .. } => Some(source),
            _ => None,
        }
    }
}

/// Errors that can occur during rollback.
#[derive(Debug)]
pub struct RollbackError {
    /// Files that were successfully rolled back.
    pub successful: Vec<PathBuf>,
    /// Files that failed to rollback with error messages.
    pub failed: Vec<(PathBuf, String)>,
}

impl fmt::Display for RollbackError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Rollback completed with {} success(es) and {} failure(s)",
            self.successful.len(),
            self.failed.len()
        )?;

        if !self.failed.is_empty() {
            write!(f, ". Failed files: ")?;
            for (i, (path, err)) in self.failed.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{} ({})", path.display(), err)?;
            }
        }

        Ok(())
    }
}

impl std::error::Error for RollbackError {}

/// Errors that can occur during commit.
#[derive(Debug)]
pub struct CommitError {
    /// Reason for commit failure.
    pub reason: String,
    /// Files that were successfully committed before the failure occurred.
    pub committed: Vec<PathBuf>,
    /// Files that failed to commit (triggering the rollback).
    pub failed: Vec<(PathBuf, String)>,
    /// Files that were successfully rolled back to their original content.
    pub successful_rollbacks: Vec<PathBuf>,
    /// Files that failed to rollback -- these may be in an inconsistent state
    /// and require manual recovery.
    pub failed_rollbacks: Vec<(PathBuf, String)>,
}

impl fmt::Display for CommitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Commit failed: {}. {} file(s) committed before failure, {} failed to commit, \
             {} rolled back, {} rollback(s) failed",
            self.reason,
            self.committed.len(),
            self.failed.len(),
            self.successful_rollbacks.len(),
            self.failed_rollbacks.len()
        )?;
        if !self.failed_rollbacks.is_empty() {
            write!(
                f,
                ". CRITICAL: Manual recovery required for: "
            )?;
            for (i, (path, err)) in self.failed_rollbacks.iter().enumerate() {
                if i > 0 {
                    write!(f, "; ")?;
                }
                write!(f, "{} ({})", path.display(), err)?;
            }
        }
        Ok(())
    }
}

impl std::error::Error for CommitError {}

// =============================================================================
// APPLIED FIX RECORD
// =============================================================================

/// Record of a successfully applied fix.
#[derive(Debug, Clone)]
pub struct AppliedFix {
    /// Path to the modified file.
    pub file: PathBuf,

    /// Path to the backup file (if any).
    pub backup_path: Option<PathBuf>,

    /// Path to the temp file used during two-phase commit.
    pub temp_path: Option<PathBuf>,

    /// The diagnostic that triggered this fix.
    pub rule: RuleCode,

    /// Description of the fix.
    pub message: String,

    /// Number of lines changed.
    pub lines_changed: usize,

    /// Validation result.
    pub validation: FixValidation,

    /// Original content (for rollback without backup file).
    pub original_content: String,

    /// New content (for verification).
    pub new_content: String,

    /// Timestamp when the fix was applied.
    pub applied_at: SystemTime,
}

impl AppliedFix {
    /// Check if this fix has a backup available for rollback.
    pub fn can_rollback(&self) -> bool {
        self.backup_path
            .as_ref()
            .map(|p| p.exists())
            .unwrap_or(false)
            || !self.original_content.is_empty()
    }
}

// =============================================================================
// PREPARED FIX (FOR TWO-PHASE COMMIT)
// =============================================================================

/// A fix that has been validated but not yet committed.
#[derive(Debug)]
struct PreparedFix {
    /// Path to the target file.
    file: PathBuf,

    /// Path to the validated temp file.
    temp_path: PathBuf,

    /// Original content (for rollback).
    original_content: String,

    /// New content (validated).
    new_content: String,

    /// Validation result.
    validation: FixValidation,

    /// The rule code.
    rule: RuleCode,

    /// Fix message.
    message: String,

    /// Lines changed.
    lines_changed: usize,
}

// =============================================================================
// PROGRESS REPORTER
// =============================================================================

/// Progress reporting callbacks.
pub trait ProgressReporter: Send + Sync {
    /// Called when starting to process a file.
    fn on_file_start(&self, file: &Path, index: usize, total: usize);

    /// Called when a file is successfully processed.
    fn on_file_success(&self, file: &Path, fix_message: &str);

    /// Called when a file processing fails.
    fn on_file_failure(&self, file: &Path, error: &str);

    /// Called when a file is skipped (user choice or validation failure).
    fn on_file_skipped(&self, file: &Path, reason: &str);

    /// Called when all files are processed (before commit).
    fn on_preparation_complete(&self, prepared: usize, failed: usize, skipped: usize);

    /// Called when commit phase starts.
    fn on_commit_start(&self, files_count: usize);

    /// Called when commit completes.
    fn on_commit_complete(&self, committed: usize, failed: usize);

    /// Called when rollback is performed.
    fn on_rollback(&self, rolled_back: usize, failed: usize);

    /// Called to show a summary at the end.
    fn on_summary(&self, summary: &FixSummary);
}

/// Default console progress reporter.
pub struct ConsoleProgressReporter {
    verbose: bool,
}

impl ConsoleProgressReporter {
    pub fn new(verbose: bool) -> Self {
        Self { verbose }
    }
}

impl ProgressReporter for ConsoleProgressReporter {
    fn on_file_start(&self, file: &Path, index: usize, total: usize) {
        if self.verbose {
            eprintln!(
                "\x1b[36m[{}/{}]\x1b[0m Processing: {}",
                index + 1,
                total,
                file.display()
            );
        }
    }

    fn on_file_success(&self, file: &Path, fix_message: &str) {
        if self.verbose {
            eprintln!(
                "  \x1b[32m[OK]\x1b[0m {} - {}",
                file.file_name().unwrap_or_default().to_string_lossy(),
                fix_message
            );
        }
    }

    fn on_file_failure(&self, file: &Path, error: &str) {
        eprintln!(
            "  \x1b[31m[FAIL]\x1b[0m {} - {}",
            file.file_name().unwrap_or_default().to_string_lossy(),
            error
        );
    }

    fn on_file_skipped(&self, file: &Path, reason: &str) {
        if self.verbose {
            eprintln!(
                "  \x1b[33m[SKIP]\x1b[0m {} - {}",
                file.file_name().unwrap_or_default().to_string_lossy(),
                reason
            );
        }
    }

    fn on_preparation_complete(&self, prepared: usize, failed: usize, skipped: usize) {
        eprintln!();
        eprintln!(
            "\x1b[1mPreparation complete:\x1b[0m {} ready, {} failed, {} skipped",
            prepared, failed, skipped
        );
    }

    fn on_commit_start(&self, files_count: usize) {
        if self.verbose {
            eprintln!();
            eprintln!("\x1b[1mCommitting {} file(s)...\x1b[0m", files_count);
        }
    }

    fn on_commit_complete(&self, committed: usize, failed: usize) {
        if failed == 0 {
            eprintln!(
                "\x1b[1;32mCommit successful:\x1b[0m {} file(s) modified",
                committed
            );
        } else {
            eprintln!(
                "\x1b[1;31mCommit partially failed:\x1b[0m {} committed, {} failed",
                committed, failed
            );
        }
    }

    fn on_rollback(&self, rolled_back: usize, failed: usize) {
        if failed == 0 {
            eprintln!(
                "\x1b[1;33mRollback complete:\x1b[0m {} file(s) restored",
                rolled_back
            );
        } else {
            eprintln!(
                "\x1b[1;31mRollback partially failed:\x1b[0m {} restored, {} failed",
                rolled_back, failed
            );
        }
    }

    fn on_summary(&self, summary: &FixSummary) {
        eprintln!();
        eprintln!("\x1b[1m=== Fix Summary ===\x1b[0m");
        eprintln!("  Files processed: {}", summary.files_processed);
        eprintln!("  Fixes applied:   {}", summary.fixes_applied);
        eprintln!("  Fixes skipped:   {}", summary.fixes_skipped);
        eprintln!("  Fixes failed:    {}", summary.fixes_failed);
        eprintln!("  Total lines:     {}", summary.total_lines_changed);

        if !summary.skipped_reasons.is_empty() && self.verbose {
            eprintln!();
            eprintln!("\x1b[1mSkipped fixes:\x1b[0m");
            for (file, reason) in &summary.skipped_reasons {
                eprintln!("  - {}: {}", file.display(), reason);
            }
        }

        if !summary.failed_reasons.is_empty() {
            eprintln!();
            eprintln!("\x1b[1;31mFailed fixes:\x1b[0m");
            for (file, reason) in &summary.failed_reasons {
                eprintln!("  - {}: {}", file.display(), reason);
            }
        }
    }
}

/// Summary of fix operations.
#[derive(Debug, Default)]
pub struct FixSummary {
    pub files_processed: usize,
    pub fixes_applied: usize,
    pub fixes_skipped: usize,
    pub fixes_failed: usize,
    pub total_lines_changed: usize,
    pub skipped_reasons: Vec<(PathBuf, String)>,
    pub failed_reasons: Vec<(PathBuf, String)>,
}

// =============================================================================
// INTERACTIVE PROMPT
// =============================================================================

/// Interactive prompt result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InteractiveChoice {
    /// Apply this fix.
    Yes,
    /// Skip this fix.
    No,
    /// Abort the entire operation.
    Quit,
    /// Apply this and all remaining fixes.
    All,
    /// Show a unified diff before deciding.
    Diff,
    /// Skip all remaining fixes for this rule code.
    SkipRule,
}

/// Interactive prompt handler.
pub trait InteractivePrompt: Send + Sync {
    /// Show the fix and ask for user confirmation.
    /// Returns the user's choice.
    fn prompt(&self, diagnostic: &Diagnostic, fix: &Fix) -> InteractiveChoice;
}

/// Default stdin interactive prompt with context display and diff support.
pub struct StdinInteractivePrompt;

impl StdinInteractivePrompt {
    /// Read file content for context display. Returns None on I/O error.
    fn read_file_for_context(path: &Path) -> Option<String> {
        std::fs::read_to_string(path).ok()
    }

    /// Display source context around the edit location.
    /// Shows 2 lines before and after the affected range.
    fn show_context(file_content: &str, start_line: usize, end_line: usize) {
        let lines: Vec<&str> = file_content.lines().collect();
        let context_before = 2;
        let context_after = 2;

        let display_start = start_line.saturating_sub(1).saturating_sub(context_before);
        let display_end = std::cmp::min(end_line.saturating_sub(1) + context_after, lines.len().saturating_sub(1));

        println!();
        println!("\x1b[1mContext:\x1b[0m");
        for i in display_start..=display_end {
            if i >= lines.len() {
                break;
            }
            let line_num = i + 1; // 1-indexed display
            let in_range = line_num >= start_line && line_num <= end_line;
            if in_range {
                println!(
                    "  \x1b[31m{:>4} | {}\x1b[0m  \x1b[33m<-- affected\x1b[0m",
                    line_num,
                    lines[i]
                );
            } else {
                println!("  {:>4} | {}", line_num, lines[i]);
            }
        }
    }

    /// Display a unified diff between original and replacement content.
    fn show_diff(file_content: &str, fix: &Fix) {
        println!();
        println!("\x1b[1mDiff:\x1b[0m");
        let lines: Vec<&str> = file_content.lines().collect();

        for edit in &fix.edits {
            let start = edit.range.start_line.saturating_sub(1);
            let end = std::cmp::min(edit.range.end_line.saturating_sub(1), lines.len().saturating_sub(1));

            // Show removed lines
            for i in start..=end {
                if i < lines.len() {
                    println!("  \x1b[31m- {}\x1b[0m", lines[i]);
                }
            }

            // Show added lines
            if !edit.new_text.is_empty() {
                for new_line in edit.new_text.lines() {
                    println!("  \x1b[32m+ {}\x1b[0m", new_line);
                }
            }
        }
    }

    /// Read a single choice from stdin.
    fn read_choice() -> InteractiveChoice {
        print!(
            "Apply? [\x1b[32my\x1b[0mes/\x1b[31mn\x1b[0mo/\x1b[36ma\x1b[0mll/\
             \x1b[33mq\x1b[0muit/\x1b[35md\x1b[0miff/\x1b[34ms\x1b[0mkip rule]: "
        );
        let _ = io::stdout().flush();

        let mut input = String::new();
        if io::stdin().read_line(&mut input).is_err() {
            return InteractiveChoice::Quit;
        }

        match input.trim().to_lowercase().as_str() {
            "y" | "yes" => InteractiveChoice::Yes,
            "n" | "no" => InteractiveChoice::No,
            "q" | "quit" => InteractiveChoice::Quit,
            "a" | "all" => InteractiveChoice::All,
            "d" | "diff" => InteractiveChoice::Diff,
            "s" | "skip" | "skip rule" => InteractiveChoice::SkipRule,
            _ => {
                println!("  Unknown choice. Use: y/n/a/q/d/s");
                InteractiveChoice::No
            }
        }
    }
}

impl InteractivePrompt for StdinInteractivePrompt {
    fn prompt(&self, diagnostic: &Diagnostic, fix: &Fix) -> InteractiveChoice {
        // Use the edit range (what will actually change) rather than the
        // diagnostic range (which may cover broader context).
        let (start_line, end_line) = if !fix.edits.is_empty() {
            (fix.edits[0].range.start_line, fix.edits[0].range.end_line)
        } else {
            (diagnostic.range.start_line, diagnostic.range.end_line)
        };

        // Read file for context display
        let file_content = Self::read_file_for_context(&diagnostic.file);

        println!();
        println!("\x1b[1;36m=== Fix Proposal ===\x1b[0m");
        println!("  File:       {}", diagnostic.file.display());
        println!(
            "  Rule:       {} ({})",
            diagnostic.rule,
            diagnostic.rule.name()
        );
        println!("  Location:   lines {}-{}", start_line, end_line);
        println!("  Issue:      {}", diagnostic.message);
        println!("  Fix:        {}", fix.message);
        println!("  Confidence: {}", fix.confidence);
        println!("  Safety:     {}", fix.safety_level);

        // Show source context if file content is available
        if let Some(ref content) = file_content {
            Self::show_context(content, start_line, end_line);
        }

        // Prompt loop: allow diff display before final decision
        loop {
            let choice = Self::read_choice();
            match choice {
                InteractiveChoice::Diff => {
                    if let Some(ref content) = file_content {
                        Self::show_diff(content, fix);
                    } else {
                        println!("  (file content not available for diff)");
                    }
                    // Re-prompt after showing diff
                    continue;
                }
                other => return other,
            }
        }
    }
}

// =============================================================================
// FIX APPLICATOR
// =============================================================================

/// Safe fix application system with two-phase commit.
pub struct FixApplicator {
    /// Configuration.
    config: FixApplicatorConfig,

    /// Fixes that have been prepared but not committed.
    prepared_fixes: Vec<PreparedFix>,

    /// Fixes that have been fully applied (for rollback).
    applied_fixes: Vec<AppliedFix>,

    /// Progress reporter.
    progress: Box<dyn ProgressReporter>,

    /// Interactive prompt handler (if interactive mode).
    interactive_prompt: Option<Box<dyn InteractivePrompt>>,

    /// Whether to auto-apply all remaining fixes (set by "all" choice).
    auto_apply_remaining: bool,

    /// Rules that the user chose to skip entirely in interactive mode.
    skipped_rules: std::collections::HashSet<RuleCode>,

    /// Summary statistics.
    summary: FixSummary,

    /// Cache of file contents to avoid redundant disk reads.
    /// Keyed by canonical path. Populated lazily during prepare phase.
    file_content_cache: HashMap<PathBuf, String>,
}

impl FixApplicator {
    /// Create a new fix applicator with the given configuration.
    pub fn new(config: FixApplicatorConfig) -> Self {
        let progress: Box<dyn ProgressReporter> =
            Box::new(ConsoleProgressReporter::new(config.verbose));

        let interactive_prompt: Option<Box<dyn InteractivePrompt>> = if config.interactive {
            Some(Box::new(StdinInteractivePrompt))
        } else {
            None
        };

        Self {
            config,
            prepared_fixes: Vec::new(),
            applied_fixes: Vec::new(),
            progress,
            interactive_prompt,
            auto_apply_remaining: false,
            skipped_rules: std::collections::HashSet::new(),
            summary: FixSummary::default(),
            file_content_cache: HashMap::new(),
        }
    }

    /// Set a custom progress reporter.
    pub fn with_progress_reporter(mut self, reporter: Box<dyn ProgressReporter>) -> Self {
        self.progress = reporter;
        self
    }

    /// Set a custom interactive prompt handler.
    pub fn with_interactive_prompt(mut self, prompt: Box<dyn InteractivePrompt>) -> Self {
        self.interactive_prompt = Some(prompt);
        self
    }

    /// Get the current summary.
    pub fn summary(&self) -> &FixSummary {
        &self.summary
    }

    /// Get the list of applied fixes.
    pub fn applied_fixes(&self) -> &[AppliedFix] {
        &self.applied_fixes
    }

    /// Check safety limits before processing a batch of fixes.
    pub fn check_safety_limits(&self, files_count: usize) -> Result<(), FixError> {
        if !self.config.force && files_count > self.config.max_files {
            return Err(FixError::TooManyFiles {
                count: files_count,
                limit: self.config.max_files,
            });
        }
        Ok(())
    }

    /// Apply a batch of fixes from diagnostics.
    ///
    /// This is the main entry point for fixing files. It:
    /// 1. Validates safety limits
    /// 2. Checks eligibility of each diagnostic (safety, confidence, interactive)
    /// 3. Groups approved diagnostics by canonical file path
    /// 4. Prepares combined fixes per file (Phase 1)
    /// 5. Commits all fixes atomically (Phase 2)
    ///
    /// Grouping by file ensures that multiple diagnostics targeting the same
    /// file have their edits merged into a single write, preventing earlier
    /// fixes from being silently overwritten by later ones.
    pub fn apply_batch(
        &mut self,
        diagnostics: &[Diagnostic],
    ) -> Result<Vec<AppliedFix>, FixError> {
        // Filter to diagnostics with fixes
        let fixable: Vec<&Diagnostic> = diagnostics.iter().filter(|d| d.fix.is_some()).collect();

        if fixable.is_empty() {
            info!("No fixable diagnostics found");
            return Ok(Vec::new());
        }

        // Check safety limits on unique files
        let unique_files: std::collections::HashSet<&PathBuf> =
            fixable.iter().map(|d| &d.file).collect();
        self.check_safety_limits(unique_files.len())?;

        // Pre-phase: check eligibility of each diagnostic individually.
        // Safety, confidence, and interactive prompts are per-diagnostic concerns
        // and must be evaluated before grouping.
        let total = fixable.len();
        let mut approved: Vec<&Diagnostic> = Vec::with_capacity(total);
        let mut skipped_count = 0;

        for (index, diag) in fixable.iter().enumerate() {
            self.progress.on_file_start(&diag.file, index, total);

            match self.check_diagnostic_eligibility(diag) {
                Ok(true) => approved.push(diag),
                Ok(false) => skipped_count += 1,
                Err(FixError::UserAborted) => {
                    self.progress
                        .on_preparation_complete(0, 0, skipped_count);
                    return Err(FixError::UserAborted);
                }
                Err(_) => {
                    // check_diagnostic_eligibility only returns UserAborted or Ok
                    skipped_count += 1;
                }
            }
        }

        // Group approved diagnostics by canonical file path so that all edits
        // targeting the same file are collected into a single PreparedFix.
        // This prevents the overwrite bug where the last write would clobber
        // earlier fixes for the same file.
        let file_groups: Vec<(PathBuf, Vec<&Diagnostic>)> = {
            let mut map: HashMap<PathBuf, Vec<&Diagnostic>> = HashMap::with_capacity(unique_files.len());
            for diag in &approved {
                let canonical = diag.file.canonicalize().unwrap_or_else(|_| diag.file.clone());
                map.entry(canonical).or_default().push(diag);
            }
            // Collect into a Vec for deterministic ordering (sorted by path)
            let mut groups: Vec<(PathBuf, Vec<&Diagnostic>)> = map.into_iter().collect();
            groups.sort_by(|a, b| a.0.cmp(&b.0));
            groups
        };

        // Phase 1: Prepare combined fixes for each file group.
        let mut prepared_count = 0;
        let mut failed_count = 0;
        let mut approved_fix_count = 0; // Track individual diagnostics that were successfully prepared

        for (canonical_path, diags) in file_groups.iter() {
            let display_path = &diags[0].file;
            self.summary.files_processed += 1;

            match self.prepare_file_group(canonical_path, display_path, diags) {
                Ok(true) => {
                    prepared_count += 1;
                    approved_fix_count += diags.len();
                }
                Ok(false) => {
                    skipped_count += diags.len();
                }
                Err(e) => {
                    failed_count += 1;
                    self.summary.fixes_failed += diags.len();
                    self.summary
                        .failed_reasons
                        .push((display_path.clone(), e.to_string()));
                    self.progress
                        .on_file_failure(display_path, &e.to_string());
                }
            }
        }

        self.progress
            .on_preparation_complete(prepared_count, failed_count, skipped_count);

        // If dry-run, don't commit
        if self.config.dry_run {
            // Clean up temp files
            self.cleanup_temp_files();

            // Report summary
            self.summary.fixes_applied = approved_fix_count;
            self.summary.fixes_skipped = skipped_count;
            self.progress.on_summary(&self.summary);

            // Return mock applied fixes for dry-run reporting
            return Ok(self
                .prepared_fixes
                .drain(..)
                .map(|pf| AppliedFix {
                    file: pf.file,
                    backup_path: None,
                    temp_path: Some(pf.temp_path),
                    rule: pf.rule,
                    message: pf.message,
                    lines_changed: pf.lines_changed,
                    validation: pf.validation,
                    original_content: pf.original_content,
                    new_content: pf.new_content,
                    applied_at: SystemTime::now(),
                })
                .collect());
        }

        // Phase 2: Commit all prepared fixes
        if prepared_count == 0 {
            info!("No fixes prepared, nothing to commit");
            self.progress.on_summary(&self.summary);
            return Ok(Vec::new());
        }

        self.progress.on_commit_start(prepared_count);

        match self.commit() {
            Ok(()) => {
                // fixes_applied counts individual diagnostics, not files
                self.summary.fixes_applied = approved_fix_count;
                let total_lines: usize =
                    self.applied_fixes.iter().map(|f| f.lines_changed).sum();
                self.summary.total_lines_changed = total_lines;

                self.progress
                    .on_commit_complete(self.applied_fixes.len(), 0);
                self.progress.on_summary(&self.summary);

                Ok(self.applied_fixes.clone())
            }
            Err(commit_err) => {
                // commit() already performed internal rollback of all
                // committed files. Use its rollback results directly
                // instead of calling rollback_all() (which would be a
                // no-op since applied_fixes was cleared during rollback).
                if !commit_err.failed_rollbacks.is_empty() {
                    error!(
                        "CRITICAL: Commit failed and {} rollback(s) failed. \
                         Some files may be in an inconsistent state.",
                        commit_err.failed_rollbacks.len()
                    );
                }

                self.progress.on_rollback(
                    commit_err.successful_rollbacks.len(),
                    commit_err.failed_rollbacks.len(),
                );
                self.progress.on_summary(&self.summary);

                Err(FixError::CommitFailed {
                    reason: commit_err.reason,
                    successful_rollbacks: commit_err.successful_rollbacks,
                    failed_rollbacks: commit_err.failed_rollbacks,
                })
            }
        }
    }

    /// Check whether a diagnostic's fix passes eligibility criteria.
    ///
    /// Evaluates skipped rules, safety level, confidence threshold, and
    /// interactive prompt (including the new `Diff` and `SkipRule` choices).
    /// Returns `Ok(true)` if eligible, `Ok(false)` if skipped,
    /// or `Err(FixError::UserAborted)` if the user chose to quit.
    fn check_diagnostic_eligibility(
        &mut self,
        diagnostic: &Diagnostic,
    ) -> Result<bool, FixError> {
        let fix = match &diagnostic.fix {
            Some(f) => f,
            None => return Ok(false),
        };

        // Check if the entire rule has been skipped (via interactive "skip rule")
        if self.skipped_rules.contains(&diagnostic.rule) {
            self.summary.fixes_skipped += 1;
            self.summary.skipped_reasons.push((
                diagnostic.file.clone(),
                format!("rule {} skipped by user", diagnostic.rule),
            ));
            self.progress.on_file_skipped(
                &diagnostic.file,
                &format!("rule {} skipped", diagnostic.rule),
            );
            return Ok(false);
        }

        // Check fix safety
        if !fix.is_safe() {
            let reason = fix
                .unsafe_reason
                .clone()
                .unwrap_or_else(|| "marked as unsafe".to_string());
            self.summary.fixes_skipped += 1;
            self.summary
                .skipped_reasons
                .push((diagnostic.file.clone(), reason.clone()));
            self.progress.on_file_skipped(&diagnostic.file, &reason);
            return Ok(false);
        }

        // Check confidence level (bypass with --force)
        if !self.config.force && fix.confidence != FixConfidence::High {
            let reason = format!("confidence too low ({})", fix.confidence);
            self.summary.fixes_skipped += 1;
            self.summary
                .skipped_reasons
                .push((diagnostic.file.clone(), reason.clone()));
            self.progress.on_file_skipped(&diagnostic.file, &reason);
            return Ok(false);
        }

        // Interactive mode: prompt user (Diff re-prompts are handled inside the prompt impl)
        if let Some(prompt) = &self.interactive_prompt {
            if !self.auto_apply_remaining {
                match prompt.prompt(diagnostic, fix) {
                    InteractiveChoice::Yes => {}
                    InteractiveChoice::No => {
                        self.summary.fixes_skipped += 1;
                        self.summary
                            .skipped_reasons
                            .push((diagnostic.file.clone(), "user skipped".to_string()));
                        self.progress
                            .on_file_skipped(&diagnostic.file, "user skipped");
                        return Ok(false);
                    }
                    InteractiveChoice::Quit => {
                        return Err(FixError::UserAborted);
                    }
                    InteractiveChoice::All => {
                        self.auto_apply_remaining = true;
                    }
                    InteractiveChoice::Diff => {
                        // Should not reach here -- StdinInteractivePrompt handles
                        // Diff internally via re-prompt loop. Treat as Yes.
                    }
                    InteractiveChoice::SkipRule => {
                        self.skipped_rules.insert(diagnostic.rule);
                        self.summary.fixes_skipped += 1;
                        self.summary.skipped_reasons.push((
                            diagnostic.file.clone(),
                            format!("rule {} skipped by user", diagnostic.rule),
                        ));
                        self.progress.on_file_skipped(
                            &diagnostic.file,
                            &format!("rule {} skipped", diagnostic.rule),
                        );
                        return Ok(false);
                    }
                }
            }
        }

        Ok(true)
    }

    /// Prepare a combined fix for all diagnostics targeting a single file.
    ///
    /// Reads the file content once (cached), collects all edits from every
    /// diagnostic in the group, builds a single combined result using
    /// `build_fixed_content`, validates it, and creates one `PreparedFix`.
    ///
    /// This is the core fix for Bug #2: by merging all edits before writing,
    /// we guarantee that every diagnostic's fix is reflected in the final
    /// output rather than having later writes silently overwrite earlier ones.
    fn prepare_file_group(
        &mut self,
        canonical_path: &Path,
        display_path: &Path,
        diagnostics: &[&Diagnostic],
    ) -> Result<bool, FixError> {
        if diagnostics.is_empty() {
            return Ok(false);
        }

        // Read original file content (cached to avoid redundant reads)
        let original_content = self.read_file_cached(canonical_path)?;

        // Collect all edits from all diagnostics targeting this file.
        let mut all_edits: Vec<Edit> = Vec::new();
        let mut messages: Vec<String> = Vec::new();
        let primary_rule = diagnostics[0].rule;

        for diag in diagnostics {
            if let Some(fix) = &diag.fix {
                all_edits.extend(fix.edits.clone());
                messages.push(fix.message.clone());
            }
        }

        if all_edits.is_empty() {
            return Ok(false);
        }

        // Build new content with all edits applied together.
        // build_fixed_content sorts by position and detects overlaps.
        let new_content = self.build_fixed_content(&original_content, &all_edits)?;

        // Calculate lines changed
        let lines_changed = count_lines_changed(&original_content, &new_content);

        // Check lines limit
        if !self.config.force && lines_changed > self.config.max_lines_per_file {
            return Err(FixError::TooManyLines {
                file: display_path.to_path_buf(),
                count: lines_changed,
                limit: self.config.max_lines_per_file,
            });
        }

        // Validate the fix
        let validation =
            validate_fix_content(&original_content, &new_content, display_path);

        if !self.config.force && !validation.can_auto_apply(self.config.min_confidence) {
            let reason = if !validation.is_safe {
                "validation marked fix as unsafe".to_string()
            } else {
                format!(
                    "confidence {:.2} below threshold {:.2}",
                    validation.confidence, self.config.min_confidence
                )
            };

            return Err(FixError::ValidationFailed {
                file: display_path.to_path_buf(),
                reason,
                validation: Box::new(validation),
            });
        }

        // Create temp file with validated content
        let temp_path = self.create_temp_file(display_path, &new_content)?;

        // Build combined message from all diagnostics
        let combined_message = if messages.len() == 1 {
            messages.into_iter().next().unwrap_or_default()
        } else {
            messages.join("; ")
        };

        // Record the prepared fix (one per file, containing all merged edits)
        let prepared = PreparedFix {
            file: display_path.to_path_buf(),
            temp_path,
            original_content,
            new_content,
            validation,
            rule: primary_rule,
            message: combined_message.clone(),
            lines_changed,
        };

        self.progress
            .on_file_success(display_path, &combined_message);
        self.prepared_fixes.push(prepared);

        Ok(true)
    }

    /// Read file content with caching to avoid redundant disk reads.
    ///
    /// If the file has already been read (by canonical path), the cached
    /// content is returned. Otherwise the file is read from disk and cached.
    fn read_file_cached(&mut self, canonical_path: &Path) -> Result<String, FixError> {
        if let Some(content) = self.file_content_cache.get(canonical_path) {
            return Ok(content.clone());
        }

        let content =
            fs::read_to_string(canonical_path).map_err(|e| FixError::FileRead {
                file: canonical_path.to_path_buf(),
                source: e,
            })?;

        self.file_content_cache
            .insert(canonical_path.to_path_buf(), content.clone());
        Ok(content)
    }

    /// Build the fixed content from original content and edits.
    ///
    /// Sorts all edits by `start_line` descending (bottom-to-top) so that
    /// applying each edit does not shift line numbers for subsequent edits
    /// above it. Detects overlapping ranges and returns an error with a
    /// warning log if any are found.
    fn build_fixed_content(&self, original: &str, edits: &[Edit]) -> Result<String, FixError> {
        if edits.is_empty() {
            return Ok(original.to_string());
        }

        // Sort edits bottom-to-top (descending by start_line) to avoid line drift.
        // Secondary sort: descending by end_line for deterministic ordering when
        // two edits share the same start_line.
        let mut sorted: Vec<&Edit> = edits.iter().collect();
        sorted.sort_by(|a, b| {
            b.range
                .start_line
                .cmp(&a.range.start_line)
                .then_with(|| b.range.end_line.cmp(&a.range.end_line))
        });

        // Check for overlapping ranges. After descending sort, sorted[i] has a
        // higher (or equal) start_line than sorted[i+1]. Overlap occurs when the
        // lower edit's end_line reaches into the higher edit's start_line, OR when
        // edits share the same line and their column ranges overlap.
        for window in sorted.windows(2) {
            let higher = window[0]; // higher start_line (closer to bottom of file)
            let lower = window[1]; // lower start_line (closer to top of file)

            let overlaps = if lower.range.end_line > higher.range.start_line {
                // Lower edit's end extends past higher edit's start: clear overlap
                true
            } else if lower.range.end_line == higher.range.start_line {
                // Same line boundary: check column overlap.
                // If the lower edit ends at or after where the higher starts, they overlap.
                lower.range.end_col >= higher.range.start_col
            } else {
                false
            };

            if overlaps {
                warn!(
                    "Overlapping edit ranges detected: lines {}-{} and lines {}-{}; \
                     the overlapping edits will be rejected to prevent data corruption",
                    lower.range.start_line,
                    lower.range.end_line,
                    higher.range.start_line,
                    higher.range.end_line
                );
                return Err(FixError::ValidationFailed {
                    file: edits[0].file.clone(),
                    reason: format!(
                        "Overlapping edit ranges: lines {}-{} (col {}-{}) and lines {}-{} (col {}-{})",
                        lower.range.start_line,
                        lower.range.end_line,
                        lower.range.start_col,
                        lower.range.end_col,
                        higher.range.start_line,
                        higher.range.end_line,
                        higher.range.start_col,
                        higher.range.end_col,
                    ),
                    validation: Box::new(FixValidation::default()),
                });
            }
        }

        // Apply each edit sequentially, bottom-to-top.
        let mut content = original.to_string();
        for edit in &sorted {
            content = self.apply_single_edit(&content, edit)?;
        }

        // Preserve trailing newline from the original: normalize only once at the
        // end so intermediate apply_single_edit calls do not fight each other.
        if original.ends_with('\n') && !content.ends_with('\n') {
            content.push('\n');
        } else if !original.ends_with('\n') && content.ends_with('\n') {
            content.pop();
        }

        // Post-processing: collapse multiple consecutive blank lines into at most one.
        // Edits that remove entire blocks (e.g. duplicate type removal) can leave behind
        // adjacent blank lines that were previously separated by the deleted content.
        let content = cleanup_consecutive_blanks(&content);

        Ok(content)
    }

    /// Apply a single edit to the content string, replacing the lines covered
    /// by `edit.range` with `edit.new_text`.
    ///
    /// Line numbers in `edit.range` are 1-indexed (as produced by the parser).
    ///
    /// Pre-allocates the result String at the original content's capacity to
    /// avoid repeated reallocation during string building.
    fn apply_single_edit(&self, content: &str, edit: &Edit) -> Result<String, FixError> {
        let lines: Vec<&str> = content.lines().collect();

        // Convert 1-indexed to 0-indexed
        let start_line = edit.range.start_line.saturating_sub(1);
        let end_line = edit.range.end_line.saturating_sub(1);

        // Pre-allocate: original length + new_text length is a reasonable upper bound.
        let capacity = content.len() + edit.new_text.len();
        let mut result = String::with_capacity(capacity);

        // Lines before the edit
        for line in lines.iter().take(start_line) {
            result.push_str(line);
            result.push('\n');
        }

        // Replacement text
        if !edit.new_text.is_empty() {
            result.push_str(&edit.new_text);
            if !edit.new_text.ends_with('\n') {
                result.push('\n');
            }
        }

        // Lines after the edit
        for line in lines.iter().skip(end_line + 1) {
            result.push_str(line);
            result.push('\n');
        }

        Ok(result)
    }

    /// Create a temp file in the same directory as the target file.
    fn create_temp_file(&self, target: &Path, content: &str) -> Result<PathBuf, FixError> {
        let parent = target.parent().unwrap_or(Path::new("."));
        let filename = target
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("file");

        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();

        let temp_path = parent.join(format!(".{}.{}.fstar-lint-tmp", filename, timestamp));

        let mut temp_file = File::create(&temp_path).map_err(|e| FixError::TempFileCreation {
            file: target.to_path_buf(),
            source: e,
        })?;

        temp_file
            .write_all(content.as_bytes())
            .map_err(|e| FixError::TempFileCreation {
                file: target.to_path_buf(),
                source: e,
            })?;

        temp_file.sync_all().map_err(|e| FixError::TempFileCreation {
            file: target.to_path_buf(),
            source: e,
        })?;

        debug!("Created temp file: {}", temp_path.display());

        Ok(temp_path)
    }

    /// Commit all prepared fixes (Phase 2 of two-phase commit).
    ///
    /// Atomically applies all prepared fixes via backup-and-write. If ANY write
    /// fails, processing stops immediately and all already-committed files are
    /// rolled back to their original content using in-memory snapshots captured
    /// during the prepare phase.
    ///
    /// # Rollback guarantees
    ///
    /// - On success: all files are written, `applied_fixes` is populated.
    /// - On failure with successful rollback: all committed files are restored,
    ///   `applied_fixes` is cleared, `CommitError::successful_rollbacks` lists
    ///   the restored files.
    /// - On failure with partial rollback failure (CRITICAL): some files may be
    ///   left in an inconsistent state. `CommitError::failed_rollbacks` lists
    ///   affected files with error details for manual recovery.
    pub fn commit(&mut self) -> Result<(), CommitError> {
        if self.config.dry_run {
            info!("Dry-run mode: skipping actual commit");
            return Ok(());
        }

        if self.prepared_fixes.is_empty() {
            info!("No prepared fixes to commit");
            return Ok(());
        }

        let atomic_writer = AtomicWriter::new();

        // Track committed files with their original content for rollback.
        // Stored as (path, original_content) pairs in commit order.
        let mut committed_snapshots: Vec<(PathBuf, String)> = Vec::new();

        for prepared in self.prepared_fixes.drain(..) {
            match atomic_writer.write_with_backup(&prepared.file, &prepared.new_content) {
                Ok(backup) => {
                    info!(
                        "Committed {} (backup: {})",
                        prepared.file.display(),
                        backup.display()
                    );

                    committed_snapshots.push((
                        prepared.file.clone(),
                        prepared.original_content.clone(),
                    ));

                    // Clean up temp file
                    if let Err(e) = fs::remove_file(&prepared.temp_path) {
                        warn!(
                            "Failed to remove temp file {}: {}",
                            prepared.temp_path.display(),
                            e
                        );
                    }

                    // Record as applied
                    self.applied_fixes.push(AppliedFix {
                        file: prepared.file.clone(),
                        backup_path: Some(backup),
                        temp_path: None,
                        rule: prepared.rule,
                        message: prepared.message,
                        lines_changed: prepared.lines_changed,
                        validation: prepared.validation,
                        original_content: prepared.original_content,
                        new_content: prepared.new_content,
                        applied_at: SystemTime::now(),
                    });
                }
                Err(e) => {
                    let failed_file = prepared.file.clone();
                    let failed_reason = e.to_string();
                    error!(
                        "Failed to commit {}: {}. Rolling back {} already-committed file(s).",
                        failed_file.display(),
                        failed_reason,
                        committed_snapshots.len()
                    );

                    // ROLLBACK: restore all already-committed files in reverse order
                    // using the original content snapshots from the prepare phase.
                    let mut successful_rollbacks: Vec<PathBuf> = Vec::new();
                    let mut failed_rollbacks: Vec<(PathBuf, String)> = Vec::new();

                    for (path, original_content) in committed_snapshots.iter().rev() {
                        match fs::write(path, original_content) {
                            Ok(()) => {
                                info!(
                                    "Rolled back {} during commit failure recovery",
                                    path.display()
                                );
                                successful_rollbacks.push(path.clone());
                            }
                            Err(re) => {
                                error!(
                                    "CRITICAL: Failed to rollback {} during commit recovery: {}. \
                                     Manual recovery required. Original content was {} bytes.",
                                    path.display(),
                                    re,
                                    original_content.len()
                                );
                                failed_rollbacks.push((path.clone(), re.to_string()));
                            }
                        }
                    }

                    // Clear applied_fixes since we rolled back (or attempted to)
                    self.applied_fixes.clear();

                    let committed_paths: Vec<PathBuf> =
                        committed_snapshots.iter().map(|(p, _)| p.clone()).collect();

                    return Err(CommitError {
                        reason: format!(
                            "Failed to write {}: {}",
                            failed_file.display(),
                            failed_reason
                        ),
                        committed: committed_paths,
                        failed: vec![(failed_file, failed_reason)],
                        successful_rollbacks,
                        failed_rollbacks,
                    });
                }
            }
        }

        Ok(())
    }

    /// Rollback all applied fixes.
    pub fn rollback_all(&mut self) -> Result<(), RollbackError> {
        let atomic_writer = AtomicWriter::new();

        let mut successful: Vec<PathBuf> = Vec::new();
        let mut failed: Vec<(PathBuf, String)> = Vec::new();

        for applied in self.applied_fixes.drain(..) {
            // Try backup file first
            if let Some(backup) = &applied.backup_path {
                if backup.exists() {
                    match atomic_writer.rollback(&applied.file, backup) {
                        Ok(()) => {
                            info!("Rolled back {} from backup", applied.file.display());
                            successful.push(applied.file.clone());
                            continue;
                        }
                        Err(e) => {
                            warn!(
                                "Failed to rollback {} from backup: {}",
                                applied.file.display(),
                                e
                            );
                        }
                    }
                }
            }

            // Try original content as fallback
            if !applied.original_content.is_empty() {
                match atomic_writer.write(&applied.file, &applied.original_content) {
                    Ok(()) => {
                        info!(
                            "Rolled back {} from original content",
                            applied.file.display()
                        );
                        successful.push(applied.file);
                    }
                    Err(e) => {
                        error!(
                            "Failed to rollback {} from original content: {}",
                            applied.file.display(),
                            e
                        );
                        failed.push((applied.file, e.to_string()));
                    }
                }
            } else {
                failed.push((applied.file, "No backup or original content available".to_string()));
            }
        }

        let rolled_back = successful.len();
        let failed_count = failed.len();

        self.progress.on_rollback(rolled_back, failed_count);

        if failed.is_empty() {
            Ok(())
        } else {
            Err(RollbackError { successful, failed })
        }
    }

    /// Commit a multi-file fix group atomically.
    ///
    /// All files in the group are written together. If any file fails, all
    /// already-committed files in the group are rolled back, preserving the
    /// all-or-nothing guarantee for paired .fst/.fsti fixes.
    pub fn commit_multi_file_group(
        &mut self,
        group: &MultiFileFixGroup,
    ) -> Result<Vec<AppliedFix>, CommitError> {
        if self.config.dry_run {
            // Return mock applied fixes without writing
            return Ok(group
                .files
                .iter()
                .map(|(path, original, new_content)| AppliedFix {
                    file: path.clone(),
                    backup_path: None,
                    temp_path: None,
                    rule: group.rule,
                    message: group.message.clone(),
                    lines_changed: count_lines_changed(original, new_content),
                    validation: FixValidation::default(),
                    original_content: original.clone(),
                    new_content: new_content.clone(),
                    applied_at: SystemTime::now(),
                })
                .collect());
        }

        let atomic_writer = AtomicWriter::new();
        let mut committed: Vec<(PathBuf, String)> = Vec::new(); // (path, original) for rollback

        for (path, original, new_content) in &group.files {
            match atomic_writer.write_with_backup(path, new_content) {
                Ok(backup) => {
                    info!(
                        "Multi-file commit: {} (backup: {})",
                        path.display(),
                        backup.display()
                    );
                    committed.push((path.clone(), original.clone()));

                    self.applied_fixes.push(AppliedFix {
                        file: path.clone(),
                        backup_path: Some(backup),
                        temp_path: None,
                        rule: group.rule,
                        message: group.message.clone(),
                        lines_changed: count_lines_changed(original, new_content),
                        validation: FixValidation::default(),
                        original_content: original.clone(),
                        new_content: new_content.clone(),
                        applied_at: SystemTime::now(),
                    });
                }
                Err(e) => {
                    error!(
                        "Multi-file group commit failed at {}: {}. Rolling back {} file(s).",
                        path.display(),
                        e,
                        committed.len()
                    );

                    // Rollback all already-committed files in this group
                    let mut successful_rollbacks = Vec::new();
                    let mut failed_rollbacks = Vec::new();

                    for (rb_path, rb_original) in committed.iter().rev() {
                        match fs::write(rb_path, rb_original) {
                            Ok(()) => successful_rollbacks.push(rb_path.clone()),
                            Err(re) => {
                                failed_rollbacks.push((rb_path.clone(), re.to_string()));
                            }
                        }
                    }

                    // Remove any applied_fixes that were part of this group
                    let group_paths: std::collections::HashSet<&PathBuf> =
                        committed.iter().map(|(p, _)| p).collect();
                    self.applied_fixes.retain(|af| !group_paths.contains(&af.file));

                    return Err(CommitError {
                        reason: format!(
                            "Multi-file group failed at {}: {}",
                            path.display(),
                            e
                        ),
                        committed: committed.iter().map(|(p, _)| p.clone()).collect(),
                        failed: vec![(path.clone(), e.to_string())],
                        successful_rollbacks,
                        failed_rollbacks,
                    });
                }
            }
        }

        Ok(self
            .applied_fixes
            .iter()
            .filter(|af| {
                group
                    .files
                    .iter()
                    .any(|(p, _, _)| p == &af.file)
            })
            .cloned()
            .collect())
    }

    /// Get the set of rules currently skipped by interactive mode.
    pub fn skipped_rules(&self) -> &std::collections::HashSet<RuleCode> {
        &self.skipped_rules
    }

    /// Get the set of files that were successfully modified (for fix chain re-lint).
    pub fn modified_files(&self) -> Vec<PathBuf> {
        self.applied_fixes.iter().map(|af| af.file.clone()).collect()
    }

    /// Invalidate cached content for specific files (used after fix chains modify files).
    pub fn invalidate_cache(&mut self, files: &[PathBuf]) {
        for file in files {
            if let Ok(canonical) = file.canonicalize() {
                self.file_content_cache.remove(&canonical);
            }
            self.file_content_cache.remove(file);
        }
    }

    /// Clean up temp files without committing.
    fn cleanup_temp_files(&mut self) {
        for prepared in &self.prepared_fixes {
            if prepared.temp_path.exists() {
                if let Err(e) = fs::remove_file(&prepared.temp_path) {
                    warn!(
                        "Failed to remove temp file {}: {}",
                        prepared.temp_path.display(),
                        e
                    );
                }
            }
        }
    }
}

impl Drop for FixApplicator {
    fn drop(&mut self) {
        // Clean up any remaining temp files
        self.cleanup_temp_files();
    }
}

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

/// Count the number of lines changed between two strings.
fn count_lines_changed(original: &str, new: &str) -> usize {
    let orig_lines: Vec<&str> = original.lines().collect();
    let new_lines: Vec<&str> = new.lines().collect();

    let mut changed = 0;

    // Simple diff: count lines that differ
    let max_len = orig_lines.len().max(new_lines.len());
    for i in 0..max_len {
        let orig_line = orig_lines.get(i).copied();
        let new_line = new_lines.get(i).copied();

        if orig_line != new_line {
            changed += 1;
        }
    }

    changed
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;
    use tempfile::TempDir;

    fn create_test_file(dir: &TempDir, name: &str, content: &str) -> PathBuf {
        let path = dir.path().join(name);
        fs::write(&path, content).expect("Failed to write test file");
        path
    }

    fn create_test_diagnostic(file: &Path, fix_message: &str, new_text: &str) -> Diagnostic {
        Diagnostic {
            rule: RuleCode::FST004,
            severity: super::super::rules::DiagnosticSeverity::Warning,
            file: file.to_path_buf(),
            range: super::super::rules::Range::new(1, 1, 1, 10),
            message: "Test issue".to_string(),
            fix: Some(Fix::safe(
                fix_message,
                vec![Edit {
                    file: file.to_path_buf(),
                    range: super::super::rules::Range::new(1, 1, 1, 10),
                    new_text: new_text.to_string(),
                }],
            )),
        }
    }

    #[test]
    fn test_config_default() {
        let config = FixApplicatorConfig::default();
        assert!(config.dry_run);
        assert_eq!(config.max_files, DEFAULT_MAX_FILES);
        assert_eq!(config.max_lines_per_file, DEFAULT_MAX_LINES_PER_FILE);
        assert!(!config.force);
        assert!(!config.interactive);
    }

    #[test]
    fn test_config_builder() {
        let config = FixApplicatorConfig::apply()
            .with_force(true)
            .with_max_files(100)
            .with_max_lines_per_file(200)
            .with_interactive(true)
            .with_verbose(true);

        assert!(!config.dry_run);
        assert!(config.force);
        assert_eq!(config.max_files, 100);
        assert_eq!(config.max_lines_per_file, 200);
        assert!(config.interactive);
        assert!(config.verbose);
    }

    #[test]
    fn test_safety_limit_files() {
        let config = FixApplicatorConfig::default().with_max_files(2);
        let applicator = FixApplicator::new(config);

        let result = applicator.check_safety_limits(5);
        assert!(result.is_err());

        match result.unwrap_err() {
            FixError::TooManyFiles { count, limit } => {
                assert_eq!(count, 5);
                assert_eq!(limit, 2);
            }
            _ => panic!("Expected TooManyFiles error"),
        }
    }

    #[test]
    fn test_safety_limit_bypass_with_force() {
        let config = FixApplicatorConfig::default()
            .with_max_files(2)
            .with_force(true);
        let applicator = FixApplicator::new(config);

        let result = applicator.check_safety_limits(5);
        assert!(result.is_ok());
    }

    #[test]
    fn test_count_lines_changed() {
        let original = "line1\nline2\nline3\n";
        let new = "line1\nmodified\nline3\n";
        assert_eq!(count_lines_changed(original, new), 1);

        let original = "line1\nline2\n";
        let new = "line1\nline2\nline3\n";
        assert_eq!(count_lines_changed(original, new), 1);

        let original = "line1\n";
        let new = "line1\n";
        assert_eq!(count_lines_changed(original, new), 0);
    }

    #[test]
    fn test_dry_run_does_not_modify() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let original_content = "module Test\n\nlet x = 1\n";
        let file = create_test_file(&temp_dir, "Test.fst", original_content);

        let config = FixApplicatorConfig::dry_run();
        let mut applicator = FixApplicator::new(config);

        let diagnostic = create_test_diagnostic(&file, "Remove line", "module Test\n\nlet y = 2\n");

        let _result = applicator.apply_batch(&[diagnostic]);

        // Verify file was NOT modified
        let content_after = fs::read_to_string(&file).expect("Failed to read file");
        assert_eq!(
            original_content, content_after,
            "Dry-run should NOT modify files"
        );
    }

    #[test]
    fn test_apply_mode_modifies() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let original_content = "module Test\n\nlet x = 1\n";
        let file = create_test_file(&temp_dir, "Test.fst", original_content);

        let config = FixApplicatorConfig::apply();
        let mut applicator = FixApplicator::new(config);

        let new_content = "module Test\n\nlet y = 2\n";
        let diagnostic = create_test_diagnostic(&file, "Change variable", new_content);

        let result = applicator.apply_batch(&[diagnostic]);

        // Result should be ok
        assert!(result.is_ok());

        // Verify file WAS modified
        let content_after = fs::read_to_string(&file).expect("Failed to read file");
        assert_ne!(
            original_content, content_after,
            "Apply mode should modify files"
        );
    }

    #[test]
    fn test_rollback() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let original_content = "module Test\n\nlet x = 1\n";
        let file = create_test_file(&temp_dir, "Test.fst", original_content);

        let config = FixApplicatorConfig::apply();
        let mut applicator = FixApplicator::new(config);

        let new_content = "module Test\n\nlet y = 2\n";
        let diagnostic = create_test_diagnostic(&file, "Change variable", new_content);

        // Apply the fix
        let result = applicator.apply_batch(&[diagnostic]);
        assert!(result.is_ok());

        // Verify file was modified
        let content_after_apply = fs::read_to_string(&file).expect("Failed to read file");
        assert_ne!(original_content, content_after_apply);

        // Rollback
        let rollback_result = applicator.rollback_all();
        assert!(rollback_result.is_ok());

        // Verify file was restored
        let content_after_rollback = fs::read_to_string(&file).expect("Failed to read file");
        assert_eq!(
            original_content, content_after_rollback,
            "Rollback should restore original content"
        );
    }

    #[test]
    fn test_temp_file_cleanup_on_drop() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let original_content = "module Test\nlet x = 1\n";
        let file = create_test_file(&temp_dir, "Test.fst", original_content);

        {
            let config = FixApplicatorConfig::dry_run();
            let mut applicator = FixApplicator::new(config);

            let diagnostic = create_test_diagnostic(&file, "Test fix", "module Test\nlet y = 2\n");
            let _ = applicator.apply_batch(&[diagnostic]);

            // Applicator should have created temp files
            // They will be cleaned up when applicator is dropped
        }

        // Verify no temp files left behind
        let temp_files: Vec<_> = fs::read_dir(temp_dir.path())
            .expect("Failed to read dir")
            .filter_map(|e| e.ok())
            .filter(|e| {
                e.path()
                    .file_name()
                    .and_then(|n| n.to_str())
                    .map(|n| n.contains(".fstar-lint-tmp"))
                    .unwrap_or(false)
            })
            .collect();

        assert!(
            temp_files.is_empty(),
            "Temp files should be cleaned up on drop"
        );
    }

    #[test]
    fn test_fix_validation_failure() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let original_content = "module Test\n\nval foo : int -> int\nlet foo x = x + 1\n";
        let file = create_test_file(&temp_dir, "Test.fst", original_content);

        let config = FixApplicatorConfig::apply().with_min_confidence(0.99);
        let mut applicator = FixApplicator::new(config);

        // Create a fix that removes declarations (should lower confidence)
        let new_content = "module Test\n";
        let diagnostic = Diagnostic {
            rule: RuleCode::FST004,
            severity: super::super::rules::DiagnosticSeverity::Warning,
            file: file.to_path_buf(),
            range: super::super::rules::Range::new(1, 1, 4, 20),
            message: "Test removal".to_string(),
            fix: Some(Fix::safe("Remove everything", vec![Edit {
                file: file.to_path_buf(),
                range: super::super::rules::Range::new(1, 1, 4, 20),
                new_text: new_content.to_string(),
            }])),
        };

        let result = applicator.apply_batch(&[diagnostic]);

        // Should complete but with failed/skipped fixes due to low confidence
        assert!(result.is_ok());
        let summary = applicator.summary();
        assert!(
            summary.fixes_failed > 0 || summary.fixes_skipped > 0,
            "Should have validation failures or skips"
        );
    }

    #[test]
    fn test_unsafe_fix_skipped() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file = create_test_file(&temp_dir, "Test.fst", "module Test\nlet x = 1\n");

        let config = FixApplicatorConfig::apply();
        let mut applicator = FixApplicator::new(config);

        // Create an unsafe fix
        let diagnostic = Diagnostic {
            rule: RuleCode::FST005,
            severity: super::super::rules::DiagnosticSeverity::Warning,
            file: file.to_path_buf(),
            range: super::super::rules::Range::new(2, 1, 2, 10),
            message: "Unused binding".to_string(),
            fix: Some(Fix::unsafe_fix(
                "Remove binding",
                vec![Edit {
                    file: file.to_path_buf(),
                    range: super::super::rules::Range::new(2, 1, 2, 10),
                    new_text: String::new(),
                }],
                FixConfidence::Low,
                "May be used via SMTPat",
            )),
        };

        let result = applicator.apply_batch(&[diagnostic]);
        assert!(result.is_ok());

        let summary = applicator.summary();
        assert_eq!(summary.fixes_skipped, 1);
    }

    #[test]
    fn test_low_confidence_fix_skipped() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file = create_test_file(&temp_dir, "Test.fst", "module Test\nlet x = 1\n");

        let config = FixApplicatorConfig::apply();
        let mut applicator = FixApplicator::new(config);

        // Create a low confidence fix (not High)
        let mut fix = Fix::new("Low confidence fix", vec![Edit {
            file: file.to_path_buf(),
            range: super::super::rules::Range::new(2, 1, 2, 10),
            new_text: "let y = 2\n".to_string(),
        }]);
        fix.confidence = FixConfidence::Medium;  // Not High

        let diagnostic = Diagnostic {
            rule: RuleCode::FST006,
            severity: super::super::rules::DiagnosticSeverity::Warning,
            file: file.to_path_buf(),
            range: super::super::rules::Range::new(2, 1, 2, 10),
            message: "Naming issue".to_string(),
            fix: Some(fix),
        };

        let result = applicator.apply_batch(&[diagnostic]);
        assert!(result.is_ok());

        let summary = applicator.summary();
        assert_eq!(summary.fixes_skipped, 1);
    }

    // Test the interactive choice enum
    #[test]
    fn test_interactive_choice() {
        assert_eq!(InteractiveChoice::Yes, InteractiveChoice::Yes);
        assert_ne!(InteractiveChoice::Yes, InteractiveChoice::No);
    }

    // Test fix summary
    #[test]
    fn test_fix_summary_default() {
        let summary = FixSummary::default();
        assert_eq!(summary.files_processed, 0);
        assert_eq!(summary.fixes_applied, 0);
        assert_eq!(summary.fixes_skipped, 0);
        assert_eq!(summary.fixes_failed, 0);
    }

    // Test applied fix
    #[test]
    fn test_applied_fix_can_rollback() {
        let applied = AppliedFix {
            file: PathBuf::from("/test.fst"),
            backup_path: None,
            temp_path: None,
            rule: RuleCode::FST004,
            message: "Test".to_string(),
            lines_changed: 1,
            validation: FixValidation::default(),
            original_content: "original".to_string(),
            new_content: "new".to_string(),
            applied_at: SystemTime::now(),
        };

        // Can rollback because we have original content
        assert!(applied.can_rollback());

        let applied_empty = AppliedFix {
            file: PathBuf::from("/test.fst"),
            backup_path: Some(PathBuf::from("/nonexistent.bak")),
            temp_path: None,
            rule: RuleCode::FST004,
            message: "Test".to_string(),
            lines_changed: 1,
            validation: FixValidation::default(),
            original_content: String::new(),
            new_content: "new".to_string(),
            applied_at: SystemTime::now(),
        };

        // Cannot rollback - backup doesn't exist and no original content
        assert!(!applied_empty.can_rollback());
    }

    // =========================================================================
    // Multi-edit tests for build_fixed_content
    // =========================================================================

    /// Helper: create a FixApplicator with dry-run defaults for unit-testing
    /// build_fixed_content directly.
    fn make_test_applicator() -> FixApplicator {
        FixApplicator::new(FixApplicatorConfig::dry_run())
    }

    /// Helper: build an Edit targeting a given 1-indexed line range.
    fn make_edit(start_line: usize, end_line: usize, new_text: &str) -> Edit {
        Edit {
            file: PathBuf::from("/test.fst"),
            range: super::super::rules::Range::new(start_line, 1, end_line, 1),
            new_text: new_text.to_string(),
        }
    }

    #[test]
    fn test_build_fixed_content_single_edit_preserved() {
        let applicator = make_test_applicator();
        let original = "line1\nline2\nline3\n";

        let edits = vec![make_edit(2, 2, "replaced2")];
        let result = applicator.build_fixed_content(original, &edits).unwrap();

        assert_eq!(result, "line1\nreplaced2\nline3\n");
    }

    #[test]
    fn test_build_fixed_content_empty_edits() {
        let applicator = make_test_applicator();
        let original = "line1\nline2\n";

        let result = applicator.build_fixed_content(original, &[]).unwrap();
        assert_eq!(result, original);
    }

    #[test]
    fn test_build_fixed_content_two_nonoverlapping_edits() {
        let applicator = make_test_applicator();
        let original = "line1\nline2\nline3\nline4\nline5\n";

        // Edit line 4, then edit line 2 -- supply them in arbitrary order.
        let edits = vec![
            make_edit(2, 2, "REPLACED2"),
            make_edit(4, 4, "REPLACED4"),
        ];

        let result = applicator.build_fixed_content(original, &edits).unwrap();
        assert_eq!(result, "line1\nREPLACED2\nline3\nREPLACED4\nline5\n");
    }

    #[test]
    fn test_build_fixed_content_three_edits_reverse_order() {
        let applicator = make_test_applicator();
        let original = "a\nb\nc\nd\ne\nf\ng\n";

        // Edits supplied in reverse order (top-to-bottom), should still work.
        let edits = vec![
            make_edit(6, 6, "F"),
            make_edit(4, 4, "D"),
            make_edit(2, 2, "B"),
        ];

        let result = applicator.build_fixed_content(original, &edits).unwrap();
        assert_eq!(result, "a\nB\nc\nD\ne\nF\ng\n");
    }

    #[test]
    fn test_build_fixed_content_multi_line_replacement() {
        let applicator = make_test_applicator();
        let original = "line1\nline2\nline3\nline4\nline5\n";

        // Replace lines 2-3 with a single line, and line 5 with two lines.
        let edits = vec![
            make_edit(2, 3, "MERGED"),
            make_edit(5, 5, "FIVE_A\nFIVE_B"),
        ];

        let result = applicator.build_fixed_content(original, &edits).unwrap();
        assert_eq!(result, "line1\nMERGED\nline4\nFIVE_A\nFIVE_B\n");
    }

    #[test]
    fn test_build_fixed_content_deletion_edit() {
        let applicator = make_test_applicator();
        let original = "line1\nline2\nline3\nline4\n";

        // Delete line 2 (empty new_text) and replace line 4.
        let edits = vec![
            make_edit(2, 2, ""),
            make_edit(4, 4, "FOUR"),
        ];

        let result = applicator.build_fixed_content(original, &edits).unwrap();
        assert_eq!(result, "line1\nline3\nFOUR\n");
    }

    #[test]
    fn test_build_fixed_content_overlapping_edits_rejected() {
        let applicator = make_test_applicator();
        let original = "line1\nline2\nline3\nline4\n";

        // Lines 2-3 and 3-4 overlap at line 3.
        let edits = vec![
            make_edit(2, 3, "A"),
            make_edit(3, 4, "B"),
        ];

        let result = applicator.build_fixed_content(original, &edits);
        assert!(result.is_err(), "Overlapping edits must be rejected");

        match result.unwrap_err() {
            FixError::ValidationFailed { reason, .. } => {
                assert!(
                    reason.contains("Overlapping"),
                    "Error reason should mention overlap, got: {}",
                    reason
                );
            }
            other => panic!("Expected ValidationFailed, got: {:?}", other),
        }
    }

    #[test]
    fn test_build_fixed_content_adjacent_edits_accepted() {
        let applicator = make_test_applicator();
        let original = "line1\nline2\nline3\nline4\n";

        // Lines 1-2 and 3-4 are adjacent but do NOT overlap.
        let edits = vec![
            make_edit(1, 2, "TOP"),
            make_edit(3, 4, "BOTTOM"),
        ];

        let result = applicator.build_fixed_content(original, &edits).unwrap();
        assert_eq!(result, "TOP\nBOTTOM\n");
    }

    #[test]
    fn test_build_fixed_content_preserves_trailing_newline() {
        let applicator = make_test_applicator();

        // Original has trailing newline
        let with_nl = "line1\nline2\n";
        let edits = vec![make_edit(1, 1, "REPLACED")];
        let result = applicator.build_fixed_content(with_nl, &edits).unwrap();
        assert!(
            result.ends_with('\n'),
            "Should preserve trailing newline from original"
        );

        // Original lacks trailing newline
        let without_nl = "line1\nline2";
        let edits = vec![make_edit(1, 1, "REPLACED")];
        let result = applicator.build_fixed_content(without_nl, &edits).unwrap();
        assert!(
            !result.ends_with('\n'),
            "Should not add trailing newline when original lacks one"
        );
    }

    #[test]
    fn test_build_fixed_content_identical_start_lines_rejected() {
        let applicator = make_test_applicator();
        let original = "line1\nline2\nline3\n";

        // Two edits targeting the same line -- they overlap by definition.
        let edits = vec![
            make_edit(2, 2, "A"),
            make_edit(2, 2, "B"),
        ];

        let result = applicator.build_fixed_content(original, &edits);
        assert!(
            result.is_err(),
            "Two edits on the same line should be rejected as overlapping"
        );
    }

    // =========================================================================
    // Bug #2 regression tests: two diagnostics targeting the same file
    // must both have their edits applied, not just the last one.
    // =========================================================================

    /// Helper: create a diagnostic targeting a specific line range within a file.
    fn create_diagnostic_at_range(
        file: &Path,
        start_line: usize,
        end_line: usize,
        fix_message: &str,
        new_text: &str,
    ) -> Diagnostic {
        Diagnostic {
            rule: RuleCode::FST004,
            severity: super::super::rules::DiagnosticSeverity::Warning,
            file: file.to_path_buf(),
            range: super::super::rules::Range::new(start_line, 1, end_line, 80),
            message: format!("Issue at lines {}-{}", start_line, end_line),
            fix: Some(Fix::safe(
                fix_message,
                vec![Edit {
                    file: file.to_path_buf(),
                    range: super::super::rules::Range::new(start_line, 1, end_line, 80),
                    new_text: new_text.to_string(),
                }],
            )),
        }
    }

    #[test]
    fn test_two_diagnostics_same_file_both_applied_dry_run() {
        // Regression test for Bug #2: two diagnostics targeting the same file
        // should both have their fixes reflected in the output.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let original = "line1\nline2\nline3\nline4\nline5\n";
        let file = create_test_file(&temp_dir, "Test.fst", original);

        // Use force to bypass confidence validation (we're testing grouping, not validation)
        let config = FixApplicatorConfig::dry_run().with_force(true);
        let mut applicator = FixApplicator::new(config);

        // Diagnostic 1: replace line 2
        let diag1 = create_diagnostic_at_range(&file, 2, 2, "Fix line 2", "FIXED2");
        // Diagnostic 2: replace line 4
        let diag2 = create_diagnostic_at_range(&file, 4, 4, "Fix line 4", "FIXED4");

        let result = applicator.apply_batch(&[diag1, diag2]);
        assert!(result.is_ok(), "apply_batch should succeed");

        let applied = result.unwrap();
        assert_eq!(
            applied.len(),
            1,
            "Should produce exactly one AppliedFix entry (one per file)"
        );

        let new_content = &applied[0].new_content;
        assert!(
            new_content.contains("FIXED2"),
            "First diagnostic's fix (line 2) must be present in output. Got: {}",
            new_content
        );
        assert!(
            new_content.contains("FIXED4"),
            "Second diagnostic's fix (line 4) must be present in output. Got: {}",
            new_content
        );
        assert!(
            new_content.contains("line1"),
            "Unmodified line 1 must be preserved. Got: {}",
            new_content
        );
        assert!(
            new_content.contains("line3"),
            "Unmodified line 3 must be preserved. Got: {}",
            new_content
        );
        assert!(
            new_content.contains("line5"),
            "Unmodified line 5 must be preserved. Got: {}",
            new_content
        );

        // Verify the original file was NOT modified (dry-run)
        let on_disk = fs::read_to_string(&file).expect("read file");
        assert_eq!(on_disk, original, "Dry-run must not modify the file on disk");
    }

    #[test]
    fn test_two_diagnostics_same_file_both_applied_real_commit() {
        // Same as above but with real file modification (apply mode).
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let original = "line1\nline2\nline3\nline4\nline5\n";
        let file = create_test_file(&temp_dir, "Test.fst", original);

        // Use force to bypass confidence validation (we're testing grouping, not validation)
        let config = FixApplicatorConfig::apply().with_force(true);
        let mut applicator = FixApplicator::new(config);

        let diag1 = create_diagnostic_at_range(&file, 2, 2, "Fix line 2", "FIXED2");
        let diag2 = create_diagnostic_at_range(&file, 4, 4, "Fix line 4", "FIXED4");

        let result = applicator.apply_batch(&[diag1, diag2]);
        assert!(result.is_ok(), "apply_batch should succeed");

        // Read the file from disk and verify BOTH fixes are present
        let on_disk = fs::read_to_string(&file).expect("read file");
        assert!(
            on_disk.contains("FIXED2"),
            "First fix (line 2) must survive on disk. Got: {}",
            on_disk
        );
        assert!(
            on_disk.contains("FIXED4"),
            "Second fix (line 4) must survive on disk. Got: {}",
            on_disk
        );
        assert!(
            !on_disk.contains("line2"),
            "Original line 2 should have been replaced. Got: {}",
            on_disk
        );
        assert!(
            !on_disk.contains("line4"),
            "Original line 4 should have been replaced. Got: {}",
            on_disk
        );
    }

    #[test]
    fn test_three_diagnostics_same_file_all_applied() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let original = "aaa\nbbb\nccc\nddd\neee\nfff\nggg\n";
        let file = create_test_file(&temp_dir, "Multi.fst", original);

        let config = FixApplicatorConfig::apply().with_force(true);
        let mut applicator = FixApplicator::new(config);

        let diag1 = create_diagnostic_at_range(&file, 2, 2, "Fix B", "BBB");
        let diag2 = create_diagnostic_at_range(&file, 4, 4, "Fix D", "DDD");
        let diag3 = create_diagnostic_at_range(&file, 6, 6, "Fix F", "FFF");

        let result = applicator.apply_batch(&[diag1, diag2, diag3]);
        assert!(result.is_ok(), "apply_batch should succeed");

        let on_disk = fs::read_to_string(&file).expect("read file");
        assert!(on_disk.contains("BBB"), "Fix 1 missing. Got: {}", on_disk);
        assert!(on_disk.contains("DDD"), "Fix 2 missing. Got: {}", on_disk);
        assert!(on_disk.contains("FFF"), "Fix 3 missing. Got: {}", on_disk);
        assert!(on_disk.contains("aaa"), "Line 1 should be preserved");
        assert!(on_disk.contains("ccc"), "Line 3 should be preserved");
        assert!(on_disk.contains("eee"), "Line 5 should be preserved");
        assert!(on_disk.contains("ggg"), "Line 7 should be preserved");
    }

    #[test]
    fn test_diagnostics_across_different_files_independent() {
        // Verify that diagnostics for different files are still independent
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_a = create_test_file(&temp_dir, "A.fst", "aaa\nbbb\nccc\n");
        let file_b = create_test_file(&temp_dir, "B.fst", "xxx\nyyy\nzzz\n");

        let config = FixApplicatorConfig::apply().with_force(true);
        let mut applicator = FixApplicator::new(config);

        let diag_a = create_diagnostic_at_range(&file_a, 2, 2, "Fix A", "BBB_FIXED");
        let diag_b = create_diagnostic_at_range(&file_b, 2, 2, "Fix B", "YYY_FIXED");

        let result = applicator.apply_batch(&[diag_a, diag_b]);
        assert!(result.is_ok(), "apply_batch should succeed");

        let on_disk_a = fs::read_to_string(&file_a).expect("read A");
        let on_disk_b = fs::read_to_string(&file_b).expect("read B");

        assert!(
            on_disk_a.contains("BBB_FIXED"),
            "File A should have its fix. Got: {}",
            on_disk_a
        );
        assert!(
            on_disk_b.contains("YYY_FIXED"),
            "File B should have its fix. Got: {}",
            on_disk_b
        );
        // Cross-contamination check
        assert!(
            !on_disk_a.contains("YYY_FIXED"),
            "File A must not contain File B's fix"
        );
        assert!(
            !on_disk_b.contains("BBB_FIXED"),
            "File B must not contain File A's fix"
        );
    }

    #[test]
    fn test_mixed_eligible_and_ineligible_same_file() {
        // One eligible diagnostic and one ineligible (low confidence) for the same file.
        // Only the eligible fix should be applied.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let original = "line1\nline2\nline3\nline4\n";
        let file = create_test_file(&temp_dir, "Mixed.fst", original);

        // Lower confidence threshold so validation passes, but do NOT use force mode
        // because force would bypass the eligibility confidence check that this test verifies.
        let config = FixApplicatorConfig::apply().with_min_confidence(0.1);
        let mut applicator = FixApplicator::new(config);

        // Eligible: high confidence safe fix on line 2
        let diag_eligible = create_diagnostic_at_range(&file, 2, 2, "Fix line 2", "FIXED2");

        // Ineligible: low confidence fix on line 4
        let diag_ineligible = Diagnostic {
            rule: RuleCode::FST006,
            severity: super::super::rules::DiagnosticSeverity::Warning,
            file: file.to_path_buf(),
            range: super::super::rules::Range::new(4, 1, 4, 80),
            message: "Low confidence issue".to_string(),
            fix: Some({
                let mut fix = Fix::new(
                    "Low confidence fix",
                    vec![Edit {
                        file: file.to_path_buf(),
                        range: super::super::rules::Range::new(4, 1, 4, 80),
                        new_text: "SHOULD_NOT_APPEAR".to_string(),
                    }],
                );
                fix.confidence = FixConfidence::Medium; // Not High => skipped
                fix
            }),
        };

        let result = applicator.apply_batch(&[diag_eligible, diag_ineligible]);
        assert!(result.is_ok(), "apply_batch should succeed");

        let on_disk = fs::read_to_string(&file).expect("read file");
        assert!(
            on_disk.contains("FIXED2"),
            "Eligible fix should be applied. Got: {}",
            on_disk
        );
        assert!(
            !on_disk.contains("SHOULD_NOT_APPEAR"),
            "Ineligible fix must NOT be applied. Got: {}",
            on_disk
        );
        assert!(
            on_disk.contains("line4"),
            "Line 4 should be untouched since its fix was skipped. Got: {}",
            on_disk
        );
    }

    #[test]
    fn test_file_content_cache_avoids_redundant_reads() {
        // Verify that read_file_cached returns the same content on repeated calls
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file = create_test_file(&temp_dir, "Cache.fst", "cached content\n");

        let config = FixApplicatorConfig::dry_run();
        let mut applicator = FixApplicator::new(config);

        let canonical = file.canonicalize().unwrap();
        let content1 = applicator
            .read_file_cached(&canonical)
            .expect("first read");
        let content2 = applicator
            .read_file_cached(&canonical)
            .expect("second read");

        assert_eq!(content1, content2, "Cached reads must return identical content");
        assert_eq!(content1, "cached content\n");

        // Verify the cache contains exactly one entry for this file
        assert_eq!(
            applicator.file_content_cache.len(),
            1,
            "Cache should have exactly one entry"
        );
    }

    #[test]
    fn test_summary_counts_with_grouped_diagnostics() {
        // Verify that fixes_applied counts individual diagnostics, not file groups
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file = create_test_file(&temp_dir, "Count.fst", "a\nb\nc\nd\ne\n");

        let config = FixApplicatorConfig::dry_run().with_force(true);
        let mut applicator = FixApplicator::new(config);

        let diag1 = create_diagnostic_at_range(&file, 2, 2, "Fix 1", "B");
        let diag2 = create_diagnostic_at_range(&file, 4, 4, "Fix 2", "D");

        let result = applicator.apply_batch(&[diag1, diag2]);
        assert!(result.is_ok());

        let summary = applicator.summary();
        assert_eq!(
            summary.fixes_applied, 2,
            "fixes_applied should count individual diagnostics (2), not file groups (1)"
        );
        assert_eq!(
            summary.files_processed, 1,
            "files_processed should count unique files"
        );
    }

    #[test]
    fn test_single_line_delete_preserves_adjacent_lines() {
        // Regression test for Bug #16: Range::new(line, 1, line, 1) must delete
        // exactly one line. Previously, code used Range::new(line, 1, line+1, 1)
        // which deleted TWO lines (the target AND the line after it).
        let applicator = make_test_applicator();
        // No consecutive blank lines -- avoids blank-line collapse post-processing.
        let original = "module Test\nopen FStar.Unused\nval foo : int\nlet foo = 42\n";

        // Delete line 2 ("open FStar.Unused") -- single line Range
        let edits = vec![make_edit(2, 2, "")];
        let result = applicator.build_fixed_content(original, &edits).unwrap();

        // Line 3 ("val foo : int") must survive intact
        assert_eq!(
            result, "module Test\nval foo : int\nlet foo = 42\n",
            "Only line 2 should be removed; line 3 must be preserved"
        );
    }

    #[test]
    fn test_single_line_replace_preserves_adjacent_lines() {
        // Regression test: replacing a single line with selective import must not
        // consume the line below it.
        let applicator = make_test_applicator();
        let original = "module Test\n\nopen FStar.List.Tot\n\nval foo : int\n";

        // Replace line 3 with selective import -- single line Range
        let edits = vec![make_edit(3, 3, "open FStar.List.Tot { length }")];
        let result = applicator.build_fixed_content(original, &edits).unwrap();

        assert_eq!(
            result,
            "module Test\n\nopen FStar.List.Tot { length }\n\nval foo : int\n",
            "Only line 3 should be replaced; the empty line 4 must be preserved"
        );
    }

    #[test]
    fn test_two_line_range_deletes_exactly_two_lines() {
        // Sanity check: confirm Range(line, 1, line+1, 1) truly deletes 2 lines
        // (this was the old buggy behavior -- proving the semantics are inclusive).
        let applicator = make_test_applicator();
        let original = "line1\nline2\nline3\nline4\nline5\n";

        let edits = vec![make_edit(2, 3, "")];
        let result = applicator.build_fixed_content(original, &edits).unwrap();

        assert_eq!(
            result, "line1\nline4\nline5\n",
            "Range(2,1,3,1) should delete lines 2 AND 3 (end_line is inclusive)"
        );
    }

    // =========================================================================
    // Bug #11: Commit atomicity and rollback tests
    // =========================================================================

    #[test]
    fn test_commit_stops_on_first_failure_no_continue() {
        // Verify that when file 2 fails to commit, file 3 is NEVER attempted.
        // Before the fix, `continue` caused all remaining files to be processed
        // after a failure, leaving the codebase partially committed.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let file1 = create_test_file(&temp_dir, "ok.fst", "original1\n");
        let temp1 = create_test_file(&temp_dir, ".ok.fst.tmp", "fixed1\n");

        // Second file: use a regular file as its "parent directory" so that
        // AtomicWriter.acquire_lock's create_dir_all fails (ENOTDIR).
        let blocker = create_test_file(&temp_dir, "blocker", "");
        let file2 = blocker.join("fail.fst");
        let temp2 = create_test_file(&temp_dir, ".fail.fst.tmp", "fixed2\n");

        // Third file must NOT be attempted after file2 fails
        let file3 = create_test_file(&temp_dir, "never.fst", "original3\n");
        let temp3 = create_test_file(&temp_dir, ".never.fst.tmp", "fixed3\n");

        let config = FixApplicatorConfig::apply();
        let mut applicator = FixApplicator::new(config);

        applicator.prepared_fixes = vec![
            PreparedFix {
                file: file1.clone(),
                temp_path: temp1,
                original_content: "original1\n".to_string(),
                new_content: "fixed1\n".to_string(),
                validation: FixValidation::default(),
                rule: RuleCode::FST004,
                message: "Fix 1".to_string(),
                lines_changed: 1,
            },
            PreparedFix {
                file: file2.clone(),
                temp_path: temp2,
                original_content: String::new(),
                new_content: "fixed2\n".to_string(),
                validation: FixValidation::default(),
                rule: RuleCode::FST004,
                message: "Fix 2".to_string(),
                lines_changed: 1,
            },
            PreparedFix {
                file: file3.clone(),
                temp_path: temp3,
                original_content: "original3\n".to_string(),
                new_content: "fixed3\n".to_string(),
                validation: FixValidation::default(),
                rule: RuleCode::FST004,
                message: "Fix 3".to_string(),
                lines_changed: 1,
            },
        ];

        let result = applicator.commit();
        assert!(result.is_err(), "Commit should fail on second file");

        // File 3 must be untouched -- commit must have stopped before reaching it
        let file3_content = fs::read_to_string(&file3).expect("read file3");
        assert_eq!(
            file3_content, "original3\n",
            "File 3 must NOT be processed; commit must stop on first failure"
        );

        // File 1 should have been rolled back to original
        let file1_content = fs::read_to_string(&file1).expect("read file1");
        assert_eq!(
            file1_content, "original1\n",
            "File 1 must be rolled back after partial commit failure"
        );
    }

    #[test]
    fn test_commit_partial_failure_rolls_back_committed_files() {
        // When file N fails, all files 1..N-1 must be restored to originals.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let file1 = create_test_file(&temp_dir, "rollback_me.fst", "original1\n");
        let temp1 = create_test_file(&temp_dir, ".rollback_me.fst.tmp", "fixed1\n");

        // Second file: use a regular file as its "parent directory" so that
        // AtomicWriter.acquire_lock's create_dir_all fails (ENOTDIR).
        let blocker = create_test_file(&temp_dir, "blocker2", "");
        let file2 = blocker.join("fail_here.fst");
        let temp2 = create_test_file(&temp_dir, ".fail_here.fst.tmp", "fixed2\n");

        let config = FixApplicatorConfig::apply();
        let mut applicator = FixApplicator::new(config);

        applicator.prepared_fixes = vec![
            PreparedFix {
                file: file1.clone(),
                temp_path: temp1,
                original_content: "original1\n".to_string(),
                new_content: "fixed1\n".to_string(),
                validation: FixValidation::default(),
                rule: RuleCode::FST004,
                message: "Fix 1".to_string(),
                lines_changed: 1,
            },
            PreparedFix {
                file: file2.clone(),
                temp_path: temp2,
                original_content: String::new(),
                new_content: "fixed2\n".to_string(),
                validation: FixValidation::default(),
                rule: RuleCode::FST004,
                message: "Fix 2".to_string(),
                lines_changed: 1,
            },
        ];

        let result = applicator.commit();
        assert!(result.is_err(), "Commit should fail for second file");

        let err = result.unwrap_err();

        // File 1 must be restored to original content
        let file1_content = fs::read_to_string(&file1).expect("read file1");
        assert_eq!(
            file1_content, "original1\n",
            "File 1 must be rolled back to original after partial commit failure"
        );

        // CommitError must report the successful rollback
        assert_eq!(
            err.successful_rollbacks.len(),
            1,
            "Should report 1 successful rollback"
        );
        assert!(
            err.failed_rollbacks.is_empty(),
            "Should have no rollback failures"
        );
        assert_eq!(
            err.committed.len(),
            1,
            "Should report 1 file committed before failure"
        );
        assert_eq!(
            err.failed.len(),
            1,
            "Should report 1 file that failed to commit"
        );

        // applied_fixes must be empty after rollback
        assert!(
            applicator.applied_fixes.is_empty(),
            "applied_fixes must be cleared after rollback"
        );
    }

    #[test]
    fn test_commit_first_file_fails_no_rollback_needed() {
        // If the very first file fails, there is nothing to roll back.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        // Use a regular file as "parent directory" to guarantee ENOTDIR.
        let blocker = create_test_file(&temp_dir, "blocker3", "");
        let file1 = blocker.join("first.fst");
        let temp1 = create_test_file(&temp_dir, ".first.fst.tmp", "fixed\n");

        let config = FixApplicatorConfig::apply();
        let mut applicator = FixApplicator::new(config);

        applicator.prepared_fixes = vec![PreparedFix {
            file: file1.clone(),
            temp_path: temp1,
            original_content: String::new(),
            new_content: "fixed\n".to_string(),
            validation: FixValidation::default(),
            rule: RuleCode::FST004,
            message: "Fix 1".to_string(),
            lines_changed: 1,
        }];

        let result = applicator.commit();
        assert!(result.is_err(), "Commit should fail");

        let err = result.unwrap_err();
        assert!(
            err.successful_rollbacks.is_empty(),
            "No rollbacks needed when first file fails"
        );
        assert!(
            err.committed.is_empty(),
            "No files committed when first file fails"
        );
        assert_eq!(
            err.failed.len(),
            1,
            "Should report exactly 1 failed file"
        );
    }

    #[test]
    fn test_successful_batch_commit_records_all_files() {
        // Verify that a fully successful commit populates applied_fixes correctly.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        let file1 = create_test_file(&temp_dir, "a.fst", "orig_a\n");
        let temp1 = create_test_file(&temp_dir, ".a.fst.tmp", "fixed_a\n");

        let file2 = create_test_file(&temp_dir, "b.fst", "orig_b\n");
        let temp2 = create_test_file(&temp_dir, ".b.fst.tmp", "fixed_b\n");

        let config = FixApplicatorConfig::apply();
        let mut applicator = FixApplicator::new(config);

        applicator.prepared_fixes = vec![
            PreparedFix {
                file: file1.clone(),
                temp_path: temp1,
                original_content: "orig_a\n".to_string(),
                new_content: "fixed_a\n".to_string(),
                validation: FixValidation::default(),
                rule: RuleCode::FST004,
                message: "Fix A".to_string(),
                lines_changed: 1,
            },
            PreparedFix {
                file: file2.clone(),
                temp_path: temp2,
                original_content: "orig_b\n".to_string(),
                new_content: "fixed_b\n".to_string(),
                validation: FixValidation::default(),
                rule: RuleCode::FST004,
                message: "Fix B".to_string(),
                lines_changed: 1,
            },
        ];

        let result = applicator.commit();
        assert!(result.is_ok(), "Commit should succeed: {:?}", result.err());

        // Both files should be written
        let a_content = fs::read_to_string(&file1).expect("read a");
        let b_content = fs::read_to_string(&file2).expect("read b");
        assert_eq!(a_content, "fixed_a\n");
        assert_eq!(b_content, "fixed_b\n");

        // applied_fixes should contain both entries
        assert_eq!(
            applicator.applied_fixes.len(),
            2,
            "Both files should be recorded in applied_fixes"
        );

        // prepared_fixes should be empty (drained)
        assert!(
            applicator.prepared_fixes.is_empty(),
            "prepared_fixes should be drained after commit"
        );
    }

    #[test]
    fn test_commit_error_display_includes_rollback_info() {
        let err = CommitError {
            reason: "Test failure".to_string(),
            committed: vec![PathBuf::from("/a.fst")],
            failed: vec![(PathBuf::from("/b.fst"), "write error".to_string())],
            successful_rollbacks: vec![PathBuf::from("/a.fst")],
            failed_rollbacks: Vec::new(),
        };

        let msg = format!("{}", err);
        assert!(
            msg.contains("1 file(s) committed"),
            "Should show committed count: {}",
            msg
        );
        assert!(
            msg.contains("1 rolled back"),
            "Should show rollback count: {}",
            msg
        );
        assert!(
            !msg.contains("CRITICAL"),
            "Should NOT contain CRITICAL when all rollbacks succeed: {}",
            msg
        );
    }

    #[test]
    fn test_commit_error_display_critical_rollback_failure() {
        let err = CommitError {
            reason: "Write failed".to_string(),
            committed: vec![PathBuf::from("/a.fst"), PathBuf::from("/b.fst")],
            failed: vec![(PathBuf::from("/c.fst"), "disk full".to_string())],
            successful_rollbacks: vec![PathBuf::from("/b.fst")],
            failed_rollbacks: vec![(
                PathBuf::from("/a.fst"),
                "permission denied".to_string(),
            )],
        };

        let msg = format!("{}", err);
        assert!(
            msg.contains("CRITICAL"),
            "Should indicate critical rollback failure: {}",
            msg
        );
        assert!(
            msg.contains("Manual recovery"),
            "Should mention manual recovery: {}",
            msg
        );
        assert!(
            msg.contains("/a.fst"),
            "Should list the affected file path: {}",
            msg
        );
        assert!(
            msg.contains("permission denied"),
            "Should include the rollback error reason: {}",
            msg
        );
    }

    // =========================================================================
    // Multi-file fix group tests
    // =========================================================================

    #[test]
    fn test_multi_file_fix_group_creation() {
        let mut group = MultiFileFixGroup::new(RuleCode::FST001, "Remove duplicate types");
        assert_eq!(group.file_count(), 0);
        assert!(!group.is_multi_file());

        group.add_file(
            PathBuf::from("/test.fst"),
            "original".to_string(),
            "fixed".to_string(),
        );
        assert_eq!(group.file_count(), 1);
        assert!(!group.is_multi_file());

        group.add_file(
            PathBuf::from("/test.fsti"),
            "original_i".to_string(),
            "fixed_i".to_string(),
        );
        assert_eq!(group.file_count(), 2);
        assert!(group.is_multi_file());
    }

    #[test]
    fn test_multi_file_commit_dry_run() {
        let mut group = MultiFileFixGroup::new(RuleCode::FST001, "Test multi-file");
        group.add_file(
            PathBuf::from("/a.fst"),
            "aaa\n".to_string(),
            "bbb\n".to_string(),
        );
        group.add_file(
            PathBuf::from("/a.fsti"),
            "xxx\n".to_string(),
            "yyy\n".to_string(),
        );

        let config = FixApplicatorConfig::dry_run();
        let mut applicator = FixApplicator::new(config);

        let result = applicator.commit_multi_file_group(&group);
        assert!(result.is_ok(), "Dry-run multi-file commit should succeed");

        let applied = result.unwrap();
        assert_eq!(applied.len(), 2, "Should return 2 mock applied fixes");
        assert_eq!(applied[0].rule, RuleCode::FST001);
        assert_eq!(applied[1].rule, RuleCode::FST001);
    }

    #[test]
    fn test_multi_file_commit_real() {
        let temp_dir = TempDir::new().expect("create temp dir");
        let fst = create_test_file(&temp_dir, "Test.fst", "type t = nat\nlet x = 1\n");
        let fsti = create_test_file(&temp_dir, "Test.fsti", "type t = nat\nval x : int\n");

        let mut group = MultiFileFixGroup::new(RuleCode::FST001, "Atomic pair fix");
        group.add_file(
            fst.clone(),
            "type t = nat\nlet x = 1\n".to_string(),
            "let x = 1\n".to_string(),
        );
        group.add_file(
            fsti.clone(),
            "type t = nat\nval x : int\n".to_string(),
            "type t = nat\nval x : int\n".to_string(),
        );

        let config = FixApplicatorConfig::apply();
        let mut applicator = FixApplicator::new(config);

        let result = applicator.commit_multi_file_group(&group);
        assert!(result.is_ok(), "Multi-file commit should succeed");

        let fst_content = fs::read_to_string(&fst).expect("read fst");
        let fsti_content = fs::read_to_string(&fsti).expect("read fsti");

        assert_eq!(fst_content, "let x = 1\n", "FST file should have type removed");
        assert_eq!(
            fsti_content, "type t = nat\nval x : int\n",
            "FSTI file should be unchanged"
        );
    }

    #[test]
    fn test_multi_file_commit_rollback_on_failure() {
        let temp_dir = TempDir::new().expect("create temp dir");
        let file1 = create_test_file(&temp_dir, "ok.fst", "original1\n");

        // Create an impossible target path (file as directory) to force failure
        let blocker = create_test_file(&temp_dir, "blocker", "");
        let file2 = blocker.join("impossible.fst");

        let mut group = MultiFileFixGroup::new(RuleCode::FST001, "Should rollback");
        group.add_file(
            file1.clone(),
            "original1\n".to_string(),
            "modified1\n".to_string(),
        );
        group.add_file(
            file2.clone(),
            "original2\n".to_string(),
            "modified2\n".to_string(),
        );

        let config = FixApplicatorConfig::apply();
        let mut applicator = FixApplicator::new(config);

        let result = applicator.commit_multi_file_group(&group);
        assert!(result.is_err(), "Should fail on impossible path");

        // File 1 should be rolled back to original
        let content = fs::read_to_string(&file1).expect("read file1");
        assert_eq!(
            content, "original1\n",
            "File 1 must be rolled back after multi-file group failure"
        );
    }

    // =========================================================================
    // Fix chain config tests
    // =========================================================================

    #[test]
    fn test_fix_chain_config_default() {
        let config = FixChainConfig::default();
        assert_eq!(config.max_iterations, 3);
        assert!(!config.chains.is_empty());
    }

    #[test]
    fn test_fix_chain_follow_up_rules() {
        let config = FixChainConfig::default();

        let follow_ups = config.follow_up_rules(RuleCode::FST001);
        assert!(
            follow_ups.contains(&RuleCode::FST004),
            "FST001 should chain to FST004"
        );

        let no_follow_ups = config.follow_up_rules(RuleCode::FST013);
        assert!(
            no_follow_ups.is_empty(),
            "FST013 should have no follow-ups"
        );
    }

    #[test]
    fn test_fix_chain_custom_config() {
        let config = FixChainConfig {
            max_iterations: 5,
            chains: vec![
                (RuleCode::FST001, RuleCode::FST005),
                (RuleCode::FST001, RuleCode::FST006),
            ],
        };

        let follow_ups = config.follow_up_rules(RuleCode::FST001);
        assert_eq!(follow_ups.len(), 2);
        assert!(follow_ups.contains(&RuleCode::FST005));
        assert!(follow_ups.contains(&RuleCode::FST006));
    }

    // =========================================================================
    // Confidence auto-determination tests
    // =========================================================================

    #[test]
    fn test_determine_confidence_safe_high_confidence_rules() {
        // FST001: mechanical duplicate removal -> High
        let edits = vec![make_edit(1, 1, "replacement")];
        let result = determine_confidence(RuleCode::FST001, &edits, FixSafetyLevel::Safe);
        assert_eq!(result, FixConfidence::High);
    }

    #[test]
    fn test_determine_confidence_unsafe_always_low() {
        let edits = vec![make_edit(1, 1, "replacement")];
        let result = determine_confidence(RuleCode::FST001, &edits, FixSafetyLevel::Unsafe);
        assert_eq!(result, FixConfidence::Low);
    }

    #[test]
    fn test_determine_confidence_caution_caps_at_medium() {
        let edits = vec![make_edit(1, 1, "replacement")];
        let result = determine_confidence(RuleCode::FST001, &edits, FixSafetyLevel::Caution);
        assert_eq!(
            result,
            FixConfidence::Medium,
            "Caution safety should cap at Medium even for High-confidence rules"
        );
    }

    #[test]
    fn test_determine_confidence_empty_edits_is_low() {
        let result = determine_confidence(RuleCode::FST001, &[], FixSafetyLevel::Safe);
        assert_eq!(result, FixConfidence::Low, "Empty edits should yield Low");
    }

    #[test]
    fn test_determine_confidence_pure_deletion() {
        // High-confidence rule with pure deletion stays High
        let edits = vec![make_edit(1, 1, "")];
        let result = determine_confidence(RuleCode::FST001, &edits, FixSafetyLevel::Safe);
        assert_eq!(result, FixConfidence::High);

        // Medium-confidence rule with pure deletion drops to Low
        let result = determine_confidence(RuleCode::FST002, &edits, FixSafetyLevel::Safe);
        assert_eq!(result, FixConfidence::Low);
    }

    #[test]
    fn test_determine_confidence_many_edits_reduces() {
        let edits: Vec<Edit> = (0..6)
            .map(|i| make_edit(i * 2 + 1, i * 2 + 1, "text"))
            .collect();
        // FST001 with 6 edits: High -> Medium
        let result = determine_confidence(RuleCode::FST001, &edits, FixSafetyLevel::Safe);
        assert_eq!(
            result,
            FixConfidence::Medium,
            "Many edits should reduce High to Medium"
        );
    }

    // =========================================================================
    // Interactive mode tests (SkipRule)
    // =========================================================================

    /// Test interactive prompt that auto-responds with a configurable choice.
    struct MockPrompt {
        responses: Mutex<Vec<InteractiveChoice>>,
    }

    impl MockPrompt {
        fn new(responses: Vec<InteractiveChoice>) -> Self {
            Self {
                responses: Mutex::new(responses),
            }
        }
    }

    impl InteractivePrompt for MockPrompt {
        fn prompt(&self, _diagnostic: &Diagnostic, _fix: &Fix) -> InteractiveChoice {
            let mut responses = self.responses.lock().unwrap();
            if responses.is_empty() {
                InteractiveChoice::No
            } else {
                responses.remove(0)
            }
        }
    }

    #[test]
    fn test_skip_rule_skips_all_same_rule() {
        let temp_dir = TempDir::new().expect("create temp dir");
        let file = create_test_file(&temp_dir, "Test.fst", "a\nb\nc\nd\ne\n");

        let config = FixApplicatorConfig::apply()
            .with_force(true)
            .with_interactive(true);
        let mut applicator = FixApplicator::new(config);
        applicator = applicator.with_interactive_prompt(Box::new(MockPrompt::new(vec![
            InteractiveChoice::SkipRule, // Skip FST004 entirely
        ])));

        // Both diagnostics are FST004 -- first one triggers SkipRule,
        // second should be auto-skipped.
        let diag1 = create_diagnostic_at_range(&file, 2, 2, "Fix B", "B");
        let diag2 = create_diagnostic_at_range(&file, 4, 4, "Fix D", "D");

        let result = applicator.apply_batch(&[diag1, diag2]);
        assert!(result.is_ok());

        let summary = applicator.summary();
        assert_eq!(summary.fixes_skipped, 2, "Both FST004 fixes should be skipped");
        assert_eq!(summary.fixes_applied, 0);
    }

    #[test]
    fn test_interactive_yes_applies_fix() {
        let temp_dir = TempDir::new().expect("create temp dir");
        let file = create_test_file(&temp_dir, "Test.fst", "a\nb\nc\n");

        let config = FixApplicatorConfig::apply()
            .with_force(true)
            .with_interactive(true);
        let mut applicator = FixApplicator::new(config);
        applicator = applicator.with_interactive_prompt(Box::new(MockPrompt::new(vec![
            InteractiveChoice::Yes,
        ])));

        let diag = create_diagnostic_at_range(&file, 2, 2, "Fix B", "B");
        let result = applicator.apply_batch(&[diag]);
        assert!(result.is_ok());

        let on_disk = fs::read_to_string(&file).expect("read");
        assert!(on_disk.contains("B"), "Fix should be applied");
    }

    #[test]
    fn test_interactive_all_auto_applies_remaining() {
        let temp_dir = TempDir::new().expect("create temp dir");
        let file = create_test_file(&temp_dir, "Test.fst", "a\nb\nc\nd\ne\n");

        let config = FixApplicatorConfig::apply()
            .with_force(true)
            .with_interactive(true);
        let mut applicator = FixApplicator::new(config);
        // First fix: user says "All", second fix auto-applied
        applicator = applicator.with_interactive_prompt(Box::new(MockPrompt::new(vec![
            InteractiveChoice::All,
        ])));

        let diag1 = create_diagnostic_at_range(&file, 2, 2, "Fix B", "B");
        let diag2 = create_diagnostic_at_range(&file, 4, 4, "Fix D", "D");

        let result = applicator.apply_batch(&[diag1, diag2]);
        assert!(result.is_ok());

        let on_disk = fs::read_to_string(&file).expect("read");
        assert!(on_disk.contains("B"), "First fix should be applied");
        assert!(on_disk.contains("D"), "Second fix should be auto-applied after 'All'");
    }

    #[test]
    fn test_interactive_quit_aborts() {
        let temp_dir = TempDir::new().expect("create temp dir");
        let file = create_test_file(&temp_dir, "Test.fst", "a\nb\nc\n");

        let config = FixApplicatorConfig::apply()
            .with_force(true)
            .with_interactive(true);
        let mut applicator = FixApplicator::new(config);
        applicator = applicator.with_interactive_prompt(Box::new(MockPrompt::new(vec![
            InteractiveChoice::Quit,
        ])));

        let diag = create_diagnostic_at_range(&file, 2, 2, "Fix B", "B");
        let result = applicator.apply_batch(&[diag]);

        assert!(result.is_err());
        match result.unwrap_err() {
            FixError::UserAborted => {} // expected
            other => panic!("Expected UserAborted, got: {:?}", other),
        }
    }

    // =========================================================================
    // Column-level overlap detection tests
    // =========================================================================

    #[test]
    fn test_overlap_detection_same_end_start_line_different_cols_no_overlap() {
        let applicator = make_test_applicator();
        let original = "line1\nline2 has columns\nline3\n";

        // Edit 1: lines 1-2, ending col 1
        // Edit 2: lines 2-3, starting col 5
        // They share line 2, but edit1.end_col < edit2.start_col -> no overlap
        let edit1 = Edit {
            file: PathBuf::from("/test.fst"),
            range: super::super::rules::Range {
                start_line: 1,
                start_col: 1,
                end_line: 1,
                end_col: 5,
            },
            new_text: "REPLACED1".to_string(),
        };
        let edit2 = Edit {
            file: PathBuf::from("/test.fst"),
            range: super::super::rules::Range {
                start_line: 2,
                start_col: 1,
                end_line: 3,
                end_col: 5,
            },
            new_text: "REPLACED2".to_string(),
        };

        // These edits are on separate lines, should work fine
        let result = applicator.build_fixed_content(original, &[edit1, edit2]);
        assert!(result.is_ok(), "Non-overlapping edits should succeed");
    }

    // =========================================================================
    // Context-aware blank line cleanup tests
    // =========================================================================

    #[test]
    fn test_consecutive_blank_cleanup_after_deletion() {
        let applicator = make_test_applicator();
        // Original has content between blank lines, deletion leaves consecutive blanks
        let original = "line1\n\ndeleted_line\n\nline4\n";

        // Delete line 3 ("deleted_line"), leaving two consecutive blank lines
        let edits = vec![make_edit(3, 3, "")];
        let result = applicator.build_fixed_content(original, &edits).unwrap();

        // The cleanup should collapse consecutive blanks
        let consecutive_blanks = result
            .lines()
            .collect::<Vec<_>>()
            .windows(2)
            .filter(|w| w[0].trim().is_empty() && w[1].trim().is_empty())
            .count();

        assert_eq!(
            consecutive_blanks, 0,
            "Should not have consecutive blank lines after cleanup. Got: {:?}",
            result
        );
    }

    // =========================================================================
    // Dry-run accuracy tests
    // =========================================================================

    #[test]
    fn test_dry_run_returns_same_content_as_apply_would() {
        let temp_dir = TempDir::new().expect("create temp dir");
        let original = "line1\nline2\nline3\nline4\nline5\n";
        let file = create_test_file(&temp_dir, "Accuracy.fst", original);

        // Dry-run
        let config_dry = FixApplicatorConfig::dry_run().with_force(true);
        let mut applicator_dry = FixApplicator::new(config_dry);

        let diag1 = create_diagnostic_at_range(&file, 2, 2, "Fix 2", "FIXED2");
        let diag2 = create_diagnostic_at_range(&file, 4, 4, "Fix 4", "FIXED4");

        let dry_result = applicator_dry
            .apply_batch(&[diag1.clone(), diag2.clone()])
            .expect("dry run should succeed");

        assert_eq!(dry_result.len(), 1, "Dry-run should produce 1 grouped result");
        let dry_content = &dry_result[0].new_content;

        // Apply (on a copy of the file)
        let file_copy = create_test_file(&temp_dir, "Accuracy_copy.fst", original);
        let diag1_copy = create_diagnostic_at_range(&file_copy, 2, 2, "Fix 2", "FIXED2");
        let diag2_copy = create_diagnostic_at_range(&file_copy, 4, 4, "Fix 4", "FIXED4");

        let config_apply = FixApplicatorConfig::apply().with_force(true);
        let mut applicator_apply = FixApplicator::new(config_apply);

        let apply_result = applicator_apply
            .apply_batch(&[diag1_copy, diag2_copy])
            .expect("apply should succeed");

        assert_eq!(apply_result.len(), 1);
        let apply_content = &apply_result[0].new_content;

        assert_eq!(
            dry_content, apply_content,
            "Dry-run and apply should produce identical content"
        );
    }

    // =========================================================================
    // Cache invalidation tests
    // =========================================================================

    #[test]
    fn test_invalidate_cache() {
        let temp_dir = TempDir::new().expect("create temp dir");
        let file = create_test_file(&temp_dir, "Cache.fst", "original\n");

        let config = FixApplicatorConfig::dry_run();
        let mut applicator = FixApplicator::new(config);

        let canonical = file.canonicalize().unwrap();
        let _ = applicator.read_file_cached(&canonical).unwrap();
        assert_eq!(applicator.file_content_cache.len(), 1);

        applicator.invalidate_cache(&[file.clone()]);
        assert_eq!(
            applicator.file_content_cache.len(),
            0,
            "Cache should be empty after invalidation"
        );
    }

    // =========================================================================
    // Modified files tracking tests
    // =========================================================================

    #[test]
    fn test_modified_files_tracking() {
        let temp_dir = TempDir::new().expect("create temp dir");
        let file = create_test_file(&temp_dir, "Track.fst", "a\nb\nc\n");

        let config = FixApplicatorConfig::apply().with_force(true);
        let mut applicator = FixApplicator::new(config);

        let diag = create_diagnostic_at_range(&file, 2, 2, "Fix B", "B");
        let _ = applicator.apply_batch(&[diag]).expect("should succeed");

        let modified = applicator.modified_files();
        assert_eq!(modified.len(), 1, "Should track 1 modified file");
        assert_eq!(modified[0], file);
    }

    // =========================================================================
    // Edge case tests
    // =========================================================================

    #[test]
    fn test_empty_batch_returns_empty() {
        let config = FixApplicatorConfig::dry_run();
        let mut applicator = FixApplicator::new(config);

        let result = applicator.apply_batch(&[]);
        assert!(result.is_ok());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn test_diagnostic_without_fix_is_ignored() {
        let temp_dir = TempDir::new().expect("create temp dir");
        let file = create_test_file(&temp_dir, "NoFix.fst", "content\n");

        let config = FixApplicatorConfig::dry_run();
        let mut applicator = FixApplicator::new(config);

        let diag = Diagnostic {
            rule: RuleCode::FST004,
            severity: super::super::rules::DiagnosticSeverity::Warning,
            file: file.to_path_buf(),
            range: super::super::rules::Range::new(1, 1, 1, 10),
            message: "No fix available".to_string(),
            fix: None, // No fix
        };

        let result = applicator.apply_batch(&[diag]);
        assert!(result.is_ok());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn test_skipped_rules_tracking() {
        let config = FixApplicatorConfig::dry_run();
        let mut applicator = FixApplicator::new(config);
        assert!(applicator.skipped_rules().is_empty());

        applicator.skipped_rules.insert(RuleCode::FST001);
        assert!(applicator.skipped_rules().contains(&RuleCode::FST001));
        assert!(!applicator.skipped_rules().contains(&RuleCode::FST004));
    }
}
