//! CLI argument definitions and validation for brrr-lint.
//!
//! Extracted into its own module so that integration tests can use
//! [`Cli::try_parse_from`] to verify argument validation without
//! spawning a subprocess.

use std::path::PathBuf;

use clap::{Parser, Subcommand};

use crate::lint::{ColorMode, DryRunFormat, OutputFormat, RuleCode};

/// Parse a positive (>= 1) usize value for CLI arguments.
fn parse_positive_usize(s: &str) -> Result<usize, String> {
    let val: usize = s
        .parse()
        .map_err(|e| format!("invalid integer: {}", e))?;
    if val == 0 {
        return Err("value must be at least 1".to_string());
    }
    Ok(val)
}

/// Validate a comma-separated list of rule codes at parse time.
///
/// Each code is checked against [`RuleCode::parse_code`].  If any token
/// is not a known code the parser rejects the whole value immediately,
/// giving the user an actionable error message from clap.
fn validate_rule_codes(s: &str) -> Result<String, String> {
    for raw in s.split(',') {
        let code = raw.trim();
        if code.is_empty() {
            continue;
        }
        if RuleCode::parse_code(code).is_none() {
            let valid: Vec<&str> = RuleCode::all()
                .iter()
                .map(|r| r.as_str())
                .collect();
            return Err(format!(
                "unknown rule code '{}'. Valid codes: {}",
                code,
                valid.join(", "),
            ));
        }
    }
    Ok(s.to_string())
}

/// brrr-lint: Fast F* Linter and Language Server.
///
/// A standalone linter and LSP server for F*, the proof-oriented programming
/// language. Detects duplicate types, unused opens, naming violations, dead
/// code, Z3 complexity patterns, security issues, and more -- with autofix
/// support.
///
/// Quick start:
///   brrr-lint check src/          Check files for issues
///   brrr-lint fix src/            Preview fixes (dry-run)
///   brrr-lint fix src/ --apply    Apply fixes
///   brrr-lint rules               List all available rules
///   brrr-lint init                Generate default .brrr-lint.toml
///   brrr-lint serve               Start LSP server (default)
#[derive(Parser, Debug)]
#[command(name = "brrr-lint")]
#[command(author)]
#[command(version)]
#[command(about = "Fast F* linter and language server with autofix", long_about = None)]
#[command(after_help = "\
CONFIGURATION:
  brrr-lint looks for a .brrr-lint.toml config file, searching from the\n\
  current directory up to the nearest .git root. Use `brrr-lint init` to\n\
  generate a default config. CLI flags always override config file settings.\n\
\n\
EXAMPLES:\n\
  brrr-lint check src/                      Check all F* files under src/\n\
  brrr-lint check . --select FST001,FST004  Only run specific rules\n\
  brrr-lint check . --exclude FST014        Skip specific rules\n\
  brrr-lint check . --severity warning      Only show warnings and above\n\
  brrr-lint fix src/ --apply                Apply safe fixes\n\
  brrr-lint fix src/ --apply --force        Also apply unsafe fixes\n\
  brrr-lint revert --latest                 Undo last fix application")]
pub struct Cli {
    /// Enable debug logging (sets log level to DEBUG).
    #[arg(short, long, global = true, help_heading = "Global Options")]
    pub debug: bool,

    /// When to use ANSI color in output.
    ///
    /// auto: enable when stdout is a terminal and NO_COLOR is unset (default).
    /// always: force color even when piped.
    /// never: disable color unconditionally.
    #[arg(
        long,
        value_enum,
        global = true,
        default_value = "auto",
        help_heading = "Global Options"
    )]
    pub color: ColorMode,

    /// Path to the F* executable (fstar.exe).
    ///
    /// Overrides the value from .brrr-lint.toml and $PATH lookup.
    #[arg(long, global = true, help_heading = "Global Options")]
    pub fstar_exe: Option<String>,

    /// Suppress all non-diagnostic output (summary, headers, etc.).
    #[arg(short, long, global = true, help_heading = "Global Options")]
    pub quiet: bool,

    /// Show additional details during execution.
    #[arg(short, long, global = true, help_heading = "Global Options")]
    pub verbose: bool,

    /// Path to a .brrr-lint.toml config file.
    ///
    /// By default, brrr-lint searches from the current directory up to
    /// the nearest .git root. This flag overrides that discovery.
    #[arg(long, global = true, help_heading = "Global Options")]
    pub config: Option<PathBuf>,

    #[command(subcommand)]
    pub command: Option<Commands>,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    /// Run the LSP server (default when no subcommand is given).
    ///
    /// Communicates over stdin/stdout using the Language Server Protocol.
    /// Configure your editor to launch `brrr-lint serve`.
    Serve {
        /// Run full verification when a file is opened.
        #[arg(long)]
        verify_on_open: bool,

        /// Run full verification when a file is saved (default: true).
        #[arg(long, default_value = "true")]
        verify_on_save: bool,

        /// Enable flycheck (continuous lax checking while typing).
        #[arg(long, default_value = "true")]
        fly_check: bool,

        /// F* query timeout in milliseconds (>= 1).
        #[arg(long, default_value = "30000", value_parser = clap::value_parser!(u64).range(1..))]
        timeout_ms: u64,

        /// Maximum concurrent F* processes (>= 1).
        #[arg(long, default_value = "4", value_parser = parse_positive_usize)]
        max_processes: usize,
    },

    /// Check F* files for lint issues.
    ///
    /// Scans the given paths (files or directories) for F* files and runs
    /// all enabled lint rules. Returns exit code 1 if any issues are found,
    /// unless --exit-zero is used.
    Check {
        /// Files or directories to check (recursive for directories).
        #[arg(required = true)]
        paths: Vec<PathBuf>,

        /// Comma-separated rule codes to enable (e.g., FST001,FST004).
        ///
        /// When specified, only these rules run. Overrides [rules.select]
        /// in .brrr-lint.toml.
        #[arg(long, value_parser = validate_rule_codes)]
        select: Option<String>,

        /// Comma-separated rule codes to skip (e.g., FST014).
        ///
        /// Takes precedence over --select. Overrides [rules.exclude]
        /// in .brrr-lint.toml. Alias: --ignore.
        #[arg(long, alias = "ignore", value_parser = validate_rule_codes)]
        exclude: Option<String>,

        /// Minimum severity to report: error, warning, info, hint.
        ///
        /// Only diagnostics at this severity or above are shown.
        /// Order: error > warning > info > hint.
        #[arg(long, value_parser = parse_severity)]
        severity: Option<SeverityFilter>,

        /// Output format for diagnostics.
        #[arg(long, value_enum, default_value = "text")]
        format: OutputFormat,

        /// Also show available fixes for each diagnostic.
        #[arg(long)]
        show_fixes: bool,

        /// Exit with code 0 even if issues are found.
        #[arg(long)]
        exit_zero: bool,

        /// Stop after collecting this many diagnostics (>= 1).
        ///
        /// Enables early termination on large codebases.
        #[arg(long, value_parser = parse_positive_usize)]
        max_diagnostics: Option<usize>,
    },

    /// Fix F* files automatically.
    ///
    /// By default runs in DRY-RUN mode: shows what would change without
    /// modifying files. Use --apply to write changes.
    ///
    /// Safety levels:
    ///   Safe    -- auto-applied with --apply
    ///   Caution -- applied with --apply but shows warning
    ///   Unsafe  -- requires --apply --force
    Fix {
        /// Files or directories to fix (recursive for directories).
        #[arg(required = true)]
        paths: Vec<PathBuf>,

        /// Comma-separated rule codes to fix (e.g., FST001,FST004).
        #[arg(long, value_parser = validate_rule_codes)]
        select: Option<String>,

        /// Comma-separated rule codes to skip.
        ///
        /// Alias: --ignore.
        #[arg(long, alias = "ignore", value_parser = validate_rule_codes)]
        exclude: Option<String>,

        /// Minimum severity to fix: error, warning, info, hint.
        #[arg(long, value_parser = parse_severity)]
        severity: Option<SeverityFilter>,

        /// Write fixes to disk (without this flag, dry-run only).
        #[arg(long)]
        apply: bool,

        /// Also apply unsafe fixes (requires --apply).
        #[arg(long)]
        force: bool,

        /// Output format for diagnostics.
        #[arg(long, value_enum, default_value = "text")]
        format: OutputFormat,

        /// Dry-run output style (when --apply is not used).
        ///
        /// concise: one line per fix with counts.
        /// full: detailed diff-style output (default).
        /// json: machine-readable JSON.
        #[arg(long, value_enum, default_value = "full")]
        dry_run_format: DryRunFormat,
    },

    /// List all available lint rules with descriptions.
    Rules,

    /// Generate a default .brrr-lint.toml configuration file.
    ///
    /// Creates the file in the current directory. Use --output to
    /// write to a different path.
    Init {
        /// Output path for the config file.
        #[arg(short, long, default_value = ".brrr-lint.toml")]
        output: PathBuf,

        /// Overwrite an existing config file.
        #[arg(long)]
        force: bool,
    },

    /// Revert files to their backed-up versions.
    ///
    /// Backups are created automatically when fixes are applied with
    /// `fix --apply`. This command restores files to a previous state.
    ///
    /// Named revert points let you snapshot and restore by name:
    ///   brrr-lint revert --create-point my-snapshot
    ///   brrr-lint revert --to-point my-snapshot
    Revert {
        /// List all backup timestamps and revert points.
        #[arg(long, conflicts_with_all = ["timestamp", "latest", "best_effort", "create_point", "to_point", "cleanup"])]
        list: bool,

        /// Revert to a specific timestamp (ms since epoch).
        #[arg(long, conflicts_with_all = ["list", "latest", "best_effort", "create_point", "to_point", "cleanup"])]
        timestamp: Option<u64>,

        /// Revert to the most recent backup.
        #[arg(long, conflicts_with_all = ["list", "timestamp", "best_effort", "create_point", "to_point", "cleanup"])]
        latest: bool,

        /// Revert to the closest available timestamp.
        #[arg(long, conflicts_with_all = ["list", "timestamp", "latest", "create_point", "to_point", "cleanup"])]
        best_effort: Option<u64>,

        /// Create a named revert point from current backups.
        #[arg(long, conflicts_with_all = ["list", "timestamp", "latest", "best_effort", "to_point", "cleanup"])]
        create_point: Option<String>,

        /// Restore a previously created named revert point.
        #[arg(long, conflicts_with_all = ["list", "timestamp", "latest", "best_effort", "create_point", "cleanup"])]
        to_point: Option<String>,

        /// Remove old backup files.
        #[arg(long, conflicts_with_all = ["list", "timestamp", "latest", "best_effort", "create_point", "to_point"])]
        cleanup: bool,

        /// Maximum age for --cleanup (e.g., "7d", "24h", "30m").
        #[arg(long, requires = "cleanup")]
        older_than: Option<String>,

        /// Prompt before reverting each file.
        #[arg(short = 'i', long)]
        interactive: bool,

        /// Preview changes without modifying files.
        #[arg(long)]
        dry_run: bool,

        /// Force revert even if files were modified since backup.
        #[arg(long)]
        force: bool,

        /// Paths to filter -- only revert files under these paths.
        #[arg()]
        paths: Vec<PathBuf>,
    },
}

// ---------------------------------------------------------------------------
// Severity filter
// ---------------------------------------------------------------------------

/// Minimum severity level for filtering diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeverityFilter {
    Error,
    Warning,
    Info,
    Hint,
}

impl SeverityFilter {
    /// Numeric rank for comparison (higher = more severe).
    pub fn rank(self) -> u8 {
        match self {
            SeverityFilter::Error => 3,
            SeverityFilter::Warning => 2,
            SeverityFilter::Info => 1,
            SeverityFilter::Hint => 0,
        }
    }

    /// Check whether a diagnostic severity passes this filter.
    pub fn passes(self, severity: &crate::lint::DiagnosticSeverity) -> bool {
        let diag_rank = match severity {
            crate::lint::DiagnosticSeverity::Error => 3,
            crate::lint::DiagnosticSeverity::Warning => 2,
            crate::lint::DiagnosticSeverity::Info => 1,
            crate::lint::DiagnosticSeverity::Hint => 0,
        };
        diag_rank >= self.rank()
    }
}

fn parse_severity(s: &str) -> Result<SeverityFilter, String> {
    match s.to_lowercase().as_str() {
        "error" => Ok(SeverityFilter::Error),
        "warning" | "warn" => Ok(SeverityFilter::Warning),
        "info" | "information" => Ok(SeverityFilter::Info),
        "hint" => Ok(SeverityFilter::Hint),
        _ => Err(format!(
            "invalid severity '{}' (valid: error, warning, info, hint)",
            s
        )),
    }
}

// ---------------------------------------------------------------------------
// Semantic validation
// ---------------------------------------------------------------------------

/// Validate semantic constraints that clap's declarative API cannot express.
///
/// Returns a list of warning messages to print to stderr. These are
/// non-fatal: the program continues but the user is informed that
/// certain flag combinations are meaningless.
pub fn validate_cli_semantics(cli: &Cli) -> Vec<String> {
    let mut warnings: Vec<String> = Vec::new();

    // --force without --apply is meaningless.
    if let Some(Commands::Fix { force, apply, .. }) = &cli.command {
        if *force && !*apply {
            warnings.push(
                "Warning: --force has no effect without --apply".to_string(),
            );
        }
    }

    // --dry-run-format with --apply is meaningless.
    if let Some(Commands::Fix {
        apply,
        dry_run_format,
        ..
    }) = &cli.command
    {
        if *apply && !matches!(dry_run_format, DryRunFormat::Full) {
            warnings.push(
                "Warning: --dry-run-format has no effect when --apply is used".to_string(),
            );
        }
    }

    // --quiet and --verbose together are contradictory.
    if cli.quiet && cli.verbose {
        warnings.push(
            "Warning: --quiet and --verbose are contradictory; --quiet takes precedence"
                .to_string(),
        );
    }

    // --fstar-exe path should exist and be executable.
    if let Some(ref path_str) = cli.fstar_exe {
        let path = std::path::Path::new(path_str);
        if !path.exists() {
            warnings.push(format!(
                "Warning: --fstar-exe path '{}' does not exist",
                path_str,
            ));
        } else if !is_executable(path) {
            warnings.push(format!(
                "Warning: --fstar-exe path '{}' exists but is not executable",
                path_str,
            ));
        }
    }

    warnings
}

/// Check whether `path` has an executable bit set (Unix) or is a file (Windows).
fn is_executable(path: &std::path::Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        match std::fs::metadata(path) {
            Ok(meta) => meta.permissions().mode() & 0o111 != 0,
            Err(_) => false,
        }
    }
    #[cfg(not(unix))]
    {
        path.is_file()
    }
}
