//! Integration tests for CLI argument validation.
//!
//! Uses [`clap::Parser::try_parse_from`] to exercise clap-level validation
//! (value parsers, range checks, conflicts) and [`validate_cli_semantics`]
//! to exercise runtime semantic warnings, all without spawning a subprocess.

use brrr_lint::cli::{Cli, Commands, SeverityFilter, validate_cli_semantics};
use clap::Parser;

// ============================================================================
// HELPERS
// ============================================================================

/// Attempt to parse a command line, returning Ok(Cli) or the clap error string.
fn try_parse(args: &[&str]) -> Result<Cli, String> {
    Cli::try_parse_from(args).map_err(|e| e.to_string())
}

/// Shorthand: parse must succeed.
fn must_parse(args: &[&str]) -> Cli {
    try_parse(args).unwrap_or_else(|e| panic!("expected parse to succeed, got:\n{}", e))
}

/// Shorthand: parse must fail and the error must contain `needle`.
fn must_fail_containing(args: &[&str], needle: &str) {
    let err = try_parse(args).expect_err("expected parse to fail");
    assert!(
        err.contains(needle),
        "error does not contain '{}'. Full error:\n{}",
        needle,
        err,
    );
}

// ============================================================================
// BUG #4 -- timeout_ms and max_processes must be >= 1
// ============================================================================

#[test]
fn serve_timeout_ms_zero_rejected() {
    must_fail_containing(
        &["brrr-lint", "serve", "--timeout-ms", "0"],
        "0",
    );
}

#[test]
fn serve_timeout_ms_one_accepted() {
    let cli = must_parse(&["brrr-lint", "serve", "--timeout-ms", "1"]);
    if let Some(Commands::Serve { timeout_ms, .. }) = cli.command {
        assert_eq!(timeout_ms, 1);
    } else {
        panic!("expected Serve command");
    }
}

#[test]
fn serve_timeout_ms_negative_rejected() {
    // clap treats "-1" as an unknown flag, so we just verify it fails.
    let result = try_parse(&["brrr-lint", "serve", "--timeout-ms", "-1"]);
    assert!(result.is_err(), "negative timeout_ms should be rejected");
}

#[test]
fn serve_max_processes_zero_rejected() {
    must_fail_containing(
        &["brrr-lint", "serve", "--max-processes", "0"],
        "must be at least 1",
    );
}

#[test]
fn serve_max_processes_one_accepted() {
    let cli = must_parse(&["brrr-lint", "serve", "--max-processes", "1"]);
    if let Some(Commands::Serve { max_processes, .. }) = cli.command {
        assert_eq!(max_processes, 1);
    } else {
        panic!("expected Serve command");
    }
}

#[test]
fn serve_defaults_are_nonzero() {
    let cli = must_parse(&["brrr-lint", "serve"]);
    if let Some(Commands::Serve {
        timeout_ms,
        max_processes,
        ..
    }) = cli.command
    {
        assert!(timeout_ms >= 1, "default timeout_ms must be >= 1");
        assert!(max_processes >= 1, "default max_processes must be >= 1");
    } else {
        panic!("expected Serve command");
    }
}

// ============================================================================
// BUG #6 -- Invalid rule codes rejected at parse time
// ============================================================================

#[test]
fn check_select_valid_code_accepted() {
    let cli = must_parse(&["brrr-lint", "check", "src/", "--select", "FST001"]);
    if let Some(Commands::Check { select, .. }) = cli.command {
        assert_eq!(select.as_deref(), Some("FST001"));
    } else {
        panic!("expected Check command");
    }
}

#[test]
fn check_select_multiple_valid_codes_accepted() {
    let cli = must_parse(&[
        "brrr-lint",
        "check",
        "src/",
        "--select",
        "FST001,FST003,FST017",
    ]);
    if let Some(Commands::Check { select, .. }) = cli.command {
        assert_eq!(select.as_deref(), Some("FST001,FST003,FST017"));
    } else {
        panic!("expected Check command");
    }
}

#[test]
fn check_select_invalid_code_rejected() {
    must_fail_containing(
        &["brrr-lint", "check", "src/", "--select", "BOGUS"],
        "unknown rule code",
    );
}

#[test]
fn check_select_mixed_valid_invalid_rejected() {
    must_fail_containing(
        &["brrr-lint", "check", "src/", "--select", "FST001,NOPE"],
        "unknown rule code 'NOPE'",
    );
}

#[test]
fn check_ignore_invalid_code_rejected() {
    must_fail_containing(
        &["brrr-lint", "check", "src/", "--ignore", "XYZ999"],
        "unknown rule code 'XYZ999'",
    );
}

#[test]
fn fix_select_invalid_code_rejected() {
    must_fail_containing(
        &["brrr-lint", "fix", "src/", "--select", "INVALID"],
        "unknown rule code",
    );
}

#[test]
fn fix_ignore_invalid_code_rejected() {
    must_fail_containing(
        &["brrr-lint", "fix", "src/", "--ignore", "INVALID"],
        "unknown rule code",
    );
}

#[test]
fn check_select_case_insensitive_accepted() {
    // RuleCode::parse_code uppercases, so lowercase input should work.
    let cli = must_parse(&["brrr-lint", "check", "src/", "--select", "fst001"]);
    if let Some(Commands::Check { select, .. }) = cli.command {
        assert!(select.is_some());
    } else {
        panic!("expected Check command");
    }
}

// ============================================================================
// BUG #3 -- --log-file removed from serve (should not parse)
// ============================================================================

#[test]
fn serve_log_file_option_removed() {
    let result = try_parse(&["brrr-lint", "serve", "--log-file", "/tmp/log.txt"]);
    assert!(
        result.is_err(),
        "--log-file should no longer be a valid serve option"
    );
}

// ============================================================================
// BUG #1 -- --force without --apply produces warning
// ============================================================================

#[test]
fn fix_force_without_apply_warns() {
    let cli = must_parse(&["brrr-lint", "fix", "src/", "--force"]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("--force has no effect without --apply")),
        "expected warning about --force without --apply, got: {:?}",
        warnings,
    );
}

#[test]
fn fix_force_with_apply_no_warning() {
    let cli = must_parse(&["brrr-lint", "fix", "src/", "--force", "--apply"]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        !warnings
            .iter()
            .any(|w| w.contains("--force has no effect")),
        "should NOT warn when --force is used with --apply, got: {:?}",
        warnings,
    );
}

#[test]
fn fix_no_force_no_warning() {
    let cli = must_parse(&["brrr-lint", "fix", "src/"]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        !warnings
            .iter()
            .any(|w| w.contains("--force")),
        "should NOT warn about --force when it is not provided, got: {:?}",
        warnings,
    );
}

// ============================================================================
// BUG #2 -- --dry-run-format with --apply produces warning
// ============================================================================

#[test]
fn fix_dry_run_format_with_apply_warns() {
    let cli = must_parse(&[
        "brrr-lint",
        "fix",
        "src/",
        "--apply",
        "--dry-run-format",
        "concise",
    ]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("--dry-run-format has no effect when --apply is used")),
        "expected warning about --dry-run-format with --apply, got: {:?}",
        warnings,
    );
}

#[test]
fn fix_dry_run_format_without_apply_no_warning() {
    let cli = must_parse(&[
        "brrr-lint",
        "fix",
        "src/",
        "--dry-run-format",
        "concise",
    ]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        !warnings
            .iter()
            .any(|w| w.contains("--dry-run-format has no effect")),
        "should NOT warn when --apply is not set, got: {:?}",
        warnings,
    );
}

#[test]
fn fix_apply_with_default_dry_run_format_no_warning() {
    // Default dry_run_format is "full" -- passing --apply alone should not warn.
    let cli = must_parse(&["brrr-lint", "fix", "src/", "--apply"]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        !warnings
            .iter()
            .any(|w| w.contains("--dry-run-format")),
        "should NOT warn about --dry-run-format when using default, got: {:?}",
        warnings,
    );
}

// ============================================================================
// BUG #5 -- --fstar-exe path validation
// ============================================================================

#[test]
fn fstar_exe_nonexistent_path_warns() {
    let cli = must_parse(&[
        "brrr-lint",
        "--fstar-exe",
        "/nonexistent/path/to/fstar.exe",
        "check",
        "src/",
    ]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("does not exist")),
        "expected warning about nonexistent --fstar-exe path, got: {:?}",
        warnings,
    );
}

#[test]
fn fstar_exe_not_set_no_warning() {
    let cli = must_parse(&["brrr-lint", "check", "src/"]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        !warnings
            .iter()
            .any(|w| w.contains("fstar-exe")),
        "should NOT warn when --fstar-exe is not provided, got: {:?}",
        warnings,
    );
}

#[cfg(unix)]
#[test]
fn fstar_exe_existing_non_executable_warns() {
    use std::io::Write;
    let tmp = tempfile::NamedTempFile::new().expect("create temp file");
    // Write something so the file exists but ensure it has no execute bit.
    writeln!(tmp.as_file(), "not an executable").ok();

    // Remove execute permission.
    let path = tmp.path();
    let perms = std::fs::Permissions::from_mode(0o644);
    std::fs::set_permissions(path, perms).expect("set permissions");

    let path_str = path.to_str().expect("temp path to str");
    let cli = must_parse(&[
        "brrr-lint",
        "--fstar-exe",
        path_str,
        "check",
        "src/",
    ]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("not executable")),
        "expected warning about non-executable --fstar-exe, got: {:?}",
        warnings,
    );
}

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

#[cfg(unix)]
#[test]
fn fstar_exe_existing_executable_no_warning() {
    use std::io::Write;
    let tmp = tempfile::NamedTempFile::new().expect("create temp file");
    writeln!(tmp.as_file(), "#!/bin/sh\necho ok").ok();

    let path = tmp.path();
    let perms = std::fs::Permissions::from_mode(0o755);
    std::fs::set_permissions(path, perms).expect("set permissions");

    let path_str = path.to_str().expect("temp path to str");
    let cli = must_parse(&[
        "brrr-lint",
        "--fstar-exe",
        path_str,
        "check",
        "src/",
    ]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        !warnings
            .iter()
            .any(|w| w.contains("fstar-exe") || w.contains("does not exist") || w.contains("not executable")),
        "should NOT warn for a valid executable, got: {:?}",
        warnings,
    );
}

// ============================================================================
// GENERAL SMOKE TESTS
// ============================================================================

#[test]
fn no_command_defaults_to_serve() {
    let cli = must_parse(&["brrr-lint"]);
    assert!(cli.command.is_none(), "no subcommand means implicit serve");
}

#[test]
fn rules_command_parses() {
    let cli = must_parse(&["brrr-lint", "rules"]);
    assert!(matches!(cli.command, Some(Commands::Rules)));
}

#[test]
fn check_requires_paths() {
    must_fail_containing(&["brrr-lint", "check"], "required");
}

#[test]
fn fix_requires_paths() {
    must_fail_containing(&["brrr-lint", "fix"], "required");
}

#[test]
fn debug_flag_global() {
    let cli = must_parse(&["brrr-lint", "--debug", "check", "src/"]);
    assert!(cli.debug);
}

// ============================================================================
// INIT SUBCOMMAND
// ============================================================================

#[test]
fn init_command_parses() {
    let cli = must_parse(&["brrr-lint", "init"]);
    if let Some(Commands::Init { output, force }) = cli.command {
        assert_eq!(output.to_str().unwrap(), ".brrr-lint.toml");
        assert!(!force);
    } else {
        panic!("expected Init command");
    }
}

#[test]
fn init_command_custom_output() {
    let cli = must_parse(&["brrr-lint", "init", "--output", "/tmp/my-config.toml"]);
    if let Some(Commands::Init { output, .. }) = cli.command {
        assert_eq!(output.to_str().unwrap(), "/tmp/my-config.toml");
    } else {
        panic!("expected Init command");
    }
}

#[test]
fn init_command_force_flag() {
    let cli = must_parse(&["brrr-lint", "init", "--force"]);
    if let Some(Commands::Init { force, .. }) = cli.command {
        assert!(force);
    } else {
        panic!("expected Init command");
    }
}

// ============================================================================
// --exclude flag (alias for --ignore)
// ============================================================================

#[test]
fn check_exclude_flag_accepted() {
    let cli = must_parse(&["brrr-lint", "check", "src/", "--exclude", "FST014"]);
    if let Some(Commands::Check { exclude, .. }) = cli.command {
        assert_eq!(exclude.as_deref(), Some("FST014"));
    } else {
        panic!("expected Check command");
    }
}

#[test]
fn check_exclude_is_ignore_alias() {
    // --ignore and --exclude should both work and fill the same field.
    let cli_exclude = must_parse(&["brrr-lint", "check", "src/", "--exclude", "FST001"]);
    let cli_ignore = must_parse(&["brrr-lint", "check", "src/", "--ignore", "FST001"]);

    if let (Some(Commands::Check { exclude: e1, .. }), Some(Commands::Check { exclude: e2, .. })) =
        (cli_exclude.command, cli_ignore.command)
    {
        assert_eq!(e1, e2);
    } else {
        panic!("expected Check commands");
    }
}

#[test]
fn check_exclude_invalid_rejected() {
    must_fail_containing(
        &["brrr-lint", "check", "src/", "--exclude", "NOPE"],
        "unknown rule code",
    );
}

#[test]
fn fix_exclude_flag_accepted() {
    let cli = must_parse(&["brrr-lint", "fix", "src/", "--exclude", "FST003"]);
    if let Some(Commands::Fix { exclude, .. }) = cli.command {
        assert_eq!(exclude.as_deref(), Some("FST003"));
    } else {
        panic!("expected Fix command");
    }
}

// ============================================================================
// --severity filter
// ============================================================================

#[test]
fn check_severity_error_accepted() {
    let cli = must_parse(&["brrr-lint", "check", "src/", "--severity", "error"]);
    if let Some(Commands::Check { severity, .. }) = cli.command {
        assert_eq!(severity, Some(SeverityFilter::Error));
    } else {
        panic!("expected Check command");
    }
}

#[test]
fn check_severity_warning_accepted() {
    let cli = must_parse(&["brrr-lint", "check", "src/", "--severity", "warning"]);
    if let Some(Commands::Check { severity, .. }) = cli.command {
        assert_eq!(severity, Some(SeverityFilter::Warning));
    } else {
        panic!("expected Check command");
    }
}

#[test]
fn check_severity_warn_alias_accepted() {
    let cli = must_parse(&["brrr-lint", "check", "src/", "--severity", "warn"]);
    if let Some(Commands::Check { severity, .. }) = cli.command {
        assert_eq!(severity, Some(SeverityFilter::Warning));
    } else {
        panic!("expected Check command");
    }
}

#[test]
fn check_severity_info_accepted() {
    let cli = must_parse(&["brrr-lint", "check", "src/", "--severity", "info"]);
    if let Some(Commands::Check { severity, .. }) = cli.command {
        assert_eq!(severity, Some(SeverityFilter::Info));
    } else {
        panic!("expected Check command");
    }
}

#[test]
fn check_severity_hint_accepted() {
    let cli = must_parse(&["brrr-lint", "check", "src/", "--severity", "hint"]);
    if let Some(Commands::Check { severity, .. }) = cli.command {
        assert_eq!(severity, Some(SeverityFilter::Hint));
    } else {
        panic!("expected Check command");
    }
}

#[test]
fn check_severity_invalid_rejected() {
    must_fail_containing(
        &["brrr-lint", "check", "src/", "--severity", "critical"],
        "invalid severity",
    );
}

#[test]
fn check_severity_default_none() {
    let cli = must_parse(&["brrr-lint", "check", "src/"]);
    if let Some(Commands::Check { severity, .. }) = cli.command {
        assert!(severity.is_none());
    } else {
        panic!("expected Check command");
    }
}

#[test]
fn fix_severity_accepted() {
    let cli = must_parse(&["brrr-lint", "fix", "src/", "--severity", "error"]);
    if let Some(Commands::Fix { severity, .. }) = cli.command {
        assert_eq!(severity, Some(SeverityFilter::Error));
    } else {
        panic!("expected Fix command");
    }
}

// ============================================================================
// SeverityFilter::passes
// ============================================================================

#[test]
fn severity_filter_passes_error_only() {
    use brrr_lint::lint::DiagnosticSeverity;
    let filter = SeverityFilter::Error;
    assert!(filter.passes(&DiagnosticSeverity::Error));
    assert!(!filter.passes(&DiagnosticSeverity::Warning));
    assert!(!filter.passes(&DiagnosticSeverity::Info));
    assert!(!filter.passes(&DiagnosticSeverity::Hint));
}

#[test]
fn severity_filter_passes_warning_and_above() {
    use brrr_lint::lint::DiagnosticSeverity;
    let filter = SeverityFilter::Warning;
    assert!(filter.passes(&DiagnosticSeverity::Error));
    assert!(filter.passes(&DiagnosticSeverity::Warning));
    assert!(!filter.passes(&DiagnosticSeverity::Info));
    assert!(!filter.passes(&DiagnosticSeverity::Hint));
}

#[test]
fn severity_filter_passes_hint_shows_all() {
    use brrr_lint::lint::DiagnosticSeverity;
    let filter = SeverityFilter::Hint;
    assert!(filter.passes(&DiagnosticSeverity::Error));
    assert!(filter.passes(&DiagnosticSeverity::Warning));
    assert!(filter.passes(&DiagnosticSeverity::Info));
    assert!(filter.passes(&DiagnosticSeverity::Hint));
}

// ============================================================================
// --quiet and --verbose global flags
// ============================================================================

#[test]
fn quiet_flag_global() {
    let cli = must_parse(&["brrr-lint", "--quiet", "check", "src/"]);
    assert!(cli.quiet);
    assert!(!cli.verbose);
}

#[test]
fn verbose_flag_global() {
    let cli = must_parse(&["brrr-lint", "--verbose", "check", "src/"]);
    assert!(cli.verbose);
    assert!(!cli.quiet);
}

#[test]
fn quiet_short_flag() {
    let cli = must_parse(&["brrr-lint", "-q", "check", "src/"]);
    assert!(cli.quiet);
}

#[test]
fn verbose_short_flag() {
    let cli = must_parse(&["brrr-lint", "-v", "check", "src/"]);
    assert!(cli.verbose);
}

#[test]
fn quiet_and_verbose_together_warns() {
    let cli = must_parse(&["brrr-lint", "--quiet", "--verbose", "check", "src/"]);
    let warnings = validate_cli_semantics(&cli);
    assert!(
        warnings.iter().any(|w| w.contains("contradictory")),
        "expected contradictory warning, got: {:?}",
        warnings,
    );
}

// ============================================================================
// --config flag
// ============================================================================

#[test]
fn config_flag_accepted() {
    let cli = must_parse(&["brrr-lint", "--config", "my-lint.toml", "check", "src/"]);
    assert_eq!(
        cli.config.as_ref().map(|p| p.to_str().unwrap()),
        Some("my-lint.toml")
    );
}

#[test]
fn config_flag_default_none() {
    let cli = must_parse(&["brrr-lint", "check", "src/"]);
    assert!(cli.config.is_none());
}

// ============================================================================
// --max-diagnostics flag
// ============================================================================

#[test]
fn check_max_diagnostics_accepted() {
    let cli = must_parse(&["brrr-lint", "check", "src/", "--max-diagnostics", "50"]);
    if let Some(Commands::Check { max_diagnostics, .. }) = cli.command {
        assert_eq!(max_diagnostics, Some(50));
    } else {
        panic!("expected Check command");
    }
}

#[test]
fn check_max_diagnostics_zero_rejected() {
    must_fail_containing(
        &["brrr-lint", "check", "src/", "--max-diagnostics", "0"],
        "must be at least 1",
    );
}

#[test]
fn check_max_diagnostics_default_none() {
    let cli = must_parse(&["brrr-lint", "check", "src/"]);
    if let Some(Commands::Check { max_diagnostics, .. }) = cli.command {
        assert!(max_diagnostics.is_none());
    } else {
        panic!("expected Check command");
    }
}

// ============================================================================
// REVERT SUBCOMMAND
// ============================================================================

#[test]
fn revert_list_parses() {
    let cli = must_parse(&["brrr-lint", "revert", "--list"]);
    if let Some(Commands::Revert { list, .. }) = cli.command {
        assert!(list);
    } else {
        panic!("expected Revert command");
    }
}

#[test]
fn revert_latest_parses() {
    let cli = must_parse(&["brrr-lint", "revert", "--latest"]);
    if let Some(Commands::Revert { latest, .. }) = cli.command {
        assert!(latest);
    } else {
        panic!("expected Revert command");
    }
}

#[test]
fn revert_dry_run_parses() {
    let cli = must_parse(&["brrr-lint", "revert", "--latest", "--dry-run"]);
    if let Some(Commands::Revert { latest, dry_run, .. }) = cli.command {
        assert!(latest);
        assert!(dry_run);
    } else {
        panic!("expected Revert command");
    }
}

#[test]
fn revert_conflicting_flags_rejected() {
    // --list and --latest conflict.
    must_fail_containing(
        &["brrr-lint", "revert", "--list", "--latest"],
        "cannot be used with",
    );
}
