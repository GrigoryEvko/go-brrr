//! brrr-lint: A fast linter and language server for F* (FStar).
//!
//! A standalone LSP server and linter for F*, the proof-oriented programming language.
//!
//! # Usage
//!
//! ```bash
//! # Run LSP server (default)
//! brrr-lint serve
//!
//! # Check F* files for issues (like ruff check)
//! brrr-lint check src/
//!
//! # Preview fixes (dry-run mode - DEFAULT, no files modified)
//! brrr-lint fix src/
//!
//! # Actually apply fixes and write changes
//! brrr-lint fix src/ --apply
//!
//! # Generate default config
//! brrr-lint init
//!
//! # Run with debug logging
//! brrr-lint --debug serve
//! ```

use brrr_lint::cli::{Cli, Commands, SeverityFilter, validate_cli_semantics};
use brrr_lint::config::LspSettings;
use brrr_lint::lint::{
    ColorMode, init_color,
    print_revert_result, LintConfig, LintEngine,
    print_timestamp_list_with_points, print_cleanup_summary,
    cleanup_old_backups, parse_duration_str,
};
use brrr_lint::lint_config::{discover_and_load_config, LintFileConfig};
use brrr_lint::server::FstarServer;

use clap::Parser;
use std::path::PathBuf;
use tower_lsp::{LspService, Server};
use tracing::{info, Level};
use tracing_subscriber::FmtSubscriber;

#[tokio::main]
async fn main() {
    let cli = Cli::parse();

    // Initialize color output before anything else writes to stdout.
    init_color(cli.color);

    // Initialize logging
    let log_level = if cli.debug {
        Level::DEBUG
    } else if cli.verbose {
        Level::INFO
    } else if cli.quiet {
        Level::WARN
    } else {
        Level::INFO
    };

    let subscriber = FmtSubscriber::builder()
        .with_max_level(log_level)
        .with_writer(std::io::stderr)
        .with_ansi(!matches!(cli.color, ColorMode::Never))
        .finish();

    if let Err(e) = tracing::subscriber::set_global_default(subscriber) {
        eprintln!("Failed to set tracing subscriber: {}", e);
        std::process::exit(brrr_lint::exit_code::INTERNAL_ERROR);
    }

    // Validate semantic constraints and print warnings.
    for warning in validate_cli_semantics(&cli) {
        eprintln!("{}", warning);
    }

    // Discover and load config file.
    let file_config = load_file_config(&cli);

    match cli.command {
        None | Some(Commands::Serve { .. }) => {
            run_server(cli).await;
        }
        Some(Commands::Check {
            paths,
            select,
            exclude,
            severity,
            format,
            show_fixes,
            exit_zero,
            max_diagnostics,
        }) => {
            let config = build_lint_config(
                select,
                exclude,
                cli.fstar_exe,
                max_diagnostics,
                severity,
                &file_config,
            );
            let engine = LintEngine::new(config);
            let exit_code = engine.check(&paths, format, show_fixes).await;
            if !exit_zero {
                std::process::exit(exit_code);
            }
        }
        Some(Commands::Fix {
            paths,
            select,
            exclude,
            severity,
            apply,
            force,
            format,
            dry_run_format,
        }) => {
            let _ = severity; // severity filtering for fix is future work
            let config = build_lint_config(
                select,
                exclude,
                cli.fstar_exe,
                None,
                None, // severity filtering for fix is future work
                &file_config,
            );
            let engine = LintEngine::new(config);
            // dry_run is the default (safe mode); --apply enables writing
            let dry_run = !apply;
            // --force only has effect when --apply is also used
            let force_apply = force && apply;
            let exit_code = engine.fix(&paths, format, dry_run, dry_run_format, force_apply).await;
            std::process::exit(exit_code);
        }
        Some(Commands::Rules) => {
            brrr_lint::lint::print_rules();
        }
        Some(Commands::Init { output, force }) => {
            run_init(&output, force);
        }
        Some(Commands::Revert {
            list,
            timestamp,
            latest,
            best_effort,
            create_point,
            to_point,
            cleanup,
            older_than,
            interactive,
            dry_run,
            force,
            paths,
        }) => {
            let exit_code = run_revert(
                list, timestamp, latest, best_effort,
                create_point, to_point,
                cleanup, older_than,
                interactive, dry_run, force,
                paths,
            );
            std::process::exit(exit_code);
        }
    }
}

/// Load the `.brrr-lint.toml` config file, respecting --config flag.
fn load_file_config(cli: &Cli) -> Option<LintFileConfig> {
    if let Some(ref explicit_path) = cli.config {
        match LintFileConfig::load(explicit_path) {
            Ok(config) => {
                info!("Loaded config from {}", explicit_path.display());
                return Some(config);
            }
            Err(e) => {
                eprintln!("Error loading config {}: {}", explicit_path.display(), e);
                std::process::exit(brrr_lint::exit_code::CONFIG_ERROR);
            }
        }
    }

    // Auto-discover config file from CWD upwards.
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    match discover_and_load_config(&cwd) {
        Ok(Some((config, path))) => {
            info!("Using config: {}", path.display());
            Some(config)
        }
        Ok(None) => None,
        Err(e) => {
            eprintln!("Warning: failed to load .brrr-lint.toml: {}", e);
            None
        }
    }
}

/// Build a `LintConfig` by merging CLI flags with the file config.
/// CLI flags always take precedence.
fn build_lint_config(
    cli_select: Option<String>,
    cli_exclude: Option<String>,
    cli_fstar_exe: Option<String>,
    cli_max_diagnostics: Option<usize>,
    _cli_severity: Option<SeverityFilter>,
    file_config: &Option<LintFileConfig>,
) -> LintConfig {
    // Merge select: CLI overrides file config.
    let select = cli_select.or_else(|| {
        file_config.as_ref().and_then(|fc| {
            if fc.rules.select.is_empty() {
                None
            } else {
                Some(fc.rules.select.join(","))
            }
        })
    });

    // Merge exclude: CLI overrides file config.
    let exclude = cli_exclude.or_else(|| {
        file_config.as_ref().and_then(|fc| {
            if fc.rules.exclude.is_empty() {
                None
            } else {
                Some(fc.rules.exclude.join(","))
            }
        })
    });

    // Merge max_diagnostics: CLI overrides file config.
    let max_diagnostics = cli_max_diagnostics.or_else(|| {
        file_config.as_ref().and_then(|fc| fc.output.max_diagnostics)
    });

    LintConfig::new(select, exclude, cli_fstar_exe)
        .with_max_diagnostics(max_diagnostics)
}

/// Execute the `init` command: generate a default `.brrr-lint.toml`.
fn run_init(output: &PathBuf, force: bool) {
    if output.exists() && !force {
        eprintln!(
            "Error: {} already exists. Use --force to overwrite.",
            output.display()
        );
        std::process::exit(brrr_lint::exit_code::CONFIG_ERROR);
    }

    match std::fs::write(output, LintFileConfig::default_toml()) {
        Ok(()) => {
            println!("Created {}", output.display());
            println!();
            println!("Edit the file to customize rule selection, severity overrides,");
            println!("file include/exclude patterns, and fix behavior.");
        }
        Err(e) => {
            eprintln!("Error writing {}: {}", output.display(), e);
            std::process::exit(brrr_lint::exit_code::IO_ERROR);
        }
    }
}

/// Execute the revert command.
#[allow(clippy::too_many_arguments)]
fn run_revert(
    list: bool,
    timestamp: Option<u64>,
    latest: bool,
    best_effort: Option<u64>,
    create_point: Option<String>,
    to_point: Option<String>,
    cleanup: bool,
    older_than: Option<String>,
    interactive: bool,
    dry_run: bool,
    _force: bool,
    paths: Vec<PathBuf>,
) -> i32 {
    use brrr_lint::lint::RevertEngine;

    // Determine search paths: use provided paths or current directory.
    let search_paths = if paths.is_empty() {
        vec![std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."))]
    } else {
        paths.clone()
    };

    // Build the revert engine.
    let mut engine = RevertEngine::new(search_paths.clone());

    // Apply path filter if a single path is provided and it's not a meta-action.
    if paths.len() == 1 && !list && !cleanup {
        let filter_path = &paths[0];
        if filter_path.to_str().map(|s| s != ".").unwrap_or(false) {
            engine = engine.with_path_filter(filter_path.clone());
        }
    }

    // ---- Handle --cleanup ----
    if cleanup {
        let max_age = match older_than {
            Some(ref s) => match parse_duration_str(s) {
                Ok(d) => d,
                Err(e) => {
                    eprintln!("Error: invalid --older-than value: {}", e);
                    return 1;
                }
            },
            None => {
                // Default: 7 days
                std::time::Duration::from_secs(7 * 86400)
            }
        };

        match cleanup_old_backups(&search_paths, max_age, dry_run) {
            Ok(summary) => {
                print_cleanup_summary(&summary, dry_run);
                return 0;
            }
            Err(e) => {
                eprintln!("Error during cleanup: {}", e);
                return 1;
            }
        }
    }

    // ---- Handle --create-point ----
    if let Some(ref name) = create_point {
        match engine.create_revert_point(name, None) {
            Ok(point) => {
                println!("Created revert point '{}' with {} file(s).", point.name, point.files.len());
                println!("Restore with: brrr-lint revert --to-point {}", name);
                return 0;
            }
            Err(e) => {
                eprintln!("Error creating revert point: {}", e);
                return 1;
            }
        }
    }

    // ---- Handle --to-point ----
    if let Some(ref name) = to_point {
        match engine.revert_to_point(name, dry_run) {
            Ok(result) => {
                print_revert_result(&result, dry_run);
                return if result.is_success() { 0 } else { 1 };
            }
            Err(e) => {
                eprintln!("Error reverting to point '{}': {}", name, e);
                return 1;
            }
        }
    }

    // ---- Handle --list ----
    if list {
        match engine.list_timestamps() {
            Ok(summaries) => {
                print_timestamp_list_with_points(&summaries, &search_paths);
                return 0;
            }
            Err(e) => {
                eprintln!("Error listing backups: {}", e);
                return 1;
            }
        }
    }

    // ---- Handle --timestamp ----
    if let Some(ts) = timestamp {
        if interactive {
            match engine.revert_interactive(ts) {
                Ok(result) => {
                    print_revert_result(&result, false);
                    return if result.is_success() { 0 } else { 1 };
                }
                Err(e) => {
                    eprintln!("Error in interactive revert: {}", e);
                    return 1;
                }
            }
        }

        match engine.revert_to_timestamp(ts, dry_run) {
            Ok(result) => {
                print_revert_result(&result, dry_run);
                return if result.is_success() { 0 } else { 1 };
            }
            Err(e) => {
                eprintln!("Error reverting to timestamp {}: {}", ts, e);
                return 1;
            }
        }
    }

    // ---- Handle --latest ----
    if latest {
        if interactive {
            match engine.get_latest_timestamp() {
                Ok(Some(ts)) => match engine.revert_interactive(ts) {
                    Ok(result) => {
                        print_revert_result(&result, false);
                        return if result.is_success() { 0 } else { 1 };
                    }
                    Err(e) => {
                        eprintln!("Error in interactive revert: {}", e);
                        return 1;
                    }
                },
                Ok(None) => {
                    eprintln!("No backups found.");
                    return 1;
                }
                Err(e) => {
                    eprintln!("Error: {}", e);
                    return 1;
                }
            }
        }

        match engine.revert_to_latest(dry_run) {
            Ok(result) => {
                print_revert_result(&result, dry_run);
                return if result.is_success() { 0 } else { 1 };
            }
            Err(e) => {
                eprintln!("Error reverting to latest backup: {}", e);
                return 1;
            }
        }
    }

    // ---- Handle --best-effort ----
    if let Some(target_ts) = best_effort {
        match engine.revert_best_effort(target_ts, dry_run) {
            Ok((actual_ts, result)) => {
                if actual_ts != target_ts {
                    println!(
                        "Note: Exact timestamp {} not found, using closest: {}",
                        target_ts, actual_ts
                    );
                }
                print_revert_result(&result, dry_run);
                return if result.is_success() { 0 } else { 1 };
            }
            Err(e) => {
                eprintln!("Error reverting (best-effort) to timestamp {}: {}", target_ts, e);
                return 1;
            }
        }
    }

    // ---- No action specified ----
    eprintln!("Error: No action specified.");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  brrr-lint revert --list                      # List backups and revert points");
    eprintln!("  brrr-lint revert --latest                    # Revert to most recent backup");
    eprintln!("  brrr-lint revert --latest -i                 # Interactive revert (pick files)");
    eprintln!("  brrr-lint revert --latest --dry-run          # Preview what would change");
    eprintln!("  brrr-lint revert --timestamp 1706123456789   # Revert to exact timestamp");
    eprintln!("  brrr-lint revert --create-point my-snapshot  # Create named snapshot");
    eprintln!("  brrr-lint revert --to-point my-snapshot      # Restore named snapshot");
    eprintln!("  brrr-lint revert --cleanup --older-than 7d   # Remove old backups");
    1
}

async fn run_server(cli: Cli) {
    // Extract serve options or use defaults
    let (verify_on_open, verify_on_save, fly_check, timeout_ms, max_processes) = match cli.command {
        Some(Commands::Serve {
            verify_on_open,
            verify_on_save,
            fly_check,
            timeout_ms,
            max_processes,
        }) => (
            verify_on_open,
            verify_on_save,
            fly_check,
            timeout_ms,
            max_processes,
        ),
        _ => (false, true, true, 30000, 4),
    };

    info!("brrr-lint LSP server starting");
    info!("Version: {}", env!("CARGO_PKG_VERSION"));
    info!("Debug: {}", cli.debug);

    // Build CLI-derived settings
    let cli_settings = LspSettings {
        verify_on_open,
        verify_on_save,
        fly_check,
        debug: cli.debug,
        timeout_ms,
        max_processes,
        fstar_exe: cli.fstar_exe,
    };

    // Create LSP service with custom F* notification and request handlers
    let (service, socket) = LspService::build(|client| FstarServer::new(client, cli_settings))
        .custom_method(
            "$/fstar/verifyToPosition",
            FstarServer::handle_verify_to_position,
        )
        .custom_method("$/fstar/restart", FstarServer::handle_restart)
        .custom_method(
            "$/fstar/killAndRestartSolver",
            FstarServer::handle_kill_and_restart_solver,
        )
        .custom_method("$/fstar/killAll", FstarServer::handle_kill_all)
        .custom_method(
            "$/fstar/getTranslatedFst",
            FstarServer::handle_get_translated_fst,
        )
        // Custom requests for querying verification state
        .custom_method(
            "$/fstar/getDiagnostics",
            FstarServer::handle_get_diagnostics,
        )
        .custom_method("$/fstar/getFragments", FstarServer::handle_get_fragments)
        .finish();

    // Run server with stdio transport
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    Server::new(stdin, stdout, socket).serve(service).await;

    info!("brrr-lint LSP server shutting down");
}
