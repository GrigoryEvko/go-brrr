//! CLI integration tests.
//!
//! Tests command-line interface functionality.

use std::path::PathBuf;
use std::process::{Command, Output};

/// Get the path to the built binary.
fn binary_path() -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    // Try release first, then debug
    let release_path = path.join("target/release/brrr");
    let debug_path = path.join("target/debug/brrr");

    if release_path.exists() {
        release_path
    } else {
        debug_path
    }
}

/// Get path to test fixtures.
fn fixtures_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
}

/// Run CLI command and return output.
fn run_cli(args: &[&str]) -> Option<Output> {
    let binary = binary_path();

    if !binary.exists() {
        return None;
    }

    Command::new(&binary).args(args).output().ok()
}

/// Check if binary exists.
fn require_binary() -> bool {
    binary_path().exists()
}

// =============================================================================
// Security CLI Tests
// =============================================================================

#[test]
fn test_security_scan_command() {
    if !require_binary() {
        eprintln!("Skipping CLI test: binary not found");
        return;
    }

    let fixtures = fixtures_path().join("security");

    let output = run_cli(&[
        "security",
        "scan",
        fixtures.to_str().unwrap(),
        "--format",
        "json",
    ]);

    if let Some(out) = output {
        // Should exit successfully
        assert!(
            out.status.success() || out.status.code() == Some(1),
            "Security scan should complete"
        );
    }
}

// =============================================================================
// Metrics CLI Tests
// =============================================================================

#[test]
fn test_metrics_complexity_command() {
    if !require_binary() {
        return;
    }

    let fixtures = fixtures_path().join("metrics");

    let output = run_cli(&[
        "metrics",
        "complexity",
        fixtures.to_str().unwrap(),
        "--lang",
        "python",
        "--format",
        "json",
    ]);

    if let Some(out) = output {
        assert!(out.status.success(), "Metrics complexity should succeed");
    }
}

// =============================================================================
// CFG CLI Tests
// =============================================================================

#[test]
fn test_cfg_command() {
    if !require_binary() {
        return;
    }

    let fixture = fixtures_path().join("metrics").join("complexity_low.py");

    let output = run_cli(&[
        "cfg",
        fixture.to_str().unwrap(),
        "simple_if",
        "--format",
        "json",
    ]);

    if let Some(out) = output {
        assert!(out.status.success(), "CFG command should succeed");
    }
}

// =============================================================================
// Error Handling Tests
// =============================================================================

#[test]
fn test_nonexistent_file_error() {
    if !require_binary() {
        return;
    }

    let output = run_cli(&["cfg", "/nonexistent/path/file.py", "function"]);

    if let Some(out) = output {
        // Should fail with non-zero exit code
        assert!(!out.status.success(), "Should fail for nonexistent file");
    }
}

#[test]
fn test_help_command() {
    if !require_binary() {
        return;
    }

    let output = run_cli(&["--help"]);

    if let Some(out) = output {
        assert!(out.status.success(), "Help should succeed");

        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("Usage")
                || stdout.contains("USAGE")
                || stdout.contains("brrr")
                || stdout.contains("Commands"),
            "Help should contain usage information"
        );
    }
}

#[test]
fn test_version_command() {
    if !require_binary() {
        return;
    }

    let output = run_cli(&["--version"]);

    if let Some(out) = output {
        assert!(out.status.success(), "Version should succeed");
    }
}

// =============================================================================
// Performance Tests
// =============================================================================

#[test]
fn test_cli_response_time() {
    use std::time::Instant;

    if !require_binary() {
        return;
    }

    let fixture = fixtures_path().join("metrics").join("complexity_low.py");

    let start = Instant::now();

    let output = run_cli(&["cfg", fixture.to_str().unwrap(), "simple_return"]);

    let duration = start.elapsed();

    if output.is_some() {
        // CLI should respond quickly for simple operations
        assert!(
            duration.as_secs() < 10,
            "CLI should respond in < 10 seconds, took {:?}",
            duration
        );
    }
}
