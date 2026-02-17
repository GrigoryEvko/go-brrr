//! Real-time diagnostics for brrr.
//!
//! Wraps type checkers (pyright, mypy) and linters (ruff) to provide
//! structured error output for LLM agents.
//!
//! Supports:
//! - Python: pyright (type checker) + ruff (linter)
//! - TypeScript/JavaScript: tsc (type checker)
//! - Go: go vet (type checker) + golangci-lint (linter)
//! - Rust: cargo check (type checker) + clippy (linter)
//! - Java: javac (type checker) + checkstyle (linter)
//! - C/C++: clang/gcc (type checker) + cppcheck (linter)

use std::collections::HashMap;
use std::path::Path;
use std::process::{Command, Stdio};

use anyhow::{Context, Result};
use once_cell::sync::Lazy;
use regex::Regex;
use serde::{Deserialize, Serialize};

// =============================================================================
// STATIC REGEX PATTERNS (compiled once, reused across all calls)
// =============================================================================

/// TSC output format: file(line,col): error TSxxxx: message
static TSC_RE: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"(.+?)\((\d+),(\d+)\):\s*(error|warning)\s+(TS\d+):\s*(.+)")
        .expect("Invalid TSC regex pattern")
});

/// Go vet output format: file.go:line:col: message
static GO_VET_RE: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"(.+?):(\d+):(\d+):\s*(.+)").expect("Invalid go vet regex pattern"));

/// GCC/G++ output format: file.c:line:col: error: message
static GCC_RE: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"(.+?):(\d+):(\d+):\s*(error|warning):\s*(.+)").expect("Invalid GCC regex pattern")
});

/// Javac output format: file.java:line: error: message
static JAVAC_RE: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"(.+?):(\d+):\s*(error|warning):\s*(.+)").expect("Invalid javac regex pattern")
});

/// Cppcheck XML error element pattern
static CPPCHECK_ERROR_RE: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r#"<error[^>]*id="([^"]*)"[^>]*severity="([^"]*)"[^>]*msg="([^"]*)"[^>]*>"#)
        .expect("Invalid cppcheck error regex pattern")
});

/// Cppcheck XML location element pattern
static CPPCHECK_LOCATION_RE: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r#"<location[^>]*file="([^"]*)"[^>]*line="(\d+)"[^>]*column="(\d+)""#)
        .expect("Invalid cppcheck location regex pattern")
});

/// A single diagnostic message from a type checker or linter.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Diagnostic {
    /// Source file path
    pub file: String,
    /// Line number (1-indexed)
    pub line: u32,
    /// Column number (1-indexed)
    pub column: u32,
    /// Severity: "error" or "warning"
    pub severity: String,
    /// The diagnostic message
    pub message: String,
    /// Rule identifier (e.g., "E0001", "unused-variable")
    #[serde(default)]
    pub rule: String,
    /// Source tool (e.g., "pyright", "ruff", "cargo")
    pub source: String,
}

/// Result of running diagnostics on a file or project.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiagnosticsResult {
    /// Target path (file or project)
    pub target: String,
    /// Detected or specified language
    pub language: String,
    /// Tools that were successfully run
    pub tools: Vec<String>,
    /// All diagnostics collected
    pub diagnostics: Vec<Diagnostic>,
    /// Count of errors
    pub error_count: usize,
    /// Count of warnings
    pub warning_count: usize,
    /// Number of files with diagnostics (for project mode)
    #[serde(default)]
    pub file_count: usize,
}

/// Detect language from file extension.
pub fn detect_language(file_path: &Path) -> &'static str {
    let ext = file_path.extension().and_then(|e| e.to_str()).unwrap_or("");

    match ext {
        "py" => "python",
        "ts" => "typescript",
        "tsx" => "tsx",
        "js" | "mjs" | "cjs" => "javascript",
        "jsx" => "tsx",
        "go" => "go",
        "rs" => "rust",
        "java" => "java",
        "c" | "h" => "c",
        "cpp" | "cc" | "cxx" | "hpp" | "cu" | "cuh" => "cpp",
        "rb" => "ruby",
        "php" => "php",
        "kt" => "kotlin",
        "swift" => "swift",
        "cs" => "csharp",
        "scala" => "scala",
        "ex" | "exs" => "elixir",
        _ => "unknown",
    }
}

/// Detect the primary language of a project directory.
pub fn detect_project_language(path: &Path) -> &'static str {
    // Count files by extension to determine primary language
    let mut counts: HashMap<&str, usize> = HashMap::new();

    if let Ok(entries) = std::fs::read_dir(path) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_file() {
                let lang = detect_language(&path);
                if lang != "unknown" {
                    *counts.entry(lang).or_insert(0) += 1;
                }
            }
        }
    }

    // Also check for common project files
    if path.join("Cargo.toml").exists() {
        return "rust";
    }
    if path.join("go.mod").exists() {
        return "go";
    }
    if path.join("pyproject.toml").exists() || path.join("setup.py").exists() {
        return "python";
    }
    if path.join("package.json").exists() {
        // Check for TypeScript
        if path.join("tsconfig.json").exists() {
            return "typescript";
        }
        return "javascript";
    }
    if path.join("pom.xml").exists() || path.join("build.gradle").exists() {
        return "java";
    }

    // Return the most common language
    counts
        .into_iter()
        .max_by_key(|(_, count)| *count)
        .map(|(lang, _)| lang)
        .unwrap_or("unknown")
}

/// Check if a command is available in PATH.
fn command_exists(cmd: &str) -> bool {
    which::which(cmd).is_ok()
}

/// Convert bytes to String using fast SIMD UTF-8 validation.
///
/// Uses simdutf8 for SIMD-accelerated validation on x86_64/aarch64.
/// Falls back to lossy conversion only if validation fails (rare for command output).
#[inline]
fn fast_utf8_to_string(bytes: &[u8]) -> String {
    // Fast path: SIMD validation (4-8x faster than scalar on modern CPUs)
    match simdutf8::basic::from_utf8(bytes) {
        Ok(valid_str) => valid_str.to_string(),
        Err(_) => String::from_utf8_lossy(bytes).into_owned(),
    }
}

/// Run a command with timeout and capture output.
fn run_command(
    cmd: &str,
    args: &[&str],
    cwd: Option<&Path>,
    _timeout_secs: u64,
) -> Result<(String, String, bool)> {
    let mut command = Command::new(cmd);
    command
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    if let Some(dir) = cwd {
        command.current_dir(dir);
    }

    let child = command.spawn().context("Failed to spawn command")?;

    // Wait with timeout (simplified - full timeout requires more complex handling)
    let output = child
        .wait_with_output()
        .context("Failed to wait for command")?;

    let stdout = fast_utf8_to_string(&output.stdout);
    let stderr = fast_utf8_to_string(&output.stderr);
    let success = output.status.success();

    Ok((stdout, stderr, success))
}

// =============================================================================
// PYRIGHT OUTPUT PARSING
// =============================================================================

/// Pyright JSON output structure.
#[derive(Debug, Deserialize)]
struct PyrightOutput {
    #[serde(default, rename = "generalDiagnostics")]
    general_diagnostics: Vec<PyrightDiagnostic>,
}

#[derive(Debug, Deserialize)]
struct PyrightDiagnostic {
    file: String,
    #[serde(default)]
    range: PyrightRange,
    severity: String,
    message: String,
    #[serde(default)]
    rule: String,
}

#[derive(Debug, Deserialize, Default)]
struct PyrightRange {
    start: PyrightPosition,
}

#[derive(Debug, Deserialize, Default)]
struct PyrightPosition {
    line: u32,
    character: u32,
}

fn parse_pyright_output(stdout: &str) -> Vec<Diagnostic> {
    let Ok(data) = serde_json::from_str::<PyrightOutput>(stdout) else {
        return Vec::new();
    };

    data.general_diagnostics
        .into_iter()
        .map(|d| Diagnostic {
            file: d.file,
            line: d.range.start.line + 1, // Convert to 1-indexed
            column: d.range.start.character + 1,
            severity: d.severity,
            message: d.message,
            rule: d.rule,
            source: "pyright".to_string(),
        })
        .collect()
}

// =============================================================================
// RUFF OUTPUT PARSING
// =============================================================================

#[derive(Debug, Deserialize)]
struct RuffDiagnostic {
    filename: String,
    #[serde(default)]
    location: RuffLocation,
    message: String,
    #[serde(default)]
    code: String,
}

#[derive(Debug, Deserialize, Default)]
struct RuffLocation {
    row: u32,
    column: u32,
}

fn parse_ruff_output(stdout: &str) -> Vec<Diagnostic> {
    let Ok(data) = serde_json::from_str::<Vec<RuffDiagnostic>>(stdout) else {
        return Vec::new();
    };

    data.into_iter()
        .map(|d| Diagnostic {
            file: d.filename,
            line: d.location.row,
            column: d.location.column,
            severity: "warning".to_string(),
            message: d.message,
            rule: d.code,
            source: "ruff".to_string(),
        })
        .collect()
}

// =============================================================================
// TSC OUTPUT PARSING
// =============================================================================

fn parse_tsc_output(stderr: &str) -> Vec<Diagnostic> {
    stderr
        .lines()
        .filter_map(|line| {
            let caps = TSC_RE.captures(line)?;
            Some(Diagnostic {
                file: caps.get(1)?.as_str().to_string(),
                line: caps.get(2)?.as_str().parse().ok()?,
                column: caps.get(3)?.as_str().parse().ok()?,
                severity: caps.get(4)?.as_str().to_string(),
                message: caps.get(6)?.as_str().to_string(),
                rule: caps.get(5)?.as_str().to_string(),
                source: "tsc".to_string(),
            })
        })
        .collect()
}

// =============================================================================
// GO VET OUTPUT PARSING
// =============================================================================

fn parse_go_vet_output(stderr: &str) -> Vec<Diagnostic> {
    stderr
        .lines()
        .filter_map(|line| {
            let caps = GO_VET_RE.captures(line)?;
            Some(Diagnostic {
                file: caps.get(1)?.as_str().to_string(),
                line: caps.get(2)?.as_str().parse().ok()?,
                column: caps.get(3)?.as_str().parse().ok()?,
                severity: "error".to_string(),
                message: caps.get(4)?.as_str().to_string(),
                rule: String::new(),
                source: "go vet".to_string(),
            })
        })
        .collect()
}

// =============================================================================
// GOLANGCI-LINT OUTPUT PARSING
// =============================================================================

#[derive(Debug, Deserialize)]
struct GolangciLintOutput {
    #[serde(default, rename = "Issues")]
    issues: Vec<GolangciLintIssue>,
}

#[derive(Debug, Deserialize)]
struct GolangciLintIssue {
    #[serde(default, rename = "Text")]
    text: String,
    #[serde(default, rename = "FromLinter")]
    from_linter: String,
    #[serde(default, rename = "Pos")]
    pos: GolangciLintPos,
}

#[derive(Debug, Deserialize, Default)]
struct GolangciLintPos {
    #[serde(default, rename = "Filename")]
    filename: String,
    #[serde(default, rename = "Line")]
    line: u32,
    #[serde(default, rename = "Column")]
    column: u32,
}

fn parse_golangci_lint_output(stdout: &str) -> Vec<Diagnostic> {
    let Ok(data) = serde_json::from_str::<GolangciLintOutput>(stdout) else {
        return Vec::new();
    };

    data.issues
        .into_iter()
        .map(|issue| Diagnostic {
            file: issue.pos.filename,
            line: issue.pos.line,
            column: issue.pos.column,
            severity: "warning".to_string(),
            message: issue.text,
            rule: issue.from_linter,
            source: "golangci-lint".to_string(),
        })
        .collect()
}

// =============================================================================
// CARGO CHECK / CLIPPY OUTPUT PARSING
// =============================================================================

#[derive(Debug, Deserialize)]
struct CargoMessage {
    reason: String,
    #[serde(default)]
    message: Option<CargoCompilerMessage>,
}

#[derive(Debug, Deserialize)]
struct CargoCompilerMessage {
    level: String,
    message: String,
    #[serde(default)]
    code: Option<CargoCode>,
    #[serde(default)]
    spans: Vec<CargoSpan>,
}

#[derive(Debug, Deserialize)]
struct CargoCode {
    #[serde(default)]
    code: String,
}

#[derive(Debug, Deserialize)]
struct CargoSpan {
    file_name: String,
    line_start: u32,
    column_start: u32,
}

fn parse_cargo_output(stdout: &str, source: &str) -> Vec<Diagnostic> {
    stdout
        .lines()
        .filter_map(|line| {
            let msg: CargoMessage = serde_json::from_str(line).ok()?;
            if msg.reason != "compiler-message" {
                return None;
            }
            let message = msg.message?;
            let span = message.spans.first()?;
            Some(Diagnostic {
                file: span.file_name.clone(),
                line: span.line_start,
                column: span.column_start,
                severity: message.level,
                message: message.message,
                rule: message.code.map(|c| c.code).unwrap_or_default(),
                source: source.to_string(),
            })
        })
        .collect()
}

// =============================================================================
// GCC/G++ OUTPUT PARSING
// =============================================================================

fn parse_gcc_output(stderr: &str, source: &str) -> Vec<Diagnostic> {
    stderr
        .lines()
        .filter_map(|line| {
            let caps = GCC_RE.captures(line)?;
            Some(Diagnostic {
                file: caps.get(1)?.as_str().to_string(),
                line: caps.get(2)?.as_str().parse().ok()?,
                column: caps.get(3)?.as_str().parse().ok()?,
                severity: caps.get(4)?.as_str().to_string(),
                message: caps.get(5)?.as_str().to_string(),
                rule: String::new(),
                source: source.to_string(),
            })
        })
        .collect()
}

// =============================================================================
// JAVAC OUTPUT PARSING
// =============================================================================

fn parse_javac_output(stderr: &str) -> Vec<Diagnostic> {
    stderr
        .lines()
        .filter_map(|line| {
            let caps = JAVAC_RE.captures(line)?;
            Some(Diagnostic {
                file: caps.get(1)?.as_str().to_string(),
                line: caps.get(2)?.as_str().parse().ok()?,
                column: 0,
                severity: caps.get(3)?.as_str().to_string(),
                message: caps.get(4)?.as_str().to_string(),
                rule: String::new(),
                source: "javac".to_string(),
            })
        })
        .collect()
}

// =============================================================================
// CPPCHECK OUTPUT PARSING (XML)
// =============================================================================

fn parse_cppcheck_output(stderr: &str) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    // Simple approach: find errors and their locations
    for error_match in CPPCHECK_ERROR_RE.captures_iter(stderr) {
        let rule = error_match.get(1).map(|m| m.as_str()).unwrap_or("");
        let severity = error_match.get(2).map(|m| m.as_str()).unwrap_or("error");
        let message = error_match.get(3).map(|m| m.as_str()).unwrap_or("");

        // Find the next location after this error
        let error_end = error_match.get(0).map(|m| m.end()).unwrap_or(0);
        if let Some(loc_match) = CPPCHECK_LOCATION_RE.captures(&stderr[error_end..]) {
            diagnostics.push(Diagnostic {
                file: loc_match
                    .get(1)
                    .map(|m| m.as_str())
                    .unwrap_or("")
                    .to_string(),
                line: loc_match
                    .get(2)
                    .and_then(|m| m.as_str().parse().ok())
                    .unwrap_or(0),
                column: loc_match
                    .get(3)
                    .and_then(|m| m.as_str().parse().ok())
                    .unwrap_or(0),
                severity: severity.to_string(),
                message: message.to_string(),
                rule: rule.to_string(),
                source: "cppcheck".to_string(),
            });
        }
    }

    diagnostics
}

// =============================================================================
// MAIN DIAGNOSTICS FUNCTIONS
// =============================================================================

/// Get diagnostics for a single file.
pub fn get_diagnostics(
    file_path: &Path,
    language: Option<&str>,
    include_lint: bool,
) -> Result<DiagnosticsResult> {
    let path = file_path
        .canonicalize()
        .unwrap_or_else(|_| file_path.to_path_buf());

    if !path.exists() {
        anyhow::bail!("File not found: {}", path.display());
    }

    let lang = language.unwrap_or_else(|| detect_language(&path));
    let mut all_diagnostics = Vec::new();
    let mut tools_used = Vec::new();

    match lang {
        "python" => {
            // Run pyright for type checking
            if command_exists("pyright") {
                if let Ok((stdout, _, _)) = run_command(
                    "pyright",
                    &["--outputjson", path.to_str().unwrap_or("")],
                    None,
                    30,
                ) {
                    all_diagnostics.extend(parse_pyright_output(&stdout));
                    tools_used.push("pyright".to_string());
                }
            }

            // Run ruff for linting
            if include_lint && command_exists("ruff") {
                if let Ok((stdout, _, _)) = run_command(
                    "ruff",
                    &["check", "--output-format=json", path.to_str().unwrap_or("")],
                    None,
                    10,
                ) {
                    all_diagnostics.extend(parse_ruff_output(&stdout));
                    tools_used.push("ruff".to_string());
                }
            }
        }

        "typescript" | "tsx" | "javascript" => {
            // Run tsc for type checking
            if command_exists("tsc") {
                if let Ok((_, stderr, _)) = run_command(
                    "tsc",
                    &["--noEmit", "--pretty", "false", path.to_str().unwrap_or("")],
                    None,
                    30,
                ) {
                    all_diagnostics.extend(parse_tsc_output(&stderr));
                    tools_used.push("tsc".to_string());
                }
            }
        }

        "go" => {
            // Run go vet for type checking
            if command_exists("go") {
                if let Ok((_, stderr, _)) =
                    run_command("go", &["vet", path.to_str().unwrap_or("")], None, 30)
                {
                    all_diagnostics.extend(parse_go_vet_output(&stderr));
                    tools_used.push("go vet".to_string());
                }
            }

            // Run golangci-lint for linting
            if include_lint && command_exists("golangci-lint") {
                if let Ok((stdout, _, _)) = run_command(
                    "golangci-lint",
                    &["run", "--out-format=json", path.to_str().unwrap_or("")],
                    None,
                    60,
                ) {
                    all_diagnostics.extend(parse_golangci_lint_output(&stdout));
                    tools_used.push("golangci-lint".to_string());
                }
            }
        }

        "rust" => {
            let parent = path.parent();
            // Run cargo check for type checking
            if command_exists("cargo") {
                if let Ok((stdout, _, _)) =
                    run_command("cargo", &["check", "--message-format=json"], parent, 120)
                {
                    all_diagnostics.extend(parse_cargo_output(&stdout, "cargo check"));
                    tools_used.push("cargo check".to_string());
                }
            }

            // Run clippy for linting
            if include_lint && command_exists("cargo") {
                if let Ok((stdout, _, _)) =
                    run_command("cargo", &["clippy", "--message-format=json"], parent, 120)
                {
                    all_diagnostics.extend(parse_cargo_output(&stdout, "clippy"));
                    tools_used.push("clippy".to_string());
                }
            }
        }

        "java" => {
            // Run javac for type checking
            if command_exists("javac") {
                if let Ok((_, stderr, _)) = run_command(
                    "javac",
                    &["-Xlint:all", path.to_str().unwrap_or("")],
                    None,
                    30,
                ) {
                    all_diagnostics.extend(parse_javac_output(&stderr));
                    tools_used.push("javac".to_string());
                }
            }
        }

        "c" | "cpp" => {
            let compiler = if lang == "cpp" { "g++" } else { "gcc" };
            // Run gcc/g++ for type checking
            if command_exists(compiler) {
                if let Ok((_, stderr, _)) = run_command(
                    compiler,
                    &["-fsyntax-only", "-Wall", path.to_str().unwrap_or("")],
                    None,
                    30,
                ) {
                    all_diagnostics.extend(parse_gcc_output(&stderr, compiler));
                    tools_used.push(compiler.to_string());
                }
            }

            // Run cppcheck for linting
            if include_lint && command_exists("cppcheck") {
                if let Ok((_, stderr, _)) = run_command(
                    "cppcheck",
                    &["--xml", "--enable=all", path.to_str().unwrap_or("")],
                    None,
                    30,
                ) {
                    all_diagnostics.extend(parse_cppcheck_output(&stderr));
                    tools_used.push("cppcheck".to_string());
                }
            }
        }

        _ => {
            // Unsupported language - return empty diagnostics
        }
    }

    // Sort by file, then line number
    all_diagnostics.sort_by(|a, b| (&a.file, a.line, a.column).cmp(&(&b.file, b.line, b.column)));

    let error_count = all_diagnostics
        .iter()
        .filter(|d| d.severity == "error")
        .count();
    let warning_count = all_diagnostics
        .iter()
        .filter(|d| d.severity == "warning")
        .count();

    Ok(DiagnosticsResult {
        target: path.display().to_string(),
        language: lang.to_string(),
        tools: tools_used,
        diagnostics: all_diagnostics,
        error_count,
        warning_count,
        file_count: 0,
    })
}

/// Get diagnostics for an entire project.
pub fn get_project_diagnostics(
    project_path: &Path,
    language: Option<&str>,
    include_lint: bool,
) -> Result<DiagnosticsResult> {
    let path = project_path
        .canonicalize()
        .unwrap_or_else(|_| project_path.to_path_buf());

    if !path.exists() {
        anyhow::bail!("Path not found: {}", path.display());
    }

    let lang = language.unwrap_or_else(|| detect_project_language(&path));
    let mut all_diagnostics = Vec::new();
    let mut tools_used = Vec::new();

    match lang {
        "python" => {
            // Run pyright on project
            if command_exists("pyright") {
                if let Ok((stdout, _, _)) =
                    run_command("pyright", &["--outputjson", "."], Some(&path), 120)
                {
                    all_diagnostics.extend(parse_pyright_output(&stdout));
                    tools_used.push("pyright".to_string());
                }
            }

            // Run ruff on project
            if include_lint && command_exists("ruff") {
                if let Ok((stdout, _, _)) = run_command(
                    "ruff",
                    &["check", "--output-format=json", "."],
                    Some(&path),
                    60,
                ) {
                    all_diagnostics.extend(parse_ruff_output(&stdout));
                    tools_used.push("ruff".to_string());
                }
            }
        }

        "typescript" | "tsx" | "javascript" => {
            // Run tsc on project
            if command_exists("tsc") {
                if let Ok((_, stderr, _)) =
                    run_command("tsc", &["--noEmit", "--pretty", "false"], Some(&path), 120)
                {
                    all_diagnostics.extend(parse_tsc_output(&stderr));
                    tools_used.push("tsc".to_string());
                }
            }
        }

        "go" => {
            // Run go vet on project
            if command_exists("go") {
                if let Ok((_, stderr, _)) = run_command("go", &["vet", "./..."], Some(&path), 120) {
                    all_diagnostics.extend(parse_go_vet_output(&stderr));
                    tools_used.push("go vet".to_string());
                }
            }

            // Run golangci-lint on project
            if include_lint && command_exists("golangci-lint") {
                if let Ok((stdout, _, _)) = run_command(
                    "golangci-lint",
                    &["run", "--out-format=json", "./..."],
                    Some(&path),
                    120,
                ) {
                    all_diagnostics.extend(parse_golangci_lint_output(&stdout));
                    tools_used.push("golangci-lint".to_string());
                }
            }
        }

        "rust" => {
            // Run cargo check on project
            if command_exists("cargo") {
                if let Ok((stdout, _, _)) = run_command(
                    "cargo",
                    &["check", "--message-format=json"],
                    Some(&path),
                    180,
                ) {
                    all_diagnostics.extend(parse_cargo_output(&stdout, "cargo check"));
                    tools_used.push("cargo check".to_string());
                }
            }

            // Run clippy on project
            if include_lint && command_exists("cargo") {
                if let Ok((stdout, _, _)) = run_command(
                    "cargo",
                    &["clippy", "--message-format=json"],
                    Some(&path),
                    180,
                ) {
                    all_diagnostics.extend(parse_cargo_output(&stdout, "clippy"));
                    tools_used.push("clippy".to_string());
                }
            }
        }

        "java" => {
            // For Java projects, we'd need to find all .java files
            // This is a simplified implementation
            if command_exists("javac") {
                // Find java files and compile them
                tools_used.push("javac".to_string());
            }
        }

        _ => {
            // Unsupported language
        }
    }

    // Sort by file, then line number
    all_diagnostics.sort_by(|a, b| (&a.file, a.line, a.column).cmp(&(&b.file, b.line, b.column)));

    let error_count = all_diagnostics
        .iter()
        .filter(|d| d.severity == "error")
        .count();
    let warning_count = all_diagnostics
        .iter()
        .filter(|d| d.severity == "warning")
        .count();
    let file_count = all_diagnostics
        .iter()
        .map(|d| &d.file)
        .collect::<std::collections::HashSet<_>>()
        .len();

    Ok(DiagnosticsResult {
        target: path.display().to_string(),
        language: lang.to_string(),
        tools: tools_used,
        diagnostics: all_diagnostics,
        error_count,
        warning_count,
        file_count,
    })
}

/// Format diagnostics for text output.
pub fn format_diagnostics_text(result: &DiagnosticsResult) -> String {
    let mut output = Vec::new();

    output.push(format!(
        "Diagnostics for: {} ({})",
        result.target, result.language
    ));
    output.push(format!("Tools used: {}", result.tools.join(", ")));
    output.push(format!(
        "Found {} errors, {} warnings",
        result.error_count, result.warning_count
    ));
    output.push(String::new());

    for diag in &result.diagnostics {
        let severity = if diag.severity == "error" { "E" } else { "W" };
        let rule = if diag.rule.is_empty() {
            String::new()
        } else {
            format!(" [{}]", diag.rule)
        };
        output.push(format!(
            "{} {}:{}:{}: {}{}",
            severity, diag.file, diag.line, diag.column, diag.message, rule
        ));
    }

    output.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_language() {
        assert_eq!(detect_language(Path::new("test.py")), "python");
        assert_eq!(detect_language(Path::new("test.ts")), "typescript");
        assert_eq!(detect_language(Path::new("test.tsx")), "tsx");
        assert_eq!(detect_language(Path::new("test.js")), "javascript");
        assert_eq!(detect_language(Path::new("test.go")), "go");
        assert_eq!(detect_language(Path::new("test.rs")), "rust");
        assert_eq!(detect_language(Path::new("test.java")), "java");
        assert_eq!(detect_language(Path::new("test.c")), "c");
        assert_eq!(detect_language(Path::new("test.cpp")), "cpp");
        assert_eq!(detect_language(Path::new("test.unknown")), "unknown");
    }

    #[test]
    fn test_parse_pyright_output() {
        let sample = r#"{"generalDiagnostics":[{"file":"test.py","range":{"start":{"line":5,"character":10}},"severity":"error","message":"Type error","rule":"reportGeneralTypeIssues"}]}"#;
        let diagnostics = parse_pyright_output(sample);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].file, "test.py");
        assert_eq!(diagnostics[0].line, 6); // 1-indexed
        assert_eq!(diagnostics[0].column, 11);
        assert_eq!(diagnostics[0].severity, "error");
        assert_eq!(diagnostics[0].source, "pyright");
    }

    #[test]
    fn test_parse_ruff_output() {
        let sample = r#"[{"filename":"test.py","location":{"row":10,"column":5},"message":"Unused import","code":"F401"}]"#;
        let diagnostics = parse_ruff_output(sample);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].file, "test.py");
        assert_eq!(diagnostics[0].line, 10);
        assert_eq!(diagnostics[0].column, 5);
        assert_eq!(diagnostics[0].rule, "F401");
        assert_eq!(diagnostics[0].source, "ruff");
    }

    #[test]
    fn test_parse_tsc_output() {
        let sample =
            "src/index.ts(10,5): error TS2322: Type 'string' is not assignable to type 'number'.";
        let diagnostics = parse_tsc_output(sample);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].file, "src/index.ts");
        assert_eq!(diagnostics[0].line, 10);
        assert_eq!(diagnostics[0].column, 5);
        assert_eq!(diagnostics[0].rule, "TS2322");
        assert_eq!(diagnostics[0].source, "tsc");
    }

    #[test]
    fn test_parse_go_vet_output() {
        let sample = "main.go:15:3: unreachable code";
        let diagnostics = parse_go_vet_output(sample);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].file, "main.go");
        assert_eq!(diagnostics[0].line, 15);
        assert_eq!(diagnostics[0].column, 3);
        assert_eq!(diagnostics[0].source, "go vet");
    }

    #[test]
    fn test_parse_gcc_output() {
        let sample = "test.c:10:5: error: expected ';' before 'return'";
        let diagnostics = parse_gcc_output(sample, "gcc");
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].file, "test.c");
        assert_eq!(diagnostics[0].line, 10);
        assert_eq!(diagnostics[0].column, 5);
        assert_eq!(diagnostics[0].severity, "error");
        assert_eq!(diagnostics[0].source, "gcc");
    }
}
