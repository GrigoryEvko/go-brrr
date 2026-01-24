//! Security analysis module for detecting vulnerabilities in source code.
//!
//! This module provides static analysis capabilities for detecting common
//! security vulnerabilities such as command injection, SQL injection,
//! unsafe deserialization, hardcoded secrets, and other security issues.
//!
//! # Unified API
//!
//! The security module provides a unified `scan_security` function that runs
//! all security analyzers in parallel and returns a consolidated report:
//!
//! ```ignore
//! use go_brrr::security::{scan_security, SecurityConfig, Severity};
//!
//! // Scan with default config (all analyzers, all severity levels)
//! let report = scan_security("./src", &SecurityConfig::default())?;
//!
//! // Scan for CI/CD (medium+ severity, medium+ confidence)
//! let ci_report = scan_security("./src", &SecurityConfig::ci())?;
//!
//! // Print SARIF output for GitHub/GitLab integration
//! println!("{}", report.to_sarif_json()?);
//!
//! // Check if scan found critical issues
//! let exit_code = report.exit_code(Severity::High);
//! ```
//!
//! # Individual Analyzers
//!
//! Each analyzer can also be used independently:
//!
//! ## SQL Injection Detection
//!
//! ```ignore
//! use go_brrr::security::injection::sql::SqlInjectionDetector;
//!
//! let detector = SqlInjectionDetector::new();
//! let findings = detector.scan_file("./src/app.py")?;
//! ```
//!
//! ## Command Injection Detection
//!
//! ```ignore
//! use go_brrr::security::injection::command::scan_command_injection;
//!
//! let findings = scan_command_injection("./src", None)?;
//! ```
//!
//! ## Secrets Detection
//!
//! ```ignore
//! use go_brrr::security::secrets::scan_secrets;
//!
//! let result = scan_secrets("./src", None)?;
//! ```
//!
//! # Output Formats
//!
//! - **JSON**: Standard JSON output for programmatic consumption
//! - **SARIF**: Static Analysis Results Interchange Format for CI/CD integration
//! - **Text**: Human-readable output for terminal display
//!
//! # Suppression
//!
//! Findings can be suppressed via inline comments:
//!
//! ```python
//! # brrr-ignore: SQLI-001
//! cursor.execute(f"SELECT * FROM users WHERE id = {user_id}")
//! ```
//!
//! Supported comment formats:
//! - `# brrr-ignore: <ID>` or `// brrr-ignore: <ID>`
//! - `# nosec <ID>`
//! - `# noqa: <ID>`
//! - `# security-ignore: <ID>`

pub mod common;
pub mod crypto;
pub mod deserialization;
pub mod injection;
pub mod input_validation;
pub mod prototype_pollution;
pub mod redos;
pub mod sarif;
pub mod secrets;
pub mod ssrf;
pub mod taint;
pub mod types;

// Re-export unified types
pub use types::{
    check_suppression, is_suppressed, Confidence, InjectionType, Location, ScanSummary,
    SecurityCategory, SecurityConfig, SecurityFinding, SecurityReport, Severity,
};

// Re-export common types for injection modules
pub use common::SourceLocation;

// Re-export individual analyzers for direct access

use std::collections::HashSet;
use std::path::Path;
use std::time::Instant;

use rayon::prelude::*;

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};

// =============================================================================
// Unified Security Scan
// =============================================================================

/// Run all security analyzers on a path and return a unified report.
///
/// This function runs all enabled analyzers in parallel, deduplicates findings,
/// applies suppression rules, and returns a consolidated security report.
///
/// # Arguments
///
/// * `path` - Path to scan (file or directory)
/// * `config` - Security configuration (severity filters, categories, etc.)
///
/// # Returns
///
/// A `SecurityReport` containing all findings and summary statistics.
///
/// # Errors
///
/// Returns an error if the path doesn't exist or scanning fails critically.
///
/// # Example
///
/// ```ignore
/// use go_brrr::security::{scan_security, SecurityConfig};
///
/// let report = scan_security("./src", &SecurityConfig::default())?;
/// println!("Found {} issues", report.summary.total_findings);
///
/// // For CI/CD with stricter settings
/// let ci_report = scan_security("./src", &SecurityConfig::ci())?;
/// std::process::exit(ci_report.exit_code(Severity::High));
/// ```
pub fn scan_security(path: impl AsRef<Path>, config: &SecurityConfig) -> Result<SecurityReport> {
    let path = path.as_ref();
    let start_time = Instant::now();

    // Collect all source files
    let files = collect_source_files(path, config)?;
    let files_scanned = files.len();

    // Run all analyzers in parallel
    let mut all_findings: Vec<SecurityFinding> = Vec::new();

    // Use parallel processing if we have multiple files
    if files.len() > 1 {
        // Build a vector of boxed closures for parallel execution
        type ScannerFn<'a> = Box<dyn Fn() -> Vec<SecurityFinding> + Send + Sync + 'a>;
        let scanners: Vec<ScannerFn> = vec![
            Box::new(|| run_sql_injection_scan(path, config)),
            Box::new(|| run_command_injection_scan(path, config)),
            Box::new(|| run_xss_scan(path, config)),
            Box::new(|| run_path_traversal_scan(path, config)),
            Box::new(|| run_secrets_scan(path, config)),
            Box::new(|| run_crypto_scan(path, config)),
            Box::new(|| run_deserialization_scan(path, config)),
            Box::new(|| run_redos_scan(path, config)),
            Box::new(|| run_log_injection_scan(path, config)),
            Box::new(|| run_header_injection_scan(path, config)),
            Box::new(|| run_template_injection_scan(path, config)),
        ];

        let findings_per_analyzer: Vec<Vec<SecurityFinding>> =
            scanners.par_iter().map(|scanner| scanner()).collect();

        for findings in findings_per_analyzer {
            all_findings.extend(findings);
        }
    } else if !files.is_empty() {
        // Single file - run analyzers sequentially
        all_findings.extend(run_sql_injection_scan(path, config));
        all_findings.extend(run_command_injection_scan(path, config));
        all_findings.extend(run_xss_scan(path, config));
        all_findings.extend(run_path_traversal_scan(path, config));
        all_findings.extend(run_secrets_scan(path, config));
        all_findings.extend(run_crypto_scan(path, config));
        all_findings.extend(run_deserialization_scan(path, config));
        all_findings.extend(run_redos_scan(path, config));
        all_findings.extend(run_log_injection_scan(path, config));
        all_findings.extend(run_header_injection_scan(path, config));
        all_findings.extend(run_template_injection_scan(path, config));
    }

    // Apply suppression detection by reading source files
    apply_suppressions(&mut all_findings);

    // Filter findings based on config
    let filtered_findings: Vec<SecurityFinding> = all_findings
        .into_iter()
        .filter(|f| config.should_include(f))
        .collect();

    // Deduplicate findings
    let (findings, duplicates_removed) = if config.deduplicate {
        deduplicate_findings(filtered_findings)
    } else {
        (filtered_findings, 0)
    };

    // Build report
    let mut report = SecurityReport::new(findings, files_scanned);
    report.summary.duplicates_removed = duplicates_removed;
    report.summary.scan_duration_ms = start_time.elapsed().as_millis() as u64;
    report.config = Some(config.clone());

    Ok(report)
}

/// Collect source files to scan based on config.
fn collect_source_files(path: &Path, config: &SecurityConfig) -> Result<Vec<std::path::PathBuf>> {
    if path.is_file() {
        return Ok(vec![path.to_path_buf()]);
    }

    let path_str = path
        .to_str()
        .ok_or_else(|| BrrrError::InvalidArgument("Invalid path encoding".to_string()))?;

    let scan_config = match &config.language {
        Some(lang) => ScanConfig::for_language(lang),
        None => ScanConfig::default(),
    };

    let scanner = ProjectScanner::new(path_str)?;
    let result = scanner.scan_with_config(&scan_config)?;

    // Limit files if max_files is specified
    let files = if config.max_files > 0 && result.files.len() > config.max_files {
        result.files.into_iter().take(config.max_files).collect()
    } else {
        result.files
    };

    Ok(files)
}

/// Apply suppression detection to findings by checking source file comments.
fn apply_suppressions(findings: &mut [SecurityFinding]) {
    // Group findings by file to minimize file reads
    let mut files_to_check: HashSet<String> = HashSet::new();
    for finding in findings.iter() {
        files_to_check.insert(finding.location.file.clone());
    }

    // Read each file once and check suppressions
    for file_path in files_to_check {
        let source = match std::fs::read_to_string(&file_path) {
            Ok(s) => s,
            Err(_) => continue,
        };

        for finding in findings.iter_mut() {
            if finding.location.file == file_path && !finding.suppressed {
                if check_suppression(&source, finding.location.start_line, &finding.id) {
                    finding.suppressed = true;
                }
            }
        }
    }
}

/// Deduplicate findings based on location and category.
/// Returns the deduplicated list and count of removed duplicates.
fn deduplicate_findings(findings: Vec<SecurityFinding>) -> (Vec<SecurityFinding>, usize) {
    let original_count = findings.len();
    let mut seen: HashSet<u64> = HashSet::new();
    let mut result: Vec<SecurityFinding> = Vec::new();

    for finding in findings {
        if seen.insert(finding.dedup_hash) {
            result.push(finding);
        }
    }

    let duplicates_removed = original_count - result.len();
    (result, duplicates_removed)
}

// =============================================================================
// Individual Scanner Wrappers
// =============================================================================

/// Run SQL injection scanner and convert to unified findings.
fn run_sql_injection_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    // Check if SQL injection is in the category filter
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("sql")
                || c.to_lowercase().contains("injection")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let detector = injection::sql::SqlInjectionDetector::new();
    let lang_str = config.language.as_deref();

    let result = if path.is_file() {
        match detector.scan_file(path.to_string_lossy().as_ref()) {
            Ok(findings) => findings,
            Err(_) => return Vec::new(),
        }
    } else {
        match detector.scan_directory(path.to_string_lossy().as_ref(), lang_str) {
            Ok(result) => result.findings,
            Err(_) => return Vec::new(),
        }
    };

    result
        .into_iter()
        .map(|f| {
            SecurityFinding::new(
                format!("SQLI-{:03}", severity_to_id(&f.severity.to_string())),
                SecurityCategory::Injection(InjectionType::Sql),
                convert_sql_severity(f.severity),
                Confidence::from_float(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!("SQL Injection via {}", f.pattern),
                f.description,
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.code_snippet)
            .with_metadata("sink_function", f.sink_function.to_string())
            .with_metadata("pattern", f.pattern.to_string())
        })
        .collect()
}

/// Run command injection scanner and convert to unified findings.
fn run_command_injection_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("command")
                || c.to_lowercase().contains("injection")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let lang_str = config.language.as_deref();

    let result = if path.is_file() {
        match injection::command::scan_file_command_injection(path, lang_str) {
            Ok(findings) => findings,
            Err(_) => return Vec::new(),
        }
    } else {
        match injection::command::scan_command_injection(path, lang_str) {
            Ok(findings) => findings,
            Err(_) => return Vec::new(),
        }
    };

    result
        .into_iter()
        .map(|f| {
            let description = format!(
                "{} via {} - tainted input: {}",
                f.kind, f.sink_function, f.tainted_input
            );
            SecurityFinding::new(
                format!("CMD-{:03}", severity_to_id(&f.severity.to_string())),
                SecurityCategory::Injection(InjectionType::Command),
                convert_cmd_severity(f.severity),
                convert_cmd_confidence(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!("Command Injection via {}", f.sink_function),
                description,
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.code_snippet.unwrap_or_default())
            .with_metadata("sink_function", f.sink_function.clone())
            .with_metadata("kind", f.kind.to_string())
        })
        .collect()
}

/// Run XSS scanner and convert to unified findings.
fn run_xss_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("xss")
                || c.to_lowercase().contains("injection")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let lang_str = config.language.as_deref();

    let result = if path.is_file() {
        match injection::xss::scan_file_xss(path) {
            Ok(findings) => findings,
            Err(_) => return Vec::new(),
        }
    } else {
        match injection::xss::scan_xss(path, lang_str) {
            Ok(scan_result) => scan_result.findings,
            Err(_) => return Vec::new(),
        }
    };

    result
        .into_iter()
        .map(|f| {
            SecurityFinding::new(
                format!("XSS-{:03}", severity_to_id(&f.severity.to_string())),
                SecurityCategory::Injection(InjectionType::Xss),
                convert_xss_severity(f.severity),
                convert_xss_confidence(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!("Cross-Site Scripting via {}", f.sink_type),
                f.description,
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.code_snippet.unwrap_or_default())
            .with_metadata("sink_type", f.sink_type.to_string())
        })
        .collect()
}

/// Run path traversal scanner and convert to unified findings.
fn run_path_traversal_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("path")
                || c.to_lowercase().contains("traversal")
                || c.to_lowercase().contains("injection")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let lang_str = config.language.as_deref();

    let result = if path.is_file() {
        match injection::path_traversal::scan_file_path_traversal(path, lang_str) {
            Ok(findings) => findings,
            Err(_) => return Vec::new(),
        }
    } else {
        match injection::path_traversal::scan_path_traversal(path, lang_str) {
            Ok(findings) => findings,
            Err(_) => return Vec::new(),
        }
    };

    result
        .into_iter()
        .map(|f| {
            SecurityFinding::new(
                format!("PATH-{:03}", severity_to_id(&f.severity.to_string())),
                SecurityCategory::Injection(InjectionType::PathTraversal),
                convert_path_severity(f.severity),
                convert_path_confidence(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!("Path Traversal via {}", f.pattern),
                f.description,
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.code_snippet.unwrap_or_default())
            .with_metadata("operation_type", f.operation_type.to_string())
            .with_metadata("pattern", f.pattern.to_string())
        })
        .collect()
}

/// Run secrets scanner and convert to unified findings.
fn run_secrets_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("secret")
                || c.to_lowercase().contains("credential")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let lang_str = config.language.as_deref();

    let result = match secrets::scan_secrets(path.to_string_lossy().as_ref(), lang_str) {
        Ok(result) => result.findings,
        Err(_) => return Vec::new(),
    };

    result
        .into_iter()
        .map(|f| {
            SecurityFinding::new(
                format!("SEC-{:03}", severity_to_id(&f.severity.to_string())),
                SecurityCategory::SecretsExposure,
                convert_secrets_severity(f.severity),
                convert_secrets_confidence(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!("{} Exposed", f.secret_type),
                f.description,
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.masked_value.clone())
            .with_metadata("secret_type", f.secret_type.to_string())
            .with_metadata("masked_value", f.masked_value)
        })
        .collect()
}

/// Run crypto scanner and convert to unified findings.
fn run_crypto_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("crypto")
                || c.to_lowercase().contains("encryption")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let lang_str = config.language.as_deref();

    let result = if path.is_file() {
        match crypto::scan_file_weak_crypto(path, lang_str) {
            Ok(findings) => findings,
            Err(_) => return Vec::new(),
        }
    } else {
        match crypto::scan_weak_crypto(path.to_string_lossy().as_ref(), lang_str) {
            Ok(result) => result.findings,
            Err(_) => return Vec::new(),
        }
    };

    result
        .into_iter()
        .map(|f| {
            SecurityFinding::new(
                format!("CRYPTO-{:03}", severity_to_id(&f.severity.to_string())),
                SecurityCategory::WeakCrypto,
                convert_crypto_severity(f.severity),
                convert_crypto_confidence(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!("{}: {}", f.issue_type, f.algorithm),
                f.description,
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.code_snippet)
            .with_metadata("algorithm", f.algorithm.to_string())
            .with_metadata("issue_type", f.issue_type.to_string())
        })
        .collect()
}

/// Run deserialization scanner and convert to unified findings.
fn run_deserialization_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("deser")
                || c.to_lowercase().contains("pickle")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let lang_str = config.language.as_deref();

    let result = match deserialization::scan_deserialization(path, lang_str) {
        Ok(findings) => findings,
        Err(_) => return Vec::new(),
    };

    result
        .into_iter()
        .map(|f| {
            SecurityFinding::new(
                format!("DESER-{:03}", severity_to_id(&f.severity.to_string())),
                SecurityCategory::UnsafeDeserialization,
                convert_deser_severity(f.severity),
                convert_deser_confidence(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!("Unsafe Deserialization via {}", f.method),
                f.description,
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.code_snippet.unwrap_or_default())
            .with_metadata("method", f.method.to_string())
            .with_metadata("input_source", f.input_source.to_string())
        })
        .collect()
}

/// Run ReDoS scanner and convert to unified findings.
fn run_redos_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("redos")
                || c.to_lowercase().contains("regex")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let lang_str = config.language.as_deref();

    let result = match redos::scan_redos(path.to_string_lossy().as_ref(), lang_str) {
        Ok(result) => result.findings,
        Err(_) => return Vec::new(),
    };

    result
        .into_iter()
        .map(|f| {
            SecurityFinding::new(
                format!("REDOS-{:03}", severity_to_id(&f.severity.to_string())),
                SecurityCategory::ReDoS,
                convert_redos_severity(f.severity),
                convert_redos_confidence(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!("ReDoS: {} in {}", f.vulnerability_type, f.regex_function),
                f.description,
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.code_snippet)
            .with_metadata("regex_pattern", f.regex_pattern)
            .with_metadata("complexity", f.complexity)
            .with_metadata("attack_string", f.attack_string)
            .with_metadata("vulnerability_type", f.vulnerability_type.to_string())
        })
        .collect()
}

/// Run log injection scanner and convert to unified findings.
fn run_log_injection_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("log")
                || c.to_lowercase().contains("injection")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let lang_str = config.language.as_deref();

    let result = if path.is_file() {
        match injection::log_injection::scan_file_log_injection(path, lang_str) {
            Ok(findings) => findings,
            Err(_) => return Vec::new(),
        }
    } else {
        match injection::log_injection::scan_log_injection(path, lang_str) {
            Ok(result) => result.findings,
            Err(_) => return Vec::new(),
        }
    };

    result
        .into_iter()
        .map(|f| {
            let category = SecurityCategory::Other("Log Injection".to_string());
            SecurityFinding::new(
                format!("LOG-{:03}", severity_to_id(&f.severity.to_string())),
                category,
                convert_log_severity(f.severity),
                convert_log_confidence(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!("Log Injection: {} in {}", f.injection_type, f.log_function),
                format!(
                    "Tainted data '{}' reaches logging sink without sanitization",
                    f.tainted_data
                ),
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.code_snippet.unwrap_or_default())
            .with_cwe(f.cwe_id)
            .with_metadata("log_function", f.log_function)
            .with_metadata("injection_type", f.injection_type.to_string())
            .with_metadata(
                "uses_structured_logging",
                f.uses_structured_logging.to_string(),
            )
        })
        .collect()
}

/// Run header injection scanner and convert to unified findings.
fn run_header_injection_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("header")
                || c.to_lowercase().contains("injection")
                || c.to_lowercase().contains("redirect")
                || c.to_lowercase().contains("cookie")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let lang_str = config.language.as_deref();

    let result = if path.is_file() {
        match injection::header_injection::scan_file_header_injection(path, lang_str) {
            Ok(findings) => findings,
            Err(_) => return Vec::new(),
        }
    } else {
        match injection::header_injection::scan_header_injection(path, lang_str) {
            Ok(result) => result.findings,
            Err(_) => return Vec::new(),
        }
    };

    result
        .into_iter()
        .map(|f| {
            let category = SecurityCategory::Other("Header Injection".to_string());
            SecurityFinding::new(
                format!("HDR-{:03}", severity_to_id(&f.severity.to_string())),
                category,
                convert_header_severity(f.severity),
                convert_header_confidence(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!(
                    "Header Injection: {} in {}",
                    f.injection_type, f.sink_function
                ),
                format!(
                    "Tainted value '{}' in header '{}' - {}",
                    f.tainted_value,
                    f.header_name,
                    f.injection_type.description()
                ),
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.code_snippet.unwrap_or_default())
            .with_cwe(f.cwe_id)
            .with_metadata("sink_function", f.sink_function)
            .with_metadata("header_name", f.header_name)
            .with_metadata("injection_type", f.injection_type.to_string())
            .with_metadata("framework_protected", f.framework_protected.to_string())
            .with_metadata("encoded_crlf_detected", f.encoded_crlf_detected.to_string())
        })
        .collect()
}

/// Run template injection (SSTI) scanner and convert to unified findings.
fn run_template_injection_scan(path: &Path, config: &SecurityConfig) -> Vec<SecurityFinding> {
    if let Some(ref cats) = config.categories {
        if !cats.iter().any(|c| {
            c.to_lowercase().contains("template")
                || c.to_lowercase().contains("ssti")
                || c.to_lowercase().contains("injection")
                || c.to_lowercase() == "all"
        }) {
            return Vec::new();
        }
    }

    let lang_str = config.language.as_deref();

    let result = if path.is_file() {
        match injection::template_injection::scan_file_template_injection(path, lang_str) {
            Ok(result) => result.findings,
            Err(_) => return Vec::new(),
        }
    } else {
        match injection::template_injection::scan_template_injection(path, lang_str) {
            Ok(result) => result.findings,
            Err(_) => return Vec::new(),
        }
    };

    result
        .into_iter()
        .map(|f| {
            let category = SecurityCategory::Injection(InjectionType::Template);
            SecurityFinding::new(
                format!("SSTI-{:03}", severity_to_id(&f.severity.to_string())),
                category,
                convert_template_severity(f.severity),
                convert_template_confidence(f.confidence),
                Location::new(
                    &f.location.file,
                    f.location.line,
                    f.location.column,
                    f.location.end_line,
                    f.location.end_column,
                ),
                format!(
                    "Template Injection ({}) via {}",
                    f.template_engine, f.sink_function
                ),
                f.description.clone(),
            )
            .with_remediation(f.remediation)
            .with_code_snippet(f.code_snippet.unwrap_or_default())
            .with_cwe(f.cwe_id)
            .with_metadata("template_engine", f.template_engine.to_string())
            .with_metadata("injection_type", f.injection_type.to_string())
            .with_metadata("sink_function", f.sink_function)
            .with_metadata("tainted_template", f.tainted_template)
            .with_metadata("tainted_variables", f.tainted_variables.join(", "))
        })
        .collect()
}

// =============================================================================
// Severity/Confidence Conversion Helpers
// =============================================================================

fn severity_to_id(sev: &str) -> u32 {
    match sev.to_uppercase().as_str() {
        "CRITICAL" => 001,
        "HIGH" => 002,
        "MEDIUM" => 003,
        "LOW" => 004,
        _ => 005,
    }
}

fn convert_sql_severity(sev: injection::sql::Severity) -> Severity {
    match sev {
        injection::sql::Severity::Critical => Severity::Critical,
        injection::sql::Severity::High => Severity::High,
        injection::sql::Severity::Medium => Severity::Medium,
        injection::sql::Severity::Low => Severity::Low,
    }
}

fn convert_cmd_severity(sev: injection::command::Severity) -> Severity {
    match sev {
        injection::command::Severity::Critical => Severity::Critical,
        injection::command::Severity::High => Severity::High,
        injection::command::Severity::Medium => Severity::Medium,
        injection::command::Severity::Low => Severity::Low,
        injection::command::Severity::Info => Severity::Info,
    }
}

fn convert_cmd_confidence(conf: injection::command::Confidence) -> Confidence {
    match conf {
        injection::command::Confidence::High => Confidence::High,
        injection::command::Confidence::Medium => Confidence::Medium,
        injection::command::Confidence::Low => Confidence::Low,
    }
}

fn convert_xss_severity(sev: injection::xss::Severity) -> Severity {
    match sev {
        injection::xss::Severity::Critical => Severity::Critical,
        injection::xss::Severity::High => Severity::High,
        injection::xss::Severity::Medium => Severity::Medium,
        injection::xss::Severity::Low => Severity::Low,
        injection::xss::Severity::Info => Severity::Info,
    }
}

fn convert_xss_confidence(conf: injection::xss::Confidence) -> Confidence {
    match conf {
        injection::xss::Confidence::High => Confidence::High,
        injection::xss::Confidence::Medium => Confidence::Medium,
        injection::xss::Confidence::Low => Confidence::Low,
    }
}

fn convert_path_severity(sev: injection::path_traversal::Severity) -> Severity {
    match sev {
        injection::path_traversal::Severity::Critical => Severity::Critical,
        injection::path_traversal::Severity::High => Severity::High,
        injection::path_traversal::Severity::Medium => Severity::Medium,
        injection::path_traversal::Severity::Low => Severity::Low,
        injection::path_traversal::Severity::Info => Severity::Info,
    }
}

fn convert_path_confidence(conf: injection::path_traversal::Confidence) -> Confidence {
    match conf {
        injection::path_traversal::Confidence::High => Confidence::High,
        injection::path_traversal::Confidence::Medium => Confidence::Medium,
        injection::path_traversal::Confidence::Low => Confidence::Low,
    }
}

fn convert_secrets_severity(sev: secrets::Severity) -> Severity {
    match sev {
        secrets::Severity::Critical => Severity::Critical,
        secrets::Severity::High => Severity::High,
        secrets::Severity::Medium => Severity::Medium,
        secrets::Severity::Low => Severity::Low,
        secrets::Severity::Info => Severity::Info,
    }
}

fn convert_secrets_confidence(conf: secrets::Confidence) -> Confidence {
    match conf {
        secrets::Confidence::High => Confidence::High,
        secrets::Confidence::Medium => Confidence::Medium,
        secrets::Confidence::Low => Confidence::Low,
    }
}

fn convert_crypto_severity(sev: crypto::Severity) -> Severity {
    match sev {
        crypto::Severity::Critical => Severity::Critical,
        crypto::Severity::High => Severity::High,
        crypto::Severity::Medium => Severity::Medium,
        crypto::Severity::Low => Severity::Low,
        crypto::Severity::Info => Severity::Info,
    }
}

fn convert_crypto_confidence(conf: crypto::Confidence) -> Confidence {
    match conf {
        crypto::Confidence::High => Confidence::High,
        crypto::Confidence::Medium => Confidence::Medium,
        crypto::Confidence::Low => Confidence::Low,
    }
}

fn convert_deser_severity(sev: deserialization::Severity) -> Severity {
    match sev {
        deserialization::Severity::Critical => Severity::Critical,
        deserialization::Severity::High => Severity::High,
        deserialization::Severity::Medium => Severity::Medium,
        deserialization::Severity::Low => Severity::Low,
        deserialization::Severity::Info => Severity::Info,
    }
}

fn convert_deser_confidence(conf: deserialization::Confidence) -> Confidence {
    match conf {
        deserialization::Confidence::High => Confidence::High,
        deserialization::Confidence::Medium => Confidence::Medium,
        deserialization::Confidence::Low => Confidence::Low,
    }
}

fn convert_redos_severity(sev: redos::Severity) -> Severity {
    match sev {
        redos::Severity::Critical => Severity::Critical,
        redos::Severity::High => Severity::High,
        redos::Severity::Medium => Severity::Medium,
        redos::Severity::Low => Severity::Low,
        redos::Severity::Info => Severity::Info,
    }
}

fn convert_redos_confidence(conf: redos::Confidence) -> Confidence {
    match conf {
        redos::Confidence::High => Confidence::High,
        redos::Confidence::Medium => Confidence::Medium,
        redos::Confidence::Low => Confidence::Low,
    }
}

fn convert_log_severity(sev: injection::log_injection::Severity) -> Severity {
    match sev {
        injection::log_injection::Severity::Critical => Severity::Critical,
        injection::log_injection::Severity::High => Severity::High,
        injection::log_injection::Severity::Medium => Severity::Medium,
        injection::log_injection::Severity::Low => Severity::Low,
        injection::log_injection::Severity::Info => Severity::Info,
    }
}

fn convert_log_confidence(conf: injection::log_injection::Confidence) -> Confidence {
    match conf {
        injection::log_injection::Confidence::High => Confidence::High,
        injection::log_injection::Confidence::Medium => Confidence::Medium,
        injection::log_injection::Confidence::Low => Confidence::Low,
    }
}

fn convert_header_severity(sev: injection::header_injection::Severity) -> Severity {
    match sev {
        injection::header_injection::Severity::Critical => Severity::Critical,
        injection::header_injection::Severity::High => Severity::High,
        injection::header_injection::Severity::Medium => Severity::Medium,
        injection::header_injection::Severity::Low => Severity::Low,
        injection::header_injection::Severity::Info => Severity::Info,
    }
}

fn convert_header_confidence(conf: injection::header_injection::Confidence) -> Confidence {
    match conf {
        injection::header_injection::Confidence::High => Confidence::High,
        injection::header_injection::Confidence::Medium => Confidence::Medium,
        injection::header_injection::Confidence::Low => Confidence::Low,
    }
}

fn convert_template_severity(sev: injection::template_injection::Severity) -> Severity {
    match sev {
        injection::template_injection::Severity::Critical => Severity::Critical,
        injection::template_injection::Severity::High => Severity::High,
        injection::template_injection::Severity::Medium => Severity::Medium,
        injection::template_injection::Severity::Low => Severity::Low,
        injection::template_injection::Severity::Info => Severity::Info,
    }
}

fn convert_template_confidence(conf: injection::template_injection::Confidence) -> Confidence {
    match conf {
        injection::template_injection::Confidence::High => Confidence::High,
        injection::template_injection::Confidence::Medium => Confidence::Medium,
        injection::template_injection::Confidence::Low => Confidence::Low,
    }
}

impl Confidence {
    /// Convert a float confidence score to Confidence level.
    fn from_float(score: f64) -> Self {
        if score >= 0.8 {
            Self::High
        } else if score >= 0.5 {
            Self::Medium
        } else {
            Self::Low
        }
    }
}

// =============================================================================
// Text Formatting
// =============================================================================

impl SecurityReport {
    /// Format the report as human-readable text.
    #[must_use]
    pub fn to_text(&self) -> String {
        let mut output = String::new();

        // Header
        output.push_str("=== Security Scan Report ===\n\n");
        output.push_str(&format!(
            "Scanned {} files in {}ms\n",
            self.summary.files_scanned, self.summary.scan_duration_ms
        ));
        output.push_str(&format!(
            "Found {} issues ({} suppressed, {} duplicates removed)\n\n",
            self.summary.total_findings,
            self.summary.suppressed_count,
            self.summary.duplicates_removed
        ));

        // Summary by severity
        if !self.summary.by_severity.is_empty() {
            output.push_str("By Severity:\n");
            for (sev, count) in &self.summary.by_severity {
                output.push_str(&format!("  {}: {}\n", sev, count));
            }
            output.push('\n');
        }

        // Summary by category
        if !self.summary.by_category.is_empty() {
            output.push_str("By Category:\n");
            for (cat, count) in &self.summary.by_category {
                output.push_str(&format!("  {}: {}\n", cat, count));
            }
            output.push('\n');
        }

        // Findings
        if !self.findings.is_empty() {
            output.push_str("=== Findings ===\n\n");

            for (i, finding) in self.findings.iter().enumerate() {
                let suppressed_marker = if finding.suppressed {
                    " [SUPPRESSED]"
                } else {
                    ""
                };

                output.push_str(&format!(
                    "{}. [{}] {} - {}{}\n",
                    i + 1,
                    finding.severity,
                    finding.id,
                    finding.title,
                    suppressed_marker
                ));
                output.push_str(&format!("   Location: {}\n", finding.location));
                output.push_str(&format!("   Confidence: {}\n", finding.confidence));

                if let Some(cwe) = finding.cwe_id {
                    output.push_str(&format!("   CWE: CWE-{}\n", cwe));
                }

                output.push_str(&format!("   Description: {}\n", finding.description));

                if !finding.code_snippet.is_empty() {
                    output.push_str("   Code:\n");
                    for line in finding.code_snippet.lines() {
                        output.push_str(&format!("     | {}\n", line));
                    }
                }

                if !finding.remediation.is_empty() {
                    output.push_str(&format!("   Fix: {}\n", finding.remediation));
                }

                output.push('\n');
            }
        }

        output
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_security_config_defaults() {
        let config = SecurityConfig::default();
        assert_eq!(config.min_severity, Severity::Low);
        assert_eq!(config.min_confidence, Confidence::Low);
        assert!(config.deduplicate);
    }

    #[test]
    fn test_ci_config() {
        let config = SecurityConfig::ci();
        assert_eq!(config.min_severity, Severity::Medium);
        assert_eq!(config.min_confidence, Confidence::Medium);
    }

    #[test]
    fn test_finding_filtering() {
        let config = SecurityConfig::default().with_min_severity(Severity::High);

        let low_finding = SecurityFinding::new(
            "TEST-001",
            SecurityCategory::SecretsExposure,
            Severity::Low,
            Confidence::High,
            Location::new("test.py", 1, 1, 1, 10),
            "Test",
            "Test finding",
        );

        let high_finding = SecurityFinding::new(
            "TEST-002",
            SecurityCategory::SecretsExposure,
            Severity::High,
            Confidence::High,
            Location::new("test.py", 2, 1, 2, 10),
            "Test",
            "Test finding",
        );

        assert!(!config.should_include(&low_finding));
        assert!(config.should_include(&high_finding));
    }

    #[test]
    fn test_deduplication() {
        let finding1 = SecurityFinding::new(
            "TEST-001",
            SecurityCategory::SecretsExposure,
            Severity::High,
            Confidence::High,
            Location::new("test.py", 10, 1, 10, 50),
            "Test",
            "Test finding",
        );

        // Same location = same dedup_hash
        let finding2 = SecurityFinding::new(
            "TEST-001",
            SecurityCategory::SecretsExposure,
            Severity::High,
            Confidence::High,
            Location::new("test.py", 10, 1, 10, 50),
            "Test",
            "Test finding",
        );

        let findings = vec![finding1, finding2];
        let (deduped, removed) = deduplicate_findings(findings);

        assert_eq!(deduped.len(), 1);
        assert_eq!(removed, 1);
    }
}
