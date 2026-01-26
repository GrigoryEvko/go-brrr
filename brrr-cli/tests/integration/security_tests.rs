//! Security analysis integration tests.
//!
//! Tests vulnerability detection across multiple vulnerability types.

use std::path::PathBuf;

use brrr::security::{
    scan_command_injection, scan_deserialization, scan_path_traversal, scan_redos, scan_secrets,
    scan_security, scan_weak_crypto, scan_xss, SecurityConfig, Severity, SqlInjectionDetector,
};

/// Get the path to test fixtures.
fn fixtures_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("security")
}

// =============================================================================
// SQL Injection Tests
// =============================================================================

#[test]
fn test_sql_injection_detection() {
    let fixture = fixtures_path().join("sql_injection.py");
    let detector = SqlInjectionDetector::new();

    let result = detector.scan_file(fixture.to_str().unwrap());
    assert!(result.is_ok(), "SQL injection scan should succeed");

    let findings = result.unwrap();

    // Should detect vulnerable patterns
    assert!(
        !findings.is_empty(),
        "Should detect SQL injection vulnerabilities"
    );
}

#[test]
fn test_sql_injection_no_false_positives() {
    let fixture = fixtures_path().join("safe_code.py");
    let detector = SqlInjectionDetector::new();

    let result = detector.scan_file(fixture.to_str().unwrap());
    assert!(result.is_ok());

    let findings = result.unwrap();

    // Should not flag safe parameterized queries as high confidence
    let high_confidence_count = findings.iter().filter(|f| f.confidence >= 0.8).count();

    assert!(
        high_confidence_count == 0,
        "Should not have high-confidence findings on safe code"
    );
}

// =============================================================================
// Command Injection Tests
// =============================================================================

#[test]
fn test_command_injection_detection() {
    let fixture = fixtures_path().join("command_injection.py");

    let result = scan_command_injection(&fixture, Some("python"));
    assert!(result.is_ok(), "Command injection scan should succeed");

    let findings = result.unwrap();

    // Should detect vulnerable patterns
    assert!(
        !findings.is_empty(),
        "Should detect command injection vulnerabilities"
    );
}

// =============================================================================
// XSS Tests
// =============================================================================

#[test]
fn test_xss_detection() {
    let fixture = fixtures_path().join("xss.ts");

    let result = scan_xss(&fixture, Some("typescript"));
    assert!(result.is_ok(), "XSS scan should succeed: {:?}", result);

    let scan_result = result.unwrap();

    // Should detect vulnerable patterns
    assert!(
        !scan_result.findings.is_empty(),
        "Should detect XSS vulnerabilities"
    );
}

// =============================================================================
// Path Traversal Tests
// =============================================================================

#[test]
fn test_path_traversal_detection() {
    let fixture = fixtures_path().join("path_traversal.py");

    let result = scan_path_traversal(&fixture, Some("python"));
    assert!(result.is_ok(), "Path traversal scan should succeed");

    let findings = result.unwrap();

    // Should detect vulnerable patterns
    assert!(
        !findings.is_empty(),
        "Should detect path traversal vulnerabilities"
    );
}

// =============================================================================
// Secrets Detection Tests
// =============================================================================

#[test]
fn test_secrets_detection() {
    let fixture = fixtures_path().join("secrets.py");

    let result = scan_secrets(fixture.to_str().unwrap(), Some("python"));
    assert!(result.is_ok(), "Secrets scan should succeed");

    let scan_result = result.unwrap();

    // Should detect hardcoded secrets
    assert!(
        !scan_result.findings.is_empty(),
        "Should detect hardcoded secrets"
    );
}

// =============================================================================
// Weak Cryptography Tests
// =============================================================================

#[test]
fn test_weak_crypto_detection() {
    let fixture = fixtures_path().join("weak_crypto.py");

    let result = scan_weak_crypto(fixture.to_str().unwrap(), Some("python"));
    assert!(result.is_ok(), "Weak crypto scan should succeed");

    let scan_result = result.unwrap();

    // Should detect weak algorithms
    assert!(
        !scan_result.findings.is_empty(),
        "Should detect weak crypto usages"
    );
}

// =============================================================================
// Unsafe Deserialization Tests
// =============================================================================

#[test]
fn test_deserialization_detection() {
    let fixture = fixtures_path().join("deserialization.py");

    let result = scan_deserialization(&fixture, Some("python"));
    assert!(result.is_ok(), "Deserialization scan should succeed");

    let findings = result.unwrap();

    // Should detect unsafe deserialization
    assert!(
        !findings.is_empty(),
        "Should detect unsafe deserialization patterns"
    );
}

// =============================================================================
// ReDoS Tests
// =============================================================================

#[test]
fn test_redos_detection() {
    let fixture = fixtures_path().join("redos.py");

    let result = scan_redos(fixture.to_str().unwrap(), Some("python"));
    assert!(result.is_ok(), "ReDoS scan should succeed");

    let scan_result = result.unwrap();

    // Should detect vulnerable regex patterns
    assert!(
        !scan_result.findings.is_empty(),
        "Should detect ReDoS vulnerabilities"
    );
}

// =============================================================================
// Unified Security Scan Tests
// =============================================================================

#[test]
fn test_unified_security_scan() {
    let fixtures_dir = fixtures_path();

    let config = SecurityConfig::default();
    let result = scan_security(&fixtures_dir, &config);

    assert!(result.is_ok(), "Unified security scan should succeed");

    let report = result.unwrap();

    // Should find vulnerabilities
    assert!(
        report.summary.total_findings > 0,
        "Should detect findings in fixture files"
    );

    // Should have breakdown by severity
    assert!(
        !report.summary.by_severity.is_empty(),
        "Should have severity breakdown"
    );
}

#[test]
fn test_unified_scan_with_severity_filter() {
    let fixtures_dir = fixtures_path();

    // Only high and critical severity
    let config = SecurityConfig::default().with_min_severity(Severity::High);
    let result = scan_security(&fixtures_dir, &config);

    assert!(result.is_ok());

    let report = result.unwrap();

    // All findings should be high or critical
    for finding in &report.findings {
        assert!(
            matches!(finding.severity, Severity::High | Severity::Critical),
            "All findings should be High or Critical severity"
        );
    }
}

#[test]
fn test_sarif_output() {
    let fixtures_dir = fixtures_path();

    let config = SecurityConfig::default();
    let result = scan_security(&fixtures_dir, &config);

    assert!(result.is_ok());

    let report = result.unwrap();

    // Should be able to generate SARIF output
    let sarif_result = report.to_sarif_json();
    assert!(sarif_result.is_ok(), "SARIF generation should succeed");

    let sarif_json = sarif_result.unwrap();

    // Validate SARIF structure
    assert!(
        sarif_json.contains("\"$schema\"") || sarif_json.contains("\"version\""),
        "SARIF should have schema or version"
    );
}

// =============================================================================
// Performance Tests
// =============================================================================

#[test]
fn test_security_scan_performance() {
    use std::time::Instant;

    let fixtures_dir = fixtures_path();

    let config = SecurityConfig::default();

    let start = Instant::now();
    let result = scan_security(&fixtures_dir, &config);
    let duration = start.elapsed();

    assert!(result.is_ok());

    // Scan should complete in reasonable time (< 10 seconds for fixture files)
    assert!(
        duration.as_secs() < 10,
        "Security scan should complete in < 10 seconds, took {:?}",
        duration
    );
}
