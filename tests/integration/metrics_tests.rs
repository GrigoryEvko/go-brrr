//! Code metrics integration tests.
//!
//! Tests complexity and maintainability metrics.

use std::path::PathBuf;

use go_brrr::metrics::{
    analyze_all_metrics, analyze_cognitive_complexity, analyze_cohesion, analyze_complexity,
    analyze_coupling, analyze_file_complexity, analyze_function_size, analyze_halstead,
    analyze_loc, analyze_maintainability, analyze_nesting, CognitiveRiskLevel, CouplingLevel,
    MetricsConfig, NestingDepthLevel, QualityGate, RiskLevel,
};

/// Get the path to test fixtures.
fn fixtures_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("metrics")
}

// =============================================================================
// Cyclomatic Complexity Tests
// =============================================================================

#[test]
fn test_cyclomatic_complexity_low() {
    let fixture = fixtures_path().join("complexity_low.py");

    let result = analyze_file_complexity(fixture.to_str().unwrap(), None);
    assert!(result.is_ok(), "Complexity analysis should succeed");

    let analysis = result.unwrap();

    // All functions should have low complexity
    for func in &analysis.functions {
        assert!(
            func.complexity <= 10,
            "Function {} should have low complexity (<=10), got {}",
            func.function_name,
            func.complexity
        );
    }
}

#[test]
fn test_cyclomatic_complexity_high() {
    let fixture = fixtures_path().join("complexity_high.py");

    let result = analyze_file_complexity(fixture.to_str().unwrap(), None);
    assert!(result.is_ok(), "Complexity analysis should succeed");

    let analysis = result.unwrap();

    // Should have some high complexity functions
    let high_complexity_funcs: Vec<_> = analysis
        .functions
        .iter()
        .filter(|f| f.complexity > 10)
        .collect();

    assert!(
        !high_complexity_funcs.is_empty(),
        "Should detect high complexity functions"
    );
}

#[test]
fn test_complexity_threshold_filtering() {
    let fixture = fixtures_path().join("complexity_high.py");

    // Analyze with threshold
    let result = analyze_complexity(
        fixture.to_str().unwrap(),
        Some("python"),
        Some(10), // Only functions with complexity > 10
    );

    assert!(result.is_ok());

    let analysis = result.unwrap();

    // All returned functions should exceed threshold
    for func in &analysis.functions {
        assert!(
            func.complexity > 10,
            "All functions should exceed threshold"
        );
    }
}

// =============================================================================
// Cognitive Complexity Tests
// =============================================================================

#[test]
fn test_cognitive_complexity() {
    let fixture = fixtures_path().join("complexity_high.py");

    let result = analyze_cognitive_complexity(fixture.to_str().unwrap(), Some("python"), None);

    assert!(
        result.is_ok(),
        "Cognitive complexity analysis should succeed"
    );

    let analysis = result.unwrap();

    // Should analyze multiple functions
    assert!(!analysis.functions.is_empty(), "Should analyze functions");
}

// =============================================================================
// Halstead Metrics Tests
// =============================================================================

#[test]
fn test_halstead_metrics() {
    let fixture = fixtures_path().join("halstead.py");

    let result = analyze_halstead(fixture.to_str().unwrap(), Some("python"), false);
    assert!(result.is_ok(), "Halstead analysis should succeed");

    let analysis = result.unwrap();

    // Should analyze multiple functions
    assert!(!analysis.functions.is_empty(), "Should analyze functions");
}

// =============================================================================
// Maintainability Index Tests
// =============================================================================

#[test]
fn test_maintainability_index() {
    let fixture = fixtures_path().join("complexity_low.py");

    let result = analyze_maintainability(fixture.to_str().unwrap(), Some("python"), None, false);
    assert!(result.is_ok(), "Maintainability analysis should succeed");

    let analysis = result.unwrap();

    // Low complexity functions should have good maintainability
    assert!(!analysis.functions.is_empty(), "Should analyze functions");
}

// =============================================================================
// Nesting Depth Tests
// =============================================================================

#[test]
fn test_nesting_depth_analysis() {
    let fixture = fixtures_path().join("nesting_deep.py");

    let result = analyze_nesting(fixture.to_str().unwrap(), Some("python"), None);
    assert!(result.is_ok(), "Nesting analysis should succeed");

    let analysis = result.unwrap();

    // Should detect deeply nested functions
    let deep_funcs: Vec<_> = analysis
        .functions
        .iter()
        .filter(|f| f.max_depth >= 5)
        .collect();

    assert!(
        !deep_funcs.is_empty(),
        "Should detect functions with nesting depth >= 5"
    );
}

// =============================================================================
// Lines of Code Tests
// =============================================================================

#[test]
fn test_loc_analysis() {
    let fixtures_dir = fixtures_path();

    let result = analyze_loc(fixtures_dir.to_str().unwrap(), Some("python"), None);
    assert!(result.is_ok(), "LOC analysis should succeed");

    let analysis = result.unwrap();

    // Should count lines
    assert!(analysis.stats.total_sloc > 0, "Should count source lines");
}

// =============================================================================
// Function Size Tests
// =============================================================================

#[test]
fn test_function_size_analysis() {
    let fixture = fixtures_path().join("class_metrics.py");

    let result = analyze_function_size(fixture.to_str().unwrap(), Some("python"), None);
    assert!(result.is_ok(), "Function size analysis should succeed");

    let analysis = result.unwrap();

    // Should analyze functions
    assert!(
        analysis.stats.total_functions > 0 || !analysis.violations.is_empty(),
        "Should analyze functions"
    );
}

// =============================================================================
// Coupling Tests
// =============================================================================

#[test]
fn test_coupling_analysis() {
    let fixture = fixtures_path().join("class_metrics.py");

    let result = analyze_coupling(
        fixture.to_str().unwrap(),
        Some("python"),
        CouplingLevel::File,
    );
    assert!(result.is_ok(), "Coupling analysis should succeed");
}

// =============================================================================
// Cohesion Tests
// =============================================================================

#[test]
fn test_cohesion_analysis() {
    let fixture = fixtures_path().join("class_metrics.py");

    let result = analyze_cohesion(fixture.to_str().unwrap(), Some("python"), None);
    assert!(result.is_ok(), "Cohesion analysis should succeed");

    let analysis = result.unwrap();

    // Should analyze classes
    // Note: May or may not find classes depending on fixture content
}

// =============================================================================
// Unified Metrics Tests
// =============================================================================

#[test]
fn test_unified_metrics_analysis() {
    let fixtures_dir = fixtures_path();

    let config = MetricsConfig::default();
    let result = analyze_all_metrics(fixtures_dir.to_str().unwrap(), Some("python"), &config);

    assert!(result.is_ok(), "Unified metrics analysis should succeed");

    let report = result.unwrap();

    // Should have function-level metrics
    assert!(
        !report.function_metrics.is_empty(),
        "Should have function metrics"
    );
}

#[test]
fn test_quality_gate() {
    let fixture = fixtures_path().join("complexity_low.py");

    let config = MetricsConfig::default();
    let result = analyze_all_metrics(fixture.to_str().unwrap(), Some("python"), &config);

    assert!(result.is_ok());

    let report = result.unwrap();

    // Quality gate check should complete
    let gate = QualityGate::default();
    let _gate_result = gate.check(&report);
    // Just verify it doesn't panic
}

// =============================================================================
// Performance Tests
// =============================================================================

#[test]
fn test_metrics_analysis_performance() {
    use std::time::Instant;

    let fixtures_dir = fixtures_path();

    let start = Instant::now();
    let result = analyze_complexity(fixtures_dir.to_str().unwrap(), Some("python"), None);
    let duration = start.elapsed();

    assert!(result.is_ok());

    // Should complete in reasonable time
    assert!(
        duration.as_secs() < 10,
        "Metrics analysis should complete in < 10 seconds, took {:?}",
        duration
    );
}
