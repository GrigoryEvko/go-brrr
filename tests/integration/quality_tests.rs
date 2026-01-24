//! Code quality analysis integration tests.

use std::path::PathBuf;

use go_brrr::quality::{
    analyze_doc_coverage, analyze_test_quality, detect_circular_dependencies, detect_clones,
    detect_long_methods, detect_structural_clones,
};

/// Get the path to test fixtures.
fn fixtures_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("quality")
}

// =============================================================================
// Clone Detection Tests (Type-1 Textual)
// =============================================================================

#[test]
fn test_textual_clone_detection() {
    let fixture = fixtures_path().join("clones.py");

    let result = detect_clones(fixture.to_str().unwrap(), Some(6), None);
    assert!(
        result.is_ok(),
        "Clone detection should succeed: {:?}",
        result
    );
}

#[test]
fn test_clone_minimum_lines() {
    let fixture = fixtures_path().join("clones.py");

    // Require at least 10 lines for a clone
    let result = detect_clones(fixture.to_str().unwrap(), Some(10), None);
    assert!(result.is_ok());
}

// =============================================================================
// Structural Clone Detection Tests (Type-2/Type-3)
// =============================================================================

#[test]
fn test_structural_clone_detection() {
    let fixture = fixtures_path().join("clones.py");

    // Detect structural clones with 80% similarity
    let result = detect_structural_clones(fixture.to_str().unwrap(), Some(0.8), None);
    assert!(
        result.is_ok(),
        "Structural clone detection should succeed: {:?}",
        result
    );
}

// =============================================================================
// Long Method Detection Tests
// =============================================================================

#[test]
fn test_long_method_detection() {
    let fixture = fixtures_path().join("long_method.py");

    let result = detect_long_methods(fixture.to_str().unwrap(), Some("python"), None);
    assert!(
        result.is_ok(),
        "Long method detection should succeed: {:?}",
        result
    );

    let analysis = result.unwrap();

    // Should detect long methods
    assert!(!analysis.findings.is_empty(), "Should detect long methods");
}

// =============================================================================
// Circular Dependency Detection Tests
// =============================================================================

#[test]
fn test_circular_dependency_detection() {
    let fixture = fixtures_path().join("circular.py");

    let result = detect_circular_dependencies(fixture.to_str().unwrap(), None);
    assert!(
        result.is_ok(),
        "Circular dependency detection should succeed: {:?}",
        result
    );
}

// =============================================================================
// Test Quality Analysis Tests
// =============================================================================

#[test]
fn test_test_quality_analysis() {
    let fixture = fixtures_path().join("test_quality_fixture.py");

    let result = analyze_test_quality(fixture.to_str().unwrap(), None, None);
    assert!(
        result.is_ok(),
        "Test quality analysis should succeed: {:?}",
        result
    );

    let analysis = result.unwrap();

    // Should analyze test functions
    assert!(
        analysis.summary.total_tests > 0,
        "Should find test functions"
    );
}

// =============================================================================
// Documentation Coverage Tests
// =============================================================================

#[test]
fn test_doc_coverage_analysis() {
    let fixtures_dir = fixtures_path();

    let result = analyze_doc_coverage(&fixtures_dir, Some("python"), None);
    assert!(
        result.is_ok(),
        "Doc coverage analysis should succeed: {:?}",
        result
    );
}

// =============================================================================
// Performance Tests
// =============================================================================

#[test]
fn test_clone_detection_performance() {
    use std::time::Instant;

    let fixture = fixtures_path().join("clones.py");

    let start = Instant::now();
    let result = detect_clones(fixture.to_str().unwrap(), Some(6), None);
    let duration = start.elapsed();

    assert!(result.is_ok());

    // Should complete quickly for small files
    assert!(
        duration.as_secs() < 5,
        "Clone detection should complete in < 5 seconds, took {:?}",
        duration
    );
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn test_empty_file_handling() {
    // Create a temp empty file
    let temp_dir = tempfile::tempdir().unwrap();
    let empty_file = temp_dir.path().join("empty.py");
    std::fs::write(&empty_file, "").unwrap();

    // Clone detection should handle empty files
    let result = detect_clones(empty_file.to_str().unwrap(), Some(6), None);
    assert!(result.is_ok(), "Should handle empty files");
}
