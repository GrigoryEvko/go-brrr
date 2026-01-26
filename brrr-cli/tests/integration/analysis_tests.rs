//! Advanced analysis integration tests.
//!
//! Tests for CFG extraction and analysis.

use std::path::PathBuf;

use brrr::cfg::extract as extract_cfg;

/// Get path to metrics fixtures (has good CFG/DFG test cases).
fn fixtures_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("metrics")
}

// =============================================================================
// CFG Extraction Tests
// =============================================================================

#[test]
fn test_cfg_extraction_simple() {
    let fixture = fixtures_path().join("complexity_low.py");

    let result = extract_cfg(fixture.to_str().unwrap(), "simple_return");
    assert!(
        result.is_ok(),
        "CFG extraction should succeed: {:?}",
        result
    );

    let cfg = result.unwrap();

    // Simple function should have entry and exit blocks
    assert!(!cfg.blocks.is_empty(), "CFG should have blocks");
}

#[test]
fn test_cfg_extraction_branches() {
    let fixture = fixtures_path().join("complexity_low.py");

    let result = extract_cfg(fixture.to_str().unwrap(), "simple_if");
    assert!(result.is_ok(), "CFG extraction should succeed");

    let cfg = result.unwrap();

    // Should have multiple blocks for branches
    assert!(
        cfg.blocks.len() >= 2,
        "Should have multiple blocks for if statement"
    );
}

#[test]
fn test_cfg_extraction_loop() {
    let fixture = fixtures_path().join("complexity_low.py");

    let result = extract_cfg(fixture.to_str().unwrap(), "simple_loop");
    assert!(result.is_ok(), "CFG extraction should succeed");

    let cfg = result.unwrap();

    // Should have loop structure
    assert!(
        cfg.blocks.len() >= 2,
        "Should have multiple blocks for loop"
    );
}

#[test]
fn test_cfg_complex_function() {
    let fixture = fixtures_path().join("complexity_high.py");

    let result = extract_cfg(fixture.to_str().unwrap(), "complex_validation");
    assert!(
        result.is_ok(),
        "CFG extraction should succeed for complex function"
    );

    let cfg = result.unwrap();

    // Complex function should have many blocks
    assert!(
        cfg.blocks.len() >= 5,
        "Complex function should have multiple blocks"
    );
}

// =============================================================================
// Performance Tests
// =============================================================================

#[test]
fn test_cfg_extraction_performance() {
    use std::time::Instant;

    let fixture = fixtures_path().join("complexity_high.py");

    let start = Instant::now();

    // Extract CFG for multiple functions
    let _ = extract_cfg(fixture.to_str().unwrap(), "complex_validation");
    let _ = extract_cfg(fixture.to_str().unwrap(), "deeply_nested_function");
    let _ = extract_cfg(fixture.to_str().unwrap(), "many_boolean_conditions");

    let duration = start.elapsed();

    assert!(
        duration.as_secs() < 5,
        "CFG extraction should complete in < 5 seconds, took {:?}",
        duration
    );
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn test_cfg_empty_function() {
    // Create temp file with empty function
    let temp_dir = tempfile::tempdir().unwrap();
    let file = temp_dir.path().join("empty.py");
    std::fs::write(&file, "def empty():\n    pass\n").unwrap();

    let result = extract_cfg(file.to_str().unwrap(), "empty");

    // Should handle empty functions
    assert!(result.is_ok(), "Should handle empty function");
}

#[test]
fn test_cfg_nonexistent_function() {
    let fixture = fixtures_path().join("complexity_low.py");

    let result = extract_cfg(fixture.to_str().unwrap(), "nonexistent_function");

    // Should return error for nonexistent function
    assert!(result.is_err(), "Should error on nonexistent function");
}
