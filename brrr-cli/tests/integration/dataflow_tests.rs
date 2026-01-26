//! Data flow analysis integration tests.

use std::path::PathBuf;

use brrr::dataflow::{
    analyze_available_expressions, analyze_constants_in_file, analyze_reaching_definitions,
    analyze_very_busy_expressions_file,
};

// Import live variables file analysis separately
use brrr::dataflow::live_variables::analyze_file as analyze_live_variables_file;

/// Get the path to test fixtures.
fn fixtures_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("dataflow")
}

// =============================================================================
// Constant Propagation Tests
// =============================================================================

#[test]
fn test_constant_propagation_simple() {
    let fixture = fixtures_path().join("constant_propagation.py");

    let result = analyze_constants_in_file(fixture.to_str().unwrap(), "constant_simple");

    // The analysis should succeed
    assert!(
        result.is_ok(),
        "Constant propagation should succeed: {:?}",
        result
    );
}

#[test]
fn test_constant_propagation_arithmetic() {
    let fixture = fixtures_path().join("constant_propagation.py");

    let result = analyze_constants_in_file(fixture.to_str().unwrap(), "constant_arithmetic");

    assert!(result.is_ok(), "Constant propagation should succeed");
}

// =============================================================================
// Live Variables Tests
// =============================================================================

#[test]
fn test_live_variables() {
    let fixture = fixtures_path().join("live_variables.py");

    let result = analyze_live_variables_file(fixture.to_str().unwrap(), "dead_store_simple");

    assert!(
        result.is_ok(),
        "Live variables analysis should succeed: {:?}",
        result
    );
}

// =============================================================================
// Reaching Definitions Tests
// =============================================================================

#[test]
fn test_reaching_definitions() {
    let fixture = fixtures_path().join("reaching_definitions.py");

    let result = analyze_reaching_definitions(fixture.to_str().unwrap(), "simple_reaching");

    assert!(
        result.is_ok(),
        "Reaching definitions should succeed: {:?}",
        result
    );

    let analysis = result.unwrap();

    // Should have definitions
    assert!(!analysis.definitions.is_empty(), "Should find definitions");
}

// =============================================================================
// Available Expressions Tests
// =============================================================================

#[test]
fn test_available_expressions() {
    let fixture = fixtures_path().join("available_expressions.py");

    let result = analyze_available_expressions(fixture.to_str().unwrap(), "cse_opportunity");

    assert!(
        result.is_ok(),
        "Available expressions should succeed: {:?}",
        result
    );
}

// =============================================================================
// Very Busy Expressions Tests
// =============================================================================

#[test]
fn test_very_busy_expressions() {
    let fixture = fixtures_path().join("available_expressions.py");

    let result =
        analyze_very_busy_expressions_file(fixture.to_str().unwrap(), "very_busy_expression");

    assert!(
        result.is_ok(),
        "Very busy expressions should succeed: {:?}",
        result
    );
}

// =============================================================================
// Performance Tests
// =============================================================================

#[test]
fn test_dataflow_analysis_performance() {
    use std::time::Instant;

    let fixture = fixtures_path().join("constant_propagation.py");

    let start = Instant::now();
    let _ = analyze_constants_in_file(fixture.to_str().unwrap(), "constant_arithmetic");
    let duration = start.elapsed();

    // Should complete in reasonable time
    assert!(
        duration.as_secs() < 5,
        "Dataflow analysis should complete in < 5 seconds, took {:?}",
        duration
    );
}
