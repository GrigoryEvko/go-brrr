//! Coverage analysis integration tests.

use std::path::PathBuf;

use go_brrr::coverage::{
    parse_coverage_file, parse_coverage_string, BranchCoverage, CoverageData, CoverageFormat,
    FileCoverage, FunctionCoverage,
};

/// Get the path to test fixtures.
fn fixtures_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("coverage")
}

// =============================================================================
// LCOV Parsing Tests
// =============================================================================

#[test]
fn test_lcov_parsing() {
    let lcov_file = fixtures_path().join("lcov.info");

    let result = parse_coverage_file(&lcov_file, Some(CoverageFormat::Lcov));
    assert!(result.is_ok(), "LCOV parsing should succeed: {:?}", result);

    let coverage = result.unwrap();

    // Should parse file coverage
    assert!(
        !coverage.files.is_empty(),
        "Should parse file coverage data"
    );
}

#[test]
fn test_lcov_parsing_string() {
    let lcov_content = r#"TN:
SF:test.py
FN:1,test_func
FNDA:1,test_func
FNF:1
FNH:1
DA:1,1
DA:2,1
DA:3,0
LF:3
LH:2
end_of_record
"#;

    let result = parse_coverage_string(lcov_content, CoverageFormat::Lcov);
    assert!(result.is_ok(), "LCOV string parsing should succeed");

    let coverage = result.unwrap();

    // Should have one file
    assert_eq!(coverage.files.len(), 1, "Should parse one file");
}

// =============================================================================
// Coverage Data Structure Tests
// =============================================================================

#[test]
fn test_coverage_data_merge() {
    let mut data1 = CoverageData::new();
    let mut file1 = FileCoverage::new();
    file1.mark_covered(1, 5);
    file1.mark_covered(2, 3);
    file1.mark_covered(3, 0); // Not covered
    data1.add_file("test.py".into(), file1);

    let mut data2 = CoverageData::new();
    let mut file2 = FileCoverage::new();
    file2.mark_covered(2, 2); // Additional coverage
    file2.mark_covered(3, 1); // Now covered
    file2.mark_covered(4, 1); // New line
    data2.add_file("test.py".into(), file2);

    // Merge
    data1.merge(&data2);

    let merged = data1.get_file(std::path::Path::new("test.py")).unwrap();

    // Line 3 should now be covered
    assert!(
        merged.is_line_covered(3),
        "Line 3 should be covered after merge"
    );
}

#[test]
fn test_coverage_summary_calculation() {
    let mut data = CoverageData::new();

    let mut file = FileCoverage::new();
    file.mark_covered(1, 1);
    file.mark_covered(2, 1);
    file.mark_covered(3, 0);
    file.mark_covered(4, 0);
    file.branches.push(BranchCoverage::new(2, 0, true, 1));
    file.branches.push(BranchCoverage::new(2, 1, false, 0));
    file.functions.push(FunctionCoverage::new("test", 1, 1));

    data.add_file("test.py".into(), file);

    // Check summary
    assert_eq!(data.summary.lines_covered, 2);
    assert_eq!(data.summary.lines_total, 4);
}

// =============================================================================
// Coverage Format Detection Tests
// =============================================================================

#[test]
fn test_format_detection() {
    use std::path::Path;

    assert_eq!(
        CoverageFormat::detect(Path::new("coverage.info")),
        Some(CoverageFormat::Lcov)
    );

    assert_eq!(
        CoverageFormat::detect(Path::new("cobertura.xml")),
        Some(CoverageFormat::Cobertura)
    );
}

#[test]
fn test_format_from_str() {
    assert_eq!(
        "lcov".parse::<CoverageFormat>().unwrap(),
        CoverageFormat::Lcov
    );
    assert_eq!(
        "cobertura".parse::<CoverageFormat>().unwrap(),
        CoverageFormat::Cobertura
    );
    assert!("unknown".parse::<CoverageFormat>().is_err());
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn test_empty_coverage() {
    let coverage = CoverageData::new();

    assert!(coverage.files.is_empty());
    assert_eq!(coverage.summary.lines_total, 0);
}

#[test]
fn test_file_coverage_line_rate() {
    let mut file_cov = FileCoverage::new();

    // Empty file has 100% coverage (nothing to cover)
    assert_eq!(file_cov.line_rate(), 1.0);

    // Add some lines
    file_cov.mark_covered(1, 1);
    file_cov.mark_covered(2, 0);

    assert!((file_cov.line_rate() - 0.5).abs() < 0.01);
}
