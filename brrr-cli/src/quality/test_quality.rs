//! Test quality metrics for analyzing test effectiveness beyond coverage.
//!
//! This module provides comprehensive analysis of test quality including:
//!
//! - **Assertion Density**: Number of assertions per test function
//! - **Test Isolation Score**: Detection of shared state and external dependencies
//! - **Boundary Testing Score**: Detection of edge case testing
//! - **Mutation Score Estimation**: Heuristic estimation without running mutations
//! - **Mock Usage Metrics**: Analysis of mock/stub patterns
//!
//! # Assertion Patterns by Language
//!
//! | Language   | Assertion Patterns                                           |
//! |------------|--------------------------------------------------------------|
//! | Python     | assert, assertEqual, assertTrue, pytest.raises, mock.assert_* |
//! | JavaScript | expect().toBe(), assert.equal(), toThrow(), rejects         |
//! | TypeScript | expect().toBe(), assert.equal(), toThrow(), rejects         |
//! | Rust       | assert!, assert_eq!, assert_ne!, #[should_panic]            |
//! | Go         | t.Error, t.Errorf, t.Fatal, testify/assert                   |
//!
//! # Test Quality Grading
//!
//! | Grade | Assertion Density | Description                              |
//! |-------|-------------------|------------------------------------------|
//! | A     | >= 4              | Comprehensive testing with multiple checks |
//! | B     | 3                 | Good testing with reasonable coverage    |
//! | C     | 2                 | Basic testing, could be improved         |
//! | D     | 1                 | Weak test, single assertion              |
//! | F     | 0                 | No assertions, test does nothing useful  |
//!
//! # Example
//!
//! ```ignore
//! use brrr::quality::test_quality::{analyze_test_quality, TestQualityConfig};
//!
//! let result = analyze_test_quality("./tests", None, None)?;
//! println!("Analyzed {} test files", result.summary.files_analyzed);
//! println!("Average assertion density: {:.2}", result.summary.avg_assertion_density);
//! for weak in &result.weak_tests {
//!     println!("Weak test: {} - {:?}", weak.function, weak.issues);
//! }
//! ```

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::debug;
use tree_sitter::{Node, Tree};

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;

// =============================================================================
// CONFIGURATION
// =============================================================================

/// Configuration for test quality analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestQualityConfig {
    /// Minimum assertion density for a test to be considered good (default: 2)
    pub min_assertion_density: f64,

    /// Consider tests with only one assertion as weak (default: true)
    pub flag_single_assertion: bool,

    /// Maximum allowed external dependencies (network, file, db) (default: 0)
    pub max_external_deps: u32,

    /// Whether to analyze mock usage (default: true)
    pub analyze_mocks: bool,

    /// Whether to check for boundary testing (default: true)
    pub check_boundary_testing: bool,

    /// Whether to estimate mutation score (default: true)
    pub estimate_mutation_score: bool,

    /// Minimum lines for a test function to analyze (default: 2)
    pub min_test_lines: u32,

    /// File patterns to identify test files (default: test_, _test, spec)
    pub test_file_patterns: Vec<String>,

    /// Function patterns to identify test functions
    pub test_function_patterns: Vec<String>,
}

impl Default for TestQualityConfig {
    fn default() -> Self {
        Self {
            min_assertion_density: 2.0,
            flag_single_assertion: true,
            max_external_deps: 0,
            analyze_mocks: true,
            check_boundary_testing: true,
            estimate_mutation_score: true,
            min_test_lines: 2,
            test_file_patterns: vec![
                "test_".into(),
                "_test".into(),
                "spec".into(),
                "tests/".into(),
                "__tests__/".into(),
            ],
            test_function_patterns: vec![
                "test_".into(),
                "_test".into(),
                "it(".into(),
                "describe(".into(),
                "#[test]".into(),
                "#[tokio::test]".into(),
                "func Test".into(),
            ],
        }
    }
}

impl TestQualityConfig {
    /// Create a strict configuration for high-quality test requirements.
    #[must_use]
    pub fn strict() -> Self {
        Self {
            min_assertion_density: 3.0,
            flag_single_assertion: true,
            max_external_deps: 0,
            analyze_mocks: true,
            check_boundary_testing: true,
            estimate_mutation_score: true,
            min_test_lines: 3,
            ..Default::default()
        }
    }

    /// Create a lenient configuration for legacy test suites.
    #[must_use]
    pub fn lenient() -> Self {
        Self {
            min_assertion_density: 1.0,
            flag_single_assertion: false,
            max_external_deps: 2,
            analyze_mocks: false,
            check_boundary_testing: false,
            estimate_mutation_score: true,
            min_test_lines: 1,
            ..Default::default()
        }
    }
}

// =============================================================================
// OUTPUT TYPES
// =============================================================================

/// Type of assertion detected in test code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AssertionType {
    /// Equality check (assertEqual, assert_eq!, toBe)
    Equality,
    /// Truthiness check (assertTrue, assert!, toBeTruthy)
    Truthiness,
    /// Exception/error check (assertRaises, toThrow, should_panic)
    Exception,
    /// Contains/membership check (assertIn, toContain)
    Contains,
    /// Comparison check (assertGreater, toBeLessThan)
    Comparison,
    /// Mock assertion (assert_called, toHaveBeenCalled)
    MockAssertion,
    /// Null/None check (assertIsNone, toBeNull)
    NullCheck,
    /// Type check (assertIsInstance, toBeInstanceOf)
    TypeCheck,
    /// Generic assertion (assert, fail)
    Generic,
}

/// Mock usage metrics for a test function.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct MockUsageMetrics {
    /// Number of mocks/patches used
    pub mock_count: u32,
    /// Whether mocks are properly verified
    pub has_mock_assertions: bool,
    /// Types of mocks detected
    pub mock_types: Vec<String>,
    /// Whether test uses dependency injection
    pub uses_dependency_injection: bool,
}

/// Issues detected in a weak test.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TestIssue {
    /// Test has no assertions
    NoAssertions,
    /// Test has only one assertion
    SingleAssertion,
    /// Test doesn't check edge cases
    NoEdgeCases,
    /// Test uses shared/global state
    SharedState,
    /// Test has external dependencies without mocking
    UnmockedDependency(String),
    /// Test lacks proper setup/teardown
    NoSetupTeardown,
    /// Test name doesn't describe behavior
    PoorNaming,
    /// Test is too long and tests multiple things
    TestsTooMuch,
    /// Assertions don't cover return value
    ReturnValueUnchecked,
    /// No negative/error case testing
    NoNegativeTesting,
}

/// Detected assertion in test code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectedAssertion {
    /// Type of assertion
    pub assertion_type: AssertionType,
    /// Line number where assertion appears
    pub line: u32,
    /// The assertion expression/call
    pub expression: String,
    /// What is being checked (if determinable)
    pub checking: Option<String>,
}

/// Quality metrics for a single test function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestFunctionQuality {
    /// Test function name
    pub name: String,
    /// Line number where test starts
    pub line: u32,
    /// Line number where test ends
    pub end_line: u32,
    /// Number of assertions in this test
    pub assertion_count: u32,
    /// Assertion density (assertions / test size factor)
    pub assertion_density: f64,
    /// Types of assertions used
    pub assertion_types: HashMap<AssertionType, u32>,
    /// List of detected assertions
    pub assertions: Vec<DetectedAssertion>,
    /// Mock usage metrics
    pub mock_usage: MockUsageMetrics,
    /// Test isolation score (0-1, 1 = fully isolated)
    pub isolation_score: f64,
    /// Boundary testing score (0-1, 1 = comprehensive edge case coverage)
    pub boundary_testing_score: f64,
    /// Estimated mutation score (0-1, likelihood of catching mutations)
    pub estimated_mutation_score: f64,
    /// Complexity of the test (cyclomatic-like)
    pub complexity: u32,
    /// Issues detected
    pub issues: Vec<TestIssue>,
    /// Quality grade (A-F)
    pub grade: char,
}

/// Quality metrics for a test file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestFileQuality {
    /// Path to the test file
    pub file: PathBuf,
    /// Total number of test functions
    pub test_count: u32,
    /// Average assertion density across all tests
    pub avg_assertion_density: f64,
    /// Average test complexity
    pub avg_test_complexity: f64,
    /// Overall isolation score for the file
    pub isolation_score: f64,
    /// Mock usage metrics aggregated
    pub mock_usage: MockUsageMetrics,
    /// Boundary testing score for the file
    pub boundary_testing_score: f64,
    /// Estimated mutation score for the file
    pub estimated_mutation_score: f64,
    /// Individual test function metrics
    pub test_functions: Vec<TestFunctionQuality>,
    /// File-level issues
    pub file_issues: Vec<String>,
}

/// A weak test that needs improvement.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WeakTest {
    /// Function name
    pub function: String,
    /// File path
    pub file: PathBuf,
    /// Line number
    pub line: u32,
    /// Issues detected
    pub issues: Vec<TestIssue>,
    /// Improvement suggestions
    pub suggestions: Vec<String>,
}

/// Suggestion for improving test quality.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestImprovement {
    /// File path
    pub file: PathBuf,
    /// Test function name
    pub function: String,
    /// Line number
    pub line: u32,
    /// Priority (1 = highest)
    pub priority: u32,
    /// Description of the improvement
    pub description: String,
    /// Category of improvement
    pub category: ImprovementCategory,
}

/// Category of test improvement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ImprovementCategory {
    /// Add more assertions
    MoreAssertions,
    /// Add edge case tests
    EdgeCases,
    /// Improve isolation
    Isolation,
    /// Add mocking
    Mocking,
    /// Split test into multiple tests
    SplitTest,
    /// Improve test naming
    Naming,
    /// Add negative testing
    NegativeTesting,
}

/// Summary statistics for the test quality analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestQualitySummary {
    /// Total files analyzed
    pub files_analyzed: u32,
    /// Total test functions found
    pub total_tests: u32,
    /// Average assertion density
    pub avg_assertion_density: f64,
    /// Average test complexity
    pub avg_complexity: f64,
    /// Average isolation score
    pub avg_isolation_score: f64,
    /// Average boundary testing score
    pub avg_boundary_score: f64,
    /// Average estimated mutation score
    pub avg_mutation_score: f64,
    /// Number of weak tests
    pub weak_test_count: u32,
    /// Grade distribution (A, B, C, D, F)
    pub grade_distribution: HashMap<char, u32>,
    /// Most common issues
    pub common_issues: Vec<(TestIssue, u32)>,
    /// Overall quality grade
    pub overall_grade: char,
}

/// Complete test quality analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestQualityAnalysis {
    /// Per-file quality metrics
    pub files: Vec<TestFileQuality>,
    /// Summary statistics
    pub summary: TestQualitySummary,
    /// List of weak tests needing attention
    pub weak_tests: Vec<WeakTest>,
    /// Improvement suggestions sorted by priority
    pub suggestions: Vec<TestImprovement>,
}

/// Error type for test quality analysis.
#[derive(Debug, thiserror::Error)]
pub enum TestQualityError {
    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    /// Parse error
    #[error("Parse error in {file}: {message}")]
    Parse { file: String, message: String },
    /// Configuration error
    #[error("Configuration error: {0}")]
    Config(String),
    /// Path error
    #[error("Path error: {0}")]
    Path(String),
}

impl From<BrrrError> for TestQualityError {
    fn from(e: BrrrError) -> Self {
        Self::Path(e.to_string())
    }
}

// =============================================================================
// LANGUAGE-SPECIFIC ASSERTION PATTERNS
// =============================================================================

/// Assertion patterns for Python.
const PYTHON_ASSERTIONS: &[(&str, AssertionType)] = &[
    // pytest / unittest assertions
    ("assert ", AssertionType::Generic),
    ("assertEqual", AssertionType::Equality),
    ("assertEquals", AssertionType::Equality),
    ("assertNotEqual", AssertionType::Equality),
    ("assertTrue", AssertionType::Truthiness),
    ("assertFalse", AssertionType::Truthiness),
    ("assertIs", AssertionType::Equality),
    ("assertIsNot", AssertionType::Equality),
    ("assertIsNone", AssertionType::NullCheck),
    ("assertIsNotNone", AssertionType::NullCheck),
    ("assertIn", AssertionType::Contains),
    ("assertNotIn", AssertionType::Contains),
    ("assertIsInstance", AssertionType::TypeCheck),
    ("assertNotIsInstance", AssertionType::TypeCheck),
    ("assertRaises", AssertionType::Exception),
    ("assertWarns", AssertionType::Exception),
    ("assertLogs", AssertionType::Generic),
    ("assertGreater", AssertionType::Comparison),
    ("assertGreaterEqual", AssertionType::Comparison),
    ("assertLess", AssertionType::Comparison),
    ("assertLessEqual", AssertionType::Comparison),
    ("assertAlmostEqual", AssertionType::Equality),
    ("assertCountEqual", AssertionType::Equality),
    ("assertListEqual", AssertionType::Equality),
    ("assertDictEqual", AssertionType::Equality),
    ("assertSetEqual", AssertionType::Equality),
    ("assertTupleEqual", AssertionType::Equality),
    ("assertRegex", AssertionType::Contains),
    ("assertNotRegex", AssertionType::Contains),
    // pytest
    ("pytest.raises", AssertionType::Exception),
    ("pytest.warns", AssertionType::Exception),
    ("pytest.approx", AssertionType::Equality),
    // mock assertions
    ("assert_called", AssertionType::MockAssertion),
    ("assert_called_once", AssertionType::MockAssertion),
    ("assert_called_with", AssertionType::MockAssertion),
    ("assert_called_once_with", AssertionType::MockAssertion),
    ("assert_any_call", AssertionType::MockAssertion),
    ("assert_has_calls", AssertionType::MockAssertion),
    ("assert_not_called", AssertionType::MockAssertion),
];

/// Assertion patterns for JavaScript/TypeScript (Jest, Mocha, Chai).
const JS_TS_ASSERTIONS: &[(&str, AssertionType)] = &[
    // Jest expect
    ("expect(", AssertionType::Generic),
    (".toBe(", AssertionType::Equality),
    (".toEqual(", AssertionType::Equality),
    (".toStrictEqual(", AssertionType::Equality),
    (".toBeTruthy(", AssertionType::Truthiness),
    (".toBeFalsy(", AssertionType::Truthiness),
    (".toBeNull(", AssertionType::NullCheck),
    (".toBeUndefined(", AssertionType::NullCheck),
    (".toBeDefined(", AssertionType::NullCheck),
    (".toBeNaN(", AssertionType::Truthiness),
    (".toContain(", AssertionType::Contains),
    (".toContainEqual(", AssertionType::Contains),
    (".toHaveLength(", AssertionType::Comparison),
    (".toBeGreaterThan(", AssertionType::Comparison),
    (".toBeGreaterThanOrEqual(", AssertionType::Comparison),
    (".toBeLessThan(", AssertionType::Comparison),
    (".toBeLessThanOrEqual(", AssertionType::Comparison),
    (".toBeCloseTo(", AssertionType::Equality),
    (".toMatch(", AssertionType::Contains),
    (".toMatchObject(", AssertionType::Equality),
    (".toThrow(", AssertionType::Exception),
    (".toThrowError(", AssertionType::Exception),
    (".rejects.", AssertionType::Exception),
    (".resolves.", AssertionType::Generic),
    (".toBeInstanceOf(", AssertionType::TypeCheck),
    // Mock assertions
    (".toHaveBeenCalled(", AssertionType::MockAssertion),
    (".toHaveBeenCalledTimes(", AssertionType::MockAssertion),
    (".toHaveBeenCalledWith(", AssertionType::MockAssertion),
    (".toHaveBeenLastCalledWith(", AssertionType::MockAssertion),
    (".toHaveBeenNthCalledWith(", AssertionType::MockAssertion),
    (".toHaveReturned(", AssertionType::MockAssertion),
    (".toHaveReturnedWith(", AssertionType::MockAssertion),
    // Chai
    ("assert.equal(", AssertionType::Equality),
    ("assert.strictEqual(", AssertionType::Equality),
    ("assert.deepEqual(", AssertionType::Equality),
    ("assert.notEqual(", AssertionType::Equality),
    ("assert.isTrue(", AssertionType::Truthiness),
    ("assert.isFalse(", AssertionType::Truthiness),
    ("assert.isNull(", AssertionType::NullCheck),
    ("assert.isNotNull(", AssertionType::NullCheck),
    ("assert.isUndefined(", AssertionType::NullCheck),
    ("assert.isDefined(", AssertionType::NullCheck),
    ("assert.throws(", AssertionType::Exception),
    ("assert.doesNotThrow(", AssertionType::Exception),
    ("assert.include(", AssertionType::Contains),
    ("assert.instanceOf(", AssertionType::TypeCheck),
    // Node.js assert
    ("assert(", AssertionType::Generic),
    ("assert.ok(", AssertionType::Truthiness),
    ("assert.fail(", AssertionType::Generic),
];

/// Assertion patterns for Rust.
const RUST_ASSERTIONS: &[(&str, AssertionType)] = &[
    ("assert!", AssertionType::Generic),
    ("assert_eq!", AssertionType::Equality),
    ("assert_ne!", AssertionType::Equality),
    ("debug_assert!", AssertionType::Generic),
    ("debug_assert_eq!", AssertionType::Equality),
    ("debug_assert_ne!", AssertionType::Equality),
    ("#[should_panic", AssertionType::Exception),
    ("panic!", AssertionType::Exception),
    // Common test crate assertions
    ("assert_matches!", AssertionType::Contains),
    ("assert_approx_eq!", AssertionType::Equality),
];

/// Assertion patterns for Go.
const GO_ASSERTIONS: &[(&str, AssertionType)] = &[
    // Standard testing
    ("t.Error(", AssertionType::Generic),
    ("t.Errorf(", AssertionType::Generic),
    ("t.Fatal(", AssertionType::Generic),
    ("t.Fatalf(", AssertionType::Generic),
    ("t.Fail(", AssertionType::Generic),
    ("t.FailNow(", AssertionType::Generic),
    // testify/assert
    ("assert.Equal(", AssertionType::Equality),
    ("assert.NotEqual(", AssertionType::Equality),
    ("assert.True(", AssertionType::Truthiness),
    ("assert.False(", AssertionType::Truthiness),
    ("assert.Nil(", AssertionType::NullCheck),
    ("assert.NotNil(", AssertionType::NullCheck),
    ("assert.Empty(", AssertionType::NullCheck),
    ("assert.NotEmpty(", AssertionType::NullCheck),
    ("assert.Contains(", AssertionType::Contains),
    ("assert.NotContains(", AssertionType::Contains),
    ("assert.Panics(", AssertionType::Exception),
    ("assert.NotPanics(", AssertionType::Exception),
    ("assert.Error(", AssertionType::Exception),
    ("assert.NoError(", AssertionType::Exception),
    ("assert.EqualError(", AssertionType::Exception),
    ("assert.Greater(", AssertionType::Comparison),
    ("assert.GreaterOrEqual(", AssertionType::Comparison),
    ("assert.Less(", AssertionType::Comparison),
    ("assert.LessOrEqual(", AssertionType::Comparison),
    ("assert.IsType(", AssertionType::TypeCheck),
    ("assert.Implements(", AssertionType::TypeCheck),
    // testify/require (same patterns, different package)
    ("require.Equal(", AssertionType::Equality),
    ("require.NotEqual(", AssertionType::Equality),
    ("require.True(", AssertionType::Truthiness),
    ("require.False(", AssertionType::Truthiness),
    ("require.Nil(", AssertionType::NullCheck),
    ("require.NotNil(", AssertionType::NullCheck),
    ("require.Error(", AssertionType::Exception),
    ("require.NoError(", AssertionType::Exception),
];

/// Assertion patterns for Java (JUnit).
const JAVA_ASSERTIONS: &[(&str, AssertionType)] = &[
    ("assertEquals(", AssertionType::Equality),
    ("assertNotEquals(", AssertionType::Equality),
    ("assertTrue(", AssertionType::Truthiness),
    ("assertFalse(", AssertionType::Truthiness),
    ("assertNull(", AssertionType::NullCheck),
    ("assertNotNull(", AssertionType::NullCheck),
    ("assertSame(", AssertionType::Equality),
    ("assertNotSame(", AssertionType::Equality),
    ("assertArrayEquals(", AssertionType::Equality),
    ("assertThrows(", AssertionType::Exception),
    ("assertDoesNotThrow(", AssertionType::Exception),
    ("assertTimeout(", AssertionType::Generic),
    ("assertTimeoutPreemptively(", AssertionType::Generic),
    ("fail(", AssertionType::Generic),
    // Hamcrest matchers
    ("assertThat(", AssertionType::Generic),
    // AssertJ
    (".isEqualTo(", AssertionType::Equality),
    (".isNotEqualTo(", AssertionType::Equality),
    (".isTrue()", AssertionType::Truthiness),
    (".isFalse()", AssertionType::Truthiness),
    (".isNull()", AssertionType::NullCheck),
    (".isNotNull()", AssertionType::NullCheck),
    (".contains(", AssertionType::Contains),
    (".containsExactly(", AssertionType::Contains),
    (".isInstanceOf(", AssertionType::TypeCheck),
    (".hasSize(", AssertionType::Comparison),
    // Mockito
    ("verify(", AssertionType::MockAssertion),
    ("verifyNoInteractions(", AssertionType::MockAssertion),
    ("verifyNoMoreInteractions(", AssertionType::MockAssertion),
];

/// Patterns indicating shared state.
const SHARED_STATE_PATTERNS: &[&str] = &[
    // Python
    "global ",
    "cls.",
    "@classmethod",
    "setUpClass",
    "tearDownClass",
    "setUpModule",
    // JavaScript/TypeScript
    "beforeAll",
    "afterAll",
    "global.",
    "window.",
    "document.",
    "globalThis.",
    // Rust
    "static mut",
    "lazy_static!",
    "once_cell",
    // Go
    "sync.Once",
    "var ",
    // Java
    "static ",
    "@BeforeClass",
    "@AfterClass",
];

/// Patterns indicating external dependencies.
const EXTERNAL_DEP_PATTERNS: &[&str] = &[
    // File I/O
    "open(",
    "read_file",
    "write_file",
    "fs.read",
    "fs.write",
    "File::",
    "os.Open",
    "ioutil.",
    "FileInputStream",
    "FileOutputStream",
    // Network
    "http.",
    "requests.",
    "fetch(",
    "axios.",
    "urllib",
    "net.Dial",
    "HttpClient",
    "WebClient",
    // Database
    "cursor.",
    "execute(",
    "query(",
    "db.",
    "sql.",
    "database.",
    "SELECT ",
    "INSERT ",
    "UPDATE ",
    "DELETE ",
    "Connection",
    "DriverManager",
    // Environment
    "os.environ",
    "os.getenv",
    "process.env",
    "env::",
    "os.Getenv",
    "System.getenv",
];

/// Patterns indicating mocking.
const MOCK_PATTERNS: &[&str] = &[
    // Python
    "@patch",
    "patch(",
    "Mock(",
    "MagicMock(",
    "mock.",
    "mocker.",
    "monkeypatch",
    // JavaScript/TypeScript
    "jest.mock(",
    "jest.fn(",
    "jest.spyOn(",
    "sinon.",
    "stub(",
    "mock(",
    "vi.mock(",
    "vi.fn(",
    // Rust
    "mockall",
    "#[automock]",
    "mock!",
    // Go
    "gomock",
    "MockController",
    "NewMock",
    "EXPECT()",
    "testify/mock",
    // Java
    "@Mock",
    "@InjectMocks",
    "Mockito.",
    "when(",
    "doReturn(",
    "doThrow(",
    "EasyMock",
    "PowerMock",
];

/// Patterns indicating boundary/edge case testing.
const BOUNDARY_PATTERNS: &[(&str, &str)] = &[
    // Null/None/Nil
    ("None", "null testing"),
    ("null", "null testing"),
    ("nil", "null testing"),
    ("undefined", "undefined testing"),
    // Empty values
    ("\"\"", "empty string testing"),
    ("''", "empty string testing"),
    ("[]", "empty collection testing"),
    ("{}", "empty dict/object testing"),
    ("vec![]", "empty vector testing"),
    // Zero
    ("= 0", "zero testing"),
    ("(0)", "zero testing"),
    ("0.0", "zero testing"),
    // Negative
    ("-1", "negative number testing"),
    ("< 0", "negative boundary testing"),
    // Max values
    ("MAX_", "max value testing"),
    ("_MAX", "max value testing"),
    ("max_value", "max value testing"),
    ("MAX_VALUE", "max value testing"),
    ("INT_MAX", "max int testing"),
    ("i32::MAX", "max int testing"),
    ("i64::MAX", "max int testing"),
    ("u64::MAX", "max uint testing"),
    ("Integer.MAX_VALUE", "max int testing"),
    ("Number.MAX_VALUE", "max number testing"),
    ("math.MaxInt", "max int testing"),
    // Min values
    ("MIN_", "min value testing"),
    ("_MIN", "min value testing"),
    ("min_value", "min value testing"),
    ("MIN_VALUE", "min value testing"),
    ("i32::MIN", "min int testing"),
    ("Integer.MIN_VALUE", "min int testing"),
    // Overflow
    ("overflow", "overflow testing"),
    ("underflow", "underflow testing"),
    // Type boundaries
    ("NaN", "NaN testing"),
    ("Infinity", "infinity testing"),
    ("f64::INFINITY", "infinity testing"),
    ("Float.POSITIVE_INFINITY", "infinity testing"),
    // Off-by-one
    ("len() - 1", "off-by-one testing"),
    ("length - 1", "off-by-one testing"),
    (".len() - 1", "off-by-one testing"),
    ("size() - 1", "off-by-one testing"),
];

// =============================================================================
// ANALYZER
// =============================================================================

/// Test quality analyzer.
pub struct TestQualityAnalyzer {
    config: TestQualityConfig,
}

impl TestQualityAnalyzer {
    /// Create a new analyzer with the given configuration.
    #[must_use]
    pub fn new(config: TestQualityConfig) -> Self {
        Self { config }
    }

    /// Analyze a single test file.
    pub fn analyze_file(&self, path: &Path, source: &str, lang: &str) -> Result<TestFileQuality> {
        let registry = LanguageRegistry::global();
        let language = registry
            .get_by_name(lang)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(lang.to_string()))?;

        let mut parser = language.parser()?;
        let tree = parser
            .parse(source.as_bytes(), None)
            .ok_or_else(|| BrrrError::Parse {
                file: path.display().to_string(),
                message: "Failed to parse source".to_string(),
            })?;

        let test_functions = self.extract_test_functions(&tree, source.as_bytes(), lang);
        let mut analyzed_functions = Vec::new();

        for (name, start_line, end_line, body) in test_functions {
            let quality = self.analyze_test_function(&name, start_line, end_line, &body, lang);
            analyzed_functions.push(quality);
        }

        // Aggregate file-level metrics
        let test_count = analyzed_functions.len() as u32;
        let avg_assertion_density = if test_count > 0 {
            analyzed_functions
                .iter()
                .map(|f| f.assertion_density)
                .sum::<f64>()
                / f64::from(test_count)
        } else {
            0.0
        };
        let avg_test_complexity = if test_count > 0 {
            analyzed_functions
                .iter()
                .map(|f| f64::from(f.complexity))
                .sum::<f64>()
                / f64::from(test_count)
        } else {
            0.0
        };
        let isolation_score = if test_count > 0 {
            analyzed_functions
                .iter()
                .map(|f| f.isolation_score)
                .sum::<f64>()
                / f64::from(test_count)
        } else {
            1.0
        };
        let boundary_testing_score = if test_count > 0 {
            analyzed_functions
                .iter()
                .map(|f| f.boundary_testing_score)
                .sum::<f64>()
                / f64::from(test_count)
        } else {
            0.0
        };
        let estimated_mutation_score = if test_count > 0 {
            analyzed_functions
                .iter()
                .map(|f| f.estimated_mutation_score)
                .sum::<f64>()
                / f64::from(test_count)
        } else {
            0.0
        };

        // Aggregate mock usage
        let mock_count: u32 = analyzed_functions
            .iter()
            .map(|f| f.mock_usage.mock_count)
            .sum();
        let has_mock_assertions = analyzed_functions
            .iter()
            .any(|f| f.mock_usage.has_mock_assertions);
        let uses_dependency_injection = analyzed_functions
            .iter()
            .any(|f| f.mock_usage.uses_dependency_injection);
        let mock_types: Vec<String> = analyzed_functions
            .iter()
            .flat_map(|f| f.mock_usage.mock_types.clone())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();

        // Check for file-level issues
        let mut file_issues = Vec::new();
        if source.contains("setUpClass")
            || source.contains("@BeforeClass")
            || source.contains("beforeAll")
        {
            file_issues
                .push("File uses class-level setup which may cause test interference".to_string());
        }
        if source.contains("global ") && lang == "python" {
            file_issues.push("File modifies global state".to_string());
        }

        Ok(TestFileQuality {
            file: path.to_path_buf(),
            test_count,
            avg_assertion_density,
            avg_test_complexity,
            isolation_score,
            mock_usage: MockUsageMetrics {
                mock_count,
                has_mock_assertions,
                mock_types,
                uses_dependency_injection,
            },
            boundary_testing_score,
            estimated_mutation_score,
            test_functions: analyzed_functions,
            file_issues,
        })
    }

    /// Extract test functions from AST.
    fn extract_test_functions(
        &self,
        tree: &Tree,
        source: &[u8],
        lang: &str,
    ) -> Vec<(String, u32, u32, String)> {
        let mut tests = Vec::new();
        let root = tree.root_node();

        self.find_test_functions(root, source, lang, &mut tests);
        tests
    }

    /// Recursively find test functions in the AST.
    fn find_test_functions(
        &self,
        node: Node,
        source: &[u8],
        lang: &str,
        tests: &mut Vec<(String, u32, u32, String)>,
    ) {
        let kind = node.kind();

        // Check if this node is a function definition
        let is_function = matches!(
            kind,
            "function_definition" |     // Python
            "function_declaration" |     // JS/TS/Go
            "function" |                 // Rust
            "function_item" |            // Rust
            "method_declaration" |       // Java
            "arrow_function" |           // JS/TS
            "method_definition" // JS/TS class methods
        );

        if is_function {
            if let Some(name) = self.get_function_name(node, source, lang) {
                if self.is_test_function(&name, node, source, lang) {
                    let start_line = node.start_position().row as u32 + 1;
                    let end_line = node.end_position().row as u32 + 1;
                    let body = self.get_node_text(node, source);
                    tests.push((name, start_line, end_line, body));
                }
            }
        }

        // Also check for describe/it blocks in JS/TS
        if (lang == "javascript" || lang == "typescript")
            && (kind == "call_expression" || kind == "expression_statement")
        {
            let text = self.get_node_text(node, source);
            if text.starts_with("it(") || text.starts_with("test(") {
                // Extract test name from string argument
                if let Some(name) = self.extract_js_test_name(&text) {
                    let start_line = node.start_position().row as u32 + 1;
                    let end_line = node.end_position().row as u32 + 1;
                    tests.push((name, start_line, end_line, text));
                }
            }
        }

        // Recurse into children
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.find_test_functions(child, source, lang, tests);
        }
    }

    /// Get function name from a function node.
    fn get_function_name(&self, node: Node, source: &[u8], lang: &str) -> Option<String> {
        // Try to get name from 'name' field first (most languages)
        if let Some(name_node) = node.child_by_field_name("name") {
            return Some(self.get_node_text(name_node, source));
        }

        // For Rust, try 'identifier' in function_item
        if lang == "rust" {
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "identifier" {
                    return Some(self.get_node_text(child, source));
                }
            }
        }

        // For Go functions
        if lang == "go" {
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "identifier" {
                    return Some(self.get_node_text(child, source));
                }
            }
        }

        None
    }

    /// Check if a function is a test function.
    fn is_test_function(&self, name: &str, node: Node, source: &[u8], lang: &str) -> bool {
        // Check name patterns
        let name_lower = name.to_lowercase();
        if name_lower.starts_with("test_")
            || name_lower.starts_with("test")
            || name_lower.ends_with("_test")
            || name_lower.ends_with("test")
            || name_lower.starts_with("it_")
            || name_lower.starts_with("should_")
        {
            return true;
        }

        // Check for test decorators/attributes
        let node_text = self.get_node_text(node, source);

        match lang {
            "python" => {
                // Check for pytest markers
                if let Some(prev) = node.prev_sibling() {
                    let prev_text = self.get_node_text(prev, source);
                    if prev_text.contains("@pytest") || prev_text.contains("@test") {
                        return true;
                    }
                }
            }
            "rust" => {
                // Check for #[test] attribute
                if node_text.contains("#[test]")
                    || node_text.contains("#[tokio::test]")
                    || node_text.contains("#[async_std::test]")
                {
                    return true;
                }
            }
            "go" => {
                // Go tests must start with Test and have *testing.T parameter
                if name.starts_with("Test") && node_text.contains("*testing.T") {
                    return true;
                }
            }
            "java" => {
                // Check for @Test annotation
                if node_text.contains("@Test") || node_text.contains("@ParameterizedTest") {
                    return true;
                }
            }
            _ => {}
        }

        false
    }

    /// Extract test name from JavaScript it() or test() call.
    fn extract_js_test_name(&self, text: &str) -> Option<String> {
        // Look for string in first argument
        let start = text.find('(')? + 1;
        let rest = &text[start..];

        if rest.starts_with('"') || rest.starts_with('\'') || rest.starts_with('`') {
            let quote = rest.chars().next()?;
            let end = rest[1..].find(quote)?;
            return Some(rest[1..end + 1].to_string());
        }

        None
    }

    /// Get text content of a node.
    fn get_node_text(&self, node: Node, source: &[u8]) -> String {
        String::from_utf8_lossy(&source[node.start_byte()..node.end_byte()]).to_string()
    }

    /// Analyze a single test function.
    fn analyze_test_function(
        &self,
        name: &str,
        start_line: u32,
        end_line: u32,
        body: &str,
        lang: &str,
    ) -> TestFunctionQuality {
        let assertions = self.count_assertions(body, lang);
        let assertion_count = assertions.len() as u32;

        // Calculate assertion density
        let lines = (end_line - start_line).max(1);
        let assertion_density = f64::from(assertion_count) / (f64::from(lines) / 10.0).max(1.0);

        // Count assertion types
        let mut assertion_types = HashMap::new();
        for assertion in &assertions {
            *assertion_types.entry(assertion.assertion_type).or_insert(0) += 1;
        }

        // Analyze mock usage
        let mock_usage = self.analyze_mock_usage(body);

        // Calculate isolation score
        let isolation_score = self.calculate_isolation_score(body);

        // Calculate boundary testing score
        let boundary_testing_score = self.calculate_boundary_score(body);

        // Estimate mutation score
        let estimated_mutation_score = self.estimate_mutation_score(&assertions, body);

        // Calculate complexity (simplified cyclomatic)
        let complexity = self.estimate_complexity(body);

        // Detect issues
        let mut issues = Vec::new();
        if assertion_count == 0 {
            issues.push(TestIssue::NoAssertions);
        } else if assertion_count == 1 && self.config.flag_single_assertion {
            issues.push(TestIssue::SingleAssertion);
        }

        if isolation_score < 0.5 {
            // Check specific isolation issues
            if body.contains("global ") || body.contains("static ") {
                issues.push(TestIssue::SharedState);
            }

            // Check for unmocked external dependencies
            for pattern in EXTERNAL_DEP_PATTERNS {
                if body.contains(pattern) && !self.has_mock_for_pattern(body, pattern) {
                    issues.push(TestIssue::UnmockedDependency((*pattern).to_string()));
                    break; // Only report first one
                }
            }
        }

        if boundary_testing_score < 0.3 && self.config.check_boundary_testing {
            issues.push(TestIssue::NoEdgeCases);
        }

        // Check for return value testing
        let has_return_check = assertions.iter().any(|a| {
            a.expression.contains("result")
                || a.expression.contains("return")
                || a.expression.contains("output")
                || a.expression.contains("actual")
        });
        if !has_return_check && assertion_count > 0 {
            issues.push(TestIssue::ReturnValueUnchecked);
        }

        // Check for negative testing
        let has_negative_test = assertions
            .iter()
            .any(|a| matches!(a.assertion_type, AssertionType::Exception))
            || body.contains("raises")
            || body.contains("Throws")
            || body.contains("Error")
            || body.contains("panic");
        if !has_negative_test && assertion_count > 0 {
            issues.push(TestIssue::NoNegativeTesting);
        }

        // Calculate grade
        let grade = self.calculate_grade(assertion_density, &issues);

        TestFunctionQuality {
            name: name.to_string(),
            line: start_line,
            end_line,
            assertion_count,
            assertion_density,
            assertion_types,
            assertions,
            mock_usage,
            isolation_score,
            boundary_testing_score,
            estimated_mutation_score,
            complexity,
            issues,
            grade,
        }
    }

    /// Count assertions in test body.
    fn count_assertions(&self, body: &str, lang: &str) -> Vec<DetectedAssertion> {
        let mut assertions = Vec::new();

        let patterns: &[(&str, AssertionType)] = match lang {
            "python" => PYTHON_ASSERTIONS,
            "javascript" | "typescript" => JS_TS_ASSERTIONS,
            "rust" => RUST_ASSERTIONS,
            "go" => GO_ASSERTIONS,
            "java" => JAVA_ASSERTIONS,
            _ => PYTHON_ASSERTIONS, // Default fallback
        };

        for (line_num, line) in body.lines().enumerate() {
            for (pattern, assertion_type) in patterns {
                if line.contains(pattern) {
                    assertions.push(DetectedAssertion {
                        assertion_type: *assertion_type,
                        line: (line_num + 1) as u32,
                        expression: line.trim().to_string(),
                        checking: self.extract_assertion_target(line, pattern),
                    });
                    break; // Only count one assertion per line
                }
            }
        }

        assertions
    }

    /// Extract what the assertion is checking.
    fn extract_assertion_target(&self, line: &str, _pattern: &str) -> Option<String> {
        // Try to extract the first argument to the assertion
        if let Some(start) = line.find('(') {
            let rest = &line[start + 1..];
            if let Some(end) = rest.find(|c| c == ',' || c == ')') {
                let target = rest[..end].trim();
                if !target.is_empty() {
                    return Some(target.to_string());
                }
            }
        }
        None
    }

    /// Analyze mock usage in test body.
    fn analyze_mock_usage(&self, body: &str) -> MockUsageMetrics {
        let mut mock_count = 0;
        let mut mock_types = Vec::new();
        let mut has_mock_assertions = false;
        let mut uses_dependency_injection = false;

        for pattern in MOCK_PATTERNS {
            if body.contains(pattern) {
                mock_count += 1;
                mock_types.push((*pattern).to_string());

                // Check if the pattern itself is an assertion pattern
                if pattern.contains("assert")
                    || pattern.contains("verify")
                    || pattern.contains("EXPECT")
                {
                    has_mock_assertions = true;
                }
            }
        }

        // Also check for mock assertion patterns directly in the body
        // These are method calls on mock objects that verify behavior
        const MOCK_ASSERTION_PATTERNS: &[&str] = &[
            // Python mock assertions
            "assert_called",
            "assert_called_once",
            "assert_called_with",
            "assert_called_once_with",
            "assert_any_call",
            "assert_has_calls",
            "assert_not_called",
            "call_count",
            // JavaScript/Jest mock assertions
            "toHaveBeenCalled",
            "toHaveBeenCalledTimes",
            "toHaveBeenCalledWith",
            "toHaveBeenLastCalledWith",
            "toHaveBeenNthCalledWith",
            "toHaveReturned",
            "toHaveReturnedWith",
            // Java Mockito
            "verify(",
            "verifyNoInteractions",
            "verifyNoMoreInteractions",
            // Go gomock
            "EXPECT(",
            ".Times(",
            ".Return(",
        ];

        for pattern in MOCK_ASSERTION_PATTERNS {
            if body.contains(pattern) {
                has_mock_assertions = true;
                break;
            }
        }

        // Check for dependency injection patterns
        if body.contains("inject")
            || body.contains("@Inject")
            || body.contains("Container")
            || body.contains("provide")
        {
            uses_dependency_injection = true;
        }

        MockUsageMetrics {
            mock_count,
            has_mock_assertions,
            mock_types,
            uses_dependency_injection,
        }
    }

    /// Calculate isolation score (0-1).
    fn calculate_isolation_score(&self, body: &str) -> f64 {
        let mut penalty: f64 = 0.0;

        // Check for shared state patterns
        for pattern in SHARED_STATE_PATTERNS {
            if body.contains(pattern) {
                penalty += 0.15;
            }
        }

        // Check for external dependencies
        for pattern in EXTERNAL_DEP_PATTERNS {
            if body.contains(pattern) && !self.has_mock_for_pattern(body, pattern) {
                penalty += 0.1;
            }
        }

        // Cap penalty at 1.0
        (1.0 - penalty.min(1.0)).max(0.0)
    }

    /// Check if there's a mock for a given pattern.
    fn has_mock_for_pattern(&self, body: &str, pattern: &str) -> bool {
        // Simplified check - look for mock patterns near the external dep
        for mock_pattern in MOCK_PATTERNS {
            if body.contains(mock_pattern) {
                // Very rough heuristic - if we have mocks, assume they might cover this
                return true;
            }
        }

        // Check for explicit mocking of the pattern
        let pattern_word = pattern
            .split(|c: char| !c.is_alphanumeric())
            .next()
            .unwrap_or("");
        body.contains(&format!("mock_{}", pattern_word.to_lowercase()))
            || body.contains(&format!("Mock{}", pattern_word))
    }

    /// Calculate boundary testing score (0-1).
    fn calculate_boundary_score(&self, body: &str) -> f64 {
        let mut edge_cases_found = HashSet::new();

        for (pattern, category) in BOUNDARY_PATTERNS {
            if body.contains(pattern) {
                edge_cases_found.insert(*category);
            }
        }

        // Score based on number of different edge case categories tested
        // Consider 5+ categories as excellent (1.0)
        let category_count = edge_cases_found.len();
        (category_count as f64 / 5.0).min(1.0)
    }

    /// Estimate mutation score without running mutations.
    fn estimate_mutation_score(&self, assertions: &[DetectedAssertion], body: &str) -> f64 {
        if assertions.is_empty() {
            return 0.0;
        }

        let mut score: f64 = 0.0;
        let mut max_possible: f64 = 0.0;

        // Score based on assertion types
        for assertion in assertions {
            max_possible += 1.0;
            score += match assertion.assertion_type {
                AssertionType::Equality => 0.8,   // Good at catching value mutations
                AssertionType::Comparison => 0.7, // Good at catching boundary mutations
                AssertionType::Exception => 0.9,  // Catches removed error handling
                AssertionType::Contains => 0.6,   // Partial coverage
                AssertionType::Truthiness => 0.5, // Can miss subtle changes
                AssertionType::NullCheck => 0.6,  // Catches null mutations
                AssertionType::TypeCheck => 0.4,  // Limited mutation coverage
                AssertionType::MockAssertion => 0.7, // Catches interaction changes
                AssertionType::Generic => 0.5,    // Unknown effectiveness
            };
        }

        // Bonus for variety of assertion types
        let type_variety = assertions
            .iter()
            .map(|a| a.assertion_type)
            .collect::<HashSet<_>>()
            .len();
        if type_variety >= 3 {
            score += 0.5;
            max_possible += 0.5;
        }

        // Bonus for testing multiple values
        let tests_multiple_values = body.contains("parameterized")
            || body.contains("@pytest.mark.parametrize")
            || body.contains("each(")
            || body.contains(".each(")
            || body.contains("table-driven")
            || body.contains("test_cases");
        if tests_multiple_values {
            score += 0.5;
            max_possible += 0.5;
        }

        // Bonus for property-based testing
        let uses_property_testing = body.contains("hypothesis")
            || body.contains("@given")
            || body.contains("fast-check")
            || body.contains("proptest")
            || body.contains("quickcheck");
        if uses_property_testing {
            score += 1.0;
            max_possible += 1.0;
        }

        if max_possible > 0.0 {
            (score / max_possible).min(1.0)
        } else {
            0.0
        }
    }

    /// Estimate cyclomatic complexity of test.
    fn estimate_complexity(&self, body: &str) -> u32 {
        let mut complexity = 1u32;

        // Count control flow statements
        let control_flow_patterns = [
            "if ", "elif ", "else:", "else {", "for ", "while ", "match ", "switch ", "case ",
            "try:", "try {", "except ", "catch ", "?", "&&", "||",
        ];

        for pattern in &control_flow_patterns {
            complexity += body.matches(pattern).count() as u32;
        }

        complexity
    }

    /// Calculate quality grade based on metrics.
    ///
    /// Grade thresholds (after issue penalties):
    /// - A: assertion_density >= 3.5
    /// - B: assertion_density >= 2.5
    /// - C: assertion_density >= 1.5
    /// - D: assertion_density >= 0.5
    /// - F: assertion_density < 0.5
    fn calculate_grade(&self, assertion_density: f64, issues: &[TestIssue]) -> char {
        // Use actual density for scoring, not bucketed value
        let base_score = assertion_density;

        // Deduct for issues
        let mut penalty: f64 = 0.0;
        for issue in issues {
            penalty += match issue {
                TestIssue::NoAssertions => 4.0,
                TestIssue::SingleAssertion => 1.0,
                TestIssue::NoEdgeCases => 0.5,
                TestIssue::SharedState => 0.5,
                TestIssue::UnmockedDependency(_) => 0.5,
                TestIssue::NoSetupTeardown => 0.25,
                TestIssue::PoorNaming => 0.25,
                TestIssue::TestsTooMuch => 1.0,
                TestIssue::ReturnValueUnchecked => 0.25,
                TestIssue::NoNegativeTesting => 0.25,
            };
        }

        let final_score = (base_score - penalty).max(0.0);

        if final_score >= 3.5 {
            'A'
        } else if final_score >= 2.5 {
            'B'
        } else if final_score >= 1.5 {
            'C'
        } else if final_score >= 0.5 {
            'D'
        } else {
            'F'
        }
    }
}

// =============================================================================
// PUBLIC API
// =============================================================================

/// Analyze test quality for a project or file.
///
/// # Arguments
///
/// * `path` - Path to analyze (file or directory)
/// * `lang` - Language filter (None = auto-detect)
/// * `config` - Analysis configuration (None = default)
///
/// # Returns
///
/// Complete test quality analysis with metrics and suggestions.
pub fn analyze_test_quality(
    path: impl AsRef<Path>,
    lang: Option<&str>,
    config: Option<TestQualityConfig>,
) -> std::result::Result<TestQualityAnalysis, TestQualityError> {
    let path = path.as_ref();
    let config = config.unwrap_or_default();
    let analyzer = TestQualityAnalyzer::new(config.clone());

    // Scan for test files
    let path_str = path
        .to_str()
        .ok_or_else(|| TestQualityError::Path("Invalid path".to_string()))?;
    let scanner =
        ProjectScanner::new(path_str).map_err(|e| TestQualityError::Path(e.to_string()))?;

    let scan_config = ScanConfig {
        language: lang.map(String::from),
        collect_metadata: true,
        ..Default::default()
    };

    let scan_result = scanner
        .scan_with_config(&scan_config)
        .map_err(|e| TestQualityError::Path(e.to_string()))?;

    // Filter to test files only (use metadata for language info)
    let test_files: Vec<_> = scan_result
        .metadata
        .into_iter()
        .filter(|f| is_test_file(&f.path, &config))
        .collect();

    debug!("Found {} test files to analyze", test_files.len());

    // Analyze files in parallel
    let file_results: Vec<_> = test_files
        .par_iter()
        .filter_map(|file| {
            let source = std::fs::read_to_string(&file.path).ok()?;
            // Use explicit language or detected language from scan
            let file_lang = lang.or(file.language.as_deref())?;
            analyzer.analyze_file(&file.path, &source, file_lang).ok()
        })
        .collect();

    // Build weak tests list
    let mut weak_tests = Vec::new();
    for file in &file_results {
        for test in &file.test_functions {
            if !test.issues.is_empty() || test.grade == 'D' || test.grade == 'F' {
                weak_tests.push(WeakTest {
                    function: test.name.clone(),
                    file: file.file.clone(),
                    line: test.line,
                    issues: test.issues.clone(),
                    suggestions: generate_suggestions_for_test(test),
                });
            }
        }
    }

    // Build improvement suggestions
    let mut suggestions: Vec<TestImprovement> = weak_tests
        .iter()
        .flat_map(|weak| {
            weak.issues.iter().map(|issue| {
                let (priority, description, category) = match issue {
                    TestIssue::NoAssertions => (
                        1,
                        "Add assertions to verify expected behavior".to_string(),
                        ImprovementCategory::MoreAssertions,
                    ),
                    TestIssue::SingleAssertion => (
                        3,
                        "Consider adding more assertions for comprehensive testing".to_string(),
                        ImprovementCategory::MoreAssertions,
                    ),
                    TestIssue::NoEdgeCases => (
                        2,
                        "Add tests for boundary conditions (null, empty, max values)".to_string(),
                        ImprovementCategory::EdgeCases,
                    ),
                    TestIssue::SharedState => (
                        2,
                        "Isolate test from shared state, use fixtures or setup methods".to_string(),
                        ImprovementCategory::Isolation,
                    ),
                    TestIssue::UnmockedDependency(dep) => (
                        2,
                        format!("Mock or stub the external dependency: {}", dep),
                        ImprovementCategory::Mocking,
                    ),
                    TestIssue::NoSetupTeardown => (
                        4,
                        "Add proper setup/teardown for test fixtures".to_string(),
                        ImprovementCategory::Isolation,
                    ),
                    TestIssue::PoorNaming => (
                        4,
                        "Rename test to describe the behavior being tested".to_string(),
                        ImprovementCategory::Naming,
                    ),
                    TestIssue::TestsTooMuch => (
                        2,
                        "Split this test into smaller, focused tests".to_string(),
                        ImprovementCategory::SplitTest,
                    ),
                    TestIssue::ReturnValueUnchecked => (
                        3,
                        "Add assertions to verify return values".to_string(),
                        ImprovementCategory::MoreAssertions,
                    ),
                    TestIssue::NoNegativeTesting => (
                        3,
                        "Add tests for error conditions and edge cases".to_string(),
                        ImprovementCategory::NegativeTesting,
                    ),
                };
                TestImprovement {
                    file: weak.file.clone(),
                    function: weak.function.clone(),
                    line: weak.line,
                    priority,
                    description,
                    category,
                }
            })
        })
        .collect();

    // Sort suggestions by priority
    suggestions.sort_by_key(|s| s.priority);

    // Calculate summary statistics
    let summary = calculate_summary(&file_results, &weak_tests);

    Ok(TestQualityAnalysis {
        files: file_results,
        summary,
        weak_tests,
        suggestions,
    })
}

/// Check if a file is a test file.
fn is_test_file(path: &Path, config: &TestQualityConfig) -> bool {
    let path_str = path.to_string_lossy().to_lowercase();

    for pattern in &config.test_file_patterns {
        if path_str.contains(&pattern.to_lowercase()) {
            return true;
        }
    }

    false
}

/// Generate suggestions for a weak test.
fn generate_suggestions_for_test(test: &TestFunctionQuality) -> Vec<String> {
    let mut suggestions = Vec::new();

    if test.assertion_count == 0 {
        suggestions.push("Add at least one assertion to verify expected behavior".to_string());
    } else if test.assertion_count == 1 {
        suggestions
            .push("Consider adding assertions for edge cases and error conditions".to_string());
    }

    if test.boundary_testing_score < 0.3 {
        suggestions
            .push("Test boundary values: null, empty, zero, negative, max values".to_string());
    }

    if test.isolation_score < 0.5 {
        suggestions.push("Improve test isolation by mocking external dependencies".to_string());
    }

    if !test.mock_usage.has_mock_assertions && test.mock_usage.mock_count > 0 {
        suggestions.push("Add assertions to verify mock interactions".to_string());
    }

    if test.estimated_mutation_score < 0.5 {
        suggestions.push("Add more specific assertions to catch subtle code changes".to_string());
    }

    suggestions
}

/// Calculate summary statistics.
fn calculate_summary(files: &[TestFileQuality], weak_tests: &[WeakTest]) -> TestQualitySummary {
    let files_analyzed = files.len() as u32;
    let total_tests: u32 = files.iter().map(|f| f.test_count).sum();

    let avg_assertion_density = if total_tests > 0 {
        files
            .iter()
            .flat_map(|f| &f.test_functions)
            .map(|t| t.assertion_density)
            .sum::<f64>()
            / f64::from(total_tests)
    } else {
        0.0
    };

    let avg_complexity = if total_tests > 0 {
        files
            .iter()
            .flat_map(|f| &f.test_functions)
            .map(|t| f64::from(t.complexity))
            .sum::<f64>()
            / f64::from(total_tests)
    } else {
        0.0
    };

    let avg_isolation_score = if total_tests > 0 {
        files
            .iter()
            .flat_map(|f| &f.test_functions)
            .map(|t| t.isolation_score)
            .sum::<f64>()
            / f64::from(total_tests)
    } else {
        1.0
    };

    let avg_boundary_score = if total_tests > 0 {
        files
            .iter()
            .flat_map(|f| &f.test_functions)
            .map(|t| t.boundary_testing_score)
            .sum::<f64>()
            / f64::from(total_tests)
    } else {
        0.0
    };

    let avg_mutation_score = if total_tests > 0 {
        files
            .iter()
            .flat_map(|f| &f.test_functions)
            .map(|t| t.estimated_mutation_score)
            .sum::<f64>()
            / f64::from(total_tests)
    } else {
        0.0
    };

    // Count grade distribution
    let mut grade_distribution = HashMap::new();
    for file in files {
        for test in &file.test_functions {
            *grade_distribution.entry(test.grade).or_insert(0) += 1;
        }
    }

    // Count common issues
    let mut issue_counts: HashMap<TestIssue, u32> = HashMap::new();
    for weak in weak_tests {
        for issue in &weak.issues {
            *issue_counts.entry(issue.clone()).or_insert(0) += 1;
        }
    }
    let mut common_issues: Vec<(TestIssue, u32)> = issue_counts.into_iter().collect();
    common_issues.sort_by(|a, b| b.1.cmp(&a.1));
    common_issues.truncate(5); // Top 5 issues

    // Calculate overall grade
    let overall_grade =
        if avg_assertion_density >= 4.0 && weak_tests.len() < total_tests as usize / 10 {
            'A'
        } else if avg_assertion_density >= 3.0 && weak_tests.len() < total_tests as usize / 5 {
            'B'
        } else if avg_assertion_density >= 2.0 && weak_tests.len() < total_tests as usize / 3 {
            'C'
        } else if avg_assertion_density >= 1.0 {
            'D'
        } else {
            'F'
        };

    TestQualitySummary {
        files_analyzed,
        total_tests,
        avg_assertion_density,
        avg_complexity,
        avg_isolation_score,
        avg_boundary_score,
        avg_mutation_score,
        weak_test_count: weak_tests.len() as u32,
        grade_distribution,
        common_issues,
        overall_grade,
    }
}

/// Format test quality analysis as human-readable text.
pub fn format_test_quality_report(analysis: &TestQualityAnalysis) -> String {
    let mut output = String::new();

    output.push_str("=== Test Quality Analysis ===\n\n");

    // Summary
    output.push_str(&format!(
        "Files analyzed: {}\n\
         Total tests: {}\n\
         Weak tests: {} ({:.1}%)\n\
         Overall grade: {}\n\n",
        analysis.summary.files_analyzed,
        analysis.summary.total_tests,
        analysis.summary.weak_test_count,
        if analysis.summary.total_tests > 0 {
            f64::from(analysis.summary.weak_test_count) / f64::from(analysis.summary.total_tests)
                * 100.0
        } else {
            0.0
        },
        analysis.summary.overall_grade,
    ));

    output.push_str("--- Metrics ---\n");
    output.push_str(&format!(
        "Avg assertion density: {:.2}\n\
         Avg complexity: {:.2}\n\
         Avg isolation score: {:.2}\n\
         Avg boundary score: {:.2}\n\
         Avg mutation score: {:.2}\n\n",
        analysis.summary.avg_assertion_density,
        analysis.summary.avg_complexity,
        analysis.summary.avg_isolation_score,
        analysis.summary.avg_boundary_score,
        analysis.summary.avg_mutation_score,
    ));

    // Grade distribution
    output.push_str("--- Grade Distribution ---\n");
    for grade in ['A', 'B', 'C', 'D', 'F'] {
        let count = analysis
            .summary
            .grade_distribution
            .get(&grade)
            .unwrap_or(&0);
        output.push_str(&format!("  {}: {}\n", grade, count));
    }
    output.push('\n');

    // Common issues
    if !analysis.summary.common_issues.is_empty() {
        output.push_str("--- Common Issues ---\n");
        for (issue, count) in &analysis.summary.common_issues {
            output.push_str(&format!("  {:?}: {}\n", issue, count));
        }
        output.push('\n');
    }

    // Weak tests
    if !analysis.weak_tests.is_empty() {
        output.push_str("--- Weak Tests ---\n");
        for weak in analysis.weak_tests.iter().take(10) {
            output.push_str(&format!(
                "  {}:{} - {}\n",
                weak.file.display(),
                weak.line,
                weak.function
            ));
            for issue in &weak.issues {
                output.push_str(&format!("    - {:?}\n", issue));
            }
        }
        if analysis.weak_tests.len() > 10 {
            output.push_str(&format!(
                "  ... and {} more\n",
                analysis.weak_tests.len() - 10
            ));
        }
        output.push('\n');
    }

    // Top suggestions
    if !analysis.suggestions.is_empty() {
        output.push_str("--- Top Improvement Suggestions ---\n");
        for suggestion in analysis.suggestions.iter().take(5) {
            output.push_str(&format!(
                "  [P{}] {}:{} {}\n    {}\n",
                suggestion.priority,
                suggestion.file.display(),
                suggestion.line,
                suggestion.function,
                suggestion.description
            ));
        }
    }

    output
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = TestQualityConfig::default();
        assert!((config.min_assertion_density - 2.0).abs() < f64::EPSILON);
        assert!(config.flag_single_assertion);
        assert_eq!(config.max_external_deps, 0);
    }

    #[test]
    fn test_strict_config() {
        let config = TestQualityConfig::strict();
        assert!((config.min_assertion_density - 3.0).abs() < f64::EPSILON);
        assert_eq!(config.min_test_lines, 3);
    }

    #[test]
    fn test_lenient_config() {
        let config = TestQualityConfig::lenient();
        assert!((config.min_assertion_density - 1.0).abs() < f64::EPSILON);
        assert!(!config.flag_single_assertion);
    }

    #[test]
    fn test_count_python_assertions() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());
        let body = r#"
def test_something():
    result = compute()
    assert result == 42
    self.assertEqual(result, 42)
    self.assertTrue(result > 0)
    with pytest.raises(ValueError):
        bad_function()
"#;
        let assertions = analyzer.count_assertions(body, "python");
        assert_eq!(assertions.len(), 4);

        let types: Vec<_> = assertions.iter().map(|a| a.assertion_type).collect();
        assert!(types.contains(&AssertionType::Generic));
        assert!(types.contains(&AssertionType::Equality));
        assert!(types.contains(&AssertionType::Truthiness));
        assert!(types.contains(&AssertionType::Exception));
    }

    #[test]
    fn test_count_rust_assertions() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());
        let body = r#"
#[test]
fn test_something() {
    let result = compute();
    assert!(result > 0);
    assert_eq!(result, 42);
    assert_ne!(result, 0);
}
"#;
        let assertions = analyzer.count_assertions(body, "rust");
        assert_eq!(assertions.len(), 3);
    }

    #[test]
    fn test_count_js_assertions() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());
        let body = r#"
it('should work', () => {
    const result = compute();
    expect(result).toBe(42);
    expect(result).toBeTruthy();
    expect(() => badFunction()).toThrow();
});
"#;
        let assertions = analyzer.count_assertions(body, "javascript");
        assert_eq!(assertions.len(), 3);
    }

    #[test]
    fn test_count_go_assertions() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());
        let body = r#"
func TestSomething(t *testing.T) {
    result := compute()
    assert.Equal(t, 42, result)
    assert.True(t, result > 0)
    assert.NoError(t, err)
}
"#;
        let assertions = analyzer.count_assertions(body, "go");
        assert_eq!(assertions.len(), 3);
    }

    #[test]
    fn test_isolation_score_clean() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());
        let body = r#"
def test_isolated():
    result = pure_function(42)
    assert result == expected
"#;
        let score = analyzer.calculate_isolation_score(body);
        assert!(score > 0.9, "Clean test should have high isolation score");
    }

    #[test]
    fn test_isolation_score_with_global() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());
        let body = r#"
def test_with_global():
    global state
    state = 42
    result = function_using_state()
    assert result == expected
"#;
        let score = analyzer.calculate_isolation_score(body);
        assert!(score < 0.9, "Test with global should have lower isolation");
    }

    #[test]
    fn test_boundary_score() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());
        let body = r#"
def test_boundaries():
    assert func(None) is None
    assert func("") == ""
    assert func([]) == []
    assert func(0) == 0
    assert func(-1) < 0
"#;
        let score = analyzer.calculate_boundary_score(body);
        assert!(score > 0.5, "Test with boundary values should score well");
    }

    #[test]
    fn test_mutation_score_estimation() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());

        // Strong test with varied assertions
        let assertions = vec![
            DetectedAssertion {
                assertion_type: AssertionType::Equality,
                line: 1,
                expression: "assert_eq!(result, 42)".to_string(),
                checking: Some("result".to_string()),
            },
            DetectedAssertion {
                assertion_type: AssertionType::Comparison,
                line: 2,
                expression: "assert!(result > 0)".to_string(),
                checking: Some("result".to_string()),
            },
            DetectedAssertion {
                assertion_type: AssertionType::Exception,
                line: 3,
                expression: "#[should_panic]".to_string(),
                checking: None,
            },
        ];
        let score = analyzer.estimate_mutation_score(&assertions, "");
        assert!(
            score > 0.6,
            "Varied assertions should have good mutation score"
        );

        // Weak test with single assertion
        let weak_assertions = vec![DetectedAssertion {
            assertion_type: AssertionType::Truthiness,
            line: 1,
            expression: "assert!(true)".to_string(),
            checking: None,
        }];
        let weak_score = analyzer.estimate_mutation_score(&weak_assertions, "");
        assert!(
            weak_score < score,
            "Single truthiness assertion should have lower score"
        );
    }

    #[test]
    fn test_grade_calculation() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());

        // Excellent test (5.0 >= 3.5 -> 'A')
        assert_eq!(analyzer.calculate_grade(5.0, &[]), 'A');

        // Good test (3.5 >= 3.5 -> 'A')
        assert_eq!(analyzer.calculate_grade(3.5, &[]), 'A');

        // Average test (2.5 >= 2.5 -> 'B')
        assert_eq!(analyzer.calculate_grade(2.5, &[]), 'B');

        // Below average (2.0 >= 1.5 -> 'C')
        assert_eq!(analyzer.calculate_grade(2.0, &[]), 'C');

        // Poor test (1.0 >= 0.5 -> 'D')
        assert_eq!(analyzer.calculate_grade(1.0, &[]), 'D');

        // Test with issues: 3.0 - 1.5 (SingleAssertion + NoEdgeCases) = 1.5 -> 'C'
        let issues = vec![TestIssue::SingleAssertion, TestIssue::NoEdgeCases];
        assert_eq!(analyzer.calculate_grade(3.0, &issues), 'C');

        // No assertions: 0.0 - 4.0 = -4.0 clamped to 0.0 -> 'F'
        let no_assertions = vec![TestIssue::NoAssertions];
        assert_eq!(analyzer.calculate_grade(0.0, &no_assertions), 'F');
    }

    #[test]
    fn test_mock_usage_detection() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());

        let body_with_mocks = r#"
@patch('module.function')
def test_with_mock(mock_func):
    mock_func.return_value = 42
    result = call_function()
    mock_func.assert_called_once()
    assert result == 42
"#;
        let metrics = analyzer.analyze_mock_usage(body_with_mocks);
        assert!(metrics.mock_count > 0);
        assert!(metrics.has_mock_assertions);
    }

    #[test]
    fn test_is_test_file() {
        let config = TestQualityConfig::default();

        assert!(is_test_file(Path::new("test_module.py"), &config));
        assert!(is_test_file(Path::new("module_test.py"), &config));
        assert!(is_test_file(Path::new("tests/unit.py"), &config));
        assert!(is_test_file(
            Path::new("src/__tests__/app.test.js"),
            &config
        ));
        assert!(is_test_file(Path::new("app.spec.ts"), &config));

        assert!(!is_test_file(Path::new("src/module.py"), &config));
        assert!(!is_test_file(Path::new("main.rs"), &config));
    }

    #[test]
    fn test_complexity_estimation() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());

        let simple_body = "assert x == 1";
        assert_eq!(analyzer.estimate_complexity(simple_body), 1);

        let complex_body = r#"
if condition:
    if nested:
        for item in items:
            if check:
                result = process()
"#;
        assert!(analyzer.estimate_complexity(complex_body) > 3);
    }

    #[test]
    fn test_analyze_test_function() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());

        let body = r#"
def test_something():
    result = compute(42)
    assert result is not None
    assert result > 0
    assert result == 84
"#;
        let quality = analyzer.analyze_test_function("test_something", 1, 6, body, "python");

        assert_eq!(quality.name, "test_something");
        assert_eq!(quality.assertion_count, 3);
        assert!(quality.assertion_density > 0.0);
        assert!(quality.issues.is_empty() || !quality.issues.contains(&TestIssue::NoAssertions));
    }

    #[test]
    fn test_property_based_testing_bonus() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());

        // With property-based testing
        let body_with_hypothesis = r#"
@given(integers())
def test_property(x):
    assert func(x) >= 0
"#;
        let assertions = analyzer.count_assertions(body_with_hypothesis, "python");
        let score_with_pbt = analyzer.estimate_mutation_score(&assertions, body_with_hypothesis);

        // Without property-based testing
        let body_without = r#"
def test_simple():
    assert func(1) >= 0
"#;
        let assertions2 = analyzer.count_assertions(body_without, "python");
        let score_without = analyzer.estimate_mutation_score(&assertions2, body_without);

        assert!(
            score_with_pbt > score_without,
            "Property-based testing should boost mutation score"
        );
    }

    #[test]
    fn test_parameterized_test_bonus() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());

        let body = r#"
@pytest.mark.parametrize("input,expected", [
    (1, 2),
    (2, 4),
    (0, 0),
    (-1, -2),
])
def test_double(input, expected):
    assert double(input) == expected
"#;
        let assertions = analyzer.count_assertions(body, "python");
        let score = analyzer.estimate_mutation_score(&assertions, body);

        assert!(
            score > 0.5,
            "Parameterized tests should have higher mutation score"
        );
    }

    #[test]
    fn test_weak_test_detection() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());

        // Test with no assertions
        let empty_body = r#"
def test_nothing():
    result = compute()
    # Oops, forgot to assert!
"#;
        let quality = analyzer.analyze_test_function("test_nothing", 1, 4, empty_body, "python");
        assert!(quality.issues.contains(&TestIssue::NoAssertions));
        assert_eq!(quality.grade, 'F');

        // Test with single assertion
        let single_assert = r#"
def test_one():
    assert compute() == 42
"#;
        let quality2 = analyzer.analyze_test_function("test_one", 1, 3, single_assert, "python");
        assert!(quality2.issues.contains(&TestIssue::SingleAssertion));
    }

    #[test]
    fn test_format_report() {
        let analysis = TestQualityAnalysis {
            files: vec![],
            summary: TestQualitySummary {
                files_analyzed: 5,
                total_tests: 20,
                avg_assertion_density: 3.5,
                avg_complexity: 2.0,
                avg_isolation_score: 0.85,
                avg_boundary_score: 0.6,
                avg_mutation_score: 0.7,
                weak_test_count: 3,
                grade_distribution: [('A', 10), ('B', 5), ('C', 3), ('D', 1), ('F', 1)]
                    .into_iter()
                    .collect(),
                common_issues: vec![(TestIssue::SingleAssertion, 2), (TestIssue::NoEdgeCases, 1)],
                overall_grade: 'B',
            },
            weak_tests: vec![],
            suggestions: vec![],
        };

        let report = format_test_quality_report(&analysis);

        assert!(report.contains("Test Quality Analysis"));
        assert!(report.contains("Files analyzed: 5"));
        assert!(report.contains("Total tests: 20"));
        assert!(report.contains("Overall grade: B"));
        assert!(report.contains("Avg assertion density: 3.50"));
    }

    #[test]
    fn test_java_assertions() {
        let analyzer = TestQualityAnalyzer::new(TestQualityConfig::default());
        let body = r#"
@Test
public void testSomething() {
    Result result = compute();
    assertEquals(42, result.getValue());
    assertTrue(result.isValid());
    assertThrows(IllegalArgumentException.class, () -> badCall());
    verify(mockService).wasCalledOnce();
}
"#;
        let assertions = analyzer.count_assertions(body, "java");
        assert_eq!(assertions.len(), 4);

        let has_mock_assertion = assertions
            .iter()
            .any(|a| a.assertion_type == AssertionType::MockAssertion);
        assert!(
            has_mock_assertion,
            "Should detect verify() as mock assertion"
        );
    }
}
