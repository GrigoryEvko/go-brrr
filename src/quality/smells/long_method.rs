//! Long Method detection for identifying methods that are too long and complex.
//!
//! A long method is a code smell where a function/method does too much work,
//! making it difficult to understand, test, and maintain. This module provides
//! comprehensive detection with context-aware analysis and actionable refactoring
//! suggestions.
//!
//! # Detection Criteria
//!
//! Methods are flagged when they exceed configurable thresholds:
//!
//! | Metric            | Default Threshold | Description                        |
//! |-------------------|-------------------|------------------------------------|
//! | Lines of code     | 30                | Total SLOC in the method           |
//! | Statements        | 25                | Number of AST statement nodes      |
//! | Local variables   | 10                | Variables declared in the method   |
//! | Cyclomatic complexity | 10            | Number of decision points + 1      |
//! | Max nesting depth | 4                 | Deepest nesting level              |
//!
//! # Context-Aware Analysis
//!
//! The detector recognizes special method categories and adjusts thresholds:
//!
//! - **Test methods**: Often have long setup/assertion phases
//! - **Configuration methods**: May legitimately initialize many values
//! - **Factory methods**: May construct complex objects
//! - **Constructors**: May need many parameters for dependency injection
//!
//! # Extraction Candidates
//!
//! The analyzer identifies code blocks that could be extracted:
//!
//! - **Consecutive statements** with shared variables (cohesive blocks)
//! - **Loop bodies** that perform complex operations
//! - **Conditional branches** with substantial logic
//! - **Try/except blocks** with complex error handling
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::quality::smells::{detect_long_methods, LongMethodConfig};
//!
//! let result = detect_long_methods("./src", None, None)?;
//! for finding in &result.findings {
//!     println!("{} at {}:{}", finding.function_name, finding.file.display(), finding.line);
//!     println!("  Lines: {}, Complexity: {}", finding.length.lines, finding.complexity.cyclomatic);
//!     for suggestion in &finding.suggestions {
//!         println!("  Suggestion: {}", suggestion.description);
//!         if let Some((start, end)) = suggestion.line_range {
//!             println!("    Extraction: lines {}-{}", start, end);
//!         }
//!     }
//! }
//! ```

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::debug;
use tree_sitter::{Node, Tree};

use crate::ast::AstExtractor;
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;
use crate::metrics::node_types::{
    FUNCTION_NODE_TYPES, STATEMENT_NODE_TYPES, VARIABLE_DECL_TYPES,
};

// =============================================================================
// CONFIGURATION
// =============================================================================

/// Configuration for long method detection thresholds.
///
/// All thresholds are adjustable. Methods are flagged when ANY threshold
/// is exceeded, allowing fine-grained control over what constitutes "long".
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LongMethodConfig {
    /// Maximum source lines of code (excluding blanks/comments)
    /// Default: 30 lines
    pub max_lines: u32,

    /// Maximum number of statements
    /// Default: 25 statements
    pub max_statements: u32,

    /// Maximum number of local variables
    /// Default: 10 variables
    pub max_variables: u32,

    /// Maximum cyclomatic complexity (decision points + 1)
    /// Default: 10
    pub max_complexity: u32,

    /// Maximum nesting depth
    /// Default: 4 levels
    pub max_nesting: u32,

    /// Maximum number of parameters
    /// Default: 5 parameters
    pub max_parameters: u32,

    /// Minimum lines for a method to be analyzed (skip trivial methods)
    /// Default: 5 lines
    pub min_lines_for_analysis: u32,

    /// Whether to apply context-aware threshold adjustments
    /// Default: true
    pub context_aware: bool,
}

impl Default for LongMethodConfig {
    fn default() -> Self {
        Self {
            max_lines: 30,
            max_statements: 25,
            max_variables: 10,
            max_complexity: 10,
            max_nesting: 4,
            max_parameters: 5,
            min_lines_for_analysis: 5,
            context_aware: true,
        }
    }
}

impl LongMethodConfig {
    /// Create a strict configuration for high-quality code.
    #[must_use]
    pub fn strict() -> Self {
        Self {
            max_lines: 20,
            max_statements: 15,
            max_variables: 6,
            max_complexity: 6,
            max_nesting: 3,
            max_parameters: 4,
            min_lines_for_analysis: 3,
            context_aware: true,
        }
    }

    /// Create a lenient configuration for legacy code.
    #[must_use]
    pub fn lenient() -> Self {
        Self {
            max_lines: 50,
            max_statements: 40,
            max_variables: 15,
            max_complexity: 15,
            max_nesting: 5,
            max_parameters: 8,
            min_lines_for_analysis: 10,
            context_aware: true,
        }
    }

    /// Adjust thresholds for test methods.
    fn adjust_for_tests(&self) -> Self {
        Self {
            max_lines: self.max_lines + 30, // Tests often have long setup
            max_statements: self.max_statements + 20,
            max_variables: self.max_variables + 10, // Many fixtures
            max_complexity: self.max_complexity + 5,
            max_nesting: self.max_nesting + 1,
            max_parameters: self.max_parameters + 3,
            min_lines_for_analysis: self.min_lines_for_analysis,
            context_aware: self.context_aware,
        }
    }

    /// Adjust thresholds for configuration/setup methods.
    fn adjust_for_configuration(&self) -> Self {
        Self {
            max_lines: self.max_lines + 20,
            max_statements: self.max_statements + 20,
            max_variables: self.max_variables + 15, // Many config values
            max_complexity: self.max_complexity,
            max_nesting: self.max_nesting,
            max_parameters: self.max_parameters,
            min_lines_for_analysis: self.min_lines_for_analysis,
            context_aware: self.context_aware,
        }
    }

    /// Adjust thresholds for factory methods.
    fn adjust_for_factory(&self) -> Self {
        Self {
            max_lines: self.max_lines + 10,
            max_statements: self.max_statements + 10,
            max_variables: self.max_variables + 5,
            max_complexity: self.max_complexity + 3,
            max_nesting: self.max_nesting,
            max_parameters: self.max_parameters + 3,
            min_lines_for_analysis: self.min_lines_for_analysis,
            context_aware: self.context_aware,
        }
    }

    /// Adjust thresholds for constructor/initializer methods.
    fn adjust_for_constructor(&self) -> Self {
        Self {
            max_lines: self.max_lines + 15,
            max_statements: self.max_statements + 15,
            max_variables: self.max_variables + 10, // DI setup
            max_complexity: self.max_complexity,
            max_nesting: self.max_nesting,
            max_parameters: self.max_parameters + 5, // DI parameters
            min_lines_for_analysis: self.min_lines_for_analysis,
            context_aware: self.context_aware,
        }
    }
}

// =============================================================================
// METRICS TYPES
// =============================================================================

/// Length-based metrics for a method.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LengthMetrics {
    /// Source lines of code (excluding blanks and comments)
    pub lines: u32,

    /// Number of statements in the method
    pub statements: u32,

    /// Number of local variables declared
    pub variables: u32,

    /// Number of parameters (excluding self/this)
    pub parameters: u32,

    /// Total line span (end_line - start_line + 1)
    pub total_span: u32,
}

/// Complexity-based metrics for a method.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityMetrics {
    /// Cyclomatic complexity (decision points + 1)
    pub cyclomatic: u32,

    /// Maximum nesting depth
    pub max_nesting: u32,

    /// Average nesting depth
    pub average_nesting: f64,

    /// Number of return/exit points
    pub exit_points: u32,

    /// Number of conditional branches
    pub branches: u32,

    /// Number of loops (for, while, etc.)
    pub loops: u32,

    /// Number of boolean operators (&&, ||, and, or)
    pub boolean_operators: u32,
}

/// Method category for context-aware analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MethodCategory {
    /// Regular method
    Normal,
    /// Test method (test_*, *_test)
    Test,
    /// Constructor/initializer (__init__, new, constructor)
    Constructor,
    /// Configuration/setup method
    Configuration,
    /// Factory method (create_*, build_*, make_*)
    Factory,
    /// Event handler/callback
    Handler,
}

impl MethodCategory {
    /// Detect category from method name.
    #[must_use]
    pub fn from_name(name: &str) -> Self {
        let lower = name.to_lowercase();

        // Test patterns
        if lower.starts_with("test_")
            || lower.starts_with("test")
            || lower.ends_with("_test")
            || lower.ends_with("test")
            || lower.starts_with("spec_")
            || lower.ends_with("_spec")
            || lower.starts_with("it_")
            || lower.starts_with("describe_")
            || lower.starts_with("should_")
        {
            return Self::Test;
        }

        // Constructor patterns
        if lower == "__init__"
            || lower == "new"
            || lower == "constructor"
            || lower == "init"
            || lower.starts_with("init_")
            || lower.ends_with("_init")
        {
            return Self::Constructor;
        }

        // Configuration patterns
        if lower.starts_with("configure_")
            || lower.starts_with("config_")
            || lower.starts_with("setup_")
            || lower.starts_with("setup")
            || lower.ends_with("_setup")
            || lower == "setup"
            || lower.starts_with("initialize_")
        {
            return Self::Configuration;
        }

        // Factory patterns
        if lower.starts_with("create_")
            || lower.starts_with("make_")
            || lower.starts_with("build_")
            || lower.starts_with("new_")
            || lower.ends_with("_factory")
            || lower.starts_with("from_")
        {
            return Self::Factory;
        }

        // Handler patterns
        if lower.starts_with("on_")
            || lower.starts_with("handle_")
            || lower.ends_with("_handler")
            || lower.ends_with("_callback")
            || lower.ends_with("_listener")
        {
            return Self::Handler;
        }

        Self::Normal
    }

    /// Get description for display.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Normal => "method",
            Self::Test => "test method",
            Self::Constructor => "constructor",
            Self::Configuration => "configuration method",
            Self::Factory => "factory method",
            Self::Handler => "event handler",
        }
    }
}

impl std::fmt::Display for MethodCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description())
    }
}

// =============================================================================
// REFACTORING SUGGESTIONS
// =============================================================================

/// Type of refactoring suggestion.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RefactoringType {
    /// Extract a section into a new method
    ExtractMethod,
    /// Replace a temporary variable with a query method
    ReplaceTempWithQuery,
    /// Decompose a complex conditional into smaller pieces
    DecomposeConditional,
    /// Convert loop to functional operations (map, filter, etc.)
    ReplaceLoopWithPipeline,
    /// Extract a guard clause to simplify main logic
    ExtractGuardClause,
    /// Move setup code to dedicated method
    ExtractSetup,
    /// Extract validation logic
    ExtractValidation,
    /// Split method by responsibility
    SplitByResponsibility,
    /// Introduce parameter object to reduce parameters
    IntroduceParameterObject,
    /// General simplification suggestion
    Simplify,
}

impl std::fmt::Display for RefactoringType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExtractMethod => write!(f, "Extract Method"),
            Self::ReplaceTempWithQuery => write!(f, "Replace Temp with Query"),
            Self::DecomposeConditional => write!(f, "Decompose Conditional"),
            Self::ReplaceLoopWithPipeline => write!(f, "Replace Loop with Pipeline"),
            Self::ExtractGuardClause => write!(f, "Extract Guard Clause"),
            Self::ExtractSetup => write!(f, "Extract Setup"),
            Self::ExtractValidation => write!(f, "Extract Validation"),
            Self::SplitByResponsibility => write!(f, "Split by Responsibility"),
            Self::IntroduceParameterObject => write!(f, "Introduce Parameter Object"),
            Self::Simplify => write!(f, "Simplify"),
        }
    }
}

/// A refactoring suggestion for reducing method length/complexity.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RefactoringSuggestion {
    /// Type of refactoring
    pub refactoring_type: RefactoringType,

    /// Human-readable description of what to do
    pub description: String,

    /// Optional line range for extraction (start, end)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_range: Option<(usize, usize)>,

    /// Suggested name for extracted method
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggested_name: Option<String>,

    /// Variables that would need to be passed as parameters
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub required_parameters: Vec<String>,

    /// Variable returned by extracted method (if any)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub return_variable: Option<String>,

    /// Confidence score (0.0 - 1.0)
    pub confidence: f64,

    /// Priority for this refactoring (higher = more impactful)
    pub priority: u32,
}

impl RefactoringSuggestion {
    /// Create a simple extract method suggestion.
    fn extract_method(
        start_line: usize,
        end_line: usize,
        suggested_name: Option<String>,
        description: String,
        confidence: f64,
    ) -> Self {
        Self {
            refactoring_type: RefactoringType::ExtractMethod,
            description,
            line_range: Some((start_line, end_line)),
            suggested_name,
            required_parameters: Vec::new(),
            return_variable: None,
            confidence,
            priority: 5,
        }
    }

    /// Create a guard clause extraction suggestion.
    fn extract_guard(line: usize, condition: &str) -> Self {
        Self {
            refactoring_type: RefactoringType::ExtractGuardClause,
            description: format!("Extract early return for condition: {}", condition),
            line_range: Some((line, line)),
            suggested_name: None,
            required_parameters: Vec::new(),
            return_variable: None,
            confidence: 0.8,
            priority: 7,
        }
    }

    /// Create a decompose conditional suggestion.
    fn decompose_conditional(start_line: usize, end_line: usize, branches: u32) -> Self {
        Self {
            refactoring_type: RefactoringType::DecomposeConditional,
            description: format!(
                "Decompose complex conditional with {} branches into separate methods",
                branches
            ),
            line_range: Some((start_line, end_line)),
            suggested_name: None,
            required_parameters: Vec::new(),
            return_variable: None,
            confidence: 0.75,
            priority: 6,
        }
    }
}

// =============================================================================
// EXTRACTION CANDIDATES
// =============================================================================

/// Type of code block that could be extracted.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BlockType {
    /// Consecutive statements forming a logical unit
    StatementBlock,
    /// Loop body
    LoopBody,
    /// Conditional branch (then or else)
    ConditionalBranch,
    /// Try block
    TryBlock,
    /// Except/catch handler
    ExceptionHandler,
    /// Validation/guard section
    ValidationBlock,
    /// Setup/initialization section
    SetupBlock,
    /// Cleanup/teardown section
    CleanupBlock,
}

/// A candidate block that could be extracted into a separate method.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExtractionCandidate {
    /// Type of block
    pub block_type: BlockType,

    /// Starting line number
    pub start_line: usize,

    /// Ending line number
    pub end_line: usize,

    /// Number of statements in this block
    pub statement_count: u32,

    /// Variables defined in this block
    pub defined_variables: Vec<String>,

    /// Variables used from outer scope
    pub used_variables: Vec<String>,

    /// Variables used after this block (potential returns)
    pub live_out_variables: Vec<String>,

    /// Suggested name based on content analysis
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggested_name: Option<String>,

    /// Extraction viability score (0.0 - 1.0)
    pub viability_score: f64,

    /// Reason for the suggested extraction
    pub reason: String,
}

// =============================================================================
// SEVERITY
// =============================================================================

/// Severity level for long method findings.
///
/// Ordered from least to most severe (Minor < Moderate < Major < Critical).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LongMethodSeverity {
    /// Minor issue, consider refactoring when convenient
    Minor,
    /// Moderate issue, should be addressed
    Moderate,
    /// Major issue, prioritize refactoring
    Major,
    /// Critical issue, refactor immediately
    Critical,
}

impl LongMethodSeverity {
    /// Calculate severity from violation counts.
    fn from_violations(
        lines_exceeded: bool,
        complexity_exceeded: bool,
        nesting_exceeded: bool,
        variables_exceeded: bool,
    ) -> Self {
        let count = [
            lines_exceeded,
            complexity_exceeded,
            nesting_exceeded,
            variables_exceeded,
        ]
        .iter()
        .filter(|&&x| x)
        .count();

        match count {
            0 => Self::Minor,
            1 => Self::Moderate,
            2 => Self::Major,
            _ => Self::Critical,
        }
    }

    /// Get ANSI color code for CLI output.
    #[must_use]
    pub const fn color_code(&self) -> &'static str {
        match self {
            Self::Minor => "\x1b[33m",    // Yellow
            Self::Moderate => "\x1b[91m", // Light red
            Self::Major => "\x1b[31m",    // Red
            Self::Critical => "\x1b[35m", // Magenta
        }
    }

    /// Get human-readable description.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Minor => "Consider refactoring when convenient",
            Self::Moderate => "Should be refactored",
            Self::Major => "Prioritize refactoring",
            Self::Critical => "Refactor immediately",
        }
    }
}

impl std::fmt::Display for LongMethodSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Minor => write!(f, "minor"),
            Self::Moderate => write!(f, "moderate"),
            Self::Major => write!(f, "major"),
            Self::Critical => write!(f, "critical"),
        }
    }
}

// =============================================================================
// FINDING STRUCTURE
// =============================================================================

/// Specific threshold violation detected.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Violation {
    /// Method exceeds line count threshold
    TooLong { lines: u32, threshold: u32 },
    /// Method has too many statements
    TooManyStatements { count: u32, threshold: u32 },
    /// Method has too many local variables
    TooManyVariables { count: u32, threshold: u32 },
    /// Method has too many parameters
    TooManyParameters { count: u32, threshold: u32 },
    /// Method complexity is too high
    TooComplex { complexity: u32, threshold: u32 },
    /// Method nesting is too deep
    TooDeep { depth: u32, threshold: u32 },
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooLong { lines, threshold } => {
                write!(f, "Too long: {} lines (threshold: {})", lines, threshold)
            }
            Self::TooManyStatements { count, threshold } => {
                write!(
                    f,
                    "Too many statements: {} (threshold: {})",
                    count, threshold
                )
            }
            Self::TooManyVariables { count, threshold } => {
                write!(
                    f,
                    "Too many variables: {} (threshold: {})",
                    count, threshold
                )
            }
            Self::TooManyParameters { count, threshold } => {
                write!(
                    f,
                    "Too many parameters: {} (threshold: {})",
                    count, threshold
                )
            }
            Self::TooComplex {
                complexity,
                threshold,
            } => {
                write!(f, "Too complex: {} (threshold: {})", complexity, threshold)
            }
            Self::TooDeep { depth, threshold } => {
                write!(f, "Too deep nesting: {} (threshold: {})", depth, threshold)
            }
        }
    }
}

/// A long method finding with full context.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LongMethodFinding {
    /// Function/method name (may include class prefix)
    pub function_name: String,

    /// File path containing the method
    pub file: PathBuf,

    /// Starting line number (1-indexed)
    pub line: usize,

    /// Ending line number (1-indexed)
    pub end_line: usize,

    /// Length-based metrics
    pub length: LengthMetrics,

    /// Complexity-based metrics
    pub complexity: ComplexityMetrics,

    /// Detected method category
    pub category: MethodCategory,

    /// Severity assessment
    pub severity: LongMethodSeverity,

    /// List of specific violations
    pub violations: Vec<Violation>,

    /// Refactoring suggestions
    pub suggestions: Vec<RefactoringSuggestion>,

    /// Extraction candidates identified
    pub extraction_candidates: Vec<ExtractionCandidate>,

    /// Overall score (higher = worse)
    pub score: f64,
}

impl LongMethodFinding {
    /// Calculate overall score from metrics.
    fn calculate_score(length: &LengthMetrics, complexity: &ComplexityMetrics) -> f64 {
        // Weighted combination of metrics
        let line_score = f64::from(length.lines) * 1.0;
        let statement_score = f64::from(length.statements) * 0.8;
        let variable_score = f64::from(length.variables) * 1.5;
        let complexity_score = f64::from(complexity.cyclomatic) * 2.0;
        let nesting_score = f64::from(complexity.max_nesting) * 3.0;

        line_score + statement_score + variable_score + complexity_score + nesting_score
    }
}

// =============================================================================
// ANALYSIS RESULT
// =============================================================================

/// Statistics for long method analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LongMethodStats {
    /// Total methods analyzed
    pub total_methods: usize,

    /// Methods flagged as long
    pub long_methods: usize,

    /// Percentage of methods flagged
    pub percentage_long: f64,

    /// Average SLOC across all methods
    pub average_lines: f64,

    /// Maximum SLOC found
    pub max_lines: u32,

    /// Average complexity
    pub average_complexity: f64,

    /// Maximum complexity found
    pub max_complexity: u32,

    /// Severity distribution
    pub severity_distribution: HashMap<String, usize>,

    /// Violation type counts
    pub violation_counts: HashMap<String, usize>,
}

impl LongMethodStats {
    /// Calculate statistics from findings.
    fn from_findings(
        total_methods: usize,
        findings: &[LongMethodFinding],
        all_lines: &[u32],
        all_complexity: &[u32],
    ) -> Self {
        let long_methods = findings.len();
        let percentage_long = if total_methods > 0 {
            (long_methods as f64 / total_methods as f64) * 100.0
        } else {
            0.0
        };

        let (average_lines, max_lines) = if all_lines.is_empty() {
            (0.0, 0)
        } else {
            let sum: u64 = all_lines.iter().map(|&l| u64::from(l)).sum();
            (
                sum as f64 / all_lines.len() as f64,
                *all_lines.iter().max().unwrap_or(&0),
            )
        };

        let (average_complexity, max_complexity) = if all_complexity.is_empty() {
            (0.0, 0)
        } else {
            let sum: u64 = all_complexity.iter().map(|&c| u64::from(c)).sum();
            (
                sum as f64 / all_complexity.len() as f64,
                *all_complexity.iter().max().unwrap_or(&0),
            )
        };

        let mut severity_distribution = HashMap::new();
        let mut violation_counts = HashMap::new();

        for finding in findings {
            *severity_distribution
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;

            for violation in &finding.violations {
                let key = match violation {
                    Violation::TooLong { .. } => "too_long",
                    Violation::TooManyStatements { .. } => "too_many_statements",
                    Violation::TooManyVariables { .. } => "too_many_variables",
                    Violation::TooManyParameters { .. } => "too_many_parameters",
                    Violation::TooComplex { .. } => "too_complex",
                    Violation::TooDeep { .. } => "too_deep",
                };
                *violation_counts.entry(key.to_string()).or_insert(0) += 1;
            }
        }

        Self {
            total_methods,
            long_methods,
            percentage_long,
            average_lines,
            max_lines,
            average_complexity,
            max_complexity,
            severity_distribution,
            violation_counts,
        }
    }
}

/// Complete long method analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LongMethodAnalysis {
    /// Path that was analyzed
    pub path: PathBuf,

    /// Language filter applied
    #[serde(skip_serializing_if = "Option::is_none")]
    pub language: Option<String>,

    /// Long method findings
    pub findings: Vec<LongMethodFinding>,

    /// Aggregate statistics
    pub stats: LongMethodStats,

    /// Configuration used
    pub config: LongMethodConfig,

    /// Analysis errors
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<LongMethodError>,
}

/// Error encountered during analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LongMethodError {
    /// File path
    pub file: PathBuf,
    /// Error message
    pub message: String,
}

// =============================================================================
// AST ANALYSIS
// =============================================================================

/// Node types for decision points (cyclomatic complexity).
const DECISION_NODES: &[&str] = &[
    "if_statement",
    "if_expression",
    "elif_clause",
    "else_if_clause",
    "for_statement",
    "for_expression",
    "for_in_statement",
    "enhanced_for_statement",
    "while_statement",
    "while_expression",
    "switch_statement",
    "switch_expression",
    "match_expression",
    "match_statement",
    "case_clause",
    "match_arm",
    "try_statement",
    "except_clause",
    "catch_clause",
    "conditional_expression",
    "ternary_expression",
    "do_statement",
    "loop_expression",
];

/// Node types for nesting constructs.
const NESTING_NODES: &[&str] = &[
    "if_statement",
    "if_expression",
    "elif_clause",
    "for_statement",
    "for_expression",
    "for_in_statement",
    "while_statement",
    "while_expression",
    "try_statement",
    "except_clause",
    "catch_clause",
    "with_statement",
    "switch_statement",
    "switch_expression",
    "match_expression",
    "do_statement",
    "loop_expression",
    "lambda",
    "arrow_function",
    "closure_expression",
    "list_comprehension",
    "dictionary_comprehension",
    "generator_expression",
];

/// Node types for return/exit points.
const EXIT_NODES: &[&str] = &[
    "return_statement",
    "return_expression",
    "throw_statement",
    "raise_statement",
    "break_statement",
    "break_expression",
];

/// Node types for loops.
const LOOP_NODES: &[&str] = &[
    "for_statement",
    "for_expression",
    "for_in_statement",
    "enhanced_for_statement",
    "while_statement",
    "while_expression",
    "do_statement",
    "loop_expression",
];

/// Method analyzer using AST.
struct MethodAnalyzer<'a> {
    source: &'a [u8],
    lines: Vec<&'a str>,
    language: &'a str,
}

impl<'a> MethodAnalyzer<'a> {
    fn new(source: &'a [u8], language: &'a str) -> Self {
        let source_str = std::str::from_utf8(source).unwrap_or("");
        let lines: Vec<&str> = source_str.lines().collect();
        Self {
            source,
            lines,
            language,
        }
    }

    /// Count SLOC within a line range.
    fn count_sloc(&self, start_line: usize, end_line: usize) -> u32 {
        let mut count = 0u32;
        for i in start_line..=end_line.min(self.lines.len().saturating_sub(1)) {
            let line = self.lines.get(i).map(|s| s.trim()).unwrap_or("");
            if !line.is_empty() && !is_comment_line(line) {
                count += 1;
            }
        }
        count
    }

    /// Analyze a function node and collect all metrics.
    fn analyze_function(
        &self,
        node: Node,
        start_line: usize,
        end_line: usize,
    ) -> (LengthMetrics, ComplexityMetrics, Vec<ExtractionCandidate>) {
        let mut statements = 0u32;
        let mut variables = 0u32;
        let mut decisions = 0u32;
        let mut max_nesting = 0u32;
        let mut exit_points = 0u32;
        let mut branches = 0u32;
        let mut loops = 0u32;
        let mut nesting_sum = 0u64;
        let mut nesting_count = 0usize;
        let mut extraction_candidates = Vec::new();

        // Depth-first traversal
        self.walk_function(
            node,
            0,
            &mut statements,
            &mut variables,
            &mut decisions,
            &mut max_nesting,
            &mut exit_points,
            &mut branches,
            &mut loops,
            &mut nesting_sum,
            &mut nesting_count,
            &mut extraction_candidates,
        );

        // Count parameters
        let parameters = self.count_parameters(node);

        // Count SLOC
        let sloc = self.count_sloc(start_line.saturating_sub(1), end_line.saturating_sub(1));

        let length = LengthMetrics {
            lines: sloc,
            statements,
            variables,
            parameters,
            total_span: (end_line - start_line + 1) as u32,
        };

        let average_nesting = if nesting_count > 0 {
            nesting_sum as f64 / nesting_count as f64
        } else {
            0.0
        };

        // Count boolean operators
        let boolean_operators = self.count_boolean_operators(node);

        let complexity = ComplexityMetrics {
            cyclomatic: decisions + 1, // McCabe's formula
            max_nesting,
            average_nesting,
            exit_points,
            branches,
            loops,
            boolean_operators,
        };

        (length, complexity, extraction_candidates)
    }

    /// Walk function body recursively.
    #[allow(clippy::too_many_arguments)]
    fn walk_function(
        &self,
        node: Node,
        depth: u32,
        statements: &mut u32,
        variables: &mut u32,
        decisions: &mut u32,
        max_nesting: &mut u32,
        exit_points: &mut u32,
        branches: &mut u32,
        loops: &mut u32,
        nesting_sum: &mut u64,
        nesting_count: &mut usize,
        candidates: &mut Vec<ExtractionCandidate>,
    ) {
        // Prevent stack overflow
        if depth > 50 {
            return;
        }

        let kind = node.kind();
        let line = node.start_position().row + 1;

        // Count statements
        if STATEMENT_NODE_TYPES.contains(&kind) {
            *statements += 1;
        }

        // Count variables
        if VARIABLE_DECL_TYPES.contains(&kind) && !FUNCTION_NODE_TYPES.contains(&kind) {
            *variables += count_declarators(node);
        }

        // Count decisions
        if DECISION_NODES.contains(&kind) {
            *decisions += 1;
        }

        // Track nesting
        let new_depth = if NESTING_NODES.contains(&kind) {
            depth + 1
        } else {
            depth
        };

        if new_depth > *max_nesting {
            *max_nesting = new_depth;
        }

        *nesting_sum += u64::from(new_depth);
        *nesting_count += 1;

        // Count exit points
        if EXIT_NODES.contains(&kind) {
            *exit_points += 1;
        }

        // Count branches
        if matches!(
            kind,
            "if_statement" | "if_expression" | "elif_clause" | "else_clause"
        ) {
            *branches += 1;
        }

        // Count loops
        if LOOP_NODES.contains(&kind) {
            *loops += 1;

            // Loop bodies are extraction candidates
            if let Some(body) = self.find_body_node(node) {
                let body_start = body.start_position().row + 1;
                let body_end = body.end_position().row + 1;
                let body_statements = self.count_body_statements(body);

                if body_statements >= 3 {
                    candidates.push(ExtractionCandidate {
                        block_type: BlockType::LoopBody,
                        start_line: body_start,
                        end_line: body_end,
                        statement_count: body_statements,
                        defined_variables: Vec::new(),
                        used_variables: Vec::new(),
                        live_out_variables: Vec::new(),
                        suggested_name: self.suggest_loop_method_name(node),
                        viability_score: if body_statements >= 5 { 0.8 } else { 0.6 },
                        reason: format!("Loop body with {} statements", body_statements),
                    });
                }
            }
        }

        // Complex conditionals are extraction candidates
        if matches!(kind, "if_statement" | "if_expression") {
            let branch_count = self.count_conditional_branches(node);
            if branch_count >= 3 {
                let end_line = node.end_position().row + 1;
                candidates.push(ExtractionCandidate {
                    block_type: BlockType::ConditionalBranch,
                    start_line: line,
                    end_line,
                    statement_count: self.count_body_statements(node),
                    defined_variables: Vec::new(),
                    used_variables: Vec::new(),
                    live_out_variables: Vec::new(),
                    suggested_name: None,
                    viability_score: 0.7,
                    reason: format!("Complex conditional with {} branches", branch_count),
                });
            }
        }

        // Try blocks are extraction candidates
        if kind == "try_statement" {
            let end_line = node.end_position().row + 1;
            let body_statements = self.count_body_statements(node);
            if body_statements >= 3 {
                candidates.push(ExtractionCandidate {
                    block_type: BlockType::TryBlock,
                    start_line: line,
                    end_line,
                    statement_count: body_statements,
                    defined_variables: Vec::new(),
                    used_variables: Vec::new(),
                    live_out_variables: Vec::new(),
                    suggested_name: None,
                    viability_score: 0.65,
                    reason: format!("Try block with {} statements", body_statements),
                });
            }
        }

        // Don't recurse into nested functions
        if FUNCTION_NODE_TYPES.contains(&kind) && depth > 0 {
            return;
        }

        // Recurse into children
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.walk_function(
                child,
                new_depth,
                statements,
                variables,
                decisions,
                max_nesting,
                exit_points,
                branches,
                loops,
                nesting_sum,
                nesting_count,
                candidates,
            );
        }
    }

    /// Count parameters in a function.
    fn count_parameters(&self, node: Node) -> u32 {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if matches!(
                child.kind(),
                "parameters" | "formal_parameters" | "parameter_list" | "function_parameters"
            ) {
                return count_param_children(child, self.source);
            }
        }
        0
    }

    /// Count boolean operators in conditions.
    fn count_boolean_operators(&self, node: Node) -> u32 {
        let mut count = 0u32;
        self.walk_for_boolean_ops(node, &mut count, 0);
        count
    }

    fn walk_for_boolean_ops(&self, node: Node, count: &mut u32, depth: u32) {
        if depth > 50 {
            return;
        }

        let kind = node.kind();
        if matches!(
            kind,
            "boolean_operator" | "binary_expression" | "logical_expression"
        ) {
            // Check for and/or/&&/||
            if let Ok(text) = node.utf8_text(self.source) {
                if text.contains("&&")
                    || text.contains("||")
                    || text.contains(" and ")
                    || text.contains(" or ")
                {
                    *count += 1;
                }
            }
        }

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.walk_for_boolean_ops(child, count, depth + 1);
        }
    }

    /// Find the body node of a control structure.
    fn find_body_node<'b>(&self, node: Node<'b>) -> Option<Node<'b>> {
        if let Some(body) = node.child_by_field_name("body") {
            return Some(body);
        }
        if let Some(consequence) = node.child_by_field_name("consequence") {
            return Some(consequence);
        }
        node.child_by_field_name("block")
    }

    /// Count statements in a body.
    fn count_body_statements(&self, node: Node) -> u32 {
        let mut count = 0u32;
        self.walk_count_statements(node, &mut count, 0);
        count
    }

    fn walk_count_statements(&self, node: Node, count: &mut u32, depth: u32) {
        if depth > 30 {
            return;
        }

        if STATEMENT_NODE_TYPES.contains(&node.kind()) {
            *count += 1;
        }

        // Don't recurse into nested functions
        if FUNCTION_NODE_TYPES.contains(&node.kind()) && depth > 0 {
            return;
        }

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.walk_count_statements(child, count, depth + 1);
        }
    }

    /// Count branches in a conditional.
    fn count_conditional_branches(&self, node: Node) -> u32 {
        let mut count = 1u32; // The main if
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if matches!(
                child.kind(),
                "elif_clause" | "else_if_clause" | "else_clause"
            ) {
                count += 1;
            }
        }
        count
    }

    /// Suggest a method name for a loop extraction.
    fn suggest_loop_method_name(&self, node: Node) -> Option<String> {
        // Try to infer from loop variable
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "identifier" || child.kind() == "pattern" {
                if let Ok(text) = child.utf8_text(self.source) {
                    if !text.is_empty() && text != "i" && text != "j" && text != "_" {
                        return Some(format!("process_{}", text));
                    }
                }
            }
        }
        None
    }
}

/// Check if a line is comment-only.
fn is_comment_line(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.starts_with('#')
        || trimmed.starts_with("//")
        || trimmed.starts_with("/*")
        || trimmed.starts_with('*')
        || trimmed.starts_with("*/")
        || trimmed.starts_with("'''")
        || trimmed.starts_with("\"\"\"")
}

/// Count declarators in a variable declaration.
fn count_declarators(node: Node) -> u32 {
    let mut count = 0u32;
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if matches!(
            child.kind(),
            "variable_declarator" | "init_declarator" | "var_spec" | "identifier"
        ) {
            count += 1;
        }
    }
    count.max(1)
}

/// Count parameters excluding self/cls/this.
fn count_param_children(params_node: Node, source: &[u8]) -> u32 {
    let mut count = 0u32;
    let mut cursor = params_node.walk();
    for child in params_node.children(&mut cursor) {
        match child.kind() {
            "(" | ")" | "," | "comment" => {}
            "identifier" => {
                let text = child.utf8_text(source).unwrap_or("");
                if text != "self" && text != "cls" && text != "this" {
                    count += 1;
                }
            }
            _ if child.kind().contains("parameter") => {
                let text = child.utf8_text(source).unwrap_or("");
                if !text.starts_with("self")
                    && !text.starts_with("cls")
                    && !text.starts_with("this")
                {
                    count += 1;
                }
            }
            _ => {
                if child.child_count() > 0 {
                    count += 1;
                }
            }
        }
    }
    count
}

// =============================================================================
// SUGGESTION GENERATION
// =============================================================================

/// Generate refactoring suggestions based on analysis.
fn generate_suggestions(
    length: &LengthMetrics,
    complexity: &ComplexityMetrics,
    candidates: &[ExtractionCandidate],
    config: &LongMethodConfig,
) -> Vec<RefactoringSuggestion> {
    let mut suggestions = Vec::new();

    // Too many parameters -> Parameter Object
    if length.parameters > config.max_parameters {
        suggestions.push(RefactoringSuggestion {
            refactoring_type: RefactoringType::IntroduceParameterObject,
            description: format!(
                "Introduce a parameter object to group {} parameters",
                length.parameters
            ),
            line_range: None,
            suggested_name: Some("Options".to_string()),
            required_parameters: Vec::new(),
            return_variable: None,
            confidence: 0.8,
            priority: 7,
        });
    }

    // Too many variables -> Extract setup or validation
    if length.variables > config.max_variables {
        suggestions.push(RefactoringSuggestion {
            refactoring_type: RefactoringType::ExtractSetup,
            description: format!(
                "Extract initialization of {} variables into a setup method",
                length.variables
            ),
            line_range: None,
            suggested_name: Some("setup_context".to_string()),
            required_parameters: Vec::new(),
            return_variable: None,
            confidence: 0.7,
            priority: 5,
        });
    }

    // Deep nesting -> Guard clauses
    if complexity.max_nesting > config.max_nesting {
        suggestions.push(RefactoringSuggestion {
            refactoring_type: RefactoringType::ExtractGuardClause,
            description: format!(
                "Extract guard clauses to reduce nesting from {} levels",
                complexity.max_nesting
            ),
            line_range: None,
            suggested_name: None,
            required_parameters: Vec::new(),
            return_variable: None,
            confidence: 0.85,
            priority: 8,
        });
    }

    // High complexity -> Split method
    if complexity.cyclomatic > config.max_complexity {
        suggestions.push(RefactoringSuggestion {
            refactoring_type: RefactoringType::SplitByResponsibility,
            description: format!(
                "Split method with complexity {} into smaller focused methods",
                complexity.cyclomatic
            ),
            line_range: None,
            suggested_name: None,
            required_parameters: Vec::new(),
            return_variable: None,
            confidence: 0.75,
            priority: 6,
        });
    }

    // Many branches -> Decompose conditional
    if complexity.branches > 3 {
        suggestions.push(RefactoringSuggestion {
            refactoring_type: RefactoringType::DecomposeConditional,
            description: format!(
                "Decompose {} conditional branches into separate methods",
                complexity.branches
            ),
            line_range: None,
            suggested_name: None,
            required_parameters: Vec::new(),
            return_variable: None,
            confidence: 0.7,
            priority: 5,
        });
    }

    // Add extraction candidate suggestions
    for candidate in candidates {
        if candidate.viability_score >= 0.6 {
            let description = match candidate.block_type {
                BlockType::LoopBody => format!(
                    "Extract loop body (lines {}-{}) into {}",
                    candidate.start_line,
                    candidate.end_line,
                    candidate
                        .suggested_name
                        .as_deref()
                        .unwrap_or("a helper method")
                ),
                BlockType::ConditionalBranch => format!(
                    "Extract conditional logic (lines {}-{}) into a dedicated method",
                    candidate.start_line, candidate.end_line
                ),
                BlockType::TryBlock => format!(
                    "Extract try/except block (lines {}-{}) into an error-handling method",
                    candidate.start_line, candidate.end_line
                ),
                _ => format!(
                    "Extract lines {}-{} into a separate method",
                    candidate.start_line, candidate.end_line
                ),
            };

            suggestions.push(RefactoringSuggestion {
                refactoring_type: RefactoringType::ExtractMethod,
                description,
                line_range: Some((candidate.start_line, candidate.end_line)),
                suggested_name: candidate.suggested_name.clone(),
                required_parameters: candidate.used_variables.clone(),
                return_variable: candidate.live_out_variables.first().cloned(),
                confidence: candidate.viability_score,
                priority: 4,
            });
        }
    }

    // Sort by priority (descending)
    suggestions.sort_by(|a, b| b.priority.cmp(&a.priority));

    suggestions
}

// =============================================================================
// PUBLIC API
// =============================================================================

/// Detect long methods in a project or file.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `language` - Optional language filter
/// * `config` - Optional configuration (uses defaults if None)
///
/// # Returns
///
/// Complete analysis with findings, statistics, and suggestions.
///
/// # Example
///
/// ```ignore
/// use go_brrr::quality::smells::{detect_long_methods, LongMethodConfig};
///
/// // Default configuration
/// let result = detect_long_methods("./src", Some("python"), None)?;
///
/// // Strict configuration
/// let strict = LongMethodConfig::strict();
/// let result = detect_long_methods("./src", None, Some(strict))?;
/// ```
pub fn detect_long_methods(
    path: impl AsRef<Path>,
    language: Option<&str>,
    config: Option<LongMethodConfig>,
) -> Result<LongMethodAnalysis> {
    let path = path.as_ref();
    let config = config.unwrap_or_default();

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Path not found: {}", path.display()),
        )));
    }

    if path.is_file() {
        return detect_long_methods_in_file(path, &config);
    }

    // Directory analysis
    let path_str = path
        .to_str()
        .ok_or_else(|| BrrrError::InvalidArgument("Invalid path encoding".to_string()))?;

    let scanner = ProjectScanner::new(path_str)?;

    let scan_config = if let Some(lang) = language {
        ScanConfig::for_language(lang)
    } else {
        ScanConfig::default()
    };

    let scan_result = scanner.scan_with_config(&scan_config)?;

    if scan_result.files.is_empty() {
        return Err(BrrrError::InvalidArgument(format!(
            "No source files found in {} (filter: {:?})",
            path.display(),
            language
        )));
    }

    debug!(
        "Analyzing {} files for long methods",
        scan_result.files.len()
    );

    // Analyze files in parallel
    let results: Vec<(
        Vec<LongMethodFinding>,
        Vec<LongMethodError>,
        Vec<u32>,
        Vec<u32>,
    )> = scan_result
        .files
        .par_iter()
        .map(|file| analyze_file_methods(file, &config))
        .collect();

    // Aggregate results
    let mut all_findings = Vec::new();
    let mut all_errors = Vec::new();
    let mut all_lines = Vec::new();
    let mut all_complexity = Vec::new();
    let mut total_methods = 0usize;

    for (findings, errors, lines, complexity) in results {
        total_methods += lines.len();
        all_findings.extend(findings);
        all_errors.extend(errors);
        all_lines.extend(lines);
        all_complexity.extend(complexity);
    }

    // Calculate statistics
    let stats =
        LongMethodStats::from_findings(total_methods, &all_findings, &all_lines, &all_complexity);

    // Sort findings by score (worst first)
    all_findings.sort_by(|a, b| {
        b.score
            .partial_cmp(&a.score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    Ok(LongMethodAnalysis {
        path: path.to_path_buf(),
        language: language.map(String::from),
        findings: all_findings,
        stats,
        config,
        errors: all_errors,
    })
}

/// Detect long methods in a single file.
pub fn detect_long_methods_in_file(
    path: impl AsRef<Path>,
    config: &LongMethodConfig,
) -> Result<LongMethodAnalysis> {
    let path = path.as_ref();

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("File not found: {}", path.display()),
        )));
    }

    let (findings, errors, all_lines, all_complexity) = analyze_file_methods(path, config);

    let total_methods = all_lines.len();
    let stats =
        LongMethodStats::from_findings(total_methods, &findings, &all_lines, &all_complexity);

    let registry = LanguageRegistry::global();
    let language = registry.detect_language(path).map(|l| l.name().to_string());

    Ok(LongMethodAnalysis {
        path: path.to_path_buf(),
        language,
        findings,
        stats,
        config: config.clone(),
        errors,
    })
}

/// Internal function to analyze all methods in a file.
fn analyze_file_methods(
    file: &Path,
    config: &LongMethodConfig,
) -> (
    Vec<LongMethodFinding>,
    Vec<LongMethodError>,
    Vec<u32>,
    Vec<u32>,
) {
    let mut findings = Vec::new();
    let mut errors = Vec::new();
    let mut all_lines = Vec::new();
    let mut all_complexity = Vec::new();

    // Read file
    let source = match std::fs::read(file) {
        Ok(s) => s,
        Err(e) => {
            errors.push(LongMethodError {
                file: file.to_path_buf(),
                message: format!("Failed to read file: {}", e),
            });
            return (findings, errors, all_lines, all_complexity);
        }
    };

    // Extract module info
    let module = match AstExtractor::extract_file(file) {
        Ok(m) => m,
        Err(e) => {
            errors.push(LongMethodError {
                file: file.to_path_buf(),
                message: format!("Failed to parse: {}", e),
            });
            return (findings, errors, all_lines, all_complexity);
        }
    };

    // Get language
    let registry = LanguageRegistry::global();
    let lang = match registry.detect_language(file) {
        Some(l) => l,
        None => {
            errors.push(LongMethodError {
                file: file.to_path_buf(),
                message: "Unknown language".to_string(),
            });
            return (findings, errors, all_lines, all_complexity);
        }
    };

    // Parse for AST
    let mut parser = match lang.parser() {
        Ok(p) => p,
        Err(e) => {
            errors.push(LongMethodError {
                file: file.to_path_buf(),
                message: format!("Parser error: {}", e),
            });
            return (findings, errors, all_lines, all_complexity);
        }
    };

    let tree = match parser.parse(&source, None) {
        Some(t) => t,
        None => {
            errors.push(LongMethodError {
                file: file.to_path_buf(),
                message: "Parse failed".to_string(),
            });
            return (findings, errors, all_lines, all_complexity);
        }
    };

    let analyzer = MethodAnalyzer::new(&source, lang.name());

    // Analyze top-level functions
    for func in &module.functions {
        if let Some(finding) = analyze_single_method(
            &analyzer,
            &tree,
            file,
            &func.name,
            func.line_number,
            func.end_line_number.unwrap_or(func.line_number),
            config,
        ) {
            all_lines.push(finding.length.lines);
            all_complexity.push(finding.complexity.cyclomatic);
            if !finding.violations.is_empty() {
                findings.push(finding);
            }
        }
    }

    // Analyze class methods
    for class in &module.classes {
        for method in &class.methods {
            let qualified_name = format!("{}.{}", class.name, method.name);
            if let Some(mut finding) = analyze_single_method(
                &analyzer,
                &tree,
                file,
                &qualified_name,
                method.line_number,
                method.end_line_number.unwrap_or(method.line_number),
                config,
            ) {
                finding.function_name = qualified_name;
                all_lines.push(finding.length.lines);
                all_complexity.push(finding.complexity.cyclomatic);
                if !finding.violations.is_empty() {
                    findings.push(finding);
                }
            }
        }
    }

    (findings, errors, all_lines, all_complexity)
}

/// Analyze a single method.
fn analyze_single_method(
    analyzer: &MethodAnalyzer,
    tree: &Tree,
    file: &Path,
    name: &str,
    start_line: usize,
    end_line: usize,
    base_config: &LongMethodConfig,
) -> Option<LongMethodFinding> {
    if start_line == 0 {
        return None;
    }

    // Find the function node
    let func_node = find_function_node(tree.root_node(), start_line)?;

    // Analyze metrics
    let (length, complexity, candidates) =
        analyzer.analyze_function(func_node, start_line, end_line);

    // Skip trivial methods
    if length.lines < base_config.min_lines_for_analysis {
        return None;
    }

    // Detect category and adjust config
    let base_name = name.split('.').last().unwrap_or(name);
    let category = MethodCategory::from_name(base_name);

    let config = if base_config.context_aware {
        match category {
            MethodCategory::Test => base_config.adjust_for_tests(),
            MethodCategory::Configuration => base_config.adjust_for_configuration(),
            MethodCategory::Factory => base_config.adjust_for_factory(),
            MethodCategory::Constructor => base_config.adjust_for_constructor(),
            _ => base_config.clone(),
        }
    } else {
        base_config.clone()
    };

    // Check for violations
    let mut violations = Vec::new();

    if length.lines > config.max_lines {
        violations.push(Violation::TooLong {
            lines: length.lines,
            threshold: config.max_lines,
        });
    }

    if length.statements > config.max_statements {
        violations.push(Violation::TooManyStatements {
            count: length.statements,
            threshold: config.max_statements,
        });
    }

    if length.variables > config.max_variables {
        violations.push(Violation::TooManyVariables {
            count: length.variables,
            threshold: config.max_variables,
        });
    }

    if length.parameters > config.max_parameters {
        violations.push(Violation::TooManyParameters {
            count: length.parameters,
            threshold: config.max_parameters,
        });
    }

    if complexity.cyclomatic > config.max_complexity {
        violations.push(Violation::TooComplex {
            complexity: complexity.cyclomatic,
            threshold: config.max_complexity,
        });
    }

    if complexity.max_nesting > config.max_nesting {
        violations.push(Violation::TooDeep {
            depth: complexity.max_nesting,
            threshold: config.max_nesting,
        });
    }

    // Calculate severity
    let severity = LongMethodSeverity::from_violations(
        length.lines > config.max_lines,
        complexity.cyclomatic > config.max_complexity,
        complexity.max_nesting > config.max_nesting,
        length.variables > config.max_variables,
    );

    // Generate suggestions
    let suggestions = generate_suggestions(&length, &complexity, &candidates, &config);

    // Calculate score
    let score = LongMethodFinding::calculate_score(&length, &complexity);

    Some(LongMethodFinding {
        function_name: name.to_string(),
        file: file.to_path_buf(),
        line: start_line,
        end_line,
        length,
        complexity,
        category,
        severity,
        violations,
        suggestions,
        extraction_candidates: candidates,
        score,
    })
}

/// Find a function node at the target line.
fn find_function_node(node: Node, target_line: usize) -> Option<Node> {
    let node_start = node.start_position().row + 1;
    let node_end = node.end_position().row + 1;

    if FUNCTION_NODE_TYPES.contains(&node.kind()) && node_start == target_line {
        return Some(node);
    }

    if target_line < node_start || target_line > node_end {
        return None;
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(found) = find_function_node(child, target_line) {
            return Some(found);
        }
    }

    None
}

// =============================================================================
// FORMATTING
// =============================================================================

/// Format long method analysis as human-readable text.
pub fn format_long_method_summary(analysis: &LongMethodAnalysis) -> String {
    let mut output = String::new();

    output.push_str("=== Long Method Analysis ===\n\n");

    output.push_str(&format!("Path: {}\n", analysis.path.display()));
    if let Some(ref lang) = analysis.language {
        output.push_str(&format!("Language: {}\n", lang));
    }
    output.push('\n');

    // Statistics
    output.push_str("Statistics:\n");
    output.push_str(&format!(
        "  Total methods: {}\n",
        analysis.stats.total_methods
    ));
    output.push_str(&format!(
        "  Long methods: {} ({:.1}%)\n",
        analysis.stats.long_methods, analysis.stats.percentage_long
    ));
    output.push_str(&format!(
        "  Average lines: {:.1}\n",
        analysis.stats.average_lines
    ));
    output.push_str(&format!("  Max lines: {}\n", analysis.stats.max_lines));
    output.push_str(&format!(
        "  Average complexity: {:.1}\n",
        analysis.stats.average_complexity
    ));
    output.push_str(&format!(
        "  Max complexity: {}\n",
        analysis.stats.max_complexity
    ));
    output.push('\n');

    // Severity distribution
    if !analysis.stats.severity_distribution.is_empty() {
        output.push_str("Severity Distribution:\n");
        for (severity, count) in &analysis.stats.severity_distribution {
            output.push_str(&format!("  {}: {}\n", severity, count));
        }
        output.push('\n');
    }

    // Findings
    if analysis.findings.is_empty() {
        output.push_str("No long methods found.\n");
    } else {
        output.push_str(&format!("Findings ({}):\n\n", analysis.findings.len()));

        for finding in &analysis.findings {
            output.push_str(&format!(
                "{}{}{} at {}:{}-{}\n",
                finding.severity.color_code(),
                finding.function_name,
                "\x1b[0m",
                finding.file.display(),
                finding.line,
                finding.end_line
            ));
            output.push_str(&format!("  Category: {}\n", finding.category.description()));
            output.push_str(&format!(
                "  Severity: {} - {}\n",
                finding.severity,
                finding.severity.description()
            ));
            output.push_str(&format!(
                "  Metrics: {} lines, {} statements, {} vars, complexity {}, nesting {}\n",
                finding.length.lines,
                finding.length.statements,
                finding.length.variables,
                finding.complexity.cyclomatic,
                finding.complexity.max_nesting
            ));

            // Violations
            if !finding.violations.is_empty() {
                output.push_str("  Violations:\n");
                for v in &finding.violations {
                    output.push_str(&format!("    - {}\n", v));
                }
            }

            // Top suggestions
            let top_suggestions: Vec<_> = finding.suggestions.iter().take(3).collect();
            if !top_suggestions.is_empty() {
                output.push_str("  Suggestions:\n");
                for s in top_suggestions {
                    output.push_str(&format!(
                        "    - [{}] {}\n",
                        s.refactoring_type, s.description
                    ));
                }
            }

            output.push('\n');
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
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn create_temp_file(content: &str, extension: &str) -> NamedTempFile {
        let mut file = tempfile::Builder::new()
            .suffix(extension)
            .tempfile()
            .expect("Failed to create temp file");
        file.write_all(content.as_bytes())
            .expect("Failed to write to temp file");
        file
    }

    #[test]
    fn test_method_category_detection() {
        assert_eq!(
            MethodCategory::from_name("test_something"),
            MethodCategory::Test
        );
        assert_eq!(MethodCategory::from_name("TestCase"), MethodCategory::Test);
        assert_eq!(
            MethodCategory::from_name("__init__"),
            MethodCategory::Constructor
        );
        assert_eq!(
            MethodCategory::from_name("new"),
            MethodCategory::Constructor
        );
        assert_eq!(
            MethodCategory::from_name("setup_database"),
            MethodCategory::Configuration
        );
        assert_eq!(
            MethodCategory::from_name("create_user"),
            MethodCategory::Factory
        );
        assert_eq!(
            MethodCategory::from_name("on_click"),
            MethodCategory::Handler
        );
        assert_eq!(
            MethodCategory::from_name("process_data"),
            MethodCategory::Normal
        );
    }

    #[test]
    fn test_simple_method_not_flagged() {
        let source = r#"
def simple():
    return 42
"#;
        let file = create_temp_file(source, ".py");
        let result = detect_long_methods_in_file(file.path(), &LongMethodConfig::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();
        assert!(analysis.findings.is_empty());
    }

    #[test]
    fn test_long_method_detected() {
        let mut lines = vec!["def long_function():".to_string()];
        for i in 0..40 {
            lines.push(format!("    x{} = {}", i, i));
        }
        lines.push("    return x0".to_string());
        let source = lines.join("\n");

        let file = create_temp_file(&source, ".py");
        let result = detect_long_methods_in_file(file.path(), &LongMethodConfig::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.findings.len(), 1);
        assert_eq!(analysis.findings[0].function_name, "long_function");
        assert!(analysis.findings[0]
            .violations
            .iter()
            .any(|v| matches!(v, Violation::TooLong { .. })));
    }

    #[test]
    fn test_complex_method_detected() {
        let source = r#"
def complex_func(a, b, c, d, e, f, g):
    if a > 0:
        if b > 0:
            if c > 0:
                if d > 0:
                    if e > 0:
                        return "deep"
    return "shallow"
"#;
        let file = create_temp_file(source, ".py");
        let result = detect_long_methods_in_file(file.path(), &LongMethodConfig::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.findings.len(), 1);
        assert!(analysis.findings[0]
            .violations
            .iter()
            .any(|v| matches!(v, Violation::TooDeep { .. })));
    }

    #[test]
    fn test_test_method_adjusted_thresholds() {
        let mut lines = vec!["def test_something():".to_string()];
        // Create a 45-line test (would fail normal 30-line threshold)
        for i in 0..45 {
            lines.push(format!("    x{} = {}", i, i));
        }
        lines.push("    assert x0 == 0".to_string());
        let source = lines.join("\n");

        let file = create_temp_file(&source, ".py");
        let config = LongMethodConfig {
            context_aware: true,
            ..LongMethodConfig::default()
        };
        let result = detect_long_methods_in_file(file.path(), &config);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        // Test method has adjusted threshold (30 + 30 = 60)
        // 45 lines should not trigger "too long"
        let too_long_violations: Vec<_> = analysis
            .findings
            .iter()
            .flat_map(|f| &f.violations)
            .filter(|v| matches!(v, Violation::TooLong { .. }))
            .collect();

        assert!(too_long_violations.is_empty());
    }

    #[test]
    fn test_severity_calculation() {
        assert_eq!(
            LongMethodSeverity::from_violations(false, false, false, false),
            LongMethodSeverity::Minor
        );
        assert_eq!(
            LongMethodSeverity::from_violations(true, false, false, false),
            LongMethodSeverity::Moderate
        );
        assert_eq!(
            LongMethodSeverity::from_violations(true, true, false, false),
            LongMethodSeverity::Major
        );
        assert_eq!(
            LongMethodSeverity::from_violations(true, true, true, false),
            LongMethodSeverity::Critical
        );
    }

    #[test]
    fn test_config_presets() {
        let default = LongMethodConfig::default();
        let strict = LongMethodConfig::strict();
        let lenient = LongMethodConfig::lenient();

        assert!(strict.max_lines < default.max_lines);
        assert!(lenient.max_lines > default.max_lines);
    }

    #[test]
    fn test_extraction_candidates() {
        let source = r#"
def process_items(items):
    results = []
    for item in items:
        validated = validate(item)
        transformed = transform(validated)
        saved = save(transformed)
        results.append(saved)
    return results
"#;
        let file = create_temp_file(source, ".py");
        let result = detect_long_methods_in_file(file.path(), &LongMethodConfig::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        // Should have found the method (even if not flagged as long)
        assert_eq!(analysis.stats.total_methods, 1);
    }

    #[test]
    fn test_statistics_calculation() {
        let mut lines = vec!["def func1():".to_string()];
        for i in 0..35 {
            lines.push(format!("    x{} = {}", i, i));
        }
        lines.push("    return x0".to_string());
        lines.push("".to_string());
        // func2 needs at least 5 lines to meet min_lines_for_analysis threshold
        lines.push("def func2():".to_string());
        lines.push("    a = 1".to_string());
        lines.push("    b = 2".to_string());
        lines.push("    c = 3".to_string());
        lines.push("    d = 4".to_string());
        lines.push("    return a + b + c + d".to_string());
        let source = lines.join("\n");

        let file = create_temp_file(&source, ".py");
        let result = detect_long_methods_in_file(file.path(), &LongMethodConfig::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.stats.total_methods, 2);
        assert_eq!(analysis.stats.long_methods, 1);
    }

    #[test]
    fn test_format_summary() {
        let analysis = LongMethodAnalysis {
            path: PathBuf::from("test.py"),
            language: Some("python".to_string()),
            findings: vec![],
            stats: LongMethodStats {
                total_methods: 10,
                long_methods: 2,
                percentage_long: 20.0,
                average_lines: 15.0,
                max_lines: 45,
                average_complexity: 5.0,
                max_complexity: 12,
                severity_distribution: HashMap::new(),
                violation_counts: HashMap::new(),
            },
            config: LongMethodConfig::default(),
            errors: vec![],
        };

        let summary = format_long_method_summary(&analysis);
        assert!(summary.contains("Long Method Analysis"));
        assert!(summary.contains("Total methods: 10"));
        assert!(summary.contains("Long methods: 2"));
    }

    #[test]
    fn test_nonexistent_file() {
        let result = detect_long_methods("/nonexistent/path/file.py", None, None);
        assert!(result.is_err());
    }

    #[test]
    fn test_empty_file() {
        let source = "# Just a comment\n";
        let file = create_temp_file(source, ".py");
        let result = detect_long_methods_in_file(file.path(), &LongMethodConfig::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.stats.total_methods, 0);
        assert!(analysis.findings.is_empty());
    }

    #[test]
    fn test_typescript_method() {
        let source = r#"
function processData(input: string): number {
    const lines = input.split('\n');
    let total = 0;
    for (const line of lines) {
        const value = parseInt(line);
        if (!isNaN(value)) {
            total += value;
        }
    }
    return total;
}
"#;
        let file = create_temp_file(source, ".ts");
        let result = detect_long_methods_in_file(file.path(), &LongMethodConfig::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.stats.total_methods, 1);
    }
}
