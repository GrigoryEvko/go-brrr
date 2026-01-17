//! Function size metrics for identifying oversized functions.
//!
//! This module provides comprehensive size metrics for functions and methods,
//! helping identify code that may benefit from refactoring. Unlike simple line
//! counting, this module uses AST analysis to provide accurate metrics.
//!
//! # Metrics Calculated
//!
//! For each function, the following metrics are computed:
//!
//! | Metric            | Description                                      |
//! |-------------------|--------------------------------------------------|
//! | SLOC              | Source Lines of Code (excluding blanks/comments) |
//! | Statements        | Number of AST statement nodes                    |
//! | Parameters        | Number of function parameters                    |
//! | Local Variables   | Number of variable declarations within function  |
//! | Return Statements | Number of return/throw points                    |
//! | Branches          | Number of branching constructs (if/switch/match) |
//!
//! # Configurable Thresholds
//!
//! Default thresholds based on software engineering best practices:
//!
//! | Metric      | Warning | Critical |
//! |-------------|---------|----------|
//! | SLOC        | > 30    | > 60     |
//! | Parameters  | > 5     | > 8      |
//! | Variables   | > 10    | > 15     |
//! | Returns     | > 5     | -        |
//!
//! # Context-Aware Analysis
//!
//! The analyzer recognizes special function patterns and adjusts suggestions:
//!
//! - **Constructors/Init**: `__init__`, `new`, `constructor` - often need many params
//! - **Test Functions**: `test_*`, `*_test` - long setup is common
//! - **Configuration**: `configure_*`, `setup_*` - many variables expected
//! - **Factories**: `create_*`, `build_*` - may have many params
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::metrics::{analyze_function_size, SizeIssue};
//!
//! let result = analyze_function_size("./src", Some("python"), None)?;
//! for func in &result.functions {
//!     if !func.issues.is_empty() {
//!         println!("{} at {}:{} has {} issues:",
//!             func.name, func.file.display(), func.line, func.issues.len());
//!         for issue in &func.issues {
//!             match issue {
//!                 SizeIssue::TooLong { sloc, threshold } =>
//!                     println!("  - Too long: {} SLOC (threshold: {})", sloc, threshold),
//!                 SizeIssue::TooManyParams { count, threshold } =>
//!                     println!("  - Too many params: {} (threshold: {})", count, threshold),
//!                 _ => {}
//!             }
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
use crate::error::{Result, BrrrError};
use crate::lang::LanguageRegistry;

// =============================================================================
// THRESHOLDS
// =============================================================================

/// Configurable thresholds for function size metrics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SizeThresholds {
    /// SLOC warning threshold (default: 30)
    pub sloc_warning: u32,
    /// SLOC critical threshold (default: 60)
    pub sloc_critical: u32,
    /// Parameters warning threshold (default: 5)
    pub params_warning: u32,
    /// Parameters critical threshold (default: 8)
    pub params_critical: u32,
    /// Local variables warning threshold (default: 10)
    pub variables_warning: u32,
    /// Local variables critical threshold (default: 15)
    pub variables_critical: u32,
    /// Return statements warning threshold (default: 5)
    pub returns_warning: u32,
    /// Branches warning threshold (default: 10)
    pub branches_warning: u32,
}

impl Default for SizeThresholds {
    fn default() -> Self {
        Self {
            sloc_warning: 30,
            sloc_critical: 60,
            params_warning: 5,
            params_critical: 8,
            variables_warning: 10,
            variables_critical: 15,
            returns_warning: 5,
            branches_warning: 10,
        }
    }
}

// =============================================================================
// TYPES
// =============================================================================

/// Severity level for size issues.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SizeSeverity {
    /// Metric exceeds warning threshold
    Warning,
    /// Metric exceeds critical threshold
    Critical,
}

impl std::fmt::Display for SizeSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Warning => write!(f, "warning"),
            Self::Critical => write!(f, "critical"),
        }
    }
}

impl SizeSeverity {
    /// Get the color code for CLI output (ANSI).
    #[must_use]
    pub const fn color_code(&self) -> &'static str {
        match self {
            Self::Warning => "\x1b[33m",  // Yellow
            Self::Critical => "\x1b[31m", // Red
        }
    }
}

/// Specific size issue detected in a function.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum SizeIssue {
    /// Function has too many source lines of code
    TooLong {
        sloc: u32,
        threshold: u32,
        severity: SizeSeverity,
    },
    /// Function has too many parameters
    TooManyParams {
        count: u32,
        threshold: u32,
        severity: SizeSeverity,
    },
    /// Function has too many local variables
    TooManyVariables {
        count: u32,
        threshold: u32,
        severity: SizeSeverity,
    },
    /// Function has too many return statements
    TooManyReturns {
        count: u32,
        threshold: u32,
        severity: SizeSeverity,
    },
    /// Function has too many branches
    TooManyBranches {
        count: u32,
        threshold: u32,
        severity: SizeSeverity,
    },
}

impl SizeIssue {
    /// Get the severity of this issue.
    #[must_use]
    pub fn severity(&self) -> SizeSeverity {
        match self {
            Self::TooLong { severity, .. }
            | Self::TooManyParams { severity, .. }
            | Self::TooManyVariables { severity, .. }
            | Self::TooManyReturns { severity, .. }
            | Self::TooManyBranches { severity, .. } => *severity,
        }
    }

    /// Get a human-readable description of the issue.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::TooLong { sloc, threshold, .. } => {
                format!(
                    "Function is too long: {} SLOC (threshold: {})",
                    sloc, threshold
                )
            }
            Self::TooManyParams {
                count, threshold, ..
            } => {
                format!(
                    "Too many parameters: {} (threshold: {})",
                    count, threshold
                )
            }
            Self::TooManyVariables {
                count, threshold, ..
            } => {
                format!(
                    "Too many local variables: {} (threshold: {})",
                    count, threshold
                )
            }
            Self::TooManyReturns {
                count, threshold, ..
            } => {
                format!(
                    "Too many return statements: {} (threshold: {})",
                    count, threshold
                )
            }
            Self::TooManyBranches {
                count, threshold, ..
            } => {
                format!("Too many branches: {} (threshold: {})", count, threshold)
            }
        }
    }

    /// Get the refactoring suggestion for this issue.
    #[must_use]
    pub fn suggestion(&self) -> &'static str {
        match self {
            Self::TooLong { .. } => {
                "Consider extracting helper functions or breaking into smaller units"
            }
            Self::TooManyParams { .. } => {
                "Consider using a parameter object, builder pattern, or grouping related parameters"
            }
            Self::TooManyVariables { .. } => {
                "Consider extracting sections into separate functions to reduce local state"
            }
            Self::TooManyReturns { .. } => {
                "Consider using early returns with guard clauses or consolidating return points"
            }
            Self::TooManyBranches { .. } => {
                "Consider using polymorphism, strategy pattern, or lookup tables"
            }
        }
    }
}

impl std::fmt::Display for SizeIssue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description())
    }
}

/// Function category for context-aware analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FunctionCategory {
    /// Regular function
    Normal,
    /// Constructor or initializer
    Constructor,
    /// Test function
    Test,
    /// Configuration/setup function
    Configuration,
    /// Factory function
    Factory,
    /// Event handler or callback
    Handler,
}

impl FunctionCategory {
    /// Detect category from function name.
    #[must_use]
    pub fn from_name(name: &str) -> Self {
        let lower = name.to_lowercase();

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

        // Test patterns
        if lower.starts_with("test_")
            || lower.starts_with("test")
            || lower.ends_with("_test")
            || lower.ends_with("test")
            || lower.starts_with("spec_")
            || lower.ends_with("_spec")
            || lower.starts_with("it_")
            || lower.starts_with("describe_")
        {
            return Self::Test;
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

    /// Get adjusted thresholds for this category.
    #[must_use]
    pub fn adjusted_thresholds(&self, base: &SizeThresholds) -> SizeThresholds {
        match self {
            Self::Constructor => SizeThresholds {
                // Constructors often need many params for DI
                params_warning: base.params_warning + 3,
                params_critical: base.params_critical + 4,
                // May need more variables for initialization
                variables_warning: base.variables_warning + 5,
                variables_critical: base.variables_critical + 5,
                ..base.clone()
            },
            Self::Test => SizeThresholds {
                // Tests can be longer due to setup/assertions
                sloc_warning: base.sloc_warning + 20,
                sloc_critical: base.sloc_critical + 30,
                // Tests often need many local variables for fixtures
                variables_warning: base.variables_warning + 5,
                variables_critical: base.variables_critical + 5,
                ..base.clone()
            },
            Self::Configuration => SizeThresholds {
                // Configuration functions naturally have many variables
                variables_warning: base.variables_warning + 10,
                variables_critical: base.variables_critical + 10,
                // May be longer
                sloc_warning: base.sloc_warning + 10,
                sloc_critical: base.sloc_critical + 20,
                ..base.clone()
            },
            Self::Factory => SizeThresholds {
                // Factories may need more params
                params_warning: base.params_warning + 2,
                params_critical: base.params_critical + 3,
                ..base.clone()
            },
            Self::Handler => SizeThresholds {
                // Handlers may have more branches for different cases
                branches_warning: base.branches_warning + 3,
                ..base.clone()
            },
            Self::Normal => base.clone(),
        }
    }

    /// Get description of the category.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Normal => "regular function",
            Self::Constructor => "constructor/initializer",
            Self::Test => "test function",
            Self::Configuration => "configuration function",
            Self::Factory => "factory function",
            Self::Handler => "event handler/callback",
        }
    }
}

impl std::fmt::Display for FunctionCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description())
    }
}

/// Complete size metrics for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSizeMetrics {
    /// Function name (may include class prefix for methods)
    pub name: String,
    /// File path containing the function
    pub file: PathBuf,
    /// Starting line number (1-indexed)
    pub line: usize,
    /// Ending line number (1-indexed)
    pub end_line: usize,
    /// Source lines of code (excluding blanks and comments)
    pub sloc: u32,
    /// Number of statements
    pub statements: u32,
    /// Number of parameters
    pub parameters: u32,
    /// Number of local variables declared
    pub local_variables: u32,
    /// Number of return statements
    pub return_statements: u32,
    /// Number of branch points (if, switch, match, etc.)
    pub branches: u32,
    /// Detected function category
    pub category: FunctionCategory,
    /// List of size issues detected
    pub issues: Vec<SizeIssue>,
    /// Refactoring suggestions based on detected issues
    pub suggestions: Vec<String>,
}

impl FunctionSizeMetrics {
    /// Check if the function has any issues.
    #[must_use]
    pub fn has_issues(&self) -> bool {
        !self.issues.is_empty()
    }

    /// Get the highest severity of all issues.
    #[must_use]
    pub fn max_severity(&self) -> Option<SizeSeverity> {
        self.issues
            .iter()
            .map(SizeIssue::severity)
            .max_by_key(|s| match s {
                SizeSeverity::Warning => 0,
                SizeSeverity::Critical => 1,
            })
    }

    /// Calculate the total "size score" - a combined metric.
    /// Higher values indicate larger/more complex functions.
    #[must_use]
    pub fn size_score(&self) -> f64 {
        // Weighted combination of metrics
        f64::from(self.sloc) * 1.0
            + f64::from(self.parameters) * 3.0
            + f64::from(self.local_variables) * 2.0
            + f64::from(self.branches) * 2.5
            + f64::from(self.return_statements) * 1.5
    }
}

/// Aggregate statistics for function size analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSizeStats {
    /// Total number of functions analyzed
    pub total_functions: usize,
    /// Number of functions with issues
    pub functions_with_issues: usize,
    /// Number of critical issues
    pub critical_issues: usize,
    /// Number of warning issues
    pub warning_issues: usize,
    /// Average SLOC per function
    pub avg_sloc: f64,
    /// Maximum SLOC found
    pub max_sloc: u32,
    /// Average parameters per function
    pub avg_parameters: f64,
    /// Maximum parameters found
    pub max_parameters: u32,
    /// Average local variables per function
    pub avg_variables: f64,
    /// Distribution by category
    pub category_distribution: HashMap<String, usize>,
    /// Issue type counts
    pub issue_counts: HashMap<String, usize>,
}

impl FunctionSizeStats {
    /// Calculate statistics from a list of function metrics.
    fn from_metrics(functions: &[FunctionSizeMetrics]) -> Self {
        if functions.is_empty() {
            return Self {
                total_functions: 0,
                functions_with_issues: 0,
                critical_issues: 0,
                warning_issues: 0,
                avg_sloc: 0.0,
                max_sloc: 0,
                avg_parameters: 0.0,
                max_parameters: 0,
                avg_variables: 0.0,
                category_distribution: HashMap::new(),
                issue_counts: HashMap::new(),
            };
        }

        let total = functions.len();
        let functions_with_issues = functions.iter().filter(|f| f.has_issues()).count();

        let critical_issues: usize = functions
            .iter()
            .flat_map(|f| &f.issues)
            .filter(|i| i.severity() == SizeSeverity::Critical)
            .count();

        let warning_issues: usize = functions
            .iter()
            .flat_map(|f| &f.issues)
            .filter(|i| i.severity() == SizeSeverity::Warning)
            .count();

        let total_sloc: u64 = functions.iter().map(|f| u64::from(f.sloc)).sum();
        let avg_sloc = total_sloc as f64 / total as f64;
        let max_sloc = functions.iter().map(|f| f.sloc).max().unwrap_or(0);

        let total_params: u64 = functions.iter().map(|f| u64::from(f.parameters)).sum();
        let avg_parameters = total_params as f64 / total as f64;
        let max_parameters = functions.iter().map(|f| f.parameters).max().unwrap_or(0);

        let total_vars: u64 = functions.iter().map(|f| u64::from(f.local_variables)).sum();
        let avg_variables = total_vars as f64 / total as f64;

        // Category distribution
        let mut category_distribution = HashMap::new();
        for func in functions {
            let key = format!("{:?}", func.category).to_lowercase();
            *category_distribution.entry(key).or_insert(0) += 1;
        }

        // Issue type counts
        let mut issue_counts = HashMap::new();
        for func in functions {
            for issue in &func.issues {
                let key = match issue {
                    SizeIssue::TooLong { .. } => "too_long",
                    SizeIssue::TooManyParams { .. } => "too_many_params",
                    SizeIssue::TooManyVariables { .. } => "too_many_variables",
                    SizeIssue::TooManyReturns { .. } => "too_many_returns",
                    SizeIssue::TooManyBranches { .. } => "too_many_branches",
                };
                *issue_counts.entry(key.to_string()).or_insert(0) += 1;
            }
        }

        Self {
            total_functions: total,
            functions_with_issues,
            critical_issues,
            warning_issues,
            avg_sloc,
            max_sloc,
            avg_parameters,
            max_parameters,
            avg_variables,
            category_distribution,
            issue_counts,
        }
    }
}

/// Complete function size analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSizeAnalysis {
    /// Path that was analyzed
    pub path: PathBuf,
    /// Language filter applied (if any)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub language: Option<String>,
    /// All function metrics
    pub functions: Vec<FunctionSizeMetrics>,
    /// Functions with issues (violations)
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub violations: Vec<FunctionSizeMetrics>,
    /// Aggregate statistics
    pub stats: FunctionSizeStats,
    /// Thresholds used for analysis
    pub thresholds: SizeThresholds,
    /// Files that could not be analyzed
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<FunctionSizeError>,
}

/// Error encountered during function size analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSizeError {
    /// File path where error occurred
    pub file: PathBuf,
    /// Error message
    pub message: String,
}

// =============================================================================
// SORT OPTIONS
// =============================================================================

/// Sorting options for function size results.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SizeSortBy {
    /// Sort by SLOC (default)
    #[default]
    Sloc,
    /// Sort by number of parameters
    Params,
    /// Sort by combined size score
    Score,
    /// Sort by number of issues
    Issues,
    /// Sort by number of variables
    Variables,
    /// Sort by number of branches
    Branches,
}

impl std::str::FromStr for SizeSortBy {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "sloc" | "lines" => Ok(Self::Sloc),
            "params" | "parameters" => Ok(Self::Params),
            "score" | "complexity" => Ok(Self::Score),
            "issues" | "violations" => Ok(Self::Issues),
            "variables" | "vars" => Ok(Self::Variables),
            "branches" => Ok(Self::Branches),
            _ => Err(format!("Unknown sort option: {}", s)),
        }
    }
}

// =============================================================================
// AST ANALYSIS
// =============================================================================

/// Node types that represent statements in various languages.
const STATEMENT_NODE_TYPES: &[&str] = &[
    // Python
    "expression_statement",
    "return_statement",
    "if_statement",
    "for_statement",
    "while_statement",
    "try_statement",
    "with_statement",
    "assert_statement",
    "raise_statement",
    "pass_statement",
    "break_statement",
    "continue_statement",
    "import_statement",
    "import_from_statement",
    "global_statement",
    "nonlocal_statement",
    "delete_statement",
    "match_statement",
    // TypeScript/JavaScript
    "return_statement",
    "switch_statement",
    "for_in_statement",
    "do_statement",
    "throw_statement",
    "variable_declaration",
    "lexical_declaration",
    // Rust
    "let_declaration",
    "return_expression",
    "if_expression",
    "match_expression",
    "for_expression",
    "while_expression",
    "loop_expression",
    "break_expression",
    "continue_expression",
    "macro_invocation",
    // Go
    "go_statement",
    "select_statement",
    "defer_statement",
    "var_declaration",
    "short_var_declaration",
    "assignment_statement",
    // Java
    "switch_expression",
    "enhanced_for_statement",
    "local_variable_declaration",
    // C/C++
    "goto_statement",
    "declaration",
    "compound_statement",
];

/// Node types for return statements.
const RETURN_NODE_TYPES: &[&str] = &[
    "return_statement",  // Python, TS/JS, Go, Java, C/C++
    "return_expression", // Rust
    "throw_statement",   // TS/JS, Java - counts as exit point
    "raise_statement",   // Python - counts as exit point
];

/// Node types for branching constructs.
const BRANCH_NODE_TYPES: &[&str] = &[
    "if_statement",
    "if_expression",
    "elif_clause",
    "else_if_clause",
    "switch_statement",
    "switch_expression",
    "match_expression",
    "match_statement",
    "conditional_expression", // ternary
    "ternary_expression",
];

/// Node types for variable declarations.
const VARIABLE_DECL_TYPES: &[&str] = &[
    // Python
    "assignment",
    "augmented_assignment",
    // TypeScript/JavaScript
    "variable_declaration",
    "lexical_declaration",
    "variable_declarator",
    // Rust
    "let_declaration",
    // Go
    "var_declaration",
    "short_var_declaration",
    "var_spec",
    // Java
    "local_variable_declaration",
    "variable_declarator",
    // C/C++
    "declaration",
    "init_declarator",
];

/// Node types for function definitions.
const FUNCTION_NODE_TYPES: &[&str] = &[
    "function_definition",    // Python
    "function_declaration",   // TS/JS, Go
    "method_definition",      // TS/JS
    "arrow_function",         // TS/JS
    "function_item",          // Rust
    "method_declaration",     // Go, Java
    "constructor_declaration", // Java
];

/// AST-based function size analyzer.
struct FunctionSizeAnalyzer<'a> {
    source: &'a [u8],
    lines: Vec<&'a str>,
}

impl<'a> FunctionSizeAnalyzer<'a> {
    fn new(source: &'a [u8]) -> Self {
        let source_str = std::str::from_utf8(source).unwrap_or("");
        let lines: Vec<&str> = source_str.lines().collect();
        Self { source, lines }
    }

    /// Count SLOC within a line range (excluding blanks and comment-only lines).
    fn count_sloc(&self, start_line: usize, end_line: usize) -> u32 {
        let mut count = 0u32;
        for i in start_line..=end_line.min(self.lines.len().saturating_sub(1)) {
            let line = self.lines.get(i).map(|s| s.trim()).unwrap_or("");
            if !line.is_empty() && !is_comment_only(line) {
                count += 1;
            }
        }
        count
    }

    /// Analyze a function node for size metrics.
    fn analyze_function(&self, node: Node) -> (u32, u32, u32, u32, u32) {
        let mut statements = 0u32;
        let mut returns = 0u32;
        let mut branches = 0u32;
        let mut variables = 0u32;

        // Count parameters
        let params = self.count_parameters(node);

        // Walk the function body
        self.walk_function_body(
            node,
            &mut statements,
            &mut returns,
            &mut branches,
            &mut variables,
            0,
        );

        (statements, params, variables, returns, branches)
    }

    /// Count function parameters.
    fn count_parameters(&self, node: Node) -> u32 {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "parameters" | "formal_parameters" | "parameter_list" | "function_parameters" => {
                    return self.count_param_children(child);
                }
                _ => {}
            }
        }
        0
    }

    /// Count parameter children in a parameter list node.
    fn count_param_children(&self, params_node: Node) -> u32 {
        let mut count = 0u32;
        let mut cursor = params_node.walk();
        for child in params_node.children(&mut cursor) {
            match child.kind() {
                // Skip punctuation and non-parameter nodes
                "(" | ")" | "," | "comment" => {}
                // Python-style self/cls don't count as "real" parameters for API complexity
                "identifier" => {
                    let text = child.utf8_text(self.source).unwrap_or("");
                    if text != "self" && text != "cls" {
                        count += 1;
                    }
                }
                // Actual parameter definitions
                "parameter"
                | "simple_parameter"
                | "typed_parameter"
                | "default_parameter"
                | "typed_default_parameter"
                | "required_parameter"
                | "optional_parameter"
                | "rest_parameter"
                | "spread_parameter"
                | "formal_parameter"
                | "variadic_parameter" => {
                    // Check for self/cls in method parameters
                    let text = child.utf8_text(self.source).unwrap_or("");
                    if !text.starts_with("self") && !text.starts_with("cls") {
                        count += 1;
                    }
                }
                _ => {
                    // May be a parameter node in some languages
                    if child.child_count() > 0 {
                        count += 1;
                    }
                }
            }
        }
        count
    }

    /// Walk the function body and count metrics.
    fn walk_function_body(
        &self,
        node: Node,
        statements: &mut u32,
        returns: &mut u32,
        branches: &mut u32,
        variables: &mut u32,
        depth: usize,
    ) {
        // Prevent infinite recursion
        if depth > 100 {
            return;
        }

        let kind = node.kind();

        // Count statements
        if STATEMENT_NODE_TYPES.contains(&kind) {
            *statements += 1;
        }

        // Count returns
        if RETURN_NODE_TYPES.contains(&kind) {
            *returns += 1;
        }

        // Count branches
        if BRANCH_NODE_TYPES.contains(&kind) {
            *branches += 1;
        }

        // Count variable declarations (but not nested function variables)
        if VARIABLE_DECL_TYPES.contains(&kind) && !FUNCTION_NODE_TYPES.contains(&kind) {
            // Count each declarator in the declaration
            let declarator_count = self.count_declarators(node);
            *variables += declarator_count.max(1);
        }

        // Don't recurse into nested function definitions
        if FUNCTION_NODE_TYPES.contains(&kind) && depth > 0 {
            return;
        }

        // Recurse into children
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.walk_function_body(child, statements, returns, branches, variables, depth + 1);
        }
    }

    /// Count declarators in a declaration node (for multiple variable declarations).
    fn count_declarators(&self, node: Node) -> u32 {
        let mut count = 0u32;
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "variable_declarator" | "init_declarator" | "var_spec" | "identifier" => {
                    count += 1;
                }
                _ => {}
            }
        }
        count
    }
}

/// Check if a line is comment-only (simple heuristic).
fn is_comment_only(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.starts_with('#')  // Python, Shell
        || trimmed.starts_with("//") // C, C++, Java, JS, Go, Rust
        || trimmed.starts_with("/*") // Block comment start
        || trimmed.starts_with('*')  // Block comment continuation
        || trimmed.starts_with("*/") // Block comment end
        || trimmed.starts_with("'''") // Python docstring
        || trimmed.starts_with("\"\"\"") // Python docstring
}

// =============================================================================
// ANALYSIS FUNCTIONS
// =============================================================================

/// Analyze function size metrics for a file or directory.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `language` - Optional language filter
/// * `thresholds` - Optional custom thresholds (uses defaults if None)
///
/// # Returns
///
/// Complete analysis with per-function metrics and statistics.
///
/// # Example
///
/// ```ignore
/// use go_brrr::metrics::function_size::{analyze_function_size, SizeThresholds};
///
/// // Use default thresholds
/// let result = analyze_function_size("./src", Some("python"), None)?;
///
/// // Use custom thresholds
/// let custom = SizeThresholds {
///     sloc_warning: 40,
///     sloc_critical: 80,
///     ..Default::default()
/// };
/// let result = analyze_function_size("./src", Some("python"), Some(custom))?;
/// ```
pub fn analyze_function_size(
    path: impl AsRef<Path>,
    language: Option<&str>,
    thresholds: Option<SizeThresholds>,
) -> Result<FunctionSizeAnalysis> {
    let path = path.as_ref();
    let thresholds = thresholds.unwrap_or_default();

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Path not found: {}", path.display()),
        )));
    }

    if path.is_file() {
        return analyze_file_function_size(path, &thresholds);
    }

    // Directory analysis
    let path_str = path
        .to_str()
        .ok_or_else(|| BrrrError::InvalidArgument("Invalid path encoding".to_string()))?;

    let scanner = ProjectScanner::new(path_str)?;

    let config = if let Some(lang) = language {
        ScanConfig::for_language(lang)
    } else {
        ScanConfig::default()
    };

    let scan_result = scanner.scan_with_config(&config)?;

    if scan_result.files.is_empty() {
        return Err(BrrrError::InvalidArgument(format!(
            "No source files found in {} (filter: {:?})",
            path.display(),
            language
        )));
    }

    debug!(
        "Analyzing {} files for function size metrics",
        scan_result.files.len()
    );

    // Analyze files in parallel
    let results: Vec<(Vec<FunctionSizeMetrics>, Vec<FunctionSizeError>)> = scan_result
        .files
        .par_iter()
        .map(|file| analyze_file_functions(file, &thresholds))
        .collect();

    // Aggregate results
    let mut all_functions = Vec::new();
    let mut all_errors = Vec::new();

    for (functions, errors) in results {
        all_functions.extend(functions);
        all_errors.extend(errors);
    }

    // Calculate statistics
    let stats = FunctionSizeStats::from_metrics(&all_functions);

    // Extract violations
    let violations: Vec<FunctionSizeMetrics> = all_functions
        .iter()
        .filter(|f| f.has_issues())
        .cloned()
        .collect();

    Ok(FunctionSizeAnalysis {
        path: path.to_path_buf(),
        language: language.map(String::from),
        functions: all_functions,
        violations,
        stats,
        thresholds,
        errors: all_errors,
    })
}

/// Analyze function size metrics for a single file.
pub fn analyze_file_function_size(
    path: impl AsRef<Path>,
    thresholds: &SizeThresholds,
) -> Result<FunctionSizeAnalysis> {
    let path = path.as_ref();

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("File not found: {}", path.display()),
        )));
    }

    let (functions, errors) = analyze_file_functions(path, thresholds);

    let stats = FunctionSizeStats::from_metrics(&functions);
    let violations: Vec<FunctionSizeMetrics> = functions
        .iter()
        .filter(|f| f.has_issues())
        .cloned()
        .collect();

    // Detect language
    let registry = LanguageRegistry::global();
    let language = registry
        .detect_language(path)
        .map(|l| l.name().to_string());

    Ok(FunctionSizeAnalysis {
        path: path.to_path_buf(),
        language,
        functions,
        violations,
        stats,
        thresholds: thresholds.clone(),
        errors,
    })
}

/// Internal function to analyze all functions in a file.
fn analyze_file_functions(
    file: &Path,
    thresholds: &SizeThresholds,
) -> (Vec<FunctionSizeMetrics>, Vec<FunctionSizeError>) {
    let mut results = Vec::new();
    let mut errors = Vec::new();

    // Read source file
    let source = match std::fs::read(file) {
        Ok(s) => s,
        Err(e) => {
            errors.push(FunctionSizeError {
                file: file.to_path_buf(),
                message: format!("Failed to read file: {}", e),
            });
            return (results, errors);
        }
    };

    // Extract module info for function list
    let module = match AstExtractor::extract_file(file) {
        Ok(m) => m,
        Err(e) => {
            errors.push(FunctionSizeError {
                file: file.to_path_buf(),
                message: format!("Failed to parse file: {}", e),
            });
            return (results, errors);
        }
    };

    // Get language for parsing
    let registry = LanguageRegistry::global();
    let lang = match registry.detect_language(file) {
        Some(l) => l,
        None => {
            errors.push(FunctionSizeError {
                file: file.to_path_buf(),
                message: "Could not detect language".to_string(),
            });
            return (results, errors);
        }
    };

    // Parse for AST analysis
    let mut parser = match lang.parser() {
        Ok(p) => p,
        Err(e) => {
            errors.push(FunctionSizeError {
                file: file.to_path_buf(),
                message: format!("Failed to create parser: {}", e),
            });
            return (results, errors);
        }
    };

    let tree = match parser.parse(&source, None) {
        Some(t) => t,
        None => {
            errors.push(FunctionSizeError {
                file: file.to_path_buf(),
                message: "Failed to parse file".to_string(),
            });
            return (results, errors);
        }
    };

    let analyzer = FunctionSizeAnalyzer::new(&source);

    // Process top-level functions
    for func in &module.functions {
        if let Some(metrics) =
            analyze_single_function(&analyzer, &tree, file, &func.name, func, thresholds)
        {
            results.push(metrics);
        }
    }

    // Process class methods
    for class in &module.classes {
        for method in &class.methods {
            let qualified_name = format!("{}.{}", class.name, method.name);
            if let Some(mut metrics) =
                analyze_single_function(&analyzer, &tree, file, &qualified_name, method, thresholds)
            {
                metrics.name = qualified_name;
                results.push(metrics);
            }
        }
    }

    (results, errors)
}

/// Analyze a single function and compute metrics.
fn analyze_single_function(
    analyzer: &FunctionSizeAnalyzer,
    tree: &Tree,
    file: &Path,
    name: &str,
    func_info: &crate::ast::FunctionInfo,
    base_thresholds: &SizeThresholds,
) -> Option<FunctionSizeMetrics> {
    let start_line = func_info.line_number;
    let end_line = func_info.end_line_number.unwrap_or(start_line);

    if start_line == 0 {
        return None;
    }

    // Find the function node in the AST
    let func_node = find_function_node(tree.root_node(), start_line)?;

    // Analyze the function
    let (statements, params, variables, returns, branches) = analyzer.analyze_function(func_node);

    // Calculate SLOC
    let sloc = analyzer.count_sloc(start_line.saturating_sub(1), end_line.saturating_sub(1));

    // Detect function category
    let base_name = name.split('.').last().unwrap_or(name);
    let category = FunctionCategory::from_name(base_name);

    // Get adjusted thresholds based on category
    let thresholds = category.adjusted_thresholds(base_thresholds);

    // Check for issues
    let mut issues = Vec::new();
    let mut suggestions = Vec::new();

    // SLOC check
    if sloc > thresholds.sloc_critical {
        let issue = SizeIssue::TooLong {
            sloc,
            threshold: thresholds.sloc_critical,
            severity: SizeSeverity::Critical,
        };
        suggestions.push(issue.suggestion().to_string());
        issues.push(issue);
    } else if sloc > thresholds.sloc_warning {
        let issue = SizeIssue::TooLong {
            sloc,
            threshold: thresholds.sloc_warning,
            severity: SizeSeverity::Warning,
        };
        suggestions.push(issue.suggestion().to_string());
        issues.push(issue);
    }

    // Parameters check (use AST-detected params, fall back to func_info)
    let param_count = if params > 0 {
        params
    } else {
        func_info.params.len() as u32
    };

    if param_count > thresholds.params_critical {
        let issue = SizeIssue::TooManyParams {
            count: param_count,
            threshold: thresholds.params_critical,
            severity: SizeSeverity::Critical,
        };
        suggestions.push(issue.suggestion().to_string());
        issues.push(issue);
    } else if param_count > thresholds.params_warning {
        let issue = SizeIssue::TooManyParams {
            count: param_count,
            threshold: thresholds.params_warning,
            severity: SizeSeverity::Warning,
        };
        suggestions.push(issue.suggestion().to_string());
        issues.push(issue);
    }

    // Variables check
    if variables > thresholds.variables_critical {
        let issue = SizeIssue::TooManyVariables {
            count: variables,
            threshold: thresholds.variables_critical,
            severity: SizeSeverity::Critical,
        };
        suggestions.push(issue.suggestion().to_string());
        issues.push(issue);
    } else if variables > thresholds.variables_warning {
        let issue = SizeIssue::TooManyVariables {
            count: variables,
            threshold: thresholds.variables_warning,
            severity: SizeSeverity::Warning,
        };
        suggestions.push(issue.suggestion().to_string());
        issues.push(issue);
    }

    // Returns check
    if returns > thresholds.returns_warning {
        let issue = SizeIssue::TooManyReturns {
            count: returns,
            threshold: thresholds.returns_warning,
            severity: SizeSeverity::Warning,
        };
        suggestions.push(issue.suggestion().to_string());
        issues.push(issue);
    }

    // Branches check
    if branches > thresholds.branches_warning {
        let issue = SizeIssue::TooManyBranches {
            count: branches,
            threshold: thresholds.branches_warning,
            severity: SizeSeverity::Warning,
        };
        suggestions.push(issue.suggestion().to_string());
        issues.push(issue);
    }

    // Deduplicate suggestions
    suggestions.sort();
    suggestions.dedup();

    Some(FunctionSizeMetrics {
        name: name.to_string(),
        file: file.to_path_buf(),
        line: start_line,
        end_line,
        sloc,
        statements,
        parameters: param_count,
        local_variables: variables,
        return_statements: returns,
        branches,
        category,
        issues,
        suggestions,
    })
}

/// Find the function node at the given line in the AST.
fn find_function_node(node: Node, target_line: usize) -> Option<Node> {
    let node_start = node.start_position().row + 1; // 1-indexed
    let node_end = node.end_position().row + 1;

    // Check if this is a function node at the target line
    if FUNCTION_NODE_TYPES.contains(&node.kind()) && node_start == target_line {
        return Some(node);
    }

    // Check if target line is within this node's range
    if target_line < node_start || target_line > node_end {
        return None;
    }

    // Recurse into children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(found) = find_function_node(child, target_line) {
            return Some(found);
        }
    }

    None
}

/// Sort functions by the specified criteria.
pub fn sort_functions(functions: &mut [FunctionSizeMetrics], sort_by: SizeSortBy, descending: bool) {
    functions.sort_by(|a, b| {
        let cmp = match sort_by {
            SizeSortBy::Sloc => a.sloc.cmp(&b.sloc),
            SizeSortBy::Params => a.parameters.cmp(&b.parameters),
            SizeSortBy::Score => a.size_score().partial_cmp(&b.size_score()).unwrap_or(std::cmp::Ordering::Equal),
            SizeSortBy::Issues => a.issues.len().cmp(&b.issues.len()),
            SizeSortBy::Variables => a.local_variables.cmp(&b.local_variables),
            SizeSortBy::Branches => a.branches.cmp(&b.branches),
        };
        if descending {
            cmp.reverse()
        } else {
            cmp
        }
    });
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
    fn test_function_category_detection() {
        assert_eq!(FunctionCategory::from_name("__init__"), FunctionCategory::Constructor);
        assert_eq!(FunctionCategory::from_name("new"), FunctionCategory::Constructor);
        assert_eq!(FunctionCategory::from_name("constructor"), FunctionCategory::Constructor);

        assert_eq!(FunctionCategory::from_name("test_something"), FunctionCategory::Test);
        assert_eq!(FunctionCategory::from_name("TestSomething"), FunctionCategory::Test);
        assert_eq!(FunctionCategory::from_name("something_test"), FunctionCategory::Test);

        assert_eq!(FunctionCategory::from_name("configure_app"), FunctionCategory::Configuration);
        assert_eq!(FunctionCategory::from_name("setup_database"), FunctionCategory::Configuration);
        assert_eq!(FunctionCategory::from_name("setup"), FunctionCategory::Configuration);

        assert_eq!(FunctionCategory::from_name("create_user"), FunctionCategory::Factory);
        assert_eq!(FunctionCategory::from_name("build_config"), FunctionCategory::Factory);

        assert_eq!(FunctionCategory::from_name("on_click"), FunctionCategory::Handler);
        assert_eq!(FunctionCategory::from_name("handle_event"), FunctionCategory::Handler);

        assert_eq!(FunctionCategory::from_name("process_data"), FunctionCategory::Normal);
    }

    #[test]
    fn test_simple_function_analysis() {
        let source = r#"
def simple():
    return 42
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_function_size(file.path(), &SizeThresholds::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].name, "simple");
        assert!(analysis.functions[0].issues.is_empty());
        assert_eq!(analysis.functions[0].category, FunctionCategory::Normal);
    }

    #[test]
    fn test_function_with_params() {
        let source = r#"
def many_params(a, b, c, d, e, f, g, h):
    return a + b + c + d + e + f + g + h
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_function_size(file.path(), &SizeThresholds::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert!(analysis.functions[0].parameters >= 6);
        // Should have "too many params" issue
        assert!(!analysis.functions[0].issues.is_empty());
    }

    #[test]
    fn test_long_function() {
        let mut lines = vec!["def long_function():".to_string()];
        for i in 0..40 {
            lines.push(format!("    x{} = {}", i, i));
        }
        lines.push("    return x0".to_string());
        let source = lines.join("\n");

        let file = create_temp_file(&source, ".py");
        let result = analyze_file_function_size(file.path(), &SizeThresholds::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert!(analysis.functions[0].sloc > 30);
        // Should have "too long" issue
        assert!(analysis.functions[0].issues.iter().any(|i| matches!(i, SizeIssue::TooLong { .. })));
    }

    #[test]
    fn test_constructor_adjusted_thresholds() {
        let source = r#"
class MyClass:
    def __init__(self, a, b, c, d, e, f, g):
        self.a = a
        self.b = b
        self.c = c
        self.d = d
        self.e = e
        self.f = f
        self.g = g
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_function_size(file.path(), &SizeThresholds::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].category, FunctionCategory::Constructor);
        // Constructor has adjusted thresholds, so 7 params should not be critical
    }

    #[test]
    fn test_test_function_adjusted_thresholds() {
        let mut lines = vec!["def test_something():".to_string()];
        lines.push("    # Setup".to_string());
        for i in 0..45 {
            lines.push(format!("    x{} = {}", i, i));
        }
        lines.push("    assert x0 == 0".to_string());
        let source = lines.join("\n");

        let file = create_temp_file(&source, ".py");
        let result = analyze_file_function_size(file.path(), &SizeThresholds::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].category, FunctionCategory::Test);
        // Test has adjusted threshold (30 + 20 = 50), so 45 lines should be OK
        let too_long_issues: Vec<_> = analysis.functions[0]
            .issues
            .iter()
            .filter(|i| matches!(i, SizeIssue::TooLong { .. }))
            .collect();
        assert!(too_long_issues.is_empty() || too_long_issues.iter().all(|i| i.severity() == SizeSeverity::Warning));
    }

    #[test]
    fn test_size_issue_display() {
        let issue = SizeIssue::TooLong {
            sloc: 50,
            threshold: 30,
            severity: SizeSeverity::Warning,
        };
        assert!(issue.to_string().contains("50"));
        assert!(issue.to_string().contains("30"));
    }

    #[test]
    fn test_sort_functions() {
        let mut functions = vec![
            FunctionSizeMetrics {
                name: "small".to_string(),
                file: PathBuf::from("test.py"),
                line: 1,
                end_line: 5,
                sloc: 5,
                statements: 3,
                parameters: 1,
                local_variables: 2,
                return_statements: 1,
                branches: 0,
                category: FunctionCategory::Normal,
                issues: vec![],
                suggestions: vec![],
            },
            FunctionSizeMetrics {
                name: "large".to_string(),
                file: PathBuf::from("test.py"),
                line: 10,
                end_line: 50,
                sloc: 40,
                statements: 30,
                parameters: 5,
                local_variables: 10,
                return_statements: 3,
                branches: 5,
                category: FunctionCategory::Normal,
                issues: vec![SizeIssue::TooLong {
                    sloc: 40,
                    threshold: 30,
                    severity: SizeSeverity::Warning,
                }],
                suggestions: vec![],
            },
        ];

        sort_functions(&mut functions, SizeSortBy::Sloc, true);
        assert_eq!(functions[0].name, "large");
        assert_eq!(functions[1].name, "small");
    }

    #[test]
    fn test_typescript_analysis() {
        let source = r#"
function simple(): number {
    return 42;
}

function withParams(a: number, b: string, c: boolean): void {
    const x = a;
    const y = b;
    console.log(x, y, c);
}
"#;
        let file = create_temp_file(source, ".ts");
        let result = analyze_file_function_size(file.path(), &SizeThresholds::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 2);
    }

    #[test]
    fn test_statistics_calculation() {
        let functions = vec![
            FunctionSizeMetrics {
                name: "f1".to_string(),
                file: PathBuf::from("test.py"),
                line: 1,
                end_line: 10,
                sloc: 10,
                statements: 8,
                parameters: 2,
                local_variables: 3,
                return_statements: 1,
                branches: 1,
                category: FunctionCategory::Normal,
                issues: vec![],
                suggestions: vec![],
            },
            FunctionSizeMetrics {
                name: "f2".to_string(),
                file: PathBuf::from("test.py"),
                line: 15,
                end_line: 50,
                sloc: 35,
                statements: 25,
                parameters: 7,
                local_variables: 8,
                return_statements: 4,
                branches: 6,
                category: FunctionCategory::Normal,
                issues: vec![
                    SizeIssue::TooLong {
                        sloc: 35,
                        threshold: 30,
                        severity: SizeSeverity::Warning,
                    },
                    SizeIssue::TooManyParams {
                        count: 7,
                        threshold: 5,
                        severity: SizeSeverity::Warning,
                    },
                ],
                suggestions: vec![],
            },
        ];

        let stats = FunctionSizeStats::from_metrics(&functions);

        assert_eq!(stats.total_functions, 2);
        assert_eq!(stats.functions_with_issues, 1);
        assert_eq!(stats.warning_issues, 2);
        assert_eq!(stats.critical_issues, 0);
        assert!((stats.avg_sloc - 22.5).abs() < 0.01);
        assert_eq!(stats.max_sloc, 35);
        assert_eq!(stats.max_parameters, 7);
    }

    #[test]
    fn test_size_score_calculation() {
        let func = FunctionSizeMetrics {
            name: "test".to_string(),
            file: PathBuf::from("test.py"),
            line: 1,
            end_line: 20,
            sloc: 20,
            statements: 15,
            parameters: 3,
            local_variables: 5,
            return_statements: 2,
            branches: 4,
            category: FunctionCategory::Normal,
            issues: vec![],
            suggestions: vec![],
        };

        let score = func.size_score();
        // 20*1.0 + 3*3.0 + 5*2.0 + 4*2.5 + 2*1.5 = 20 + 9 + 10 + 10 + 3 = 52
        assert!((score - 52.0).abs() < 0.01);
    }

    #[test]
    fn test_empty_file() {
        let source = "# Just a comment\n";
        let file = create_temp_file(source, ".py");
        let result = analyze_file_function_size(file.path(), &SizeThresholds::default());

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 0);
        assert_eq!(analysis.stats.total_functions, 0);
    }

    #[test]
    fn test_nonexistent_file() {
        let result = analyze_function_size("/nonexistent/path/file.py", None, None);
        assert!(result.is_err());
    }
}
