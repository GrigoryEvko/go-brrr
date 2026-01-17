//! Nesting depth metrics for code complexity analysis.
//!
//! This module measures how deeply nested code structures are within functions.
//! Deep nesting is a strong indicator of code complexity that makes code harder
//! to understand, test, and maintain.
//!
//! # Nesting Constructs Tracked
//!
//! The analyzer tracks nesting from various language constructs:
//!
//! | Category          | Constructs                                      |
//! |-------------------|-------------------------------------------------|
//! | Control Flow      | if, for, while, switch/match, try               |
//! | Closures/Lambdas  | lambda, arrow functions, closures               |
//! | Callbacks         | Nested function expressions (common in JS)      |
//! | Comprehensions    | List/dict/set comprehensions with conditions    |
//! | Blocks            | Named blocks in Rust, defer in Go               |
//!
//! # Risk Levels
//!
//! Nesting depth is classified into risk levels:
//!
//! - **Good (1-3)**: Acceptable nesting, code is readable
//! - **Acceptable (4-5)**: Consider refactoring
//! - **Complex (6-7)**: Hard to understand, should refactor
//! - **Severe (8+)**: Refactor immediately
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::metrics::{analyze_nesting, NestingDepthLevel};
//!
//! let result = analyze_nesting("./src", Some("python"), Some(5))?;
//! for func in &result.functions {
//!     if func.risk_level == NestingDepthLevel::Severe {
//!         println!("Deep nesting in {}: depth {} at line {}",
//!             func.function_name, func.max_depth, func.deepest_line);
//!         for suggestion in &func.suggestions {
//!             println!("  - {}", suggestion);
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
// TYPES
// =============================================================================

/// Risk level classification based on nesting depth.
///
/// Thresholds are based on software engineering best practices and
/// readability research.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum NestingDepthLevel {
    /// Max depth 1-3: Good, acceptable nesting
    Good,
    /// Max depth 4-5: Acceptable but consider simplifying
    Acceptable,
    /// Max depth 6-7: Complex, hard to understand
    Complex,
    /// Max depth 8+: Severe, refactor immediately
    Severe,
}

impl NestingDepthLevel {
    /// Classify nesting depth into risk level.
    #[must_use]
    pub fn from_depth(depth: u32) -> Self {
        match depth {
            0..=3 => Self::Good,
            4..=5 => Self::Acceptable,
            6..=7 => Self::Complex,
            _ => Self::Severe,
        }
    }

    /// Get human-readable description.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Good => "Good nesting depth, code is readable",
            Self::Acceptable => "Acceptable, consider simplifying if possible",
            Self::Complex => "Complex nesting, hard to understand",
            Self::Severe => "Severe nesting, refactor immediately",
        }
    }

    /// Get the color code for CLI output (ANSI).
    #[must_use]
    pub const fn color_code(&self) -> &'static str {
        match self {
            Self::Good => "\x1b[32m",       // Green
            Self::Acceptable => "\x1b[33m", // Yellow
            Self::Complex => "\x1b[31m",    // Red
            Self::Severe => "\x1b[35m",     // Magenta
        }
    }

    /// Get numeric threshold for this level.
    #[must_use]
    pub const fn threshold(&self) -> u32 {
        match self {
            Self::Good => 3,
            Self::Acceptable => 5,
            Self::Complex => 7,
            Self::Severe => u32::MAX,
        }
    }
}

impl std::fmt::Display for NestingDepthLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Good => write!(f, "good"),
            Self::Acceptable => write!(f, "acceptable"),
            Self::Complex => write!(f, "complex"),
            Self::Severe => write!(f, "severe"),
        }
    }
}

/// Type of construct that contributes to nesting.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum NestingConstruct {
    /// if statement
    If,
    /// else if / elif clause
    ElseIf,
    /// else clause
    Else,
    /// for loop
    For,
    /// while loop
    While,
    /// do-while loop
    DoWhile,
    /// switch / match statement
    Switch,
    /// try block
    Try,
    /// catch / except clause
    Catch,
    /// finally clause
    Finally,
    /// lambda / anonymous function
    Lambda,
    /// closure expression
    Closure,
    /// callback function (nested function expression)
    Callback,
    /// list/dict/set comprehension
    Comprehension,
    /// with statement (Python context manager)
    With,
    /// unsafe block (Rust)
    Unsafe,
    /// async block (Rust)
    Async,
    /// loop expression (Rust infinite loop)
    Loop,
    /// select statement (Go channels)
    Select,
    /// defer statement (Go)
    Defer,
    /// Named/labeled block
    Block,
    /// Generic nesting construct
    Other(String),
}

impl std::fmt::Display for NestingConstruct {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::If => write!(f, "if"),
            Self::ElseIf => write!(f, "else if"),
            Self::Else => write!(f, "else"),
            Self::For => write!(f, "for"),
            Self::While => write!(f, "while"),
            Self::DoWhile => write!(f, "do-while"),
            Self::Switch => write!(f, "switch/match"),
            Self::Try => write!(f, "try"),
            Self::Catch => write!(f, "catch"),
            Self::Finally => write!(f, "finally"),
            Self::Lambda => write!(f, "lambda"),
            Self::Closure => write!(f, "closure"),
            Self::Callback => write!(f, "callback"),
            Self::Comprehension => write!(f, "comprehension"),
            Self::With => write!(f, "with"),
            Self::Unsafe => write!(f, "unsafe"),
            Self::Async => write!(f, "async"),
            Self::Loop => write!(f, "loop"),
            Self::Select => write!(f, "select"),
            Self::Defer => write!(f, "defer"),
            Self::Block => write!(f, "block"),
            Self::Other(name) => write!(f, "{}", name),
        }
    }
}

/// Information about a deeply nested location.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeepNesting {
    /// Line number where deep nesting occurs
    pub line: usize,
    /// Nesting depth at this location
    pub depth: u32,
    /// Stack of constructs leading to this depth (e.g., ["if", "for", "if", "try"])
    pub construct_stack: Vec<String>,
}

/// Nesting metrics for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NestingMetrics {
    /// Function name (may include class prefix for methods)
    pub function_name: String,
    /// File path containing the function
    pub file: PathBuf,
    /// Starting line number (1-indexed)
    pub line: usize,
    /// Ending line number (1-indexed)
    pub end_line: usize,
    /// Maximum nesting depth in the function
    pub max_depth: u32,
    /// Average nesting depth across all lines
    pub average_depth: f64,
    /// Line with the deepest nesting
    pub deepest_line: usize,
    /// All locations with deep nesting (above threshold)
    pub deep_locations: Vec<DeepNesting>,
    /// Risk level classification
    pub risk_level: NestingDepthLevel,
    /// Suggestions for reducing nesting
    pub suggestions: Vec<String>,
    /// Depth histogram (depth -> line count)
    pub depth_distribution: HashMap<u32, usize>,
}

/// Simplified nesting info for summary output.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionNesting {
    /// Function name
    pub name: String,
    /// Starting line number
    pub line: usize,
    /// Maximum nesting depth
    pub max_depth: u32,
    /// Risk level
    pub risk_level: NestingDepthLevel,
}

impl From<&NestingMetrics> for FunctionNesting {
    fn from(nm: &NestingMetrics) -> Self {
        Self {
            name: nm.function_name.clone(),
            line: nm.line,
            max_depth: nm.max_depth,
            risk_level: nm.risk_level,
        }
    }
}

/// Statistics for nesting analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NestingStats {
    /// Total functions analyzed
    pub total_functions: usize,
    /// Average maximum depth across functions
    pub average_max_depth: f64,
    /// Global maximum depth found
    pub global_max_depth: u32,
    /// Minimum maximum depth found
    pub min_max_depth: u32,
    /// Median maximum depth
    pub median_max_depth: u32,
    /// Risk level distribution
    pub risk_distribution: HashMap<String, usize>,
    /// Functions with depth > 5 (common threshold)
    pub functions_over_threshold: usize,
}

impl NestingStats {
    /// Calculate statistics from nesting metrics.
    fn from_metrics(results: &[NestingMetrics]) -> Self {
        if results.is_empty() {
            return Self {
                total_functions: 0,
                average_max_depth: 0.0,
                global_max_depth: 0,
                min_max_depth: 0,
                median_max_depth: 0,
                risk_distribution: HashMap::new(),
                functions_over_threshold: 0,
            };
        }

        let depths: Vec<u32> = results.iter().map(|r| r.max_depth).collect();
        let total = depths.len();
        let sum: u64 = depths.iter().map(|&d| u64::from(d)).sum();
        let average = sum as f64 / total as f64;

        let max = depths.iter().copied().max().unwrap_or(0);
        let min = depths.iter().copied().min().unwrap_or(0);

        let mut sorted = depths.clone();
        sorted.sort_unstable();
        let median = if total % 2 == 0 {
            (sorted[total / 2 - 1] + sorted[total / 2]) / 2
        } else {
            sorted[total / 2]
        };

        let mut risk_distribution = HashMap::new();
        for r in results {
            *risk_distribution
                .entry(r.risk_level.to_string())
                .or_insert(0) += 1;
        }

        let functions_over_threshold = results.iter().filter(|r| r.max_depth > 5).count();

        Self {
            total_functions: total,
            average_max_depth: average,
            global_max_depth: max,
            min_max_depth: min,
            median_max_depth: median,
            risk_distribution,
            functions_over_threshold,
        }
    }
}

/// Complete nesting analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NestingAnalysis {
    /// Path that was analyzed
    pub path: PathBuf,
    /// Language filter applied
    pub language: Option<String>,
    /// Individual function nesting metrics
    pub functions: Vec<NestingMetrics>,
    /// Functions exceeding threshold
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violations: Option<Vec<NestingMetrics>>,
    /// Aggregate statistics
    pub stats: NestingStats,
    /// Threshold used for filtering
    #[serde(skip_serializing_if = "Option::is_none")]
    pub threshold: Option<u32>,
    /// Analysis errors
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<NestingAnalysisError>,
}

/// Error during nesting analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NestingAnalysisError {
    /// File path
    pub file: PathBuf,
    /// Error message
    pub message: String,
}

// =============================================================================
// NESTING CALCULATOR
// =============================================================================

/// Calculator for nesting depth with language-specific handling.
struct NestingCalculator<'a> {
    language: &'a str,
    current_depth: u32,
    max_depth: u32,
    deepest_line: usize,
    /// Stack of constructs at each depth level
    construct_stack: Vec<NestingConstruct>,
    /// Depth at each line (line number -> depth)
    line_depths: HashMap<usize, u32>,
    /// Deep nesting locations found
    deep_locations: Vec<DeepNesting>,
    /// Threshold for recording deep locations
    threshold: u32,
}

impl<'a> NestingCalculator<'a> {
    fn new(language: &'a str, threshold: u32) -> Self {
        Self {
            language,
            current_depth: 0,
            max_depth: 0,
            deepest_line: 0,
            construct_stack: Vec::new(),
            line_depths: HashMap::new(),
            deep_locations: Vec::new(),
            threshold,
        }
    }

    /// Enter a nesting level.
    fn enter_nesting(&mut self, construct: NestingConstruct, line: usize) {
        self.current_depth += 1;
        self.construct_stack.push(construct);

        // Update max depth tracking
        if self.current_depth > self.max_depth {
            self.max_depth = self.current_depth;
            self.deepest_line = line;
        }

        // Record depth at this line
        self.line_depths
            .entry(line)
            .and_modify(|d| *d = (*d).max(self.current_depth))
            .or_insert(self.current_depth);

        // Record deep location if above threshold
        if self.current_depth > self.threshold {
            let stack: Vec<String> = self
                .construct_stack
                .iter()
                .map(|c| c.to_string())
                .collect();

            self.deep_locations.push(DeepNesting {
                line,
                depth: self.current_depth,
                construct_stack: stack,
            });
        }
    }

    /// Exit a nesting level.
    fn exit_nesting(&mut self) {
        self.current_depth = self.current_depth.saturating_sub(1);
        self.construct_stack.pop();
    }

    /// Process a node and its children.
    fn process_node(&mut self, node: Node) {
        let line = node.start_position().row + 1;
        let kind = node.kind();

        // Record depth at this line
        self.line_depths
            .entry(line)
            .and_modify(|d| *d = (*d).max(self.current_depth))
            .or_insert(self.current_depth);

        // Check if this node increases nesting
        let construct = self.classify_nesting_construct(node, kind);

        if let Some(c) = construct {
            self.enter_nesting(c, line);
            self.process_children(node);
            self.exit_nesting();
        } else {
            self.process_children(node);
        }
    }

    /// Process all children of a node.
    fn process_children(&mut self, node: Node) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.process_node(child);
        }
    }

    /// Classify a node as a nesting construct (or None if it doesn't add nesting).
    fn classify_nesting_construct(&self, node: Node, kind: &str) -> Option<NestingConstruct> {
        match self.language {
            "python" => self.classify_python_construct(node, kind),
            "typescript" | "javascript" | "tsx" | "jsx" => {
                self.classify_javascript_construct(node, kind)
            }
            "rust" => self.classify_rust_construct(node, kind),
            "go" => self.classify_go_construct(node, kind),
            "java" => self.classify_java_construct(node, kind),
            "c" | "cpp" => self.classify_c_construct(node, kind),
            _ => self.classify_generic_construct(kind),
        }
    }

    /// Classify Python nesting constructs.
    fn classify_python_construct(&self, node: Node, kind: &str) -> Option<NestingConstruct> {
        match kind {
            "if_statement" => Some(NestingConstruct::If),
            "elif_clause" => Some(NestingConstruct::ElseIf),
            "else_clause" => {
                // Check if parent is if_statement
                if node.parent().is_some_and(|p| p.kind() == "if_statement") {
                    Some(NestingConstruct::Else)
                } else {
                    None
                }
            }
            "for_statement" => Some(NestingConstruct::For),
            "while_statement" => Some(NestingConstruct::While),
            "try_statement" => Some(NestingConstruct::Try),
            "except_clause" | "except_group_clause" => Some(NestingConstruct::Catch),
            "finally_clause" => Some(NestingConstruct::Finally),
            "with_statement" => Some(NestingConstruct::With),
            "match_statement" => Some(NestingConstruct::Switch),
            "lambda" => Some(NestingConstruct::Lambda),
            "list_comprehension" | "dictionary_comprehension" | "set_comprehension"
            | "generator_expression" => Some(NestingConstruct::Comprehension),
            _ => None,
        }
    }

    /// Classify JavaScript/TypeScript nesting constructs.
    fn classify_javascript_construct(&self, node: Node, kind: &str) -> Option<NestingConstruct> {
        match kind {
            "if_statement" => Some(NestingConstruct::If),
            "else_clause" => Some(NestingConstruct::Else),
            "for_statement" | "for_in_statement" | "for_of_statement" => {
                Some(NestingConstruct::For)
            }
            "while_statement" => Some(NestingConstruct::While),
            "do_statement" => Some(NestingConstruct::DoWhile),
            "switch_statement" => Some(NestingConstruct::Switch),
            "try_statement" => Some(NestingConstruct::Try),
            "catch_clause" => Some(NestingConstruct::Catch),
            "finally_clause" => Some(NestingConstruct::Finally),
            "arrow_function" | "function_expression" => {
                // Check if this is a callback (nested in a call)
                if self.is_callback(node) {
                    Some(NestingConstruct::Callback)
                } else {
                    Some(NestingConstruct::Lambda)
                }
            }
            _ => None,
        }
    }

    /// Check if a function expression is a callback (nested in a call expression).
    fn is_callback(&self, node: Node) -> bool {
        let mut current = node.parent();
        while let Some(parent) = current {
            match parent.kind() {
                "call_expression" | "method_invocation" => return true,
                "arguments" | "argument_list" => {
                    // Continue checking parent
                }
                "function_declaration"
                | "function_definition"
                | "method_definition"
                | "arrow_function" => {
                    // Reached another function boundary
                    return false;
                }
                _ => {}
            }
            current = parent.parent();
        }
        false
    }

    /// Classify Rust nesting constructs.
    fn classify_rust_construct(&self, _node: Node, kind: &str) -> Option<NestingConstruct> {
        match kind {
            "if_expression" | "if_let_expression" => Some(NestingConstruct::If),
            "else_clause" => Some(NestingConstruct::Else),
            "for_expression" => Some(NestingConstruct::For),
            "while_expression" | "while_let_expression" => Some(NestingConstruct::While),
            "loop_expression" => Some(NestingConstruct::Loop),
            "match_expression" => Some(NestingConstruct::Switch),
            "closure_expression" => Some(NestingConstruct::Closure),
            "unsafe_block" => Some(NestingConstruct::Unsafe),
            "async_block" => Some(NestingConstruct::Async),
            "block" => {
                // Named blocks add nesting
                // Note: We skip regular blocks as they don't add logical nesting
                None
            }
            _ => None,
        }
    }

    /// Classify Go nesting constructs.
    fn classify_go_construct(&self, _node: Node, kind: &str) -> Option<NestingConstruct> {
        match kind {
            "if_statement" => Some(NestingConstruct::If),
            "for_statement" => Some(NestingConstruct::For),
            "expression_switch_statement" | "type_switch_statement" => {
                Some(NestingConstruct::Switch)
            }
            "select_statement" => Some(NestingConstruct::Select),
            "func_literal" => Some(NestingConstruct::Closure),
            "defer_statement" => Some(NestingConstruct::Defer),
            _ => None,
        }
    }

    /// Classify Java nesting constructs.
    fn classify_java_construct(&self, _node: Node, kind: &str) -> Option<NestingConstruct> {
        match kind {
            "if_statement" => Some(NestingConstruct::If),
            "for_statement" | "enhanced_for_statement" => Some(NestingConstruct::For),
            "while_statement" => Some(NestingConstruct::While),
            "do_statement" => Some(NestingConstruct::DoWhile),
            "switch_expression" | "switch_statement" => Some(NestingConstruct::Switch),
            "try_statement" => Some(NestingConstruct::Try),
            "catch_clause" => Some(NestingConstruct::Catch),
            "finally_clause" => Some(NestingConstruct::Finally),
            "lambda_expression" => Some(NestingConstruct::Lambda),
            _ => None,
        }
    }

    /// Classify C/C++ nesting constructs.
    fn classify_c_construct(&self, _node: Node, kind: &str) -> Option<NestingConstruct> {
        match kind {
            "if_statement" => Some(NestingConstruct::If),
            "else_clause" => Some(NestingConstruct::Else),
            "for_statement" | "for_range_loop" => Some(NestingConstruct::For),
            "while_statement" => Some(NestingConstruct::While),
            "do_statement" => Some(NestingConstruct::DoWhile),
            "switch_statement" => Some(NestingConstruct::Switch),
            "try_statement" => Some(NestingConstruct::Try),
            "catch_clause" => Some(NestingConstruct::Catch),
            "lambda_expression" => Some(NestingConstruct::Lambda),
            _ => None,
        }
    }

    /// Generic classification for unknown languages.
    fn classify_generic_construct(&self, kind: &str) -> Option<NestingConstruct> {
        if kind.contains("if") && !kind.contains("elif") {
            Some(NestingConstruct::If)
        } else if kind.contains("for") || kind.contains("while") {
            Some(NestingConstruct::For)
        } else if kind.contains("switch") || kind.contains("match") {
            Some(NestingConstruct::Switch)
        } else if kind.contains("try") {
            Some(NestingConstruct::Try)
        } else if kind.contains("catch") || kind.contains("except") {
            Some(NestingConstruct::Catch)
        } else if kind.contains("lambda") || kind.contains("closure") {
            Some(NestingConstruct::Lambda)
        } else {
            None
        }
    }

    /// Calculate average depth from line depths.
    fn average_depth(&self) -> f64 {
        if self.line_depths.is_empty() {
            return 0.0;
        }
        let sum: u64 = self.line_depths.values().map(|&d| u64::from(d)).sum();
        sum as f64 / self.line_depths.len() as f64
    }

    /// Build depth distribution histogram.
    fn depth_distribution(&self) -> HashMap<u32, usize> {
        let mut dist = HashMap::new();
        for &depth in self.line_depths.values() {
            *dist.entry(depth).or_insert(0) += 1;
        }
        dist
    }
}

// =============================================================================
// SUGGESTION GENERATOR
// =============================================================================

/// Generate suggestions for reducing nesting depth.
fn generate_suggestions(metrics: &NestingMetrics, language: &str) -> Vec<String> {
    let mut suggestions = Vec::new();

    if metrics.max_depth <= 3 {
        return suggestions;
    }

    // Check for patterns in deep locations
    for location in &metrics.deep_locations {
        let stack = &location.construct_stack;

        // Early return suggestion for nested ifs at top level
        if stack.first() == Some(&"if".to_string())
            && stack.iter().filter(|&s| s == "if").count() >= 2
        {
            suggestions.push(format!(
                "Consider using early return/guard clauses to reduce nesting at line {}",
                location.line
            ));
        }

        // Extract function for deeply nested code
        if location.depth >= 5 {
            suggestions.push(format!(
                "Consider extracting nested code at line {} into a separate function",
                location.line
            ));
        }

        // Callback hell detection (JavaScript)
        if (language == "javascript" || language == "typescript")
            && stack.iter().filter(|s| *s == "callback").count() >= 2
        {
            suggestions.push(format!(
                "Consider using async/await or Promises to flatten callbacks at line {}",
                location.line
            ));
        }

        // Loop with conditional
        if stack.contains(&"for".to_string()) && stack.contains(&"if".to_string()) {
            suggestions.push(format!(
                "Consider using filter/map/reduce to simplify loop with conditions at line {}",
                location.line
            ));
        }
    }

    // General suggestions based on max depth
    if metrics.max_depth >= 6 {
        suggestions.push(
            "Consider applying the 'Extract Method' refactoring to reduce overall complexity"
                .to_string(),
        );
    }

    if metrics.max_depth >= 4 && metrics.average_depth > 2.0 {
        suggestions.push(
            "Consider restructuring to use polymorphism instead of nested conditionals".to_string(),
        );
    }

    // Deduplicate suggestions
    suggestions.sort();
    suggestions.dedup();

    suggestions
}

// =============================================================================
// PUBLIC API
// =============================================================================

/// Analyze nesting depth for a project or directory.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `language` - Optional language filter
/// * `threshold` - Optional depth threshold for filtering (default: 5)
///
/// # Returns
///
/// Complete analysis result with individual metrics and statistics.
pub fn analyze_nesting(
    path: impl AsRef<Path>,
    language: Option<&str>,
    threshold: Option<u32>,
) -> Result<NestingAnalysis> {
    let path = path.as_ref();

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Path not found: {}", path.display()),
        )));
    }

    if path.is_file() {
        return analyze_file_nesting(path, threshold);
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
        "Analyzing {} files for nesting depth",
        scan_result.files.len()
    );

    let depth_threshold = threshold.unwrap_or(5);

    // Analyze files in parallel
    let results: Vec<(Vec<NestingMetrics>, Vec<NestingAnalysisError>)> = scan_result
        .files
        .par_iter()
        .map(|file| analyze_file_functions_nesting(file, depth_threshold))
        .collect();

    // Aggregate results
    let mut all_functions = Vec::new();
    let mut all_errors = Vec::new();

    for (functions, errors) in results {
        all_functions.extend(functions);
        all_errors.extend(errors);
    }

    // Calculate statistics
    let stats = NestingStats::from_metrics(&all_functions);

    // Filter violations
    let violations = threshold.map(|t| {
        all_functions
            .iter()
            .filter(|f| f.max_depth > t)
            .cloned()
            .collect::<Vec<_>>()
    });

    Ok(NestingAnalysis {
        path: path.to_path_buf(),
        language: language.map(String::from),
        functions: all_functions,
        violations,
        stats,
        threshold,
        errors: all_errors,
    })
}

/// Analyze nesting depth for a single file.
pub fn analyze_file_nesting(
    file: impl AsRef<Path>,
    threshold: Option<u32>,
) -> Result<NestingAnalysis> {
    let file = file.as_ref();

    if !file.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("File not found: {}", file.display()),
        )));
    }

    if !file.is_file() {
        return Err(BrrrError::InvalidArgument(format!(
            "Expected a file, got directory: {}",
            file.display()
        )));
    }

    let depth_threshold = threshold.unwrap_or(5);
    let (functions, errors) = analyze_file_functions_nesting(file, depth_threshold);

    let stats = NestingStats::from_metrics(&functions);

    let violations = threshold.map(|t| {
        functions
            .iter()
            .filter(|f| f.max_depth > t)
            .cloned()
            .collect::<Vec<_>>()
    });

    let registry = LanguageRegistry::global();
    let language = registry
        .detect_language(file)
        .map(|l| l.name().to_string());

    Ok(NestingAnalysis {
        path: file.to_path_buf(),
        language,
        functions,
        violations,
        stats,
        threshold,
        errors,
    })
}

/// Internal function to analyze all functions in a file.
fn analyze_file_functions_nesting(
    file: &Path,
    threshold: u32,
) -> (Vec<NestingMetrics>, Vec<NestingAnalysisError>) {
    let mut results = Vec::new();
    let mut errors = Vec::new();

    // Read file content
    let source = match std::fs::read(file) {
        Ok(s) => s,
        Err(e) => {
            errors.push(NestingAnalysisError {
                file: file.to_path_buf(),
                message: format!("Failed to read file: {}", e),
            });
            return (results, errors);
        }
    };

    // Get language
    let registry = LanguageRegistry::global();
    let lang = match registry.detect_language(file) {
        Some(l) => l,
        None => {
            errors.push(NestingAnalysisError {
                file: file.to_path_buf(),
                message: "Unknown language".to_string(),
            });
            return (results, errors);
        }
    };

    // Parse file
    let mut parser = match lang.parser() {
        Ok(p) => p,
        Err(e) => {
            errors.push(NestingAnalysisError {
                file: file.to_path_buf(),
                message: format!("Failed to create parser: {}", e),
            });
            return (results, errors);
        }
    };

    let tree = match parser.parse(&source, None) {
        Some(t) => t,
        None => {
            errors.push(NestingAnalysisError {
                file: file.to_path_buf(),
                message: "Failed to parse file".to_string(),
            });
            return (results, errors);
        }
    };

    // Extract module info to get function list
    let module = match AstExtractor::extract_file(file) {
        Ok(m) => m,
        Err(e) => {
            errors.push(NestingAnalysisError {
                file: file.to_path_buf(),
                message: format!("Failed to extract AST: {}", e),
            });
            return (results, errors);
        }
    };

    let lang_name = lang.name();

    // Analyze top-level functions
    for func in &module.functions {
        let result = analyze_function_nesting(
            &source,
            &tree,
            &func.name,
            func.line_number,
            func.end_line_number.unwrap_or(func.line_number),
            file,
            lang_name,
            threshold,
        );
        results.push(result);
    }

    // Analyze class methods
    for class in &module.classes {
        for method in &class.methods {
            let qualified_name = format!("{}.{}", class.name, method.name);
            let mut result = analyze_function_nesting(
                &source,
                &tree,
                &qualified_name,
                method.line_number,
                method.end_line_number.unwrap_or(method.line_number),
                file,
                lang_name,
                threshold,
            );
            result.function_name = qualified_name;
            results.push(result);
        }

        // Analyze nested classes recursively
        analyze_nested_classes_nesting(
            &source,
            &tree,
            class,
            &class.name,
            file,
            lang_name,
            threshold,
            &mut results,
        );
    }

    (results, errors)
}

/// Recursively analyze nested class methods.
fn analyze_nested_classes_nesting(
    source: &[u8],
    tree: &Tree,
    class: &crate::ast::types::ClassInfo,
    class_prefix: &str,
    file: &Path,
    lang_name: &str,
    threshold: u32,
    results: &mut Vec<NestingMetrics>,
) {
    for nested in &class.inner_classes {
        let nested_prefix = format!("{}.{}", class_prefix, nested.name);

        for method in &nested.methods {
            let qualified_name = format!("{}.{}", nested_prefix, method.name);
            let mut result = analyze_function_nesting(
                source,
                tree,
                &qualified_name,
                method.line_number,
                method.end_line_number.unwrap_or(method.line_number),
                file,
                lang_name,
                threshold,
            );
            result.function_name = qualified_name;
            results.push(result);
        }

        // Recurse
        analyze_nested_classes_nesting(
            source,
            tree,
            nested,
            &nested_prefix,
            file,
            lang_name,
            threshold,
            results,
        );
    }
}

/// Analyze nesting depth for a single function.
fn analyze_function_nesting(
    source: &[u8],
    tree: &Tree,
    function_name: &str,
    start_line: usize,
    end_line: usize,
    file: &Path,
    language: &str,
    threshold: u32,
) -> NestingMetrics {
    // Find the function node
    let func_node = find_function_node(tree.root_node(), function_name, start_line, source, language);

    if let Some(node) = func_node {
        let mut calculator = NestingCalculator::new(language, threshold);

        // Find and process function body
        if let Some(body) = find_function_body(node, language) {
            calculator.process_node(body);
        } else {
            // Fallback: process all children
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if !is_function_signature_part(child.kind(), language) {
                    calculator.process_node(child);
                }
            }
        }

        let average = calculator.average_depth();
        let distribution = calculator.depth_distribution();
        let risk_level = NestingDepthLevel::from_depth(calculator.max_depth);

        let mut metrics = NestingMetrics {
            function_name: function_name.to_string(),
            file: file.to_path_buf(),
            line: start_line,
            end_line,
            max_depth: calculator.max_depth,
            average_depth: average,
            deepest_line: calculator.deepest_line,
            deep_locations: calculator.deep_locations,
            risk_level,
            suggestions: Vec::new(),
            depth_distribution: distribution,
        };

        // Generate suggestions
        metrics.suggestions = generate_suggestions(&metrics, language);

        return metrics;
    }

    // Fallback
    NestingMetrics {
        function_name: function_name.to_string(),
        file: file.to_path_buf(),
        line: start_line,
        end_line,
        max_depth: 0,
        average_depth: 0.0,
        deepest_line: start_line,
        deep_locations: Vec::new(),
        risk_level: NestingDepthLevel::Good,
        suggestions: Vec::new(),
        depth_distribution: HashMap::new(),
    }
}

/// Find the body node of a function.
fn find_function_body<'a>(node: Node<'a>, language: &str) -> Option<Node<'a>> {
    let body_field = match language {
        "python" => "body",
        "typescript" | "javascript" | "tsx" | "jsx" => "body",
        "rust" => "body",
        "go" => "body",
        "java" => "body",
        "c" | "cpp" => "body",
        _ => "body",
    };

    node.child_by_field_name(body_field)
}

/// Check if a node kind is part of the function signature.
fn is_function_signature_part(kind: &str, _language: &str) -> bool {
    matches!(
        kind,
        "parameters"
            | "formal_parameters"
            | "parameter_list"
            | "type_parameters"
            | "return_type"
            | "type_annotation"
            | "type"
            | "decorator"
            | "modifiers"
            | "visibility_modifier"
            | "identifier"
            | "name"
            | "def"
            | "fn"
            | "func"
            | "function"
            | "async"
            | "("
            | ")"
            | "{"
            | "}"
            | ":"
            | "->"
    )
}

/// Find a function node by name and line number.
fn find_function_node<'a>(
    root: Node<'a>,
    function_name: &str,
    start_line: usize,
    source: &[u8],
    language: &str,
) -> Option<Node<'a>> {
    let simple_name = function_name.rsplit('.').next().unwrap_or(function_name);

    let function_kinds: &[&str] = match language {
        "python" => &["function_definition"],
        "typescript" | "javascript" | "tsx" | "jsx" => {
            &["function_declaration", "method_definition", "arrow_function"]
        }
        "rust" => &["function_item"],
        "go" => &["function_declaration", "method_declaration"],
        "java" => &["method_declaration", "constructor_declaration"],
        "c" | "cpp" => &["function_definition"],
        _ => &["function_definition", "function_declaration"],
    };

    find_node_recursive(root, simple_name, start_line, source, function_kinds)
}

/// Recursively find a function node.
fn find_node_recursive<'a>(
    node: Node<'a>,
    target_name: &str,
    target_line: usize,
    source: &[u8],
    function_kinds: &[&str],
) -> Option<Node<'a>> {
    let node_line = node.start_position().row + 1;

    if function_kinds.contains(&node.kind()) && node_line == target_line {
        if let Some(name_node) = node.child_by_field_name("name") {
            let name =
                std::str::from_utf8(&source[name_node.start_byte()..name_node.end_byte()])
                    .unwrap_or("");
            if name == target_name {
                return Some(node);
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(found) =
            find_node_recursive(child, target_name, target_line, source, function_kinds)
        {
            return Some(found);
        }
    }

    None
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
    fn test_depth_level_classification() {
        assert_eq!(NestingDepthLevel::from_depth(0), NestingDepthLevel::Good);
        assert_eq!(NestingDepthLevel::from_depth(3), NestingDepthLevel::Good);
        assert_eq!(NestingDepthLevel::from_depth(4), NestingDepthLevel::Acceptable);
        assert_eq!(NestingDepthLevel::from_depth(5), NestingDepthLevel::Acceptable);
        assert_eq!(NestingDepthLevel::from_depth(6), NestingDepthLevel::Complex);
        assert_eq!(NestingDepthLevel::from_depth(7), NestingDepthLevel::Complex);
        assert_eq!(NestingDepthLevel::from_depth(8), NestingDepthLevel::Severe);
        assert_eq!(NestingDepthLevel::from_depth(100), NestingDepthLevel::Severe);
    }

    #[test]
    fn test_simple_function_no_nesting() {
        let source = r#"
def simple():
    return 42
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].function_name, "simple");
        assert_eq!(analysis.functions[0].max_depth, 0);
        assert_eq!(analysis.functions[0].risk_level, NestingDepthLevel::Good);
    }

    #[test]
    fn test_single_if_nesting() {
        let source = r#"
def with_if(x):
    if x > 0:
        return 1
    return 0
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].max_depth, 1);
    }

    #[test]
    fn test_nested_constructs() {
        let source = r#"
def nested(x, items):
    if x > 0:
        for item in items:
            if item > 5:
                print(item)
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // if -> for -> if = depth 3
        assert_eq!(analysis.functions[0].max_depth, 3);
        assert_eq!(analysis.functions[0].risk_level, NestingDepthLevel::Good);
    }

    #[test]
    fn test_deeply_nested() {
        let source = r#"
def deeply_nested(a, b, c, d, e, f):
    if a:
        if b:
            if c:
                if d:
                    if e:
                        if f:
                            return True
    return False
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), Some(3));

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].max_depth, 6);
        assert_eq!(analysis.functions[0].risk_level, NestingDepthLevel::Complex);

        // Should have deep locations recorded (depth > 3)
        assert!(!analysis.functions[0].deep_locations.is_empty());

        // Should have suggestions
        assert!(!analysis.functions[0].suggestions.is_empty());
    }

    #[test]
    fn test_try_except_nesting() {
        let source = r#"
def with_try(x):
    try:
        if x > 0:
            return 1 / x
    except ZeroDivisionError:
        return 0
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // try -> if = 2, plus catch adds one more = 2 or 3 depending on implementation
        assert!(analysis.functions[0].max_depth >= 2);
    }

    #[test]
    fn test_loop_nesting() {
        let source = r#"
def nested_loops(items):
    for i in items:
        for j in items:
            for k in items:
                print(i, j, k)
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].max_depth, 3);
    }

    #[test]
    fn test_class_methods() {
        let source = r#"
class Example:
    def simple(self):
        return 1

    def nested(self, x):
        if x > 0:
            for i in range(x):
                print(i)
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 2);

        let simple = analysis
            .functions
            .iter()
            .find(|f| f.function_name == "Example.simple");
        let nested = analysis
            .functions
            .iter()
            .find(|f| f.function_name == "Example.nested");

        assert!(simple.is_some());
        assert!(nested.is_some());

        assert_eq!(simple.unwrap().max_depth, 0);
        assert_eq!(nested.unwrap().max_depth, 2);
    }

    #[test]
    fn test_threshold_filtering() {
        let source = r#"
def shallow():
    if True:
        return 1

def deep(a, b, c, d):
    if a:
        if b:
            if c:
                if d:
                    return True
    return False
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), Some(2));

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert!(analysis.violations.is_some());
        let violations = analysis.violations.unwrap();

        // Only 'deep' should be a violation
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].function_name, "deep");
    }

    #[test]
    fn test_typescript_nesting() {
        let source = r#"
function nested(x: number): void {
    if (x > 0) {
        for (let i = 0; i < x; i++) {
            console.log(i);
        }
    }
}
"#;
        let file = create_temp_file(source, ".ts");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].max_depth, 2);
    }

    #[test]
    fn test_statistics() {
        let metrics = vec![
            NestingMetrics {
                function_name: "f1".to_string(),
                file: PathBuf::new(),
                line: 1,
                end_line: 5,
                max_depth: 2,
                average_depth: 1.0,
                deepest_line: 3,
                deep_locations: vec![],
                risk_level: NestingDepthLevel::Good,
                suggestions: vec![],
                depth_distribution: HashMap::new(),
            },
            NestingMetrics {
                function_name: "f2".to_string(),
                file: PathBuf::new(),
                line: 10,
                end_line: 20,
                max_depth: 6,
                average_depth: 3.0,
                deepest_line: 15,
                deep_locations: vec![],
                risk_level: NestingDepthLevel::Complex,
                suggestions: vec![],
                depth_distribution: HashMap::new(),
            },
        ];

        let stats = NestingStats::from_metrics(&metrics);

        assert_eq!(stats.total_functions, 2);
        assert_eq!(stats.global_max_depth, 6);
        assert_eq!(stats.min_max_depth, 2);
        assert_eq!(stats.functions_over_threshold, 1);
        assert!((stats.average_max_depth - 4.0).abs() < 0.01);
    }

    #[test]
    fn test_nonexistent_file() {
        let result = analyze_file_nesting("/nonexistent/path/file.py", None);
        assert!(result.is_err());
    }

    #[test]
    fn test_empty_file() {
        let source = "# Just a comment\n";
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 0);
        assert_eq!(analysis.stats.total_functions, 0);
    }

    #[test]
    fn test_comprehension_nesting() {
        let source = r#"
def with_comprehension(items):
    result = [x for x in items if x > 0]
    return result
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // Comprehension should add 1 level of nesting
        assert!(analysis.functions[0].max_depth >= 1);
    }

    #[test]
    fn test_lambda_nesting() {
        let source = r#"
def with_lambda(items):
    if items:
        result = map(lambda x: x * 2, items)
        return list(result)
    return []
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // if -> lambda = 2
        assert!(analysis.functions[0].max_depth >= 2);
    }

    #[test]
    fn test_with_statement_nesting() {
        let source = r#"
def with_context(path):
    with open(path) as f:
        for line in f:
            if line.strip():
                print(line)
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_nesting(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // with -> for -> if = 3
        assert_eq!(analysis.functions[0].max_depth, 3);
    }
}
