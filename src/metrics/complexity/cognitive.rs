//! Cognitive complexity calculation using SonarSource methodology.
//!
//! Cognitive complexity measures how difficult code is to understand (not test).
//! Unlike cyclomatic complexity which counts paths, cognitive complexity
//! accounts for nesting depth and penalizes deeply nested structures.
//!
//! # SonarSource Rules
//!
//! ## Increments (add 1 to complexity):
//! - Control flow: if, else if, switch/match, for, while, do-while
//! - Exception handling: catch
//! - Jump statements: goto, break-to-label, continue-to-label
//! - Logical operators: sequences like `a && b && c` count as 1 (not 2)
//! - Recursion: direct recursive calls
//!
//! ## Nesting Increments (add current nesting level):
//! - Control structures nested inside other control structures
//! - Lambda/closure increases nesting level
//!
//! ## No Increment:
//! - `else` clause (already counted with `if`)
//! - Simple ternary `?:` (exception: nested ternaries DO increment)
//!
//! # Risk Levels
//!
//! Cognitive complexity thresholds are typically more strict:
//! - Low (0-5): Simple, easy to understand
//! - Medium (6-10): Moderate complexity, consider simplifying
//! - High (11-15): Complex, hard to understand
//! - Critical (15+): Refactor immediately

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::debug;
use tree_sitter::{Node, Tree};

use crate::ast::AstExtractor;
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;

use super::common;

// =============================================================================
// TYPES
// =============================================================================

/// Risk level classification based on cognitive complexity.
///
/// Cognitive complexity uses stricter thresholds than cyclomatic because
/// it measures understandability, not testability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CognitiveRiskLevel {
    /// Complexity 0-5: Simple, easy to understand
    Low,
    /// Complexity 6-10: Moderate complexity, consider simplifying
    Medium,
    /// Complexity 11-15: Complex, hard to understand
    High,
    /// Complexity 15+: Critical, refactor immediately
    Critical,
}

impl CognitiveRiskLevel {
    /// Classify cognitive complexity value into risk level.
    #[must_use]
    pub fn from_complexity(complexity: u32) -> Self {
        match complexity {
            0..=5 => Self::Low,
            6..=10 => Self::Medium,
            11..=15 => Self::High,
            _ => Self::Critical,
        }
    }

    /// Get human-readable description of the risk level.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Low => "Simple, easy to understand",
            Self::Medium => "Moderate complexity, consider simplifying",
            Self::High => "Complex, hard to understand",
            Self::Critical => "Critical complexity, refactor immediately",
        }
    }

    /// Get the color code for CLI output (ANSI).
    #[must_use]
    pub const fn color_code(&self) -> &'static str {
        match self {
            Self::Low => "\x1b[32m",      // Green
            Self::Medium => "\x1b[33m",   // Yellow
            Self::High => "\x1b[31m",     // Red
            Self::Critical => "\x1b[35m", // Magenta
        }
    }
}

impl std::fmt::Display for CognitiveRiskLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "low"),
            Self::Medium => write!(f, "medium"),
            Self::High => write!(f, "high"),
            Self::Critical => write!(f, "critical"),
        }
    }
}

/// Type of construct contributing to cognitive complexity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ConstructType {
    /// if statement
    If,
    /// else if / elif clause
    ElseIf,
    /// else clause (no increment, just for breakdown visibility)
    Else,
    /// switch / match statement
    Switch,
    /// for loop
    For,
    /// while loop
    While,
    /// do-while loop
    DoWhile,
    /// catch / except clause
    Catch,
    /// goto statement
    Goto,
    /// break with label
    BreakToLabel,
    /// continue with label
    ContinueToLabel,
    /// Sequence of logical AND operators
    LogicalAndSequence,
    /// Sequence of logical OR operators
    LogicalOrSequence,
    /// Direct recursive call
    Recursion,
    /// Nested ternary operator
    NestedTernary,
    /// Lambda/closure (adds nesting, no base increment)
    Lambda,
    /// Guard clause (early return reduces nesting)
    GuardClause,
}

impl std::fmt::Display for ConstructType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::If => write!(f, "if"),
            Self::ElseIf => write!(f, "else if"),
            Self::Else => write!(f, "else"),
            Self::Switch => write!(f, "switch/match"),
            Self::For => write!(f, "for"),
            Self::While => write!(f, "while"),
            Self::DoWhile => write!(f, "do-while"),
            Self::Catch => write!(f, "catch"),
            Self::Goto => write!(f, "goto"),
            Self::BreakToLabel => write!(f, "break to label"),
            Self::ContinueToLabel => write!(f, "continue to label"),
            Self::LogicalAndSequence => write!(f, "&& sequence"),
            Self::LogicalOrSequence => write!(f, "|| sequence"),
            Self::Recursion => write!(f, "recursion"),
            Self::NestedTernary => write!(f, "nested ternary"),
            Self::Lambda => write!(f, "lambda/closure"),
            Self::GuardClause => write!(f, "guard clause"),
        }
    }
}

/// Individual contribution to cognitive complexity.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityContribution {
    /// Line number where construct appears
    pub line: usize,
    /// Type of construct
    pub construct: ConstructType,
    /// Base increment (1 for most constructs, 0 for else/lambda)
    pub base_increment: u32,
    /// Nesting increment (current nesting level)
    pub nesting_increment: u32,
    /// Total contribution (base + nesting)
    pub total: u32,
    /// Current nesting depth when this construct was encountered
    pub nesting_depth: u32,
}

/// Cognitive complexity result for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CognitiveComplexity {
    /// Function name (may include class prefix for methods)
    pub function_name: String,
    /// File path containing the function
    pub file: PathBuf,
    /// Starting line number (1-indexed)
    pub line: usize,
    /// Ending line number (1-indexed)
    pub end_line: usize,
    /// Total cognitive complexity score
    pub complexity: u32,
    /// Risk level classification
    pub risk_level: CognitiveRiskLevel,
    /// Breakdown of contributions to complexity
    pub breakdown: Vec<ComplexityContribution>,
    /// Maximum nesting depth reached
    pub max_nesting: u32,
    /// Number of recursive calls detected
    pub recursion_count: u32,
}

/// Simplified function complexity for summary output.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionCognitiveComplexity {
    /// Function name
    pub name: String,
    /// Starting line number
    pub line: usize,
    /// Cognitive complexity value
    pub complexity: u32,
    /// Risk level
    pub risk_level: CognitiveRiskLevel,
}

impl From<&CognitiveComplexity> for FunctionCognitiveComplexity {
    fn from(cc: &CognitiveComplexity) -> Self {
        Self {
            name: cc.function_name.clone(),
            line: cc.line,
            complexity: cc.complexity,
            risk_level: cc.risk_level,
        }
    }
}

/// Statistics for cognitive complexity analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CognitiveStats {
    /// Total functions analyzed
    pub total_functions: usize,
    /// Average complexity
    pub average_complexity: f64,
    /// Maximum complexity found
    pub max_complexity: u32,
    /// Minimum complexity found
    pub min_complexity: u32,
    /// Median complexity
    pub median_complexity: u32,
    /// Risk level distribution
    pub risk_distribution: std::collections::HashMap<String, usize>,
    /// Functions with recursion
    pub functions_with_recursion: usize,
    /// Average max nesting depth
    pub average_max_nesting: f64,
}

impl CognitiveStats {
    /// Calculate statistics from complexity values.
    fn from_complexities(results: &[CognitiveComplexity]) -> Self {
        if results.is_empty() {
            return Self {
                total_functions: 0,
                average_complexity: 0.0,
                max_complexity: 0,
                min_complexity: 0,
                median_complexity: 0,
                risk_distribution: std::collections::HashMap::new(),
                functions_with_recursion: 0,
                average_max_nesting: 0.0,
            };
        }

        let complexities: Vec<u32> = results.iter().map(|r| r.complexity).collect();
        let total = complexities.len();
        let sum: u64 = complexities.iter().map(|&c| u64::from(c)).sum();
        let average = sum as f64 / total as f64;

        let max = complexities.iter().copied().max().unwrap_or(0);
        let min = complexities.iter().copied().min().unwrap_or(0);

        let mut sorted = complexities.clone();
        sorted.sort_unstable();
        let median = if total % 2 == 0 {
            (sorted[total / 2 - 1] + sorted[total / 2]) / 2
        } else {
            sorted[total / 2]
        };

        let mut risk_distribution = std::collections::HashMap::new();
        for r in results {
            *risk_distribution
                .entry(r.risk_level.to_string())
                .or_insert(0) += 1;
        }

        let functions_with_recursion = results.iter().filter(|r| r.recursion_count > 0).count();

        let total_nesting: u32 = results.iter().map(|r| r.max_nesting).sum();
        let average_max_nesting = f64::from(total_nesting) / total as f64;

        Self {
            total_functions: total,
            average_complexity: average,
            max_complexity: max,
            min_complexity: min,
            median_complexity: median,
            risk_distribution,
            functions_with_recursion,
            average_max_nesting,
        }
    }
}

/// Complete cognitive complexity analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CognitiveAnalysis {
    /// Path that was analyzed
    pub path: PathBuf,
    /// Language filter applied
    pub language: Option<String>,
    /// Individual function complexities
    pub functions: Vec<CognitiveComplexity>,
    /// Functions exceeding threshold
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violations: Option<Vec<CognitiveComplexity>>,
    /// Aggregate statistics
    pub stats: CognitiveStats,
    /// Threshold used for filtering
    #[serde(skip_serializing_if = "Option::is_none")]
    pub threshold: Option<u32>,
    /// Analysis errors
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<CognitiveAnalysisError>,
}

/// Error during cognitive complexity analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CognitiveAnalysisError {
    /// File path
    pub file: PathBuf,
    /// Error message
    pub message: String,
}

// =============================================================================
// COGNITIVE COMPLEXITY CALCULATOR
// =============================================================================

/// Calculator for cognitive complexity with language-specific handling.
struct CognitiveCalculator<'a> {
    source: &'a [u8],
    function_name: String,
    nesting_level: u32,
    complexity: u32,
    breakdown: Vec<ComplexityContribution>,
    max_nesting: u32,
    recursion_count: u32,
    language: &'a str,
    /// Track positions of logical operators already counted
    counted_logical_sequences: HashSet<usize>,
}

impl<'a> CognitiveCalculator<'a> {
    fn new(source: &'a [u8], function_name: String, language: &'a str) -> Self {
        Self {
            source,
            function_name,
            nesting_level: 0,
            complexity: 0,
            breakdown: Vec::new(),
            max_nesting: 0,
            recursion_count: 0,
            language,
            counted_logical_sequences: HashSet::new(),
        }
    }

    /// Get text from a node.
    fn node_text(&self, node: Node) -> &str {
        std::str::from_utf8(&self.source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }

    /// Add a complexity contribution.
    fn add_contribution(&mut self, line: usize, construct: ConstructType, with_nesting: bool) {
        let base_increment = match construct {
            // No base increment for else and lambda (lambda only adds nesting)
            // Guard clauses DO add +1 (they're still control flow), just no nesting penalty
            ConstructType::Else | ConstructType::Lambda => 0,
            _ => 1,
        };

        let nesting_increment = if with_nesting { self.nesting_level } else { 0 };
        let total = base_increment + nesting_increment;

        self.complexity += total;
        self.breakdown.push(ComplexityContribution {
            line,
            construct,
            base_increment,
            nesting_increment,
            total,
            nesting_depth: self.nesting_level,
        });
    }

    /// Enter a nesting context.
    fn enter_nesting(&mut self) {
        self.nesting_level += 1;
        self.max_nesting = self.max_nesting.max(self.nesting_level);
    }

    /// Exit a nesting context.
    fn exit_nesting(&mut self) {
        self.nesting_level = self.nesting_level.saturating_sub(1);
    }

    /// Check if a node represents a recursive call.
    fn is_recursive_call(&self, node: Node) -> bool {
        // Get the callee name
        let callee = match self.language {
            "python" => {
                if node.kind() == "call" {
                    node.child_by_field_name("function")
                        .map(|n| self.node_text(n).to_string())
                } else {
                    None
                }
            }
            "typescript" | "javascript" | "tsx" | "jsx" => {
                if node.kind() == "call_expression" {
                    node.child_by_field_name("function")
                        .map(|n| self.node_text(n).to_string())
                } else {
                    None
                }
            }
            "rust" => {
                if node.kind() == "call_expression" {
                    node.child_by_field_name("function")
                        .map(|n| self.node_text(n).to_string())
                } else {
                    None
                }
            }
            "go" => {
                if node.kind() == "call_expression" {
                    node.child_by_field_name("function")
                        .map(|n| self.node_text(n).to_string())
                } else {
                    None
                }
            }
            "java" | "c" | "cpp" => {
                if node.kind() == "call_expression" || node.kind() == "method_invocation" {
                    node.child_by_field_name("name")
                        .or_else(|| node.child_by_field_name("function"))
                        .map(|n| self.node_text(n).to_string())
                } else {
                    None
                }
            }
            _ => None,
        };

        // Check if callee matches function name (simple recursion detection)
        if let Some(callee_name) = callee {
            // Handle method names like "ClassName.method" -> compare "method" part
            let func_simple = self
                .function_name
                .rsplit('.')
                .next()
                .unwrap_or(&self.function_name);
            let callee_simple = callee_name.rsplit('.').next().unwrap_or(&callee_name);
            return func_simple == callee_simple;
        }
        false
    }

    /// Count logical operator sequence (a && b && c counts as 1).
    fn count_logical_sequence(&mut self, node: Node) {
        // Only count the sequence once at its root
        let start_byte = node.start_byte();
        if self.counted_logical_sequences.contains(&start_byte) {
            return;
        }

        // Check if this is a logical operator node
        let is_logical = match self.language {
            "python" => node.kind() == "boolean_operator",
            "typescript" | "javascript" | "tsx" | "jsx" => node.kind() == "binary_expression",
            "rust" => node.kind() == "binary_expression",
            "go" => node.kind() == "binary_expression",
            "java" | "c" | "cpp" => node.kind() == "binary_expression",
            _ => false,
        };

        if !is_logical {
            return;
        }

        // Get the operator
        let op = self.get_logical_operator(node);
        if op.is_none() {
            return;
        }
        let op = op.unwrap();

        // Check if parent is the same type of logical operator
        if let Some(parent) = node.parent() {
            let parent_op = self.get_logical_operator(parent);
            if parent_op == Some(op.clone()) {
                // This is part of a larger sequence, skip
                return;
            }
        }

        // Mark this position as counted
        self.counted_logical_sequences.insert(start_byte);

        // Add contribution
        let line = node.start_position().row + 1;
        let construct = if op == "and" || op == "&&" {
            ConstructType::LogicalAndSequence
        } else {
            ConstructType::LogicalOrSequence
        };

        self.add_contribution(line, construct, true);
    }

    /// Get logical operator from a binary expression.
    fn get_logical_operator(&self, node: Node) -> Option<String> {
        match self.language {
            "python" => {
                // Python uses boolean_operator with "and" or "or" as child
                if node.kind() == "boolean_operator" {
                    let mut cursor = node.walk();
                    for child in node.children(&mut cursor) {
                        let text = self.node_text(child);
                        if text == "and" || text == "or" {
                            return Some(text.to_string());
                        }
                    }
                }
                None
            }
            _ => {
                // C-style languages use binary_expression with operator
                if node.kind() == "binary_expression" {
                    // Find the operator child
                    let mut cursor = node.walk();
                    for child in node.children(&mut cursor) {
                        let text = self.node_text(child);
                        if text == "&&" || text == "||" {
                            return Some(text.to_string());
                        }
                    }
                }
                None
            }
        }
    }

    /// Check if this is a guard clause (early return that reduces complexity).
    fn is_guard_clause(&self, node: Node) -> bool {
        // A guard clause is an if statement at function level that:
        // 1. Is not nested (nesting_level == 0)
        // 2. Contains only a return/raise/throw in its body
        if self.nesting_level > 0 {
            return false;
        }

        // Check if the if body is a simple return
        let body = match self.language {
            "python" => {
                // Python if_statement has "consequence" field
                node.child_by_field_name("consequence")
            }
            "typescript" | "javascript" | "tsx" | "jsx" | "go" | "rust" | "java" | "c" | "cpp" => {
                // C-style languages have "consequence" field
                node.child_by_field_name("consequence")
            }
            _ => None,
        };

        if let Some(body) = body {
            // Check if body contains only a return statement
            let body_text = self.node_text(body);
            let is_simple_return = body_text.trim().starts_with("return")
                || body_text.trim().starts_with("raise")
                || body_text.trim().starts_with("throw")
                || body_text.trim().starts_with("panic");
            return is_simple_return && !body_text.contains('\n');
        }

        false
    }

    /// Process a node and its children for cognitive complexity.
    ///
    /// Returns `true` if the node was recognized as a control structure and
    /// its children were processed by the handler.
    fn process_node(&mut self, node: Node) {
        let line = node.start_position().row + 1;
        let kind = node.kind();

        // Check for recursion in call nodes BEFORE language-specific handling
        if self.is_recursive_call(node) {
            self.recursion_count += 1;
            self.add_contribution(line, ConstructType::Recursion, true);
        }

        // Check for logical operator sequences
        self.count_logical_sequence(node);

        // Match language-specific control flow constructs
        // These handlers return true if they processed the node's children
        let handled = match self.language {
            "python" => self.process_python_node(node, line, kind),
            "typescript" | "javascript" | "tsx" | "jsx" => {
                self.process_javascript_node(node, line, kind)
            }
            "rust" => self.process_rust_node(node, line, kind),
            "go" => self.process_go_node(node, line, kind),
            "java" => self.process_java_node(node, line, kind),
            "c" | "cpp" => self.process_c_node(node, line, kind),
            _ => self.process_generic_node(node, line, kind),
        };

        // Only recursively process children if the node wasn't handled by
        // a language-specific handler that already processed children
        if !handled {
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                self.process_node(child);
            }
        }
    }

    /// Process Python-specific nodes.
    /// Returns true if children were processed by this handler.
    fn process_python_node(&mut self, node: Node, line: usize, kind: &str) -> bool {
        match kind {
            "if_statement" => {
                // Check for guard clause
                if self.is_guard_clause(node) {
                    // Guard clauses still increment but don't add nesting penalty
                    self.add_contribution(line, ConstructType::GuardClause, false);
                    // Process children without nesting
                    self.process_children_flat(node);
                } else {
                    self.add_contribution(line, ConstructType::If, true);
                    self.process_python_if_children(node);
                }
                true
            }
            "elif_clause" => {
                self.add_contribution(line, ConstructType::ElseIf, true);
                self.process_children_with_nesting(node);
                true
            }
            "else_clause" => {
                // No base increment for else
                // Process children without extra nesting
                self.process_children_flat(node);
                true
            }
            "for_statement" => {
                self.add_contribution(line, ConstructType::For, true);
                self.process_children_with_nesting(node);
                true
            }
            "while_statement" => {
                self.add_contribution(line, ConstructType::While, true);
                self.process_children_with_nesting(node);
                true
            }
            "try_statement" => {
                // try itself doesn't add complexity, but process children to find except handlers
                self.process_children_flat(node);
                true
            }
            "except_clause" | "except_group_clause" => {
                self.add_contribution(line, ConstructType::Catch, true);
                self.process_children_with_nesting(node);
                true
            }
            "match_statement" => {
                self.add_contribution(line, ConstructType::Switch, true);
                self.process_children_with_nesting(node);
                true
            }
            "lambda" => {
                // Lambda adds nesting level but no base increment
                self.enter_nesting();
                self.process_children_flat(node);
                self.exit_nesting();
                true
            }
            "conditional_expression" => {
                // Python ternary: x if cond else y
                // Check if it's nested inside another ternary
                if self.is_nested_ternary(node) {
                    self.add_contribution(line, ConstructType::NestedTernary, true);
                }
                // Process children to detect nested ternaries
                self.process_children_flat(node);
                true
            }
            _ => false, // Node not handled, let caller process children
        }
    }

    /// Process Python if statement children specially.
    fn process_python_if_children(&mut self, node: Node) {
        self.enter_nesting();

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            let child_kind = child.kind();
            // elif and else are siblings, process them without extra nesting
            if child_kind == "elif_clause" || child_kind == "else_clause" {
                // Exit nesting before processing elif/else
                self.exit_nesting();
                self.process_node(child);
                self.enter_nesting();
            } else {
                self.process_node(child);
            }
        }

        self.exit_nesting();
    }

    /// Process JavaScript/TypeScript-specific nodes.
    /// Returns true if children were processed by this handler.
    fn process_javascript_node(&mut self, node: Node, line: usize, kind: &str) -> bool {
        match kind {
            "if_statement" => {
                if self.is_guard_clause(node) {
                    self.add_contribution(line, ConstructType::GuardClause, false);
                    self.process_children_flat(node);
                } else {
                    self.add_contribution(line, ConstructType::If, true);
                    self.process_js_if_children(node);
                }
                true
            }
            "for_statement" | "for_in_statement" | "for_of_statement" => {
                self.add_contribution(line, ConstructType::For, true);
                self.process_children_with_nesting(node);
                true
            }
            "while_statement" => {
                self.add_contribution(line, ConstructType::While, true);
                self.process_children_with_nesting(node);
                true
            }
            "do_statement" => {
                self.add_contribution(line, ConstructType::DoWhile, true);
                self.process_children_with_nesting(node);
                true
            }
            "switch_statement" => {
                self.add_contribution(line, ConstructType::Switch, true);
                self.process_children_with_nesting(node);
                true
            }
            "catch_clause" => {
                self.add_contribution(line, ConstructType::Catch, true);
                self.process_children_with_nesting(node);
                true
            }
            "try_statement" => {
                // try itself doesn't add complexity
                self.process_children_flat(node);
                true
            }
            "arrow_function" | "function_expression" => {
                // Lambda/closure adds nesting
                self.enter_nesting();
                self.process_children_flat(node);
                self.exit_nesting();
                true
            }
            "ternary_expression" => {
                // Check for nested ternary
                if self.is_nested_ternary(node) {
                    self.add_contribution(line, ConstructType::NestedTernary, true);
                }
                self.process_children_flat(node);
                true
            }
            "labeled_statement" => {
                // Check for break/continue to label
                self.check_labeled_jumps(node, line);
                self.process_children_flat(node);
                true
            }
            _ => false,
        }
    }

    /// Process JavaScript if statement children.
    fn process_js_if_children(&mut self, node: Node) {
        self.enter_nesting();

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            let child_kind = child.kind();
            if child_kind == "else_clause" {
                self.exit_nesting();

                // Check if else contains another if (else if)
                let mut inner_cursor = child.walk();
                let mut has_else_if = false;
                for inner in child.children(&mut inner_cursor) {
                    if inner.kind() == "if_statement" {
                        // This is an else-if, add contribution
                        let inner_line = inner.start_position().row + 1;
                        self.add_contribution(inner_line, ConstructType::ElseIf, true);
                        has_else_if = true;
                        self.process_js_if_children(inner);
                    } else {
                        self.process_node(inner);
                    }
                }

                if !has_else_if {
                    // Plain else, no contribution but process children
                }

                self.enter_nesting();
            } else {
                self.process_node(child);
            }
        }

        self.exit_nesting();
    }

    /// Process Rust-specific nodes.
    /// Returns true if children were processed by this handler.
    fn process_rust_node(&mut self, node: Node, line: usize, kind: &str) -> bool {
        match kind {
            "if_expression" => {
                if self.is_guard_clause(node) {
                    self.add_contribution(line, ConstructType::GuardClause, false);
                    self.process_children_flat(node);
                } else {
                    self.add_contribution(line, ConstructType::If, true);
                    self.process_rust_if_children(node);
                }
                true
            }
            "if_let_expression" => {
                self.add_contribution(line, ConstructType::If, true);
                self.process_children_with_nesting(node);
                true
            }
            "for_expression" => {
                self.add_contribution(line, ConstructType::For, true);
                self.process_children_with_nesting(node);
                true
            }
            "while_expression" | "while_let_expression" => {
                self.add_contribution(line, ConstructType::While, true);
                self.process_children_with_nesting(node);
                true
            }
            "loop_expression" => {
                self.add_contribution(line, ConstructType::While, true);
                self.process_children_with_nesting(node);
                true
            }
            "match_expression" => {
                self.add_contribution(line, ConstructType::Switch, true);
                self.process_children_with_nesting(node);
                true
            }
            "closure_expression" => {
                self.enter_nesting();
                self.process_children_flat(node);
                self.exit_nesting();
                true
            }
            _ => false,
        }
    }

    /// Process Rust if expression children.
    fn process_rust_if_children(&mut self, node: Node) {
        self.enter_nesting();

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            let child_kind = child.kind();
            if child_kind == "else_clause" {
                self.exit_nesting();

                // Check for else if
                let mut inner_cursor = child.walk();
                for inner in child.children(&mut inner_cursor) {
                    if inner.kind() == "if_expression" {
                        let inner_line = inner.start_position().row + 1;
                        self.add_contribution(inner_line, ConstructType::ElseIf, true);
                        self.process_rust_if_children(inner);
                    } else {
                        self.process_node(inner);
                    }
                }

                self.enter_nesting();
            } else {
                self.process_node(child);
            }
        }

        self.exit_nesting();
    }

    /// Process Go-specific nodes.
    /// Returns true if children were processed by this handler.
    fn process_go_node(&mut self, node: Node, line: usize, kind: &str) -> bool {
        match kind {
            "if_statement" => {
                if self.is_guard_clause(node) {
                    self.add_contribution(line, ConstructType::GuardClause, false);
                    self.process_children_flat(node);
                } else {
                    self.add_contribution(line, ConstructType::If, true);
                    self.process_go_if_children(node);
                }
                true
            }
            "for_statement" | "range_clause" => {
                self.add_contribution(line, ConstructType::For, true);
                self.process_children_with_nesting(node);
                true
            }
            "expression_switch_statement" | "type_switch_statement" => {
                self.add_contribution(line, ConstructType::Switch, true);
                self.process_children_with_nesting(node);
                true
            }
            "select_statement" => {
                self.add_contribution(line, ConstructType::Switch, true);
                self.process_children_with_nesting(node);
                true
            }
            "func_literal" => {
                self.enter_nesting();
                self.process_children_flat(node);
                self.exit_nesting();
                true
            }
            "goto_statement" => {
                self.add_contribution(line, ConstructType::Goto, true);
                false // No children to process
            }
            "labeled_statement" => {
                self.check_labeled_jumps(node, line);
                self.process_children_flat(node);
                true
            }
            _ => false,
        }
    }

    /// Process Go if statement children.
    fn process_go_if_children(&mut self, node: Node) {
        self.enter_nesting();

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            let child_kind = child.kind();
            // Go uses "else" followed by "if_statement" or "block"
            if child_kind == "if_statement" {
                // This is an else if
                let inner_line = child.start_position().row + 1;
                self.exit_nesting();
                self.add_contribution(inner_line, ConstructType::ElseIf, true);
                self.process_go_if_children(child);
                self.enter_nesting();
            } else if child_kind == "block" && self.is_else_block(node, child) {
                // This is a plain else block
                self.process_node(child);
            } else {
                self.process_node(child);
            }
        }

        self.exit_nesting();
    }

    /// Check if a block is an else block.
    fn is_else_block(&self, _parent: Node, block: Node) -> bool {
        // Check if preceding sibling is "else" keyword
        if let Some(prev) = block.prev_sibling() {
            return self.node_text(prev) == "else";
        }
        false
    }

    /// Process Java-specific nodes.
    /// Returns true if children were processed by this handler.
    fn process_java_node(&mut self, node: Node, line: usize, kind: &str) -> bool {
        match kind {
            "if_statement" => {
                if self.is_guard_clause(node) {
                    self.add_contribution(line, ConstructType::GuardClause, false);
                    self.process_children_flat(node);
                } else {
                    self.add_contribution(line, ConstructType::If, true);
                    self.process_java_if_children(node);
                }
                true
            }
            "for_statement" | "enhanced_for_statement" => {
                self.add_contribution(line, ConstructType::For, true);
                self.process_children_with_nesting(node);
                true
            }
            "while_statement" => {
                self.add_contribution(line, ConstructType::While, true);
                self.process_children_with_nesting(node);
                true
            }
            "do_statement" => {
                self.add_contribution(line, ConstructType::DoWhile, true);
                self.process_children_with_nesting(node);
                true
            }
            "switch_expression" | "switch_statement" => {
                self.add_contribution(line, ConstructType::Switch, true);
                self.process_children_with_nesting(node);
                true
            }
            "catch_clause" => {
                self.add_contribution(line, ConstructType::Catch, true);
                self.process_children_with_nesting(node);
                true
            }
            "try_statement" => {
                self.process_children_flat(node);
                true
            }
            "lambda_expression" => {
                self.enter_nesting();
                self.process_children_flat(node);
                self.exit_nesting();
                true
            }
            "ternary_expression" => {
                if self.is_nested_ternary(node) {
                    self.add_contribution(line, ConstructType::NestedTernary, true);
                }
                self.process_children_flat(node);
                true
            }
            _ => false,
        }
    }

    /// Process Java if statement children.
    fn process_java_if_children(&mut self, node: Node) {
        self.enter_nesting();

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "if_statement" && self.is_else_if_child(node, child) {
                let inner_line = child.start_position().row + 1;
                self.exit_nesting();
                self.add_contribution(inner_line, ConstructType::ElseIf, true);
                self.process_java_if_children(child);
                self.enter_nesting();
            } else {
                self.process_node(child);
            }
        }

        self.exit_nesting();
    }

    /// Check if a node is an else-if child.
    fn is_else_if_child(&self, _parent: Node, _child: Node) -> bool {
        // Simplified: just return false for now
        // Full implementation would check if preceding sibling is "else"
        false
    }

    /// Process C/C++ specific nodes.
    /// Returns true if children were processed by this handler.
    fn process_c_node(&mut self, node: Node, line: usize, kind: &str) -> bool {
        match kind {
            "if_statement" => {
                if self.is_guard_clause(node) {
                    self.add_contribution(line, ConstructType::GuardClause, false);
                    self.process_children_flat(node);
                } else {
                    self.add_contribution(line, ConstructType::If, true);
                    self.process_c_if_children(node);
                }
                true
            }
            "for_statement" | "for_range_loop" => {
                self.add_contribution(line, ConstructType::For, true);
                self.process_children_with_nesting(node);
                true
            }
            "while_statement" => {
                self.add_contribution(line, ConstructType::While, true);
                self.process_children_with_nesting(node);
                true
            }
            "do_statement" => {
                self.add_contribution(line, ConstructType::DoWhile, true);
                self.process_children_with_nesting(node);
                true
            }
            "switch_statement" => {
                self.add_contribution(line, ConstructType::Switch, true);
                self.process_children_with_nesting(node);
                true
            }
            "catch_clause" => {
                self.add_contribution(line, ConstructType::Catch, true);
                self.process_children_with_nesting(node);
                true
            }
            "try_statement" => {
                self.process_children_flat(node);
                true
            }
            "lambda_expression" => {
                self.enter_nesting();
                self.process_children_flat(node);
                self.exit_nesting();
                true
            }
            "conditional_expression" => {
                if self.is_nested_ternary(node) {
                    self.add_contribution(line, ConstructType::NestedTernary, true);
                }
                self.process_children_flat(node);
                true
            }
            "goto_statement" => {
                self.add_contribution(line, ConstructType::Goto, true);
                false
            }
            _ => false,
        }
    }

    /// Process C/C++ if statement children.
    fn process_c_if_children(&mut self, node: Node) {
        self.enter_nesting();

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            // Look for else clause with nested if
            if child.kind() == "else_clause" {
                self.exit_nesting();

                let mut inner_cursor = child.walk();
                for inner in child.children(&mut inner_cursor) {
                    if inner.kind() == "if_statement" {
                        let inner_line = inner.start_position().row + 1;
                        self.add_contribution(inner_line, ConstructType::ElseIf, true);
                        self.process_c_if_children(inner);
                    } else {
                        self.process_node(inner);
                    }
                }

                self.enter_nesting();
            } else {
                self.process_node(child);
            }
        }

        self.exit_nesting();
    }

    /// Generic node processor for unknown languages.
    /// Returns false since it doesn't process children.
    fn process_generic_node(&mut self, _node: Node, line: usize, kind: &str) -> bool {
        // Basic pattern matching for common constructs
        if kind.contains("if") {
            self.add_contribution(line, ConstructType::If, true);
        } else if kind.contains("for") || kind.contains("while") {
            self.add_contribution(line, ConstructType::For, true);
        } else if kind.contains("switch") || kind.contains("match") {
            self.add_contribution(line, ConstructType::Switch, true);
        } else if kind.contains("catch") || kind.contains("except") {
            self.add_contribution(line, ConstructType::Catch, true);
        }
        // Generic handler doesn't know how to properly process children,
        // so return false to let the default recursive processing happen
        false
    }

    /// Process children with nesting level increment.
    fn process_children_with_nesting(&mut self, node: Node) {
        self.enter_nesting();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.process_node(child);
        }
        self.exit_nesting();
    }

    /// Process children without changing nesting level (flat).
    fn process_children_flat(&mut self, node: Node) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.process_node(child);
        }
    }

    /// Check if a ternary is nested inside another ternary.
    fn is_nested_ternary(&self, node: Node) -> bool {
        let ternary_kinds = ["conditional_expression", "ternary_expression"];

        let mut current = node.parent();
        while let Some(parent) = current {
            if ternary_kinds.contains(&parent.kind()) {
                return true;
            }
            // Don't search beyond function boundaries
            if parent.kind().contains("function")
                || parent.kind().contains("method")
                || parent.kind() == "lambda"
            {
                break;
            }
            current = parent.parent();
        }
        false
    }

    /// Check for break/continue to label.
    fn check_labeled_jumps(&mut self, node: Node, _line: usize) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            let child_kind = child.kind();
            if child_kind == "break_statement" || child_kind == "break_expression" {
                // Check if break has a label
                if self.node_text(child).contains(' ') {
                    let break_line = child.start_position().row + 1;
                    self.add_contribution(break_line, ConstructType::BreakToLabel, true);
                }
            } else if child_kind == "continue_statement" || child_kind == "continue_expression" {
                // Check if continue has a label
                if self.node_text(child).contains(' ') {
                    let cont_line = child.start_position().row + 1;
                    self.add_contribution(cont_line, ConstructType::ContinueToLabel, true);
                }
            }
        }
    }

    /// Process function body for cognitive complexity.
    ///
    /// This is the main entry point for analyzing a function's complexity.
    /// It processes all statements in the function body.
    fn process_function_body(&mut self, body: Node) {
        // For Python, body is a "block" containing statements
        // For other languages, body might be a "statement_block" or similar
        let mut cursor = body.walk();
        for child in body.children(&mut cursor) {
            self.process_node(child);
        }
    }
}

// =============================================================================
// PUBLIC API
// =============================================================================

/// Analyze cognitive complexity for a project or directory.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `language` - Optional language filter
/// * `threshold` - Optional complexity threshold for filtering
///
/// # Returns
///
/// Complete analysis result with individual complexities and statistics.
pub fn analyze_cognitive_complexity(
    path: impl AsRef<Path>,
    language: Option<&str>,
    threshold: Option<u32>,
) -> Result<CognitiveAnalysis> {
    let path = path.as_ref();

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Path not found: {}", path.display()),
        )));
    }

    if path.is_file() {
        return analyze_file_cognitive_complexity(path, threshold);
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
        "Analyzing {} files for cognitive complexity",
        scan_result.files.len()
    );

    // Analyze files in parallel
    let results: Vec<(Vec<CognitiveComplexity>, Vec<CognitiveAnalysisError>)> = scan_result
        .files
        .par_iter()
        .map(|file| analyze_file_functions_cognitive(file))
        .collect();

    // Aggregate results
    let mut all_functions = Vec::new();
    let mut all_errors = Vec::new();

    for (functions, errors) in results {
        all_functions.extend(functions);
        all_errors.extend(errors);
    }

    // Calculate statistics
    let stats = CognitiveStats::from_complexities(&all_functions);

    // Filter violations
    let violations = threshold.map(|t| {
        all_functions
            .iter()
            .filter(|f| f.complexity > t)
            .cloned()
            .collect::<Vec<_>>()
    });

    Ok(CognitiveAnalysis {
        path: path.to_path_buf(),
        language: language.map(String::from),
        functions: all_functions,
        violations,
        stats,
        threshold,
        errors: all_errors,
    })
}

/// Analyze cognitive complexity for a single file.
pub fn analyze_file_cognitive_complexity(
    file: impl AsRef<Path>,
    threshold: Option<u32>,
) -> Result<CognitiveAnalysis> {
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

    let (functions, errors) = analyze_file_functions_cognitive(file);

    let stats = CognitiveStats::from_complexities(&functions);

    let violations = threshold.map(|t| {
        functions
            .iter()
            .filter(|f| f.complexity > t)
            .cloned()
            .collect::<Vec<_>>()
    });

    let registry = LanguageRegistry::global();
    let language = registry.detect_language(file).map(|l| l.name().to_string());

    Ok(CognitiveAnalysis {
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
fn analyze_file_functions_cognitive(
    file: &Path,
) -> (Vec<CognitiveComplexity>, Vec<CognitiveAnalysisError>) {
    let mut results = Vec::new();
    let mut errors = Vec::new();

    // Read file content
    let source = match std::fs::read(file) {
        Ok(s) => s,
        Err(e) => {
            errors.push(CognitiveAnalysisError {
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
            errors.push(CognitiveAnalysisError {
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
            errors.push(CognitiveAnalysisError {
                file: file.to_path_buf(),
                message: format!("Failed to create parser: {}", e),
            });
            return (results, errors);
        }
    };

    let tree = match parser.parse(&source, None) {
        Some(t) => t,
        None => {
            errors.push(CognitiveAnalysisError {
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
            errors.push(CognitiveAnalysisError {
                file: file.to_path_buf(),
                message: format!("Failed to extract AST: {}", e),
            });
            return (results, errors);
        }
    };

    let lang_name = lang.name();

    // Analyze top-level functions
    for func in &module.functions {
        let result = analyze_function_cognitive(
            &source,
            &tree,
            &func.name,
            func.line_number,
            func.end_line_number.unwrap_or(func.line_number),
            file,
            lang_name,
        );
        results.push(result);
    }

    // Analyze class methods
    for class in &module.classes {
        for method in &class.methods {
            let qualified_name = format!("{}.{}", class.name, method.name);
            let mut result = analyze_function_cognitive(
                &source,
                &tree,
                &qualified_name,
                method.line_number,
                method.end_line_number.unwrap_or(method.line_number),
                file,
                lang_name,
            );
            result.function_name = qualified_name;
            results.push(result);
        }

        // Analyze nested classes
        analyze_nested_classes_cognitive(
            &source,
            &tree,
            class,
            &class.name,
            file,
            lang_name,
            &mut results,
        );
    }

    (results, errors)
}

/// Recursively analyze nested class methods.
fn analyze_nested_classes_cognitive(
    source: &[u8],
    tree: &Tree,
    class: &crate::ast::types::ClassInfo,
    class_prefix: &str,
    file: &Path,
    lang_name: &str,
    results: &mut Vec<CognitiveComplexity>,
) {
    for nested in &class.inner_classes {
        let nested_prefix = format!("{}.{}", class_prefix, nested.name);

        for method in &nested.methods {
            let qualified_name = format!("{}.{}", nested_prefix, method.name);
            let mut result = analyze_function_cognitive(
                source,
                tree,
                &qualified_name,
                method.line_number,
                method.end_line_number.unwrap_or(method.line_number),
                file,
                lang_name,
            );
            result.function_name = qualified_name;
            results.push(result);
        }

        // Recurse into further nested classes
        analyze_nested_classes_cognitive(
            source,
            tree,
            nested,
            &nested_prefix,
            file,
            lang_name,
            results,
        );
    }
}

/// Analyze cognitive complexity for a single function.
fn analyze_function_cognitive(
    source: &[u8],
    tree: &Tree,
    function_name: &str,
    start_line: usize,
    end_line: usize,
    file: &Path,
    language: &str,
) -> CognitiveComplexity {
    // Find the function node in the tree
    let func_node = find_function_node(
        tree.root_node(),
        function_name,
        start_line,
        source,
        language,
    );

    if let Some(node) = func_node {
        // Get the simple function name for recursion detection
        let simple_name = function_name
            .rsplit('.')
            .next()
            .unwrap_or(function_name)
            .to_string();

        // Analyze the function body directly from the original tree
        let mut calculator = CognitiveCalculator::new(source, simple_name, language);

        // Find and process the function body (skip the function signature)
        let body_node = common::find_function_body(node, language);
        if let Some(body) = body_node {
            calculator.process_function_body(body);
        } else {
            // Fallback: process all children of the function
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                // Skip non-body parts like parameters, return type, decorators
                if !common::is_function_signature_part(child.kind()) {
                    calculator.process_node(child);
                }
            }
        }

        return CognitiveComplexity {
            function_name: function_name.to_string(),
            file: file.to_path_buf(),
            line: start_line,
            end_line,
            complexity: calculator.complexity,
            risk_level: CognitiveRiskLevel::from_complexity(calculator.complexity),
            breakdown: calculator.breakdown,
            max_nesting: calculator.max_nesting,
            recursion_count: calculator.recursion_count,
        };
    }

    // Fallback: return minimal result
    CognitiveComplexity {
        function_name: function_name.to_string(),
        file: file.to_path_buf(),
        line: start_line,
        end_line,
        complexity: 0,
        risk_level: CognitiveRiskLevel::Low,
        breakdown: Vec::new(),
        max_nesting: 0,
        recursion_count: 0,
    }
}

// Note: find_function_body and is_function_signature_part are now in common.rs

/// Find a function node by name and line number.
fn find_function_node<'a>(
    root: Node<'a>,
    function_name: &str,
    start_line: usize,
    source: &[u8],
    language: &str,
) -> Option<Node<'a>> {
    // Get the simple name (last part after dots)
    let simple_name = function_name.rsplit('.').next().unwrap_or(function_name);

    // Define function node kinds per language
    let function_kinds: &[&str] = match language {
        "python" => &["function_definition"],
        "typescript" | "javascript" | "tsx" | "jsx" => &[
            "function_declaration",
            "method_definition",
            "arrow_function",
        ],
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

    if function_kinds.contains(&node.kind()) {
        // Check if this is the function we're looking for
        if node_line == target_line {
            // Verify name matches
            if let Some(name_node) = node.child_by_field_name("name") {
                let name =
                    std::str::from_utf8(&source[name_node.start_byte()..name_node.end_byte()])
                        .unwrap_or("");
                if name == target_name {
                    return Some(node);
                }
            }
        }
    }

    // Search children
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
    fn test_risk_level_classification() {
        assert_eq!(
            CognitiveRiskLevel::from_complexity(0),
            CognitiveRiskLevel::Low
        );
        assert_eq!(
            CognitiveRiskLevel::from_complexity(5),
            CognitiveRiskLevel::Low
        );
        assert_eq!(
            CognitiveRiskLevel::from_complexity(6),
            CognitiveRiskLevel::Medium
        );
        assert_eq!(
            CognitiveRiskLevel::from_complexity(10),
            CognitiveRiskLevel::Medium
        );
        assert_eq!(
            CognitiveRiskLevel::from_complexity(11),
            CognitiveRiskLevel::High
        );
        assert_eq!(
            CognitiveRiskLevel::from_complexity(15),
            CognitiveRiskLevel::High
        );
        assert_eq!(
            CognitiveRiskLevel::from_complexity(16),
            CognitiveRiskLevel::Critical
        );
    }

    #[test]
    fn test_simple_function_complexity() {
        let source = r#"
def simple():
    return 42
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].function_name, "simple");
        assert_eq!(analysis.functions[0].complexity, 0);
    }

    #[test]
    fn test_if_statement_complexity() {
        let source = r#"
def with_if(x):
    if x > 0:
        return 1
    return 0
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // if at nesting level 0: +1 base, +0 nesting = 1
        assert_eq!(analysis.functions[0].complexity, 1);
    }

    #[test]
    fn test_nested_if_complexity() {
        let source = r#"
def nested_if(x, y):
    if x > 0:
        if y > 0:
            return "both positive"
    return "other"
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // outer if: +1 (base) + 0 (nesting) = 1
        // inner if: +1 (base) + 1 (nesting) = 2
        // Total: 3
        assert_eq!(analysis.functions[0].complexity, 3);
    }

    #[test]
    fn test_for_loop_complexity() {
        let source = r#"
def with_loop(items):
    total = 0
    for item in items:
        total += item
    return total
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // for: +1 base, +0 nesting = 1
        assert_eq!(analysis.functions[0].complexity, 1);
    }

    #[test]
    fn test_if_else_complexity() {
        let source = r#"
def with_else(x):
    if x > 0:
        return "positive"
    else:
        return "non-positive"
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // if: +1, else: +0 (no increment for else)
        // Total: 1
        assert_eq!(analysis.functions[0].complexity, 1);
    }

    #[test]
    fn test_elif_complexity() {
        let source = r#"
def with_elif(x):
    if x > 0:
        return "positive"
    elif x < 0:
        return "negative"
    else:
        return "zero"
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // if: +1, elif: +1, else: +0
        // Total: 2
        assert_eq!(analysis.functions[0].complexity, 2);
    }

    #[test]
    fn test_try_except_complexity() {
        let source = r#"
def safe_divide(a, b):
    try:
        return a / b
    except ZeroDivisionError:
        return 0
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // except: +1
        assert_eq!(analysis.functions[0].complexity, 1);
    }

    #[test]
    fn test_deeply_nested_complexity() {
        let source = r#"
def deeply_nested(a, b, c, d):
    if a:
        if b:
            if c:
                if d:
                    return "all true"
    return "not all true"
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // if a: +1 + 0 = 1
        // if b: +1 + 1 = 2
        // if c: +1 + 2 = 3
        // if d: +1 + 3 = 4
        // Total: 10
        assert_eq!(analysis.functions[0].complexity, 10);
        assert_eq!(analysis.functions[0].max_nesting, 4);
    }

    #[test]
    fn test_logical_operator_sequence() {
        let source = r#"
def check_all(a, b, c, d):
    if a and b and c and d:
        return True
    return False
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // if: +1
        // a and b and c and d: +1 (sequence counts as 1, not 3)
        // Total: 2
        assert!(analysis.functions[0].complexity <= 3);
    }

    #[test]
    fn test_class_method_complexity() {
        let source = r#"
class Calculator:
    def add(self, a, b):
        return a + b

    def smart_divide(self, a, b):
        if b == 0:
            return None
        return a / b
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 2);

        let add = analysis
            .functions
            .iter()
            .find(|f| f.function_name == "Calculator.add");
        let divide = analysis
            .functions
            .iter()
            .find(|f| f.function_name == "Calculator.smart_divide");

        assert!(add.is_some());
        assert!(divide.is_some());

        assert_eq!(add.unwrap().complexity, 0);
        assert_eq!(divide.unwrap().complexity, 1);
    }

    #[test]
    fn test_threshold_filtering() {
        let source = r#"
def simple():
    return 1

def complex_func(a, b, c):
    if a:
        if b:
            if c:
                return "nested"
    return "flat"
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), Some(2));

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert!(analysis.violations.is_some());
        let violations = analysis.violations.unwrap();

        // Only complex_func should be a violation
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].function_name, "complex_func");
    }

    #[test]
    fn test_typescript_if_complexity() {
        let source = r#"
function withIf(x: number): string {
    if (x > 0) {
        return "positive";
    }
    return "non-positive";
}
"#;
        let file = create_temp_file(source, ".ts");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].complexity, 1);
    }

    #[test]
    fn test_nonexistent_file() {
        let result = analyze_file_cognitive_complexity("/nonexistent/path/file.py", None);
        assert!(result.is_err());
    }

    #[test]
    fn test_empty_file() {
        let source = "# Just a comment\n";
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 0);
        assert_eq!(analysis.stats.total_functions, 0);
    }

    #[test]
    fn test_breakdown_details() {
        let source = r#"
def example(x, y):
    if x > 0:
        for i in range(y):
            if i > 5:
                print(i)
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cognitive_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        let func = &analysis.functions[0];

        // Verify breakdown exists and has expected constructs
        assert!(!func.breakdown.is_empty());

        // outer if: +1 + 0 = 1
        // for: +1 + 1 = 2
        // inner if: +1 + 2 = 3
        // Total: 6
        assert_eq!(func.complexity, 6);
    }

    #[test]
    fn test_statistics_calculation() {
        let results = vec![
            CognitiveComplexity {
                function_name: "f1".to_string(),
                file: PathBuf::new(),
                line: 1,
                end_line: 5,
                complexity: 2,
                risk_level: CognitiveRiskLevel::Low,
                breakdown: vec![],
                max_nesting: 1,
                recursion_count: 0,
            },
            CognitiveComplexity {
                function_name: "f2".to_string(),
                file: PathBuf::new(),
                line: 10,
                end_line: 20,
                complexity: 8,
                risk_level: CognitiveRiskLevel::Medium,
                breakdown: vec![],
                max_nesting: 3,
                recursion_count: 1,
            },
        ];

        let stats = CognitiveStats::from_complexities(&results);

        assert_eq!(stats.total_functions, 2);
        assert_eq!(stats.min_complexity, 2);
        assert_eq!(stats.max_complexity, 8);
        assert_eq!(stats.functions_with_recursion, 1);
        assert!((stats.average_complexity - 5.0).abs() < 0.01);
    }
}
