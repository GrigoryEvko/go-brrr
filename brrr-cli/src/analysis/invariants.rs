//! Invariant Inference for Contract-Based Programming.
//!
//! This module provides static analysis capabilities for inferring
//! preconditions, postconditions, loop invariants, and class invariants
//! from source code. It extracts explicit assertions and infers implicit
//! contracts from guard clauses, type hints, and comparison operators.
//!
//! # Supported Invariant Types
//!
//! - **Preconditions**: Conditions that must hold before function execution
//!   - Explicit assertions (`assert x > 0`)
//!   - Guard clauses (`if x is None: raise`)
//!   - Type checks (`if not isinstance(x, int): raise`)
//!   - Range checks (`if x < 0: raise`)
//!
//! - **Postconditions**: Conditions that must hold after function execution
//!   - Return value checks before return statements
//!   - Final assertions
//!   - Return type annotations
//!
//! - **Loop Invariants**: Conditions that hold at loop entry
//!   - Variables not modified in loop body
//!   - Bounds on loop variables
//!   - Monotonicity (always increasing/decreasing)
//!
//! - **Class Invariants**: Conditions that hold for all instances
//!   - Field validation in constructors
//!   - Property constraints
//!
//! # Example
//!
//! ```ignore
//! use brrr::analysis::invariants::{analyze_invariants, InvariantAnalyzer};
//!
//! // Analyze a Python file
//! let analysis = analyze_invariants("src/main.py", None)?;
//!
//! // Analyze a specific function
//! let func_analysis = analyze_invariants_function("src/main.py", "divide", None)?;
//!
//! // Print inferred preconditions
//! for pre in &func_analysis.preconditions {
//!     println!("Precondition: {} (confidence: {:.2})", pre.expression, pre.confidence);
//! }
//! ```
//!
//! # Confidence Levels
//!
//! - **1.0**: Explicit assertion or documented contract
//! - **0.9**: Guard clause with raise/throw
//! - **0.8**: Type check or isinstance check
//! - **0.7**: Comparison check that raises
//! - **0.6**: Inferred from type hints
//! - **0.5**: Inferred from variable naming
//! - **0.4**: Inferred from usage patterns

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::error::{BrrrError, Result};

// =============================================================================
// Error Types
// =============================================================================

/// Errors that can occur during invariant analysis.
#[derive(Error, Debug)]
pub enum InvariantError {
    /// File could not be read.
    #[error("Failed to read file: {path}")]
    FileReadError {
        path: String,
        #[source]
        source: std::io::Error,
    },

    /// Language not supported.
    #[error("Language not supported: {lang}")]
    UnsupportedLanguage { lang: String },

    /// Function not found in file.
    #[error("Function not found: {name}")]
    FunctionNotFound { name: String },

    /// Parse error.
    #[error("Failed to parse source: {message}")]
    ParseError { message: String },

    /// CFG extraction failed.
    #[error("CFG extraction failed: {message}")]
    CfgError { message: String },
}

impl From<InvariantError> for BrrrError {
    fn from(e: InvariantError) -> Self {
        BrrrError::Analysis(e.to_string())
    }
}

// =============================================================================
// Core Types
// =============================================================================

/// Type of invariant detected or inferred.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InvariantType {
    /// Must hold before function execution.
    Precondition,
    /// Must hold after function execution.
    Postcondition,
    /// Must hold at loop entry on every iteration.
    LoopInvariant,
    /// Must hold for all instances of a class.
    ClassInvariant,
    /// Explicit assertion in code.
    Assertion,
}

impl std::fmt::Display for InvariantType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InvariantType::Precondition => write!(f, "precondition"),
            InvariantType::Postcondition => write!(f, "postcondition"),
            InvariantType::LoopInvariant => write!(f, "loop_invariant"),
            InvariantType::ClassInvariant => write!(f, "class_invariant"),
            InvariantType::Assertion => write!(f, "assertion"),
        }
    }
}

/// Source location in code.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Location {
    /// Line number (1-indexed).
    pub line: usize,
    /// Column number (0-indexed, optional).
    pub column: Option<usize>,
    /// End line (for multi-line constructs).
    pub end_line: Option<usize>,
    /// End column (optional).
    pub end_column: Option<usize>,
}

impl Location {
    /// Create a new location.
    #[inline]
    #[must_use]
    pub fn new(line: usize) -> Self {
        Self {
            line,
            column: None,
            end_line: None,
            end_column: None,
        }
    }

    /// Create a location with column.
    #[inline]
    #[must_use]
    pub fn with_column(line: usize, column: usize) -> Self {
        Self {
            line,
            column: Some(column),
            end_line: None,
            end_column: None,
        }
    }

    /// Create a location with range.
    #[inline]
    #[must_use]
    pub fn with_range(line: usize, column: usize, end_line: usize, end_column: usize) -> Self {
        Self {
            line,
            column: Some(column),
            end_line: Some(end_line),
            end_column: Some(end_column),
        }
    }
}

/// Evidence supporting an inferred invariant.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Evidence {
    /// Type of evidence.
    pub kind: EvidenceKind,
    /// Location of the evidence in source.
    pub location: Location,
    /// Description of the evidence.
    pub description: String,
    /// The source code snippet that provides evidence.
    pub code_snippet: Option<String>,
}

/// Kind of evidence supporting an invariant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EvidenceKind {
    /// Explicit assert statement.
    ExplicitAssert,
    /// Guard clause (if-raise pattern).
    GuardClause,
    /// Type annotation.
    TypeAnnotation,
    /// isinstance/typeof check.
    TypeCheck,
    /// Comparison that raises on failure.
    ComparisonCheck,
    /// Documentation comment.
    Documentation,
    /// Variable naming convention.
    NamingConvention,
    /// Usage pattern in code.
    UsagePattern,
    /// Loop bound.
    LoopBound,
    /// Return statement.
    ReturnStatement,
    /// Property access pattern.
    PropertyAccess,
}

impl std::fmt::Display for EvidenceKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvidenceKind::ExplicitAssert => write!(f, "explicit_assert"),
            EvidenceKind::GuardClause => write!(f, "guard_clause"),
            EvidenceKind::TypeAnnotation => write!(f, "type_annotation"),
            EvidenceKind::TypeCheck => write!(f, "type_check"),
            EvidenceKind::ComparisonCheck => write!(f, "comparison_check"),
            EvidenceKind::Documentation => write!(f, "documentation"),
            EvidenceKind::NamingConvention => write!(f, "naming_convention"),
            EvidenceKind::UsagePattern => write!(f, "usage_pattern"),
            EvidenceKind::LoopBound => write!(f, "loop_bound"),
            EvidenceKind::ReturnStatement => write!(f, "return_statement"),
            EvidenceKind::PropertyAccess => write!(f, "property_access"),
        }
    }
}

/// An inferred or detected invariant.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Invariant {
    /// Type of invariant.
    pub invariant_type: InvariantType,
    /// The invariant expression (e.g., "x > 0", "b != 0").
    pub expression: String,
    /// Location where the invariant was inferred/detected.
    pub location: Location,
    /// Confidence level (0.0 to 1.0).
    pub confidence: f64,
    /// Evidence supporting this invariant.
    pub evidence: Vec<Evidence>,
    /// Variable(s) involved in the invariant.
    pub variables: Vec<String>,
    /// Whether this is an explicit invariant (assertion) or inferred.
    pub is_explicit: bool,
}

impl Invariant {
    /// Create a new invariant.
    #[must_use]
    pub fn new(
        invariant_type: InvariantType,
        expression: String,
        location: Location,
        confidence: f64,
    ) -> Self {
        Self {
            invariant_type,
            expression,
            location,
            confidence,
            evidence: Vec::new(),
            variables: Vec::new(),
            is_explicit: false,
        }
    }

    /// Add evidence to this invariant.
    #[must_use]
    pub fn with_evidence(mut self, evidence: Evidence) -> Self {
        self.evidence.push(evidence);
        self
    }

    /// Add a variable involved in this invariant.
    #[must_use]
    pub fn with_variable(mut self, variable: String) -> Self {
        if !self.variables.contains(&variable) {
            self.variables.push(variable);
        }
        self
    }

    /// Mark as explicit assertion.
    #[must_use]
    pub fn as_explicit(mut self) -> Self {
        self.is_explicit = true;
        self.confidence = 1.0;
        self
    }
}

/// Suggested assertion for improving code quality.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SuggestedAssertion {
    /// Location to insert the assertion.
    pub location: Location,
    /// The assertion expression.
    pub assertion: String,
    /// Reason for the suggestion.
    pub reason: String,
    /// Confidence in the suggestion (0.0 to 1.0).
    pub confidence: f64,
    /// Category of the suggestion.
    pub category: SuggestionCategory,
}

/// Category of assertion suggestion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SuggestionCategory {
    /// Null/None check.
    NullCheck,
    /// Type validation.
    TypeCheck,
    /// Range/bounds check.
    RangeCheck,
    /// Collection non-empty check.
    NonEmpty,
    /// Return value validation.
    ReturnValidation,
    /// Loop invariant assertion.
    LoopInvariant,
    /// State validation.
    StateValidation,
}

/// Loop invariant details.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoopInvariantInfo {
    /// Loop variable (if identifiable).
    pub loop_variable: Option<String>,
    /// Variables not modified in loop.
    pub unmodified_variables: Vec<String>,
    /// Variables with monotonic behavior.
    pub monotonic_variables: Vec<MonotonicVariable>,
    /// Bound expressions for loop variable.
    pub bounds: Option<LoopBounds>,
}

/// A variable with monotonic behavior in a loop.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonotonicVariable {
    /// Variable name.
    pub name: String,
    /// Direction of monotonicity.
    pub direction: MonotonicDirection,
    /// Confidence level.
    pub confidence: f64,
}

/// Direction of monotonic change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MonotonicDirection {
    /// Value only increases.
    Increasing,
    /// Value only decreases.
    Decreasing,
    /// Value stays constant.
    Constant,
}

/// Bounds on a loop variable.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoopBounds {
    /// Lower bound expression.
    pub lower: Option<String>,
    /// Upper bound expression.
    pub upper: Option<String>,
    /// Whether bounds are inclusive.
    pub inclusive: bool,
}

// =============================================================================
// Analysis Result Types
// =============================================================================

/// Complete invariant analysis for a function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionInvariantAnalysis {
    /// Function name.
    pub function: String,
    /// File containing the function.
    pub file: String,
    /// Start line of function.
    pub start_line: usize,
    /// End line of function.
    pub end_line: usize,
    /// Inferred/detected preconditions.
    pub preconditions: Vec<Invariant>,
    /// Inferred/detected postconditions.
    pub postconditions: Vec<Invariant>,
    /// Loop invariants by loop location.
    pub loop_invariants: HashMap<usize, Vec<Invariant>>,
    /// Loop details.
    pub loop_details: HashMap<usize, LoopInvariantInfo>,
    /// Suggested assertions.
    pub suggested_assertions: Vec<SuggestedAssertion>,
    /// Analysis metrics.
    pub metrics: InvariantMetrics,
}

/// File-level invariant analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileInvariantAnalysis {
    /// File path.
    pub file: String,
    /// Language detected.
    pub language: String,
    /// Function-level analyses.
    pub functions: Vec<FunctionInvariantAnalysis>,
    /// Class invariants.
    pub class_invariants: HashMap<String, Vec<Invariant>>,
    /// Summary statistics.
    pub summary: InvariantSummary,
}

/// Metrics for invariant analysis.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct InvariantMetrics {
    /// Number of explicit assertions found.
    pub explicit_assertions: usize,
    /// Number of inferred preconditions.
    pub inferred_preconditions: usize,
    /// Number of inferred postconditions.
    pub inferred_postconditions: usize,
    /// Number of loop invariants found.
    pub loop_invariants_count: usize,
    /// Number of suggested assertions.
    pub suggestions_count: usize,
    /// Average confidence of inferred invariants.
    pub average_confidence: f64,
    /// Number of guard clauses detected.
    pub guard_clauses: usize,
    /// Number of type checks detected.
    pub type_checks: usize,
}

/// Summary statistics for file analysis.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct InvariantSummary {
    /// Total functions analyzed.
    pub functions_analyzed: usize,
    /// Total invariants found.
    pub total_invariants: usize,
    /// Invariants by type.
    pub by_type: HashMap<String, usize>,
    /// Average confidence across all invariants.
    pub average_confidence: f64,
    /// Total suggestions generated.
    pub total_suggestions: usize,
}

// =============================================================================
// Invariant Analyzer
// =============================================================================

/// Main invariant analyzer.
pub struct InvariantAnalyzer {
    /// Source code content.
    source: String,
    /// Lines of source (for quick access).
    lines: Vec<String>,
    /// Language being analyzed.
    language: String,
}

impl InvariantAnalyzer {
    /// Create a new analyzer for source code.
    ///
    /// # Arguments
    ///
    /// * `source` - The source code to analyze
    /// * `language` - The programming language
    ///
    /// # Returns
    ///
    /// A new analyzer instance.
    #[must_use]
    pub fn new(source: &str, language: &str) -> Self {
        let lines: Vec<String> = source.lines().map(String::from).collect();
        Self {
            source: source.to_string(),
            lines,
            language: language.to_string(),
        }
    }

    /// Create analyzer from a file.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to the source file
    /// * `language` - Optional language override (auto-detected if None)
    ///
    /// # Errors
    ///
    /// Returns error if file cannot be read or language is unsupported.
    pub fn from_file(path: &str, language: Option<&str>) -> Result<Self> {
        let source = fs::read_to_string(path).map_err(|e| {
            BrrrError::from(InvariantError::FileReadError {
                path: path.to_string(),
                source: e,
            })
        })?;

        let lang = match language {
            Some(l) => l.to_string(),
            None => detect_language(path)?,
        };

        Ok(Self::new(&source, &lang))
    }

    /// Analyze a specific function for invariants.
    ///
    /// # Arguments
    ///
    /// * `function_name` - Name of the function to analyze
    ///
    /// # Returns
    ///
    /// Complete invariant analysis for the function.
    pub fn analyze_function(&self, function_name: &str) -> Result<FunctionInvariantAnalysis> {
        // Find function in source
        let (start_line, end_line) = self.find_function_range(function_name)?;

        // Extract function body
        let body_lines: Vec<&str> = self.lines[start_line - 1..end_line]
            .iter()
            .map(String::as_str)
            .collect();

        // Analyze preconditions
        let preconditions = self.extract_preconditions(&body_lines, start_line);

        // Analyze postconditions
        let postconditions = self.extract_postconditions(&body_lines, start_line);

        // Analyze loops
        let (loop_invariants, loop_details) = self.extract_loop_invariants(&body_lines, start_line);

        // Generate suggestions
        let suggestions = self.generate_suggestions(&body_lines, start_line, &preconditions);

        // Calculate metrics
        let metrics = self.calculate_metrics(
            &preconditions,
            &postconditions,
            &loop_invariants,
            &suggestions,
        );

        Ok(FunctionInvariantAnalysis {
            function: function_name.to_string(),
            file: String::new(), // Will be set by caller
            start_line,
            end_line,
            preconditions,
            postconditions,
            loop_invariants,
            loop_details,
            suggested_assertions: suggestions,
            metrics,
        })
    }

    /// Find the line range of a function.
    fn find_function_range(&self, function_name: &str) -> Result<(usize, usize)> {
        let patterns = match self.language.as_str() {
            "python" => vec![
                format!("def {}(", function_name),
                format!("async def {}(", function_name),
            ],
            "typescript" | "javascript" => vec![
                format!("function {}(", function_name),
                format!("async function {}(", function_name),
                format!("{} = function(", function_name),
                format!("{} = (", function_name),
                format!("const {} = (", function_name),
                format!("let {} = (", function_name),
                format!("{}(", function_name), // method in class
            ],
            "rust" => vec![
                format!("fn {}(", function_name),
                format!("pub fn {}(", function_name),
                format!("async fn {}(", function_name),
                format!("pub async fn {}(", function_name),
            ],
            "go" => vec![
                format!("func {}(", function_name),
                format!("func ("), // methods - will need refinement
            ],
            "java" | "kotlin" | "csharp" => vec![
                format!(" {}(", function_name),
                format!("\t{}(", function_name),
            ],
            "c" | "cpp" => vec![
                format!(" {}(", function_name),
                format!("*{}(", function_name),
            ],
            _ => vec![format!("{}(", function_name)],
        };

        let mut start_line = None;
        for (idx, line) in self.lines.iter().enumerate() {
            let trimmed = line.trim();
            for pattern in &patterns {
                if trimmed.contains(pattern.as_str()) || line.contains(pattern.as_str()) {
                    start_line = Some(idx + 1);
                    break;
                }
            }
            if start_line.is_some() {
                break;
            }
        }

        let start = start_line.ok_or_else(|| {
            BrrrError::from(InvariantError::FunctionNotFound {
                name: function_name.to_string(),
            })
        })?;

        // Find end of function
        let end = self.find_function_end(start);

        Ok((start, end))
    }

    /// Find the end line of a function starting at given line.
    fn find_function_end(&self, start_line: usize) -> usize {
        let start_idx = start_line - 1;
        if start_idx >= self.lines.len() {
            return start_line;
        }

        match self.language.as_str() {
            "python" => {
                // Find the indentation level of the function definition
                let def_line = &self.lines[start_idx];
                let base_indent = def_line.len() - def_line.trim_start().len();

                // Find colon and move to next line
                let mut in_function = false;
                for (idx, line) in self.lines[start_idx..].iter().enumerate() {
                    let trimmed = line.trim();
                    if trimmed.is_empty() || trimmed.starts_with('#') {
                        continue;
                    }

                    let indent = line.len() - line.trim_start().len();
                    if idx == 0 {
                        // First line is the def line
                        if trimmed.ends_with(':') {
                            in_function = true;
                        }
                        continue;
                    }

                    if in_function && indent <= base_indent && !trimmed.is_empty() {
                        // Found line at same or lower indent - function ended
                        return start_idx + idx; // 0-indexed line before this one + 1 = line number
                    }
                }
                // Function goes to end of file
                self.lines.len()
            }
            "rust" | "go" | "java" | "c" | "cpp" | "csharp" | "kotlin" | "typescript"
            | "javascript" => {
                // Brace-matching languages
                let mut brace_count = 0;
                let mut found_first_brace = false;

                for (idx, line) in self.lines[start_idx..].iter().enumerate() {
                    for ch in line.chars() {
                        if ch == '{' {
                            brace_count += 1;
                            found_first_brace = true;
                        } else if ch == '}' {
                            brace_count -= 1;
                            if found_first_brace && brace_count == 0 {
                                return start_idx + idx + 1;
                            }
                        }
                    }
                }
                self.lines.len()
            }
            _ => {
                // Default: look for next function or end of file
                start_line + 50.min(self.lines.len() - start_idx)
            }
        }
    }

    /// Extract preconditions from function body.
    fn extract_preconditions(&self, body: &[&str], start_line: usize) -> Vec<Invariant> {
        let mut preconditions = Vec::new();

        for (idx, line) in body.iter().enumerate() {
            let line_num = start_line + idx;
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty() || is_comment(trimmed, &self.language) {
                continue;
            }

            // Extract explicit assertions
            if let Some(inv) = self.extract_assert_precondition(trimmed, line_num) {
                preconditions.push(inv);
                continue;
            }

            // Extract guard clauses
            if let Some(inv) = self.extract_guard_clause(trimmed, line_num, body, idx) {
                preconditions.push(inv);
                continue;
            }

            // Extract type checks
            if let Some(inv) = self.extract_type_check(trimmed, line_num) {
                preconditions.push(inv);
                continue;
            }

            // Stop at first non-guard statement (preconditions are at the top)
            if is_substantive_statement(trimmed, &self.language) {
                break;
            }
        }

        preconditions
    }

    /// Extract an assertion as a precondition.
    fn extract_assert_precondition(&self, line: &str, line_num: usize) -> Option<Invariant> {
        let assertion = match self.language.as_str() {
            "python" => {
                if line.starts_with("assert ") {
                    Some(line.trim_start_matches("assert ").trim())
                } else {
                    None
                }
            }
            "rust" => {
                if line.starts_with("assert!(") || line.starts_with("debug_assert!(") {
                    extract_macro_arg(line)
                } else {
                    None
                }
            }
            "typescript" | "javascript" => {
                if line.starts_with("console.assert(") {
                    extract_parenthesized_arg(line, "console.assert")
                } else if line.contains("assert(") {
                    extract_parenthesized_arg(line, "assert")
                } else {
                    None
                }
            }
            "go" => {
                // Go doesn't have assertions, but we can detect panic patterns
                None
            }
            "java" | "kotlin" => {
                if line.starts_with("assert ") {
                    Some(
                        line.trim_start_matches("assert ")
                            .trim_end_matches(';')
                            .trim(),
                    )
                } else {
                    None
                }
            }
            "c" | "cpp" => {
                if line.starts_with("assert(") {
                    extract_parenthesized_arg(line, "assert")
                } else {
                    None
                }
            }
            _ => None,
        };

        assertion.map(|expr| {
            let variables = extract_variables_from_expr(expr);
            let mut inv = Invariant::new(
                InvariantType::Precondition,
                expr.to_string(),
                Location::new(line_num),
                1.0,
            )
            .as_explicit()
            .with_evidence(Evidence {
                kind: EvidenceKind::ExplicitAssert,
                location: Location::new(line_num),
                description: "Explicit assert statement".to_string(),
                code_snippet: Some(line.to_string()),
            });

            for var in variables {
                inv = inv.with_variable(var);
            }
            inv
        })
    }

    /// Extract a guard clause as a precondition.
    fn extract_guard_clause(
        &self,
        line: &str,
        line_num: usize,
        body: &[&str],
        idx: usize,
    ) -> Option<Invariant> {
        // Pattern: if <condition>: raise/throw/return/panic
        let (condition, raises) = match self.language.as_str() {
            "python" => {
                if line.starts_with("if ") && line.ends_with(':') {
                    let condition = line.trim_start_matches("if ").trim_end_matches(':').trim();
                    // Check if next line raises
                    let next_line = body.get(idx + 1).map(|l| l.trim());
                    let raises = next_line
                        .map_or(false, |l| l.starts_with("raise") || l.starts_with("return"));
                    (Some(condition), raises)
                } else if line.starts_with("if ") && line.contains("raise ") {
                    // Single-line: if x is None: raise ValueError()
                    if let Some(pos) = line.find(':') {
                        let condition = line[3..pos].trim();
                        (Some(condition), true)
                    } else {
                        (None, false)
                    }
                } else {
                    (None, false)
                }
            }
            "typescript" | "javascript" => {
                if line.starts_with("if (") || line.starts_with("if(") {
                    if let Some(condition) = extract_if_condition(line) {
                        // Check if body contains throw
                        let has_throw = line.contains("throw ")
                            || body
                                .get(idx + 1)
                                .map_or(false, |l| l.trim().starts_with("throw "));
                        (Some(condition), has_throw)
                    } else {
                        (None, false)
                    }
                } else {
                    (None, false)
                }
            }
            "rust" => {
                if line.starts_with("if ") {
                    if let Some(condition) = extract_rust_if_condition(line) {
                        let has_panic = line.contains("panic!")
                            || line.contains("return Err")
                            || body.get(idx + 1).map_or(false, |l| {
                                let t = l.trim();
                                t.starts_with("panic!") || t.starts_with("return Err")
                            });
                        (Some(condition), has_panic)
                    } else {
                        (None, false)
                    }
                } else {
                    (None, false)
                }
            }
            "go" => {
                if line.starts_with("if ") {
                    if let Some(condition) = extract_go_if_condition(line) {
                        let has_panic = line.contains("panic(")
                            || line.contains("return ")
                            || body.get(idx + 1).map_or(false, |l| {
                                let t = l.trim();
                                t.starts_with("panic(") || t.starts_with("return ")
                            });
                        (Some(condition), has_panic)
                    } else {
                        (None, false)
                    }
                } else {
                    (None, false)
                }
            }
            "java" | "kotlin" | "csharp" => {
                if line.starts_with("if (") || line.starts_with("if(") {
                    if let Some(condition) = extract_if_condition(line) {
                        let has_throw = line.contains("throw ")
                            || body
                                .get(idx + 1)
                                .map_or(false, |l| l.trim().starts_with("throw "));
                        (Some(condition), has_throw)
                    } else {
                        (None, false)
                    }
                } else {
                    (None, false)
                }
            }
            "c" | "cpp" => {
                if line.starts_with("if (") || line.starts_with("if(") {
                    if let Some(condition) = extract_if_condition(line) {
                        let has_error = line.contains("return ")
                            || line.contains("abort()")
                            || line.contains("exit(")
                            || body.get(idx + 1).map_or(false, |l| {
                                let t = l.trim();
                                t.starts_with("return ")
                                    || t.contains("abort()")
                                    || t.contains("exit(")
                            });
                        (Some(condition), has_error)
                    } else {
                        (None, false)
                    }
                } else {
                    (None, false)
                }
            }
            _ => (None, false),
        };

        if let Some(cond) = condition {
            if raises {
                // Negate the condition to get the precondition
                let precond = negate_condition(cond, &self.language);
                let variables = extract_variables_from_expr(cond);

                let mut inv = Invariant::new(
                    InvariantType::Precondition,
                    precond,
                    Location::new(line_num),
                    0.9,
                )
                .with_evidence(Evidence {
                    kind: EvidenceKind::GuardClause,
                    location: Location::new(line_num),
                    description: "Guard clause with raise/throw".to_string(),
                    code_snippet: Some(line.to_string()),
                });

                for var in variables {
                    inv = inv.with_variable(var);
                }
                return Some(inv);
            }
        }

        None
    }

    /// Extract type check as a precondition.
    fn extract_type_check(&self, line: &str, line_num: usize) -> Option<Invariant> {
        match self.language.as_str() {
            "python" => {
                // isinstance(x, Type) check in guard
                if line.contains("isinstance(") && (line.contains("not ") || line.contains("if ")) {
                    if let Some((var, type_name)) = extract_isinstance(line) {
                        let precond = format!("isinstance({}, {})", var, type_name);
                        return Some(
                            Invariant::new(
                                InvariantType::Precondition,
                                precond,
                                Location::new(line_num),
                                0.8,
                            )
                            .with_variable(var.to_string())
                            .with_evidence(Evidence {
                                kind: EvidenceKind::TypeCheck,
                                location: Location::new(line_num),
                                description: "Type check guard".to_string(),
                                code_snippet: Some(line.to_string()),
                            }),
                        );
                    }
                }
            }
            "typescript" => {
                // typeof x === 'type' check
                if line.contains("typeof ") && line.contains("===") {
                    if let Some((var, type_name)) = extract_typeof(line) {
                        let precond = format!("typeof {} === '{}'", var, type_name);
                        return Some(
                            Invariant::new(
                                InvariantType::Precondition,
                                precond,
                                Location::new(line_num),
                                0.8,
                            )
                            .with_variable(var.to_string())
                            .with_evidence(Evidence {
                                kind: EvidenceKind::TypeCheck,
                                location: Location::new(line_num),
                                description: "typeof check".to_string(),
                                code_snippet: Some(line.to_string()),
                            }),
                        );
                    }
                }
            }
            "java" | "kotlin" | "csharp" => {
                // instanceof check
                if line.contains("instanceof ") {
                    if let Some((var, type_name)) = extract_instanceof(line) {
                        let precond = format!("{} instanceof {}", var, type_name);
                        return Some(
                            Invariant::new(
                                InvariantType::Precondition,
                                precond,
                                Location::new(line_num),
                                0.8,
                            )
                            .with_variable(var.to_string())
                            .with_evidence(Evidence {
                                kind: EvidenceKind::TypeCheck,
                                location: Location::new(line_num),
                                description: "instanceof check".to_string(),
                                code_snippet: Some(line.to_string()),
                            }),
                        );
                    }
                }
            }
            _ => {}
        }
        None
    }

    /// Extract postconditions from function body.
    fn extract_postconditions(&self, body: &[&str], start_line: usize) -> Vec<Invariant> {
        let mut postconditions = Vec::new();

        // Look for assertions near return statements
        let mut prev_line: Option<&str> = None;
        for (idx, line) in body.iter().enumerate() {
            let line_num = start_line + idx;
            let trimmed = line.trim();

            // Check for assertion before return
            if is_return_statement(trimmed, &self.language) {
                if let Some(prev) = prev_line {
                    if let Some(inv) =
                        self.extract_assert_postcondition(prev, line_num - 1, trimmed)
                    {
                        postconditions.push(inv);
                    }
                }

                // Also analyze return value for implicit postconditions
                if let Some(inv) = self.extract_return_postcondition(trimmed, line_num) {
                    postconditions.push(inv);
                }
            }

            prev_line = Some(trimmed);
        }

        // Look for final assertions at end of function
        for (idx, line) in body.iter().enumerate().rev() {
            let line_num = start_line + idx;
            let trimmed = line.trim();

            if trimmed.is_empty() || is_comment(trimmed, &self.language) {
                continue;
            }

            if is_assert_statement(trimmed, &self.language) {
                if let Some(inv) = self.extract_assert_postcondition(trimmed, line_num, "") {
                    postconditions.push(inv);
                }
            }

            // Only look at last few lines
            if body.len() - idx > 5 {
                break;
            }
        }

        postconditions
    }

    /// Extract assertion as postcondition.
    fn extract_assert_postcondition(
        &self,
        line: &str,
        line_num: usize,
        return_line: &str,
    ) -> Option<Invariant> {
        let assertion = match self.language.as_str() {
            "python" => {
                if line.starts_with("assert ") {
                    Some(line.trim_start_matches("assert ").trim())
                } else {
                    None
                }
            }
            "rust" => {
                if line.starts_with("assert!") || line.starts_with("debug_assert!") {
                    extract_macro_arg(line)
                } else {
                    None
                }
            }
            _ => {
                if line.starts_with("assert") {
                    extract_parenthesized_arg(line, "assert")
                } else {
                    None
                }
            }
        };

        assertion.map(|expr| {
            let variables = extract_variables_from_expr(expr);
            let mut inv = Invariant::new(
                InvariantType::Postcondition,
                expr.to_string(),
                Location::new(line_num),
                1.0,
            )
            .as_explicit()
            .with_evidence(Evidence {
                kind: EvidenceKind::ExplicitAssert,
                location: Location::new(line_num),
                description: if return_line.is_empty() {
                    "Final assertion".to_string()
                } else {
                    "Assertion before return".to_string()
                },
                code_snippet: Some(line.to_string()),
            });

            for var in variables {
                inv = inv.with_variable(var);
            }
            inv
        })
    }

    /// Extract implicit postcondition from return statement.
    fn extract_return_postcondition(&self, line: &str, line_num: usize) -> Option<Invariant> {
        let return_expr = match self.language.as_str() {
            "python" => {
                if line.starts_with("return ") {
                    Some(line.trim_start_matches("return ").trim())
                } else {
                    None
                }
            }
            "rust" => {
                // Rust has implicit returns too
                if line.starts_with("return ") {
                    Some(line.trim_start_matches("return ").trim_end_matches(';'))
                } else if !line.contains("let ") && !line.contains("=") && line.ends_with(';') {
                    // Might be implicit return
                    None
                } else {
                    None
                }
            }
            _ => {
                if line.starts_with("return ") {
                    Some(line.trim_start_matches("return ").trim_end_matches(';'))
                } else {
                    None
                }
            }
        };

        if let Some(expr) = return_expr {
            // Infer type from literal
            if let Some(postcond) = infer_return_type_postcondition(expr) {
                return Some(
                    Invariant::new(
                        InvariantType::Postcondition,
                        postcond,
                        Location::new(line_num),
                        0.6,
                    )
                    .with_evidence(Evidence {
                        kind: EvidenceKind::ReturnStatement,
                        location: Location::new(line_num),
                        description: "Inferred from return value".to_string(),
                        code_snippet: Some(line.to_string()),
                    }),
                );
            }
        }

        None
    }

    /// Extract loop invariants.
    fn extract_loop_invariants(
        &self,
        body: &[&str],
        start_line: usize,
    ) -> (
        HashMap<usize, Vec<Invariant>>,
        HashMap<usize, LoopInvariantInfo>,
    ) {
        let mut invariants: HashMap<usize, Vec<Invariant>> = HashMap::new();
        let mut details: HashMap<usize, LoopInvariantInfo> = HashMap::new();

        // Find loops
        for (idx, line) in body.iter().enumerate() {
            let line_num = start_line + idx;
            let trimmed = line.trim();

            let (loop_var, bounds) = self.detect_loop_start(trimmed);
            if loop_var.is_some() || bounds.is_some() {
                // Found a loop - analyze it
                let loop_end = self.find_loop_end(body, idx);
                let loop_body = &body[idx..=loop_end.min(body.len() - 1)];

                // Find variables modified in loop
                let modified = self.find_modified_variables(loop_body);

                // Find variables used but not modified (potential invariants)
                let used = self.find_used_variables(loop_body);
                let unmodified: Vec<String> = used
                    .iter()
                    .filter(|v| !modified.contains(*v))
                    .cloned()
                    .collect();

                // Detect monotonic variables
                let monotonic = self.detect_monotonic_variables(loop_body, &modified);

                let loop_info = LoopInvariantInfo {
                    loop_variable: loop_var.clone(),
                    unmodified_variables: unmodified.clone(),
                    monotonic_variables: monotonic,
                    bounds: bounds.clone(),
                };

                // Generate invariants
                let mut loop_invs = Vec::new();

                // Unmodified variable invariants
                for var in &unmodified {
                    loop_invs.push(
                        Invariant::new(
                            InvariantType::LoopInvariant,
                            format!("{} is unchanged", var),
                            Location::new(line_num),
                            0.7,
                        )
                        .with_variable(var.clone())
                        .with_evidence(Evidence {
                            kind: EvidenceKind::LoopBound,
                            location: Location::new(line_num),
                            description: "Variable not modified in loop".to_string(),
                            code_snippet: None,
                        }),
                    );
                }

                // Bounds invariants
                if let Some(ref b) = bounds {
                    if let Some(ref lv) = loop_var {
                        if let Some(ref lower) = b.lower {
                            loop_invs.push(
                                Invariant::new(
                                    InvariantType::LoopInvariant,
                                    format!("{} >= {}", lv, lower),
                                    Location::new(line_num),
                                    0.8,
                                )
                                .with_variable(lv.clone())
                                .with_evidence(Evidence {
                                    kind: EvidenceKind::LoopBound,
                                    location: Location::new(line_num),
                                    description: "Loop lower bound".to_string(),
                                    code_snippet: Some(trimmed.to_string()),
                                }),
                            );
                        }
                        if let Some(ref upper) = b.upper {
                            let op = if b.inclusive { "<=" } else { "<" };
                            loop_invs.push(
                                Invariant::new(
                                    InvariantType::LoopInvariant,
                                    format!("{} {} {}", lv, op, upper),
                                    Location::new(line_num),
                                    0.8,
                                )
                                .with_variable(lv.clone())
                                .with_evidence(Evidence {
                                    kind: EvidenceKind::LoopBound,
                                    location: Location::new(line_num),
                                    description: "Loop upper bound".to_string(),
                                    code_snippet: Some(trimmed.to_string()),
                                }),
                            );
                        }
                    }
                }

                invariants.insert(line_num, loop_invs);
                details.insert(line_num, loop_info);
            }
        }

        (invariants, details)
    }

    /// Detect loop start and extract loop variable/bounds.
    fn detect_loop_start(&self, line: &str) -> (Option<String>, Option<LoopBounds>) {
        match self.language.as_str() {
            "python" => {
                if line.starts_with("for ") {
                    // for x in range(n):
                    if let Some(rest) = line.strip_prefix("for ") {
                        if let Some(in_pos) = rest.find(" in ") {
                            let var = rest[..in_pos].trim().to_string();
                            let iterable = rest[in_pos + 4..].trim().trim_end_matches(':');

                            // Parse range(...)
                            if iterable.starts_with("range(") {
                                let bounds = parse_python_range(iterable);
                                return (Some(var), bounds);
                            } else {
                                return (Some(var), None);
                            }
                        }
                    }
                } else if line.starts_with("while ") {
                    return (None, None);
                }
            }
            "rust" => {
                if line.starts_with("for ") {
                    // for x in 0..n { or for x in collection {
                    if let Some(rest) = line.strip_prefix("for ") {
                        if let Some(in_pos) = rest.find(" in ") {
                            let var = rest[..in_pos].trim().to_string();
                            let iterable = rest[in_pos + 4..].trim().trim_end_matches('{').trim();

                            // Parse range (0..n or 0..=n)
                            if let Some(bounds) = parse_rust_range(iterable) {
                                return (Some(var), Some(bounds));
                            }
                            return (Some(var), None);
                        }
                    }
                } else if line.starts_with("while ") || line.starts_with("loop ") {
                    return (None, None);
                }
            }
            "go" => {
                if line.starts_with("for ") {
                    // for i := 0; i < n; i++ {
                    if let Some((var, bounds)) = parse_go_for_loop(line) {
                        return (Some(var), Some(bounds));
                    }
                    // for _, x := range collection {
                    if line.contains(" range ") {
                        if let Some(var) = extract_go_range_var(line) {
                            return (Some(var), None);
                        }
                    }
                    return (None, None);
                }
            }
            "java" | "c" | "cpp" | "csharp" | "kotlin" => {
                if line.starts_with("for (") || line.starts_with("for(") {
                    // C-style for loop
                    if let Some((var, bounds)) = parse_c_style_for_loop(line) {
                        return (Some(var), Some(bounds));
                    }
                }
                if line.starts_with("while ") || line.starts_with("while(") {
                    return (None, None);
                }
            }
            "typescript" | "javascript" => {
                if line.starts_with("for (") || line.starts_with("for(") {
                    // for (let i = 0; i < n; i++) or for (const x of collection)
                    if line.contains(" of ") || line.contains(" in ") {
                        if let Some(var) = extract_js_for_of_var(line) {
                            return (Some(var), None);
                        }
                    }
                    if let Some((var, bounds)) = parse_c_style_for_loop(line) {
                        return (Some(var), Some(bounds));
                    }
                }
                if line.starts_with("while ") || line.starts_with("while(") {
                    return (None, None);
                }
            }
            _ => {}
        }
        (None, None)
    }

    /// Find end of loop starting at given index.
    fn find_loop_end(&self, body: &[&str], start_idx: usize) -> usize {
        if start_idx >= body.len() {
            return start_idx;
        }

        match self.language.as_str() {
            "python" => {
                let loop_line = body[start_idx];
                let base_indent = loop_line.len() - loop_line.trim_start().len();

                for (idx, line) in body[start_idx + 1..].iter().enumerate() {
                    let trimmed = line.trim();
                    if trimmed.is_empty() {
                        continue;
                    }
                    let indent = line.len() - line.trim_start().len();
                    if indent <= base_indent {
                        return start_idx + idx;
                    }
                }
                body.len() - 1
            }
            _ => {
                // Brace matching
                let mut brace_count = 0;
                let mut found_first_brace = false;

                for (idx, line) in body[start_idx..].iter().enumerate() {
                    for ch in line.chars() {
                        if ch == '{' {
                            brace_count += 1;
                            found_first_brace = true;
                        } else if ch == '}' {
                            brace_count -= 1;
                            if found_first_brace && brace_count == 0 {
                                return start_idx + idx;
                            }
                        }
                    }
                }
                body.len() - 1
            }
        }
    }

    /// Find variables modified in a block of code.
    fn find_modified_variables(&self, block: &[&str]) -> HashSet<String> {
        let mut modified = HashSet::new();

        for line in block {
            let trimmed = line.trim();

            // Assignment patterns
            match self.language.as_str() {
                "python" => {
                    // x = ..., x += ..., x -= ..., etc.
                    if let Some(eq_pos) = trimmed.find('=') {
                        if eq_pos > 0 {
                            let before_eq = &trimmed[..eq_pos];
                            // Check it's not ==, !=, <=, >=
                            let prev_char = before_eq.chars().last();
                            if !matches!(prev_char, Some('=') | Some('!') | Some('<') | Some('>')) {
                                // Extract variable name (handle augmented assignment)
                                let var_part = before_eq
                                    .trim_end_matches(['+', '-', '*', '/', '%', '&', '|', '^']);
                                let var = var_part.trim().split('[').next().unwrap_or("").trim();
                                if is_valid_identifier(var) {
                                    modified.insert(var.to_string());
                                }
                            }
                        }
                    }
                }
                "rust" => {
                    // let mut x = ..., x = ..., x += ...
                    if trimmed.starts_with("let ") || trimmed.starts_with("let mut ") {
                        if let Some(eq_pos) = trimmed.find('=') {
                            let before = &trimmed[..eq_pos];
                            let var = before
                                .trim_start_matches("let ")
                                .trim_start_matches("mut ")
                                .split(':')
                                .next()
                                .unwrap_or("")
                                .trim();
                            if is_valid_identifier(var) {
                                modified.insert(var.to_string());
                            }
                        }
                    } else if let Some(eq_pos) = trimmed.find('=') {
                        if eq_pos > 0 {
                            let before_eq = &trimmed[..eq_pos];
                            let prev_char = before_eq.chars().last();
                            if !matches!(prev_char, Some('=') | Some('!') | Some('<') | Some('>')) {
                                let var_part = before_eq
                                    .trim_end_matches(['+', '-', '*', '/', '%', '&', '|', '^']);
                                let var = var_part.trim().split('.').next().unwrap_or("").trim();
                                if is_valid_identifier(var) {
                                    modified.insert(var.to_string());
                                }
                            }
                        }
                    }
                }
                _ => {
                    // Generic assignment detection
                    if let Some(eq_pos) = trimmed.find('=') {
                        if eq_pos > 0 {
                            let before_eq = &trimmed[..eq_pos];
                            let prev_char = before_eq.chars().last();
                            if !matches!(prev_char, Some('=') | Some('!') | Some('<') | Some('>')) {
                                // Handle various declaration patterns
                                let var_part = before_eq
                                    .trim_end_matches(['+', '-', '*', '/', '%', '&', '|', '^'])
                                    .trim_start_matches("let ")
                                    .trim_start_matches("const ")
                                    .trim_start_matches("var ")
                                    .trim_start_matches("mut ");
                                let var = var_part
                                    .split([' ', '\t', ':', '['])
                                    .last()
                                    .unwrap_or("")
                                    .trim();
                                if is_valid_identifier(var) {
                                    modified.insert(var.to_string());
                                }
                            }
                        }
                    }
                }
            }

            // Increment/decrement
            if trimmed.contains("++") || trimmed.contains("--") {
                let var = trimmed
                    .trim_end_matches("++")
                    .trim_end_matches("--")
                    .trim_start_matches("++")
                    .trim_start_matches("--")
                    .trim()
                    .trim_end_matches(';');
                if is_valid_identifier(var) {
                    modified.insert(var.to_string());
                }
            }
        }

        modified
    }

    /// Find variables used in a block of code.
    fn find_used_variables(&self, block: &[&str]) -> HashSet<String> {
        let mut used = HashSet::new();
        let identifier_pattern = regex::Regex::new(r"\b([a-zA-Z_][a-zA-Z0-9_]*)\b").ok();

        if let Some(ref pattern) = identifier_pattern {
            for line in block {
                for cap in pattern.captures_iter(line) {
                    let var = cap.get(1).map_or("", |m| m.as_str());
                    if !is_keyword(var, &self.language) && is_valid_identifier(var) {
                        used.insert(var.to_string());
                    }
                }
            }
        }

        used
    }

    /// Detect variables with monotonic behavior in loop.
    fn detect_monotonic_variables(
        &self,
        block: &[&str],
        modified: &HashSet<String>,
    ) -> Vec<MonotonicVariable> {
        let mut monotonic = Vec::new();

        for var in modified {
            let mut only_increases = true;
            let mut only_decreases = true;
            let mut has_modification = false;

            for line in block {
                let trimmed = line.trim();

                // Check for increment patterns
                if trimmed.contains(&format!("{} += ", var))
                    || trimmed.contains(&format!("{} = {} + ", var, var))
                    || trimmed.contains(&format!("{}++", var))
                    || trimmed.contains(&format!("++{}", var))
                {
                    only_decreases = false;
                    has_modification = true;
                }

                // Check for decrement patterns
                if trimmed.contains(&format!("{} -= ", var))
                    || trimmed.contains(&format!("{} = {} - ", var, var))
                    || trimmed.contains(&format!("{}--", var))
                    || trimmed.contains(&format!("--{}", var))
                {
                    only_increases = false;
                    has_modification = true;
                }

                // Generic assignment breaks monotonicity
                if trimmed.starts_with(&format!("{} = ", var))
                    && !trimmed.contains(&format!("{} = {} +", var, var))
                    && !trimmed.contains(&format!("{} = {} -", var, var))
                {
                    only_increases = false;
                    only_decreases = false;
                }
            }

            if has_modification {
                if only_increases {
                    monotonic.push(MonotonicVariable {
                        name: var.clone(),
                        direction: MonotonicDirection::Increasing,
                        confidence: 0.8,
                    });
                } else if only_decreases {
                    monotonic.push(MonotonicVariable {
                        name: var.clone(),
                        direction: MonotonicDirection::Decreasing,
                        confidence: 0.8,
                    });
                }
            }
        }

        monotonic
    }

    /// Generate suggested assertions.
    fn generate_suggestions(
        &self,
        body: &[&str],
        start_line: usize,
        existing_preconditions: &[Invariant],
    ) -> Vec<SuggestedAssertion> {
        let mut suggestions = Vec::new();

        // Track which parameters already have checks
        let checked_params: HashSet<_> = existing_preconditions
            .iter()
            .flat_map(|inv| inv.variables.iter().cloned())
            .collect();

        // Find function parameters
        if let Some(first_line) = body.first() {
            let params = extract_parameters(first_line, &self.language);

            // Suggest null checks for unchecked parameters
            for param in &params {
                if !checked_params.contains(param) {
                    // Check parameter naming for hints
                    let suggestion = match self.language.as_str() {
                        "python" => {
                            if param.ends_with("_list")
                                || param.ends_with("_array")
                                || param == "items"
                            {
                                Some(SuggestedAssertion {
                                    location: Location::new(start_line + 1),
                                    assertion: format!(
                                        "assert {} is not None and len({}) > 0",
                                        param, param
                                    ),
                                    reason:
                                        "Parameter appears to be a collection - validate non-empty"
                                            .to_string(),
                                    confidence: 0.5,
                                    category: SuggestionCategory::NonEmpty,
                                })
                            } else {
                                Some(SuggestedAssertion {
                                    location: Location::new(start_line + 1),
                                    assertion: format!("assert {} is not None", param),
                                    reason: "Parameter may need null validation".to_string(),
                                    confidence: 0.4,
                                    category: SuggestionCategory::NullCheck,
                                })
                            }
                        }
                        "typescript" | "javascript" => Some(SuggestedAssertion {
                            location: Location::new(start_line + 1),
                            assertion: format!(
                                "if ({} === null || {} === undefined) throw new Error(\"...\")",
                                param, param
                            ),
                            reason: "Parameter may need null/undefined validation".to_string(),
                            confidence: 0.4,
                            category: SuggestionCategory::NullCheck,
                        }),
                        "rust" => {
                            // Rust has Option/Result, so null checks are less common
                            None
                        }
                        "go" => Some(SuggestedAssertion {
                            location: Location::new(start_line + 1),
                            assertion: format!(
                                "if {} == nil {{ return nil, errors.New(\"...\") }}",
                                param
                            ),
                            reason: "Parameter may need nil check".to_string(),
                            confidence: 0.4,
                            category: SuggestionCategory::NullCheck,
                        }),
                        _ => None,
                    };

                    if let Some(s) = suggestion {
                        suggestions.push(s);
                    }
                }
            }
        }

        // Look for division operations without denominator checks
        for (idx, line) in body.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.contains(" / ") || trimmed.contains(" // ") || trimmed.contains(" % ") {
                // Extract denominator
                if let Some(denom) = extract_denominator(trimmed) {
                    if is_valid_identifier(&denom) && !checked_params.contains(&denom) {
                        suggestions.push(SuggestedAssertion {
                            location: Location::new(start_line + idx),
                            assertion: match self.language.as_str() {
                                "python" => format!("assert {} != 0, \"Division by zero\"", denom),
                                "rust" => format!("assert!({} != 0, \"Division by zero\");", denom),
                                _ => format!("assert({} != 0)", denom),
                            },
                            reason: "Division operation - consider checking for zero".to_string(),
                            confidence: 0.7,
                            category: SuggestionCategory::RangeCheck,
                        });
                    }
                }
            }
        }

        suggestions
    }

    /// Calculate metrics for the analysis.
    fn calculate_metrics(
        &self,
        preconditions: &[Invariant],
        postconditions: &[Invariant],
        loop_invariants: &HashMap<usize, Vec<Invariant>>,
        suggestions: &[SuggestedAssertion],
    ) -> InvariantMetrics {
        let explicit = preconditions.iter().filter(|i| i.is_explicit).count()
            + postconditions.iter().filter(|i| i.is_explicit).count();

        let inferred_pre = preconditions.iter().filter(|i| !i.is_explicit).count();
        let inferred_post = postconditions.iter().filter(|i| !i.is_explicit).count();

        let loop_count: usize = loop_invariants.values().map(|v| v.len()).sum();

        let guard_clauses = preconditions
            .iter()
            .filter(|i| {
                i.evidence
                    .iter()
                    .any(|e| e.kind == EvidenceKind::GuardClause)
            })
            .count();

        let type_checks = preconditions
            .iter()
            .filter(|i| i.evidence.iter().any(|e| e.kind == EvidenceKind::TypeCheck))
            .count();

        let all_confidences: Vec<f64> = preconditions
            .iter()
            .chain(postconditions.iter())
            .chain(loop_invariants.values().flatten())
            .map(|i| i.confidence)
            .collect();

        let avg_confidence = if all_confidences.is_empty() {
            0.0
        } else {
            all_confidences.iter().sum::<f64>() / all_confidences.len() as f64
        };

        InvariantMetrics {
            explicit_assertions: explicit,
            inferred_preconditions: inferred_pre,
            inferred_postconditions: inferred_post,
            loop_invariants_count: loop_count,
            suggestions_count: suggestions.len(),
            average_confidence: avg_confidence,
            guard_clauses,
            type_checks,
        }
    }

    /// Analyze all functions in the source.
    pub fn analyze_all(&self) -> Result<Vec<FunctionInvariantAnalysis>> {
        let functions = self.find_all_functions();
        let mut analyses = Vec::new();

        for func_name in functions {
            if let Ok(analysis) = self.analyze_function(&func_name) {
                analyses.push(analysis);
            }
        }

        Ok(analyses)
    }

    /// Find all function names in the source.
    fn find_all_functions(&self) -> Vec<String> {
        let mut functions = Vec::new();

        let patterns: Vec<&str> = match self.language.as_str() {
            "python" => vec!["def ", "async def "],
            "rust" => vec!["fn ", "pub fn ", "async fn ", "pub async fn "],
            "go" => vec!["func "],
            "typescript" | "javascript" => vec!["function ", "async function "],
            "java" | "kotlin" | "csharp" => vec!["void ", "public ", "private ", "protected "],
            "c" | "cpp" => vec!["void ", "int ", "char ", "float ", "double "],
            _ => vec!["fn ", "function ", "def "],
        };

        for line in &self.lines {
            let trimmed = line.trim();
            for pattern in &patterns {
                if trimmed.starts_with(pattern) || trimmed.contains(&format!(" {}", pattern)) {
                    if let Some(name) = extract_function_name(trimmed, &self.language) {
                        functions.push(name);
                    }
                    break;
                }
            }
        }

        functions
    }
}

// =============================================================================
// Public API Functions
// =============================================================================

/// Analyze a file for invariants.
///
/// # Arguments
///
/// * `path` - Path to the source file
/// * `language` - Optional language override
///
/// # Returns
///
/// File-level invariant analysis.
///
/// # Errors
///
/// Returns error if file cannot be read or parsed.
pub fn analyze_invariants(path: &str, language: Option<&str>) -> Result<FileInvariantAnalysis> {
    let analyzer = InvariantAnalyzer::from_file(path, language)?;
    let functions = analyzer.analyze_all()?;

    let mut by_type: HashMap<String, usize> = HashMap::new();
    let mut total = 0;
    let mut total_confidence = 0.0;
    let mut confidence_count = 0;
    let mut total_suggestions = 0;

    for func in &functions {
        for inv in &func.preconditions {
            *by_type.entry(inv.invariant_type.to_string()).or_insert(0) += 1;
            total += 1;
            total_confidence += inv.confidence;
            confidence_count += 1;
        }
        for inv in &func.postconditions {
            *by_type.entry(inv.invariant_type.to_string()).or_insert(0) += 1;
            total += 1;
            total_confidence += inv.confidence;
            confidence_count += 1;
        }
        for invs in func.loop_invariants.values() {
            for inv in invs {
                *by_type.entry(inv.invariant_type.to_string()).or_insert(0) += 1;
                total += 1;
                total_confidence += inv.confidence;
                confidence_count += 1;
            }
        }
        total_suggestions += func.suggested_assertions.len();
    }

    let avg_confidence = if confidence_count > 0 {
        total_confidence / confidence_count as f64
    } else {
        0.0
    };

    let functions_analyzed = functions.len();

    Ok(FileInvariantAnalysis {
        file: path.to_string(),
        language: analyzer.language.clone(),
        functions,
        class_invariants: HashMap::new(), // TODO: Implement class invariant detection
        summary: InvariantSummary {
            functions_analyzed,
            total_invariants: total,
            by_type,
            average_confidence: avg_confidence,
            total_suggestions,
        },
    })
}

/// Analyze a specific function for invariants.
///
/// # Arguments
///
/// * `path` - Path to the source file
/// * `function_name` - Name of the function to analyze
/// * `language` - Optional language override
///
/// # Returns
///
/// Function-level invariant analysis.
///
/// # Errors
///
/// Returns error if file cannot be read, function not found, or parse fails.
pub fn analyze_invariants_function(
    path: &str,
    function_name: &str,
    language: Option<&str>,
) -> Result<FunctionInvariantAnalysis> {
    let analyzer = InvariantAnalyzer::from_file(path, language)?;
    let mut analysis = analyzer.analyze_function(function_name)?;
    analysis.file = path.to_string();
    Ok(analysis)
}

/// Analyze source code directly for invariants.
///
/// # Arguments
///
/// * `source` - Source code to analyze
/// * `language` - Programming language
///
/// # Returns
///
/// List of function analyses.
pub fn analyze_invariants_source(
    source: &str,
    language: &str,
) -> Result<Vec<FunctionInvariantAnalysis>> {
    let analyzer = InvariantAnalyzer::new(source, language);
    analyzer.analyze_all()
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Detect language from file extension.
fn detect_language(path: &str) -> Result<String> {
    let ext = Path::new(path)
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or("");

    match ext {
        "py" => Ok("python".to_string()),
        "ts" => Ok("typescript".to_string()),
        "js" => Ok("javascript".to_string()),
        "rs" => Ok("rust".to_string()),
        "go" => Ok("go".to_string()),
        "java" => Ok("java".to_string()),
        "kt" => Ok("kotlin".to_string()),
        "cs" => Ok("csharp".to_string()),
        "c" => Ok("c".to_string()),
        "cpp" | "cc" | "cxx" | "hpp" | "cu" | "cuh" => Ok("cpp".to_string()),
        _ => Err(BrrrError::from(InvariantError::UnsupportedLanguage {
            lang: ext.to_string(),
        })),
    }
}

/// Check if a line is a comment.
fn is_comment(line: &str, language: &str) -> bool {
    match language {
        "python" => line.starts_with('#'),
        "rust" | "go" | "java" | "c" | "cpp" | "csharp" | "kotlin" | "typescript"
        | "javascript" => line.starts_with("//") || line.starts_with("/*") || line.starts_with('*'),
        _ => line.starts_with('#') || line.starts_with("//"),
    }
}

/// Check if a line is a substantive statement (not guard/setup/definition).
fn is_substantive_statement(line: &str, language: &str) -> bool {
    // Skip if it's a guard clause pattern
    if line.starts_with("if ")
        && (line.contains("raise") || line.contains("throw") || line.contains("panic"))
    {
        return false;
    }
    if line.starts_with("assert") {
        return false;
    }

    match language {
        "python" => {
            // Skip function definitions, guards, assertions, docstrings, etc.
            !line.starts_with("def ")
                && !line.starts_with("async def ")
                && !line.starts_with("if ")
                && !line.starts_with("assert ")
                && !line.starts_with("raise ")
                && !line.starts_with("\"\"\"")
                && !line.starts_with("'''")
                && !line.is_empty()
                && !line.starts_with('#')
        }
        "rust" => {
            !line.starts_with("fn ")
                && !line.starts_with("pub fn ")
                && !line.starts_with("async fn ")
                && !line.starts_with("pub async fn ")
                && !line.starts_with("if ")
                && !line.starts_with("assert!")
                && !line.starts_with("debug_assert!")
                && !line.is_empty()
        }
        "go" => !line.starts_with("func ") && !line.starts_with("if ") && !line.is_empty(),
        "typescript" | "javascript" => {
            !line.starts_with("function ")
                && !line.starts_with("async function ")
                && !line.starts_with("if ")
                && !line.starts_with("if(")
                && !line.is_empty()
        }
        _ => !line.starts_with("if ") && !line.starts_with("if(") && !line.is_empty(),
    }
}

/// Check if a line is a return statement.
fn is_return_statement(line: &str, language: &str) -> bool {
    match language {
        "rust" => line.starts_with("return ") || (line.ends_with(';') && !line.contains('=')),
        _ => line.starts_with("return ") || line.starts_with("return;"),
    }
}

/// Check if a line is an assert statement.
fn is_assert_statement(line: &str, language: &str) -> bool {
    match language {
        "python" => line.starts_with("assert "),
        "rust" => line.starts_with("assert!") || line.starts_with("debug_assert!"),
        _ => line.starts_with("assert") && line.contains('('),
    }
}

/// Extract argument from a Rust macro invocation.
fn extract_macro_arg(line: &str) -> Option<&str> {
    let start = line.find('(')?;
    let end = line.rfind(')')?;
    if start < end {
        Some(line[start + 1..end].trim())
    } else {
        None
    }
}

/// Extract argument from a parenthesized function call.
fn extract_parenthesized_arg<'a>(line: &'a str, prefix: &str) -> Option<&'a str> {
    let start = line.find(prefix)?;
    let paren_start = line[start..].find('(')?;
    let abs_start = start + paren_start + 1;

    // Find matching closing paren
    let mut depth = 1;
    let mut end = abs_start;
    for (i, ch) in line[abs_start..].chars().enumerate() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    end = abs_start + i;
                    break;
                }
            }
            _ => {}
        }
    }

    if end > abs_start {
        Some(line[abs_start..end].trim())
    } else {
        None
    }
}

/// Extract if condition from various languages.
fn extract_if_condition(line: &str) -> Option<&str> {
    let start = line.find('(')?;
    let mut depth = 1;
    let mut end = start + 1;

    for (i, ch) in line[start + 1..].chars().enumerate() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    end = start + 1 + i;
                    break;
                }
            }
            _ => {}
        }
    }

    if end > start + 1 {
        Some(line[start + 1..end].trim())
    } else {
        None
    }
}

/// Extract if condition from Rust code.
fn extract_rust_if_condition(line: &str) -> Option<&str> {
    let after_if = line.strip_prefix("if ")?.trim();
    // Find where condition ends (before { or let)
    let end = after_if.find('{').or_else(|| after_if.find(" let "))?;
    Some(after_if[..end].trim())
}

/// Extract if condition from Go code.
fn extract_go_if_condition(line: &str) -> Option<&str> {
    let after_if = line.strip_prefix("if ")?.trim();
    let end = after_if.find('{')?;
    // Handle short variable declaration: if err := foo(); err != nil {
    let condition = &after_if[..end];
    if let Some(semi) = condition.rfind(';') {
        Some(condition[semi + 1..].trim())
    } else {
        Some(condition.trim())
    }
}

/// Negate a boolean condition.
fn negate_condition(condition: &str, language: &str) -> String {
    let trimmed = condition.trim();

    // Handle "not" prefix
    if trimmed.starts_with("not ") {
        return trimmed[4..].trim().to_string();
    }
    if trimmed.starts_with('!') {
        return trimmed[1..].trim().to_string();
    }

    // Handle comparison operators
    if trimmed.contains(" is None") {
        return trimmed.replace(" is None", " is not None");
    }
    if trimmed.contains(" is not None") {
        return trimmed.replace(" is not None", " is None");
    }
    if trimmed.contains(" == ") {
        return trimmed.replace(" == ", " != ");
    }
    if trimmed.contains(" != ") {
        return trimmed.replace(" != ", " == ");
    }
    if trimmed.contains(" < ") {
        return trimmed.replace(" < ", " >= ");
    }
    if trimmed.contains(" > ") {
        return trimmed.replace(" > ", " <= ");
    }
    if trimmed.contains(" <= ") {
        return trimmed.replace(" <= ", " > ");
    }
    if trimmed.contains(" >= ") {
        return trimmed.replace(" >= ", " < ");
    }
    if trimmed.contains(" === ") {
        return trimmed.replace(" === ", " !== ");
    }
    if trimmed.contains(" !== ") {
        return trimmed.replace(" !== ", " === ");
    }

    // Fallback: wrap with not/!
    match language {
        "python" => format!("not ({})", trimmed),
        _ => format!("!({})", trimmed),
    }
}

/// Extract variables from an expression.
fn extract_variables_from_expr(expr: &str) -> Vec<String> {
    let mut variables = Vec::new();
    let re = regex::Regex::new(r"\b([a-zA-Z_][a-zA-Z0-9_]*)\b").ok();

    if let Some(pattern) = re {
        for cap in pattern.captures_iter(expr) {
            let var = cap.get(1).map_or("", |m| m.as_str());
            // Filter out common keywords and literals
            if is_valid_identifier(var)
                && !is_common_keyword_or_literal(var)
                && !variables.contains(&var.to_string())
            {
                variables.push(var.to_string());
            }
        }
    }

    variables
}

/// Check if string is a valid identifier.
fn is_valid_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let first = s.chars().next().unwrap();
    if !first.is_alphabetic() && first != '_' {
        return false;
    }
    s.chars().all(|c| c.is_alphanumeric() || c == '_')
}

/// Check if identifier is a language keyword.
fn is_keyword(s: &str, language: &str) -> bool {
    match language {
        "python" => matches!(
            s,
            "and"
                | "as"
                | "assert"
                | "async"
                | "await"
                | "break"
                | "class"
                | "continue"
                | "def"
                | "del"
                | "elif"
                | "else"
                | "except"
                | "False"
                | "finally"
                | "for"
                | "from"
                | "global"
                | "if"
                | "import"
                | "in"
                | "is"
                | "lambda"
                | "None"
                | "nonlocal"
                | "not"
                | "or"
                | "pass"
                | "raise"
                | "return"
                | "True"
                | "try"
                | "while"
                | "with"
                | "yield"
        ),
        "rust" => matches!(
            s,
            "as" | "async"
                | "await"
                | "break"
                | "const"
                | "continue"
                | "crate"
                | "dyn"
                | "else"
                | "enum"
                | "extern"
                | "false"
                | "fn"
                | "for"
                | "if"
                | "impl"
                | "in"
                | "let"
                | "loop"
                | "match"
                | "mod"
                | "move"
                | "mut"
                | "pub"
                | "ref"
                | "return"
                | "self"
                | "Self"
                | "static"
                | "struct"
                | "super"
                | "trait"
                | "true"
                | "type"
                | "unsafe"
                | "use"
                | "where"
                | "while"
        ),
        "go" => matches!(
            s,
            "break"
                | "case"
                | "chan"
                | "const"
                | "continue"
                | "default"
                | "defer"
                | "else"
                | "fallthrough"
                | "for"
                | "func"
                | "go"
                | "goto"
                | "if"
                | "import"
                | "interface"
                | "map"
                | "package"
                | "range"
                | "return"
                | "select"
                | "struct"
                | "switch"
                | "type"
                | "var"
                | "true"
                | "false"
                | "nil"
        ),
        _ => false,
    }
}

/// Check if identifier is a common keyword or literal across languages.
fn is_common_keyword_or_literal(s: &str) -> bool {
    matches!(
        s,
        // Boolean literals
        "true" | "false" | "null" | "nil" | "None" | "True" | "False"
            | "undefined" | "NaN" | "Infinity"
            // Type names
            | "int" | "float" | "str" | "bool" | "string" | "number"
            // Common builtins
            | "len" | "print" | "range" | "type" | "isinstance"
            // Python operators/keywords
            | "and" | "or" | "not" | "in" | "is"
            // JavaScript/TypeScript operators
            | "typeof" | "instanceof"
    )
}

/// Extract isinstance arguments.
fn extract_isinstance(line: &str) -> Option<(&str, &str)> {
    let start = line.find("isinstance(")?;
    let inner_start = start + 11;
    let inner_end = line[inner_start..].find(')')?;
    let inner = &line[inner_start..inner_start + inner_end];
    let parts: Vec<&str> = inner.split(',').collect();
    if parts.len() >= 2 {
        Some((parts[0].trim(), parts[1].trim()))
    } else {
        None
    }
}

/// Extract typeof check arguments.
fn extract_typeof(line: &str) -> Option<(&str, &str)> {
    // Pattern: typeof x === 'type'
    let typeof_pos = line.find("typeof ")?;
    let after_typeof = &line[typeof_pos + 7..];
    let var_end = after_typeof.find([' ', ')'])?;
    let var = &after_typeof[..var_end];

    // Find the type string
    let quote_start = line.find(['\'', '"'])?;
    let quote_char = line.chars().nth(quote_start)?;
    let quote_end = line[quote_start + 1..].find(quote_char)?;
    let type_name = &line[quote_start + 1..quote_start + 1 + quote_end];

    Some((var, type_name))
}

/// Extract instanceof arguments.
fn extract_instanceof(line: &str) -> Option<(&str, &str)> {
    let pos = line.find(" instanceof ")?;
    let before = &line[..pos];
    let after = &line[pos + 12..];

    // Get variable (last word before instanceof)
    let var = before.split_whitespace().last()?;

    // Get type (first word after instanceof)
    let type_name = after.split_whitespace().next()?;

    Some((var, type_name.trim_end_matches([';', ')'])))
}

/// Parse Python range() call.
fn parse_python_range(s: &str) -> Option<LoopBounds> {
    let inner = s.strip_prefix("range(")?.strip_suffix(')')?;
    let parts: Vec<&str> = inner.split(',').map(|s| s.trim()).collect();

    match parts.len() {
        1 => Some(LoopBounds {
            lower: Some("0".to_string()),
            upper: Some(parts[0].to_string()),
            inclusive: false,
        }),
        2 | 3 => Some(LoopBounds {
            lower: Some(parts[0].to_string()),
            upper: Some(parts[1].to_string()),
            inclusive: false,
        }),
        _ => None,
    }
}

/// Parse Rust range expression.
fn parse_rust_range(s: &str) -> Option<LoopBounds> {
    if let Some(pos) = s.find("..=") {
        let lower = s[..pos].trim();
        let upper = s[pos + 3..].trim();
        return Some(LoopBounds {
            lower: if lower.is_empty() {
                None
            } else {
                Some(lower.to_string())
            },
            upper: if upper.is_empty() {
                None
            } else {
                Some(upper.to_string())
            },
            inclusive: true,
        });
    }
    if let Some(pos) = s.find("..") {
        let lower = s[..pos].trim();
        let upper = s[pos + 2..].trim();
        return Some(LoopBounds {
            lower: if lower.is_empty() {
                None
            } else {
                Some(lower.to_string())
            },
            upper: if upper.is_empty() {
                None
            } else {
                Some(upper.to_string())
            },
            inclusive: false,
        });
    }
    None
}

/// Parse Go for loop.
fn parse_go_for_loop(line: &str) -> Option<(String, LoopBounds)> {
    // for i := 0; i < n; i++ {
    let after_for = line.strip_prefix("for ")?.trim();

    // Split by semicolons
    let parts: Vec<&str> = after_for.split(';').collect();
    if parts.len() < 3 {
        return None;
    }

    // Parse init: i := 0
    let init = parts[0].trim();
    let var = if let Some(pos) = init.find(":=") {
        init[..pos].trim().to_string()
    } else if let Some(pos) = init.find('=') {
        init[..pos].trim().split_whitespace().last()?.to_string()
    } else {
        return None;
    };

    let lower = if let Some(pos) = init.find(":=") {
        init[pos + 2..].trim().to_string()
    } else if let Some(pos) = init.find('=') {
        init[pos + 1..].trim().to_string()
    } else {
        "0".to_string()
    };

    // Parse condition: i < n
    let cond = parts[1].trim();
    let (upper, inclusive) = if cond.contains("<=") {
        let pos = cond.find("<=")?;
        (cond[pos + 2..].trim().to_string(), true)
    } else if cond.contains('<') {
        let pos = cond.find('<')?;
        (
            cond[pos + 1..]
                .trim()
                .trim_end_matches(['{', ' '])
                .to_string(),
            false,
        )
    } else {
        return None;
    };

    Some((
        var,
        LoopBounds {
            lower: Some(lower),
            upper: Some(upper),
            inclusive,
        },
    ))
}

/// Extract variable from Go range loop.
fn extract_go_range_var(line: &str) -> Option<String> {
    // for _, x := range collection { or for i, x := range collection {
    let after_for = line.strip_prefix("for ")?.trim();
    let assign_pos = after_for.find(":=")?;
    let vars_part = &after_for[..assign_pos];

    // Get last variable before :=
    let parts: Vec<&str> = vars_part.split(',').map(|s| s.trim()).collect();
    let var = parts.last()?.to_string();

    if var == "_" && parts.len() > 1 {
        Some(parts[0].to_string())
    } else if var != "_" {
        Some(var)
    } else {
        None
    }
}

/// Parse C-style for loop.
fn parse_c_style_for_loop(line: &str) -> Option<(String, LoopBounds)> {
    // for (int i = 0; i < n; i++) or for (let i = 0; i < n; i++)
    let start = line.find('(')?;
    let end = line.rfind(')')?;
    if start >= end {
        return None;
    }

    let inner = &line[start + 1..end];
    let parts: Vec<&str> = inner.split(';').collect();
    if parts.len() < 3 {
        return None;
    }

    // Parse init
    let init = parts[0].trim();
    let eq_pos = init.find('=')?;
    let var_part = &init[..eq_pos];
    let var = var_part.split_whitespace().last()?.trim().to_string();
    let lower = init[eq_pos + 1..].trim().to_string();

    // Parse condition
    let cond = parts[1].trim();
    let (upper, inclusive) = if cond.contains("<=") {
        let pos = cond.find("<=")?;
        (cond[pos + 2..].trim().to_string(), true)
    } else if cond.contains('<') {
        let pos = cond.find('<')?;
        (cond[pos + 1..].trim().to_string(), false)
    } else if cond.contains(">=") {
        // Decreasing loop
        let pos = cond.find(">=")?;
        (cond[pos + 2..].trim().to_string(), true)
    } else if cond.contains('>') {
        let pos = cond.find('>')?;
        (cond[pos + 1..].trim().to_string(), false)
    } else {
        return None;
    };

    Some((
        var,
        LoopBounds {
            lower: Some(lower),
            upper: Some(upper),
            inclusive,
        },
    ))
}

/// Extract variable from JS for-of loop.
fn extract_js_for_of_var(line: &str) -> Option<String> {
    // for (const x of collection) or for (let x of collection)
    let start = line.find('(')?;
    let of_pos = line.find(" of ").or_else(|| line.find(" in "))?;

    let var_part = &line[start + 1..of_pos];
    let var = var_part.split_whitespace().last()?.to_string();

    Some(var)
}

/// Extract function parameters from definition line.
fn extract_parameters(line: &str, language: &str) -> Vec<String> {
    let mut params = Vec::new();

    let start = match line.find('(') {
        Some(pos) => pos,
        None => return params,
    };
    let end = match line.rfind(')') {
        Some(pos) => pos,
        None => return params,
    };
    if start >= end {
        return params;
    }

    let inner = &line[start + 1..end];
    if inner.trim().is_empty() {
        return params;
    }

    for param in inner.split(',') {
        let cleaned = param.trim();
        if cleaned.is_empty() {
            continue;
        }

        let name = match language {
            "python" => {
                // Handle type hints: x: int, x: Optional[str] = None
                cleaned
                    .split(':')
                    .next()
                    .map(|s| s.split('=').next().unwrap_or(s).trim())
            }
            "rust" => {
                // Handle patterns: x: i32, mut x: String
                cleaned
                    .split(':')
                    .next()
                    .map(|s| s.trim_start_matches("mut ").trim())
            }
            "typescript" => {
                // Handle: x: number, x?: string
                cleaned
                    .split(':')
                    .next()
                    .map(|s| s.trim_end_matches('?').trim())
            }
            "go" => {
                // Handle: x int, x, y int
                cleaned.split_whitespace().next()
            }
            "java" | "csharp" | "kotlin" => {
                // Handle: int x, String x
                cleaned.split_whitespace().last()
            }
            "c" | "cpp" => {
                // Handle: int x, const char* x
                let words: Vec<&str> = cleaned.split_whitespace().collect();
                words
                    .last()
                    .map(|s| s.trim_start_matches('*').trim_start_matches('&'))
            }
            _ => cleaned.split_whitespace().last(),
        };

        if let Some(n) = name {
            let n = n.trim();
            if is_valid_identifier(n) && n != "self" && n != "this" && n != "cls" {
                params.push(n.to_string());
            }
        }
    }

    params
}

/// Extract denominator from division expression.
fn extract_denominator(line: &str) -> Option<String> {
    // Find division operator
    let div_pos = line
        .find(" / ")
        .or_else(|| line.find(" // "))
        .or_else(|| line.find(" % "))?;

    let op_len = if line[div_pos..].starts_with(" // ") {
        4
    } else {
        3
    };
    let after_div = &line[div_pos + op_len..];

    // Get first identifier after division
    let end = after_div
        .find(|c: char| !c.is_alphanumeric() && c != '_')
        .unwrap_or(after_div.len());

    let denom = after_div[..end].trim();
    if is_valid_identifier(denom) {
        Some(denom.to_string())
    } else {
        None
    }
}

/// Infer postcondition from return value.
fn infer_return_type_postcondition(expr: &str) -> Option<String> {
    let trimmed = expr.trim();

    // Numeric literals
    if trimmed.parse::<i64>().is_ok() || trimmed.parse::<f64>().is_ok() {
        return Some(format!("result == {}", trimmed));
    }

    // Boolean literals
    if trimmed == "True" || trimmed == "true" {
        return Some("result == true".to_string());
    }
    if trimmed == "False" || trimmed == "false" {
        return Some("result == false".to_string());
    }

    // Empty collection
    if trimmed == "[]" || trimmed == "{}" || trimmed == "()" {
        return Some("len(result) == 0".to_string());
    }

    // None/null
    if trimmed == "None" || trimmed == "null" || trimmed == "nil" {
        return Some("result is None".to_string());
    }

    None
}

/// Extract function name from definition line.
fn extract_function_name(line: &str, language: &str) -> Option<String> {
    match language {
        "python" => {
            let after_def = line
                .strip_prefix("async def ")
                .or_else(|| line.strip_prefix("def "))?;
            let paren_pos = after_def.find('(')?;
            Some(after_def[..paren_pos].trim().to_string())
        }
        "rust" => {
            let patterns = ["pub async fn ", "async fn ", "pub fn ", "fn "];
            for pattern in patterns {
                if let Some(after) = line.strip_prefix(pattern) {
                    let end = after.find(['(', '<'])?;
                    return Some(after[..end].trim().to_string());
                }
            }
            None
        }
        "go" => {
            let after_func = line.strip_prefix("func ")?;
            // Handle methods: func (r *Receiver) Method()
            let name_start = if after_func.starts_with('(') {
                after_func.find(')')? + 1
            } else {
                0
            };
            let after = &after_func[name_start..].trim_start();
            let end = after.find(['(', '['])?;
            Some(after[..end].trim().to_string())
        }
        "typescript" | "javascript" => {
            if line.contains("function ") {
                let after = line
                    .strip_prefix("async function ")
                    .or_else(|| line.strip_prefix("function "))?;
                let end = after.find(['(', '<'])?;
                Some(after[..end].trim().to_string())
            } else if line.contains(" = ") && line.contains('(') {
                // Arrow function or function expression
                let eq_pos = line.find('=')?;
                let before = &line[..eq_pos];
                let name = before.split_whitespace().last()?.trim();
                Some(name.to_string())
            } else {
                None
            }
        }
        _ => {
            // Generic: find identifier before (
            let paren_pos = line.find('(')?;
            let before = &line[..paren_pos];
            let name = before.split_whitespace().last()?.trim();
            Some(name.to_string())
        }
    }
}

// =============================================================================
// Output Formats
// =============================================================================

/// Format for invariant analysis output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OutputFormat {
    /// JSON output.
    #[default]
    Json,
    /// Human-readable text output.
    Text,
    /// Compact summary.
    Compact,
}

/// Format analysis result as JSON.
pub fn format_json(analysis: &FileInvariantAnalysis) -> Result<String> {
    serde_json::to_string_pretty(analysis).map_err(|e| BrrrError::Serialization(e.to_string()))
}

/// Format function analysis as JSON.
pub fn format_function_json(analysis: &FunctionInvariantAnalysis) -> Result<String> {
    serde_json::to_string_pretty(analysis).map_err(|e| BrrrError::Serialization(e.to_string()))
}

/// Format analysis as human-readable text.
pub fn format_text(analysis: &FileInvariantAnalysis) -> String {
    let mut output = String::new();

    output.push_str(&format!("Invariant Analysis: {}\n", analysis.file));
    output.push_str(&format!("Language: {}\n", analysis.language));
    output.push_str(&format!(
        "Functions analyzed: {}\n\n",
        analysis.summary.functions_analyzed
    ));

    for func in &analysis.functions {
        output.push_str(&format!(
            "Function: {} (lines {}-{})\n",
            func.function, func.start_line, func.end_line
        ));

        if !func.preconditions.is_empty() {
            output.push_str("  Preconditions:\n");
            for inv in &func.preconditions {
                output.push_str(&format!(
                    "    - {} (confidence: {:.2}{})\n",
                    inv.expression,
                    inv.confidence,
                    if inv.is_explicit { ", explicit" } else { "" }
                ));
            }
        }

        if !func.postconditions.is_empty() {
            output.push_str("  Postconditions:\n");
            for inv in &func.postconditions {
                output.push_str(&format!(
                    "    - {} (confidence: {:.2}{})\n",
                    inv.expression,
                    inv.confidence,
                    if inv.is_explicit { ", explicit" } else { "" }
                ));
            }
        }

        if !func.loop_invariants.is_empty() {
            output.push_str("  Loop Invariants:\n");
            for (line, invs) in &func.loop_invariants {
                output.push_str(&format!("    At line {}:\n", line));
                for inv in invs {
                    output.push_str(&format!(
                        "      - {} (confidence: {:.2})\n",
                        inv.expression, inv.confidence
                    ));
                }
            }
        }

        if !func.suggested_assertions.is_empty() {
            output.push_str("  Suggested Assertions:\n");
            for sug in &func.suggested_assertions {
                output.push_str(&format!(
                    "    - Line {}: {} ({:.2})\n      Reason: {}\n",
                    sug.location.line, sug.assertion, sug.confidence, sug.reason
                ));
            }
        }

        output.push('\n');
    }

    // Summary
    output.push_str("Summary:\n");
    output.push_str(&format!(
        "  Total invariants: {}\n",
        analysis.summary.total_invariants
    ));
    output.push_str(&format!(
        "  Average confidence: {:.2}\n",
        analysis.summary.average_confidence
    ));
    output.push_str(&format!(
        "  Total suggestions: {}\n",
        analysis.summary.total_suggestions
    ));

    if !analysis.summary.by_type.is_empty() {
        output.push_str("  By type:\n");
        for (t, count) in &analysis.summary.by_type {
            output.push_str(&format!("    {}: {}\n", t, count));
        }
    }

    output
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_explicit_assert_precondition_python() {
        let source = r#"
def divide(a, b):
    assert b != 0, "Division by zero"
    return a / b
"#;
        let analyzer = InvariantAnalyzer::new(source, "python");
        let result = analyzer.analyze_function("divide").unwrap();

        assert!(!result.preconditions.is_empty());
        let pre = &result.preconditions[0];
        assert_eq!(pre.invariant_type, InvariantType::Precondition);
        assert!(pre.expression.contains("b != 0"));
        assert_eq!(pre.confidence, 1.0);
        assert!(pre.is_explicit);
    }

    #[test]
    fn test_guard_clause_precondition_python() {
        let source = r#"
def process(data):
    if data is None:
        raise ValueError("data cannot be None")
    return data.process()
"#;
        let analyzer = InvariantAnalyzer::new(source, "python");
        let result = analyzer.analyze_function("process").unwrap();

        assert!(!result.preconditions.is_empty());
        let pre = &result.preconditions[0];
        assert!(pre.expression.contains("is not None"));
        assert_eq!(pre.confidence, 0.9);
        assert!(!pre.is_explicit);
    }

    #[test]
    fn test_type_check_precondition_python() {
        let source = r#"
def validate(x):
    if not isinstance(x, int):
        raise TypeError("x must be int")
    return x * 2
"#;
        let analyzer = InvariantAnalyzer::new(source, "python");
        let result = analyzer.analyze_function("validate").unwrap();

        // Should find isinstance check
        let has_type_check = result
            .preconditions
            .iter()
            .any(|p| p.evidence.iter().any(|e| e.kind == EvidenceKind::TypeCheck));
        assert!(has_type_check || !result.preconditions.is_empty());
    }

    #[test]
    fn test_postcondition_from_return_assert() {
        let source = r#"
def compute(x):
    result = x * 2
    assert result >= 0
    return result
"#;
        let analyzer = InvariantAnalyzer::new(source, "python");
        let result = analyzer.analyze_function("compute").unwrap();

        assert!(!result.postconditions.is_empty());
        let post = &result.postconditions[0];
        assert!(post.expression.contains("result >= 0"));
    }

    #[test]
    fn test_loop_invariant_unmodified_variable() {
        let source = r#"
def sum_list(items):
    total = 0
    n = len(items)
    for i in range(n):
        total += items[i]
    return total
"#;
        let analyzer = InvariantAnalyzer::new(source, "python");
        let result = analyzer.analyze_function("sum_list").unwrap();

        // Should find loop invariant for n (not modified in loop)
        assert!(!result.loop_invariants.is_empty());
    }

    #[test]
    fn test_loop_bounds_python() {
        let source = r#"
def process_range(n):
    for i in range(0, n):
        print(i)
"#;
        let analyzer = InvariantAnalyzer::new(source, "python");
        let result = analyzer.analyze_function("process_range").unwrap();

        // Check loop details have bounds
        assert!(!result.loop_details.is_empty());
        for (_line, info) in &result.loop_details {
            assert!(info.bounds.is_some());
            let bounds = info.bounds.as_ref().unwrap();
            assert_eq!(bounds.lower.as_deref(), Some("0"));
            assert!(bounds.upper.is_some());
        }
    }

    #[test]
    fn test_rust_assert_macro() {
        let source = r#"
fn divide(a: i32, b: i32) -> i32 {
    assert!(b != 0, "Division by zero");
    a / b
}
"#;
        let analyzer = InvariantAnalyzer::new(source, "rust");
        let result = analyzer.analyze_function("divide").unwrap();

        assert!(!result.preconditions.is_empty());
        let pre = &result.preconditions[0];
        assert!(pre.expression.contains("b != 0"));
        assert!(pre.is_explicit);
    }

    #[test]
    fn test_go_nil_check() {
        let source = r#"
func process(data *Data) error {
    if data == nil {
        return errors.New("data is nil")
    }
    return nil
}
"#;
        let analyzer = InvariantAnalyzer::new(source, "go");
        let result = analyzer.analyze_function("process").unwrap();

        // Should infer precondition from nil check
        assert!(!result.preconditions.is_empty());
    }

    #[test]
    fn test_typescript_throw_guard() {
        let source = r#"
function validate(x: number): number {
    if (x < 0) {
        throw new Error("x must be non-negative");
    }
    return x * 2;
}
"#;
        let analyzer = InvariantAnalyzer::new(source, "typescript");
        let result = analyzer.analyze_function("validate").unwrap();

        assert!(!result.preconditions.is_empty());
        let pre = &result.preconditions[0];
        assert!(pre.expression.contains(">=") || pre.expression.contains(">= 0"));
    }

    #[test]
    fn test_suggestion_generation() {
        let source = r#"
def risky_divide(a, b):
    return a / b
"#;
        let analyzer = InvariantAnalyzer::new(source, "python");
        let result = analyzer.analyze_function("risky_divide").unwrap();

        // Should suggest checking b != 0
        assert!(!result.suggested_assertions.is_empty());
        let has_div_suggestion = result
            .suggested_assertions
            .iter()
            .any(|s| s.assertion.contains("!= 0") || s.assertion.contains("Division"));
        assert!(has_div_suggestion);
    }

    #[test]
    fn test_negate_condition() {
        assert_eq!(negate_condition("x is None", "python"), "x is not None");
        assert_eq!(negate_condition("x is not None", "python"), "x is None");
        assert_eq!(negate_condition("x == 0", "python"), "x != 0");
        assert_eq!(negate_condition("x < 0", "python"), "x >= 0");
        assert_eq!(negate_condition("not valid", "python"), "valid");
        assert_eq!(negate_condition("!valid", "javascript"), "valid");
    }

    #[test]
    fn test_extract_variables() {
        let vars = extract_variables_from_expr("x > 0 and y < 10");
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));
        assert!(!vars.contains(&"and".to_string()));
    }

    #[test]
    fn test_parse_python_range() {
        let bounds = parse_python_range("range(10)").unwrap();
        assert_eq!(bounds.lower.as_deref(), Some("0"));
        assert_eq!(bounds.upper.as_deref(), Some("10"));
        assert!(!bounds.inclusive);

        let bounds2 = parse_python_range("range(1, n)").unwrap();
        assert_eq!(bounds2.lower.as_deref(), Some("1"));
        assert_eq!(bounds2.upper.as_deref(), Some("n"));
    }

    #[test]
    fn test_parse_rust_range() {
        let bounds = parse_rust_range("0..n").unwrap();
        assert_eq!(bounds.lower.as_deref(), Some("0"));
        assert_eq!(bounds.upper.as_deref(), Some("n"));
        assert!(!bounds.inclusive);

        let bounds2 = parse_rust_range("0..=n").unwrap();
        assert_eq!(bounds2.lower.as_deref(), Some("0"));
        assert_eq!(bounds2.upper.as_deref(), Some("n"));
        assert!(bounds2.inclusive);
    }

    #[test]
    fn test_metrics_calculation() {
        let source = r#"
def example(x, y):
    assert x is not None
    assert y > 0
    for i in range(10):
        x += i
    result = x + y
    assert result >= 0
    return result
"#;
        let analyzer = InvariantAnalyzer::new(source, "python");
        let result = analyzer.analyze_function("example").unwrap();

        assert!(result.metrics.explicit_assertions > 0);
        assert!(result.metrics.loop_invariants_count > 0);
    }

    #[test]
    fn test_find_modified_variables_python() {
        let analyzer = InvariantAnalyzer::new("", "python");
        let block = vec!["x = 1", "y += 2", "z = z + 1"];
        let modified = analyzer.find_modified_variables(&block);

        assert!(modified.contains("x"));
        assert!(modified.contains("y"));
        assert!(modified.contains("z"));
    }

    #[test]
    fn test_monotonic_detection() {
        let analyzer = InvariantAnalyzer::new("", "python");
        let block = vec!["for i in range(10):", "    counter += 1", "    total += x"];
        let modified: HashSet<String> =
            ["counter", "total"].iter().map(|s| s.to_string()).collect();
        let monotonic = analyzer.detect_monotonic_variables(&block, &modified);

        assert!(!monotonic.is_empty());
        let counter_mono = monotonic.iter().find(|m| m.name == "counter");
        assert!(counter_mono.is_some());
        assert_eq!(
            counter_mono.unwrap().direction,
            MonotonicDirection::Increasing
        );
    }

    #[test]
    fn test_output_format_json() {
        let analysis = FileInvariantAnalysis {
            file: "test.py".to_string(),
            language: "python".to_string(),
            functions: vec![],
            class_invariants: HashMap::new(),
            summary: InvariantSummary::default(),
        };

        let json = format_json(&analysis).unwrap();
        assert!(json.contains("test.py"));
        assert!(json.contains("python"));
    }

    #[test]
    fn test_output_format_text() {
        let analysis = FileInvariantAnalysis {
            file: "test.py".to_string(),
            language: "python".to_string(),
            functions: vec![FunctionInvariantAnalysis {
                function: "example".to_string(),
                file: "test.py".to_string(),
                start_line: 1,
                end_line: 5,
                preconditions: vec![Invariant::new(
                    InvariantType::Precondition,
                    "x > 0".to_string(),
                    Location::new(2),
                    0.9,
                )],
                postconditions: vec![],
                loop_invariants: HashMap::new(),
                loop_details: HashMap::new(),
                suggested_assertions: vec![],
                metrics: InvariantMetrics::default(),
            }],
            class_invariants: HashMap::new(),
            summary: InvariantSummary {
                functions_analyzed: 1,
                total_invariants: 1,
                by_type: [("precondition".to_string(), 1)].into_iter().collect(),
                average_confidence: 0.9,
                total_suggestions: 0,
            },
        };

        let text = format_text(&analysis);
        assert!(text.contains("test.py"));
        assert!(text.contains("example"));
        assert!(text.contains("x > 0"));
        assert!(text.contains("Preconditions"));
    }
}
