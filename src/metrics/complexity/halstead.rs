//! Halstead complexity metrics calculation.
//!
//! Halstead metrics measure software complexity based on operator and operand counts.
//! Originally proposed by Maurice Halstead in 1977, these metrics provide insights
//! into code complexity, development effort, and potential bug density.
//!
//! # Metrics Overview
//!
//! ## Base Counts
//! - **n1**: Number of distinct operators
//! - **n2**: Number of distinct operands
//! - **N1**: Total number of operators
//! - **N2**: Total number of operands
//!
//! ## Derived Metrics
//! - **Vocabulary (n)**: n = n1 + n2
//! - **Length (N)**: N = N1 + N2
//! - **Calculated Length (N^)**: N^ = n1 * log2(n1) + n2 * log2(n2)
//! - **Volume (V)**: V = N * log2(n) - program size in bits
//! - **Difficulty (D)**: D = (n1/2) * (N2/n2) - error-proneness
//! - **Effort (E)**: E = D * V - mental effort to develop
//! - **Time (T)**: T = E / 18 seconds - development time estimate
//! - **Bugs (B)**: B = V / 3000 - estimated bug count
//!
//! # Operator/Operand Classification
//!
//! ## Operators
//! - Arithmetic: `+`, `-`, `*`, `/`, `%`, `**`, `//`
//! - Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`
//! - Logical: `&&`, `||`, `!`, `and`, `or`, `not`
//! - Assignment: `=`, `+=`, `-=`, etc.
//! - Structural: `()`, `[]`, `{}`, `.`, `,`, `;`, `:`
//! - Language-specific: `->`, `=>`, `::`, `?`, `?:`, `?.`, `??`
//! - Keywords (control flow): `if`, `else`, `while`, `for`, `return`, etc.
//!
//! ## Operands
//! - Identifiers (variables, functions, types)
//! - Literals (numbers, strings, booleans)
//! - Value keywords: `true`, `false`, `null`, `None`, `nil`

use std::collections::{HashMap, HashSet};
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

/// Halstead complexity metrics for a single function or file.
///
/// These metrics quantify the complexity of code based on the vocabulary
/// of operators and operands used.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HalsteadMetrics {
    /// Number of distinct operators (n1)
    pub distinct_operators: u32,
    /// Number of distinct operands (n2)
    pub distinct_operands: u32,
    /// Total number of operators (N1)
    pub total_operators: u32,
    /// Total number of operands (N2)
    pub total_operands: u32,
    /// Vocabulary: n = n1 + n2
    pub vocabulary: u32,
    /// Program length: N = N1 + N2
    pub length: u32,
    /// Calculated (estimated) length: N^ = n1 * log2(n1) + n2 * log2(n2)
    pub calculated_length: f64,
    /// Volume: V = N * log2(n) - size in bits
    pub volume: f64,
    /// Difficulty: D = (n1/2) * (N2/n2) - error-proneness
    pub difficulty: f64,
    /// Effort: E = D * V - mental effort
    pub effort: f64,
    /// Time to program: T = E / 18 seconds
    pub time_seconds: f64,
    /// Estimated bugs: B = V / 3000
    pub bugs: f64,
}

impl Default for HalsteadMetrics {
    fn default() -> Self {
        Self {
            distinct_operators: 0,
            distinct_operands: 0,
            total_operators: 0,
            total_operands: 0,
            vocabulary: 0,
            length: 0,
            calculated_length: 0.0,
            volume: 0.0,
            difficulty: 0.0,
            effort: 0.0,
            time_seconds: 0.0,
            bugs: 0.0,
        }
    }
}

impl HalsteadMetrics {
    /// Calculate derived metrics from base counts.
    ///
    /// Given n1, n2, N1, N2, computes all derived Halstead metrics.
    /// Handles edge cases (zeros) to avoid division by zero or log(0).
    #[must_use]
    pub fn from_counts(n1: u32, n2: u32, total_n1: u32, total_n2: u32) -> Self {
        let vocabulary = n1 + n2;
        let length = total_n1 + total_n2;

        // Calculate estimated length: N^ = n1 * log2(n1) + n2 * log2(n2)
        let calculated_length = if n1 > 0 && n2 > 0 {
            f64::from(n1) * f64::from(n1).log2() + f64::from(n2) * f64::from(n2).log2()
        } else {
            0.0
        };

        // Volume: V = N * log2(n)
        let volume = if vocabulary > 0 {
            f64::from(length) * f64::from(vocabulary).log2()
        } else {
            0.0
        };

        // Difficulty: D = (n1/2) * (N2/n2)
        let difficulty = if n2 > 0 {
            (f64::from(n1) / 2.0) * (f64::from(total_n2) / f64::from(n2))
        } else {
            0.0
        };

        // Effort: E = D * V
        let effort = difficulty * volume;

        // Time: T = E / 18 (Stroud number - elementary mental discriminations per second)
        let time_seconds = effort / 18.0;

        // Bugs: B = V / 3000 (empirically derived constant)
        let bugs = volume / 3000.0;

        Self {
            distinct_operators: n1,
            distinct_operands: n2,
            total_operators: total_n1,
            total_operands: total_n2,
            vocabulary,
            length,
            calculated_length,
            volume,
            difficulty,
            effort,
            time_seconds,
            bugs,
        }
    }

    /// Get a quality assessment based on metrics.
    #[must_use]
    pub fn quality_assessment(&self) -> HalsteadQuality {
        // Volume thresholds (based on industry experience)
        let volume_level = if self.volume < 100.0 {
            QualityLevel::Low
        } else if self.volume < 1000.0 {
            QualityLevel::Medium
        } else if self.volume < 8000.0 {
            QualityLevel::High
        } else {
            QualityLevel::VeryHigh
        };

        // Difficulty thresholds
        let difficulty_level = if self.difficulty < 5.0 {
            QualityLevel::Low
        } else if self.difficulty < 15.0 {
            QualityLevel::Medium
        } else if self.difficulty < 30.0 {
            QualityLevel::High
        } else {
            QualityLevel::VeryHigh
        };

        HalsteadQuality {
            volume_level,
            difficulty_level,
        }
    }
}

/// Quality level based on Halstead metrics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum QualityLevel {
    /// Low complexity, easy to understand
    Low,
    /// Medium complexity, moderate effort
    Medium,
    /// High complexity, significant effort
    High,
    /// Very high complexity, consider refactoring
    VeryHigh,
}

impl std::fmt::Display for QualityLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "low"),
            Self::Medium => write!(f, "medium"),
            Self::High => write!(f, "high"),
            Self::VeryHigh => write!(f, "very_high"),
        }
    }
}

/// Quality assessment based on Halstead metrics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HalsteadQuality {
    /// Volume-based complexity level
    pub volume_level: QualityLevel,
    /// Difficulty-based complexity level
    pub difficulty_level: QualityLevel,
}

/// Halstead analysis result for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionHalstead {
    /// Function name (may include class prefix for methods)
    pub function_name: String,
    /// File path containing the function
    pub file: PathBuf,
    /// Starting line number (1-indexed)
    pub line: usize,
    /// Ending line number (1-indexed)
    pub end_line: usize,
    /// Halstead metrics
    pub metrics: HalsteadMetrics,
    /// Quality assessment
    pub quality: HalsteadQuality,
    /// Distinct operators found
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operators: Option<Vec<String>>,
    /// Distinct operands found
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operands: Option<Vec<String>>,
}

/// Aggregate Halstead statistics for a project.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HalsteadStats {
    /// Total functions analyzed
    pub total_functions: usize,
    /// Average volume
    pub avg_volume: f64,
    /// Maximum volume
    pub max_volume: f64,
    /// Average difficulty
    pub avg_difficulty: f64,
    /// Maximum difficulty
    pub max_difficulty: f64,
    /// Total estimated bugs across all functions
    pub total_bugs: f64,
    /// Total estimated development time (seconds)
    pub total_time_seconds: f64,
}

impl HalsteadStats {
    /// Calculate statistics from a list of function results.
    fn from_functions(functions: &[FunctionHalstead]) -> Self {
        if functions.is_empty() {
            return Self {
                total_functions: 0,
                avg_volume: 0.0,
                max_volume: 0.0,
                avg_difficulty: 0.0,
                max_difficulty: 0.0,
                total_bugs: 0.0,
                total_time_seconds: 0.0,
            };
        }

        let total = functions.len();
        let volumes: Vec<f64> = functions.iter().map(|f| f.metrics.volume).collect();
        let difficulties: Vec<f64> = functions.iter().map(|f| f.metrics.difficulty).collect();
        let bugs: f64 = functions.iter().map(|f| f.metrics.bugs).sum();
        let time: f64 = functions.iter().map(|f| f.metrics.time_seconds).sum();

        Self {
            total_functions: total,
            avg_volume: volumes.iter().sum::<f64>() / total as f64,
            max_volume: volumes.iter().cloned().fold(0.0, f64::max),
            avg_difficulty: difficulties.iter().sum::<f64>() / total as f64,
            max_difficulty: difficulties.iter().cloned().fold(0.0, f64::max),
            total_bugs: bugs,
            total_time_seconds: time,
        }
    }
}

/// Complete Halstead analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HalsteadAnalysis {
    /// Path that was analyzed
    pub path: PathBuf,
    /// Language filter applied
    pub language: Option<String>,
    /// Individual function results
    pub functions: Vec<FunctionHalstead>,
    /// Aggregate statistics
    pub stats: HalsteadStats,
    /// Analysis errors encountered
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<HalsteadError>,
}

/// Error encountered during Halstead analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HalsteadError {
    /// File path where error occurred
    pub file: PathBuf,
    /// Error message
    pub message: String,
}

// =============================================================================
// OPERATOR/OPERAND DEFINITIONS
// =============================================================================

/// Language-agnostic operator categories.
///
/// These operators are common across most programming languages.
const COMMON_OPERATORS: &[&str] = &[
    // Arithmetic
    "+", "-", "*", "/", "%",
    // Comparison
    "==", "!=", "<", ">", "<=", ">=",
    // Assignment
    "=", "+=", "-=", "*=", "/=", "%=",
    // Bitwise
    "&", "|", "^", "~", "<<", ">>",
    "&=", "|=", "^=", "<<=", ">>=",
    // Logical (symbols)
    "&&", "||", "!",
    // Member access
    ".", ",", ";",
    // Brackets (counted as operators)
    "(", ")", "[", "]", "{", "}",
    // Other common
    "?", ":",
];

/// Python-specific operators.
const PYTHON_OPERATORS: &[&str] = &[
    // Python-specific
    "**", "//", "@", "->",
    "**=", "//=", "@=",
    // Python keywords as operators
    "and", "or", "not", "in", "is",
    "if", "else", "elif", "while", "for",
    "try", "except", "finally", "raise",
    "with", "as", "from", "import",
    "def", "class", "return", "yield",
    "break", "continue", "pass",
    "lambda", "assert", "del",
    "global", "nonlocal", "async", "await",
];

/// Python value keywords (operands).
const PYTHON_VALUE_KEYWORDS: &[&str] = &["True", "False", "None"];

/// TypeScript/JavaScript-specific operators.
const TYPESCRIPT_OPERATORS: &[&str] = &[
    // Arrow and optional chaining
    "=>", "?.", "??", "??=",
    // Type operators
    "as", "typeof", "instanceof", "keyof", "readonly",
    // Increment/decrement
    "++", "--",
    // Ternary (already have ? and :)
    // Keywords as operators
    "if", "else", "while", "for", "do",
    "switch", "case", "default",
    "try", "catch", "finally", "throw",
    "return", "break", "continue",
    "function", "class", "new", "delete",
    "void", "in", "of",
    "import", "export", "from",
    "let", "const", "var",
    "async", "await", "yield",
    "type", "interface", "enum", "namespace",
    "extends", "implements",
    // Spread/rest
    "...",
];

/// TypeScript/JavaScript value keywords (operands).
const TYPESCRIPT_VALUE_KEYWORDS: &[&str] = &["true", "false", "null", "undefined", "this", "super"];

/// Rust-specific operators.
const RUST_OPERATORS: &[&str] = &[
    // Rust-specific
    "::", "->", "=>", "..", "..=",
    "?",
    // Reference operators
    "&mut",
    // Keywords as operators
    "if", "else", "while", "for", "loop",
    "match", "return", "break", "continue",
    "fn", "struct", "enum", "impl", "trait",
    "pub", "mod", "use", "crate", "super",
    "let", "mut", "ref", "const", "static",
    "unsafe", "async", "await", "move",
    "where", "type", "as", "in", "dyn",
    "box", "yield",
];

/// Rust value keywords (operands).
const RUST_VALUE_KEYWORDS: &[&str] = &["true", "false", "self", "Self"];

/// Go-specific operators.
const GO_OPERATORS: &[&str] = &[
    // Go-specific
    ":=", "<-", "...",
    // Keywords as operators
    "if", "else", "for", "range",
    "switch", "case", "default", "select",
    "func", "return", "break", "continue",
    "go", "defer", "chan",
    "type", "struct", "interface",
    "package", "import", "const", "var",
    "fallthrough", "goto", "map",
];

/// Go value keywords (operands).
const GO_VALUE_KEYWORDS: &[&str] = &["true", "false", "nil", "iota"];

/// Java-specific operators.
const JAVA_OPERATORS: &[&str] = &[
    // Java-specific
    "->", "::",
    "++", "--",
    "instanceof",
    // Keywords as operators
    "if", "else", "while", "for", "do",
    "switch", "case", "default",
    "try", "catch", "finally", "throw", "throws",
    "return", "break", "continue",
    "class", "interface", "enum", "extends", "implements",
    "new", "void",
    "public", "private", "protected", "static", "final",
    "abstract", "synchronized", "volatile", "transient",
    "import", "package",
    "assert", "native", "strictfp",
];

/// Java value keywords (operands).
const JAVA_VALUE_KEYWORDS: &[&str] = &["true", "false", "null", "this", "super"];

/// C/C++-specific operators.
const C_CPP_OPERATORS: &[&str] = &[
    // C/C++ specific
    "->", "::", ".*", "->*",
    "++", "--",
    "sizeof", "alignof",
    // Keywords as operators
    "if", "else", "while", "for", "do",
    "switch", "case", "default",
    "return", "break", "continue", "goto",
    "struct", "union", "enum", "class", "typedef",
    "const", "volatile", "static", "extern", "register",
    "inline", "virtual", "explicit", "friend",
    "public", "private", "protected",
    "new", "delete", "throw", "try", "catch",
    "namespace", "using", "template", "typename",
    "auto", "decltype", "constexpr", "noexcept",
];

/// C/C++ value keywords (operands).
const C_CPP_VALUE_KEYWORDS: &[&str] = &["true", "false", "nullptr", "NULL", "this"];

// =============================================================================
// TOKEN EXTRACTION
// =============================================================================

/// Token collector that classifies tokens as operators or operands.
struct TokenCollector {
    operators: HashMap<String, u32>,
    operands: HashMap<String, u32>,
    operator_set: HashSet<&'static str>,
    value_keywords: HashSet<&'static str>,
    /// Language name for potential future use in language-specific tokenization
    #[allow(dead_code)]
    language: String,
}

impl TokenCollector {
    /// Create a new token collector for a specific language.
    fn new(language: &str) -> Self {
        let mut operator_set: HashSet<&'static str> = COMMON_OPERATORS.iter().copied().collect();
        let mut value_keywords: HashSet<&'static str> = HashSet::new();

        match language.to_lowercase().as_str() {
            "python" => {
                operator_set.extend(PYTHON_OPERATORS.iter().copied());
                value_keywords.extend(PYTHON_VALUE_KEYWORDS.iter().copied());
            }
            "typescript" | "javascript" | "tsx" | "jsx" => {
                operator_set.extend(TYPESCRIPT_OPERATORS.iter().copied());
                value_keywords.extend(TYPESCRIPT_VALUE_KEYWORDS.iter().copied());
            }
            "rust" => {
                operator_set.extend(RUST_OPERATORS.iter().copied());
                value_keywords.extend(RUST_VALUE_KEYWORDS.iter().copied());
            }
            "go" => {
                operator_set.extend(GO_OPERATORS.iter().copied());
                value_keywords.extend(GO_VALUE_KEYWORDS.iter().copied());
            }
            "java" => {
                operator_set.extend(JAVA_OPERATORS.iter().copied());
                value_keywords.extend(JAVA_VALUE_KEYWORDS.iter().copied());
            }
            "c" | "cpp" | "c++" => {
                operator_set.extend(C_CPP_OPERATORS.iter().copied());
                value_keywords.extend(C_CPP_VALUE_KEYWORDS.iter().copied());
            }
            _ => {
                // Default to common + Python-style for unknown languages
                operator_set.extend(PYTHON_OPERATORS.iter().copied());
                value_keywords.extend(PYTHON_VALUE_KEYWORDS.iter().copied());
            }
        }

        Self {
            operators: HashMap::new(),
            operands: HashMap::new(),
            operator_set,
            value_keywords,
            language: language.to_lowercase(),
        }
    }

    /// Process a tree-sitter node and collect tokens.
    fn collect_from_node(&mut self, node: Node, source: &[u8]) {
        self.visit_node(node, source);
    }

    /// Recursively visit nodes and classify tokens.
    fn visit_node(&mut self, node: Node, source: &[u8]) {
        let kind = node.kind();
        let text = node.utf8_text(source).unwrap_or("");

        // Classify based on node kind and text
        self.classify_node(kind, text);

        // Recurse into children
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.visit_node(child, source);
        }
    }

    /// Classify a node as operator or operand based on its kind and text.
    fn classify_node(&mut self, kind: &str, text: &str) {
        // Skip empty or whitespace-only text
        if text.trim().is_empty() {
            return;
        }

        // Check if it's explicitly an operator
        if self.is_operator_kind(kind) || self.operator_set.contains(text) {
            self.add_operator(text);
            return;
        }

        // Check if it's an operand
        if self.is_operand_kind(kind) {
            self.add_operand(text);
            return;
        }

        // Value keywords are operands
        if self.value_keywords.contains(text) {
            self.add_operand(text);
            return;
        }

        // Keywords that are in operator set are operators
        if self.operator_set.contains(text) {
            self.add_operator(text);
        }
    }

    /// Check if a node kind represents an operator.
    fn is_operator_kind(&self, kind: &str) -> bool {
        matches!(
            kind,
            // Binary operators
            "binary_operator"
                | "unary_operator"
                | "comparison_operator"
                | "boolean_operator"
                | "augmented_assignment"
                | "assignment"
                | "assignment_expression"
                // Specific operator tokens
                | "+"
                | "-"
                | "*"
                | "/"
                | "%"
                | "**"
                | "//"
                | "=="
                | "!="
                | "<"
                | ">"
                | "<="
                | ">="
                | "&&"
                | "||"
                | "&"
                | "|"
                | "^"
                | "~"
                | "<<"
                | ">>"
                | "="
                | "+="
                | "-="
                | "*="
                | "/="
                | "!"
                | "?"
                // Punctuation as operators
                | "("
                | ")"
                | "["
                | "]"
                | "{"
                | "}"
                | "."
                | ","
                | ";"
                | ":"
                | "->"
                | "=>"
                | "::"
                | "?."
                | "??"
                // Language-specific operator nodes
                | "spread_element"
                | "rest_pattern"
                | "arrow_function"
                | "ternary_expression"
                | "conditional_expression"
        )
    }

    /// Check if a node kind represents an operand.
    fn is_operand_kind(&self, kind: &str) -> bool {
        matches!(
            kind,
            // Identifiers
            "identifier"
                | "field_identifier"
                | "property_identifier"
                | "type_identifier"
                | "shorthand_property_identifier"
                | "shorthand_field_identifier"
                // Literals
                | "number"
                | "integer"
                | "float"
                | "string"
                | "string_literal"
                | "raw_string_literal"
                | "char_literal"
                | "boolean"
                | "true"
                | "false"
                | "none"
                | "null"
                | "nil"
                // Composite literals
                | "template_string"
                | "regex"
                | "regex_literal"
                // Python specific
                | "attribute"
                // Rust specific
                | "self"
                | "crate"
                | "metavariable"
                // TypeScript specific
                | "this"
                | "super"
                | "undefined"
        )
    }

    /// Add an operator occurrence.
    fn add_operator(&mut self, text: &str) {
        let normalized = self.normalize_token(text);
        if !normalized.is_empty() {
            *self.operators.entry(normalized).or_insert(0) += 1;
        }
    }

    /// Add an operand occurrence.
    fn add_operand(&mut self, text: &str) {
        let normalized = self.normalize_token(text);
        if !normalized.is_empty() {
            *self.operands.entry(normalized).or_insert(0) += 1;
        }
    }

    /// Normalize a token for counting.
    fn normalize_token(&self, text: &str) -> String {
        let trimmed = text.trim();

        // Normalize string literals to a canonical form
        if (trimmed.starts_with('"') && trimmed.ends_with('"'))
            || (trimmed.starts_with('\'') && trimmed.ends_with('\''))
            || (trimmed.starts_with('`') && trimmed.ends_with('`'))
        {
            // Keep the actual string content for operand uniqueness
            return trimmed.to_string();
        }

        trimmed.to_string()
    }

    /// Compute final Halstead metrics.
    fn compute_metrics(&self) -> HalsteadMetrics {
        let n1 = self.operators.len() as u32;
        let n2 = self.operands.len() as u32;
        let total_n1: u32 = self.operators.values().sum();
        let total_n2: u32 = self.operands.values().sum();

        HalsteadMetrics::from_counts(n1, n2, total_n1, total_n2)
    }

    /// Get distinct operators.
    fn distinct_operators(&self) -> Vec<String> {
        let mut ops: Vec<String> = self.operators.keys().cloned().collect();
        ops.sort();
        ops
    }

    /// Get distinct operands.
    fn distinct_operands(&self) -> Vec<String> {
        let mut ops: Vec<String> = self.operands.keys().cloned().collect();
        ops.sort();
        ops
    }
}

// =============================================================================
// ANALYSIS FUNCTIONS
// =============================================================================

/// Analyze Halstead metrics for a project or directory.
///
/// Scans all source files, extracts functions, and calculates Halstead
/// metrics for each function.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `language` - Optional language filter
/// * `include_tokens` - Whether to include operator/operand lists in output
///
/// # Returns
///
/// Complete Halstead analysis with function metrics and statistics.
pub fn analyze_halstead(
    path: impl AsRef<Path>,
    language: Option<&str>,
    include_tokens: bool,
) -> Result<HalsteadAnalysis> {
    let path = path.as_ref();

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Path not found: {}", path.display()),
        )));
    }

    if path.is_file() {
        return analyze_file_halstead(path, include_tokens);
    }

    // Directory analysis
    let path_str = path.to_str().ok_or_else(|| {
        BrrrError::InvalidArgument("Invalid path encoding".to_string())
    })?;

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

    debug!("Analyzing {} files for Halstead metrics", scan_result.files.len());

    // Analyze files in parallel
    let results: Vec<(Vec<FunctionHalstead>, Vec<HalsteadError>)> = scan_result
        .files
        .par_iter()
        .map(|file| analyze_file_functions_halstead(file, include_tokens))
        .collect();

    // Aggregate results
    let mut all_functions = Vec::new();
    let mut all_errors = Vec::new();

    for (functions, errors) in results {
        all_functions.extend(functions);
        all_errors.extend(errors);
    }

    let stats = HalsteadStats::from_functions(&all_functions);

    Ok(HalsteadAnalysis {
        path: path.to_path_buf(),
        language: language.map(String::from),
        functions: all_functions,
        stats,
        errors: all_errors,
    })
}

/// Analyze Halstead metrics for a single file.
pub fn analyze_file_halstead(
    file: impl AsRef<Path>,
    include_tokens: bool,
) -> Result<HalsteadAnalysis> {
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

    let (functions, errors) = analyze_file_functions_halstead(file, include_tokens);
    let stats = HalsteadStats::from_functions(&functions);

    // Detect language
    let registry = LanguageRegistry::global();
    let language = registry
        .detect_language(file)
        .map(|l| l.name().to_string());

    Ok(HalsteadAnalysis {
        path: file.to_path_buf(),
        language,
        functions,
        stats,
        errors,
    })
}

/// Analyze a single function and compute Halstead metrics.
fn analyze_function_halstead(
    file: &Path,
    function_name: &str,
    start_line: usize,
    end_line: usize,
    include_tokens: bool,
) -> Result<FunctionHalstead> {
    let source = std::fs::read_to_string(file)?;
    let registry = LanguageRegistry::global();

    let lang = registry
        .detect_language(file)
        .ok_or_else(|| BrrrError::UnsupportedLanguage(
            file.extension()
                .and_then(|e| e.to_str())
                .unwrap_or("unknown")
                .to_string()
        ))?;

    let mut parser = lang.parser()?;
    let tree = parser.parse(&source, None).ok_or_else(|| {
        BrrrError::Parse {
            file: file.display().to_string(),
            message: "Failed to parse file".to_string(),
        }
    })?;

    // Find the function node by line range
    let function_node = find_function_node(&tree, start_line, end_line);

    let node_to_analyze = function_node.unwrap_or_else(|| tree.root_node());

    // Collect tokens
    let mut collector = TokenCollector::new(lang.name());
    collector.collect_from_node(node_to_analyze, source.as_bytes());

    let metrics = collector.compute_metrics();
    let quality = metrics.quality_assessment();

    Ok(FunctionHalstead {
        function_name: function_name.to_string(),
        file: file.to_path_buf(),
        line: start_line,
        end_line,
        metrics,
        quality,
        operators: if include_tokens {
            Some(collector.distinct_operators())
        } else {
            None
        },
        operands: if include_tokens {
            Some(collector.distinct_operands())
        } else {
            None
        },
    })
}

/// Find a function node by line range.
fn find_function_node(tree: &Tree, start_line: usize, end_line: usize) -> Option<Node<'_>> {
    let root = tree.root_node();
    find_function_node_recursive(root, start_line, end_line)
}

/// Recursively search for a function node matching the line range.
fn find_function_node_recursive(node: Node<'_>, start_line: usize, end_line: usize) -> Option<Node<'_>> {
    let node_start = node.start_position().row + 1; // 1-indexed
    let node_end = node.end_position().row + 1;

    // Check if this node matches
    if is_function_node(&node) && node_start == start_line && node_end >= end_line {
        return Some(node);
    }

    // Search children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(found) = find_function_node_recursive(child, start_line, end_line) {
            return Some(found);
        }
    }

    None
}

/// Check if a node represents a function definition.
fn is_function_node(node: &Node) -> bool {
    matches!(
        node.kind(),
        "function_definition"
            | "function_declaration"
            | "method_definition"
            | "function_item"
            | "function"
            | "method"
            | "arrow_function"
            | "function_expression"
            | "method_declaration"
    )
}

/// Analyze all functions in a file.
fn analyze_file_functions_halstead(
    file: &Path,
    include_tokens: bool,
) -> (Vec<FunctionHalstead>, Vec<HalsteadError>) {
    let mut results = Vec::new();
    let mut errors = Vec::new();

    // Extract module info to get function list
    let module = match AstExtractor::extract_file(file) {
        Ok(m) => m,
        Err(e) => {
            errors.push(HalsteadError {
                file: file.to_path_buf(),
                message: format!("Failed to parse file: {}", e),
            });
            return (results, errors);
        }
    };

    // Analyze top-level functions
    for func in &module.functions {
        let start_line = func.line_number;
        let end_line = func.end_line_number.unwrap_or(start_line);
        match analyze_function_halstead(file, &func.name, start_line, end_line, include_tokens) {
            Ok(halstead) => results.push(halstead),
            Err(e) => {
                debug!("Failed to analyze function {}: {}", func.name, e);
                errors.push(HalsteadError {
                    file: file.to_path_buf(),
                    message: format!("Failed to analyze {}: {}", func.name, e),
                });
            }
        }
    }

    // Analyze class methods
    for class in &module.classes {
        for method in &class.methods {
            let qualified_name = format!("{}.{}", class.name, method.name);
            let start_line = method.line_number;
            let end_line = method.end_line_number.unwrap_or(start_line);
            match analyze_function_halstead(file, &qualified_name, start_line, end_line, include_tokens) {
                Ok(halstead) => results.push(halstead),
                Err(e) => {
                    debug!("Failed to analyze method {}: {}", qualified_name, e);
                    errors.push(HalsteadError {
                        file: file.to_path_buf(),
                        message: format!("Failed to analyze {}: {}", qualified_name, e),
                    });
                }
            }
        }
    }

    (results, errors)
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
    fn test_halstead_from_counts() {
        // Simple example: n1=5, n2=4, N1=10, N2=8
        let metrics = HalsteadMetrics::from_counts(5, 4, 10, 8);

        assert_eq!(metrics.distinct_operators, 5);
        assert_eq!(metrics.distinct_operands, 4);
        assert_eq!(metrics.total_operators, 10);
        assert_eq!(metrics.total_operands, 8);
        assert_eq!(metrics.vocabulary, 9);
        assert_eq!(metrics.length, 18);

        // Volume = 18 * log2(9) = 18 * 3.17 = 57.0+
        assert!(metrics.volume > 50.0 && metrics.volume < 60.0);

        // Difficulty = (5/2) * (8/4) = 2.5 * 2 = 5.0
        assert!((metrics.difficulty - 5.0).abs() < 0.1);
    }

    #[test]
    fn test_halstead_zero_counts() {
        let metrics = HalsteadMetrics::from_counts(0, 0, 0, 0);

        assert_eq!(metrics.vocabulary, 0);
        assert_eq!(metrics.length, 0);
        assert_eq!(metrics.volume, 0.0);
        assert_eq!(metrics.difficulty, 0.0);
        assert_eq!(metrics.effort, 0.0);
    }

    #[test]
    fn test_quality_assessment() {
        // Low complexity
        let low = HalsteadMetrics::from_counts(3, 2, 5, 4);
        let quality = low.quality_assessment();
        assert_eq!(quality.volume_level, QualityLevel::Low);

        // Higher complexity
        let high = HalsteadMetrics::from_counts(50, 100, 500, 1000);
        let quality = high.quality_assessment();
        assert!(matches!(quality.volume_level, QualityLevel::High | QualityLevel::VeryHigh));
    }

    #[test]
    fn test_token_collector_python() {
        let collector = TokenCollector::new("python");

        // Check that Python operators are recognized
        assert!(collector.operator_set.contains("and"));
        assert!(collector.operator_set.contains("or"));
        assert!(collector.operator_set.contains("**"));
        assert!(collector.operator_set.contains("//"));

        // Check value keywords
        assert!(collector.value_keywords.contains("True"));
        assert!(collector.value_keywords.contains("False"));
        assert!(collector.value_keywords.contains("None"));
    }

    #[test]
    fn test_token_collector_rust() {
        let collector = TokenCollector::new("rust");

        // Check Rust-specific operators
        assert!(collector.operator_set.contains("::"));
        assert!(collector.operator_set.contains("=>"));
        assert!(collector.operator_set.contains("?"));
        assert!(collector.operator_set.contains("mut"));

        // Check value keywords
        assert!(collector.value_keywords.contains("true"));
        assert!(collector.value_keywords.contains("false"));
        assert!(collector.value_keywords.contains("self"));
    }

    #[test]
    fn test_token_collector_typescript() {
        let collector = TokenCollector::new("typescript");

        // Check TypeScript-specific operators
        assert!(collector.operator_set.contains("=>"));
        assert!(collector.operator_set.contains("?."));
        assert!(collector.operator_set.contains("??"));
        assert!(collector.operator_set.contains("as"));

        // Check value keywords
        assert!(collector.value_keywords.contains("null"));
        assert!(collector.value_keywords.contains("undefined"));
        assert!(collector.value_keywords.contains("this"));
    }

    #[test]
    fn test_simple_python_function() {
        let source = r#"
def add(a, b):
    return a + b
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_halstead(file.path(), true);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        let func = &analysis.functions[0];
        assert_eq!(func.function_name, "add");

        // Should have operators: def, (, ), :, return, +
        // Should have operands: add, a, b (a and b appear multiple times)
        assert!(func.metrics.distinct_operators > 0);
        assert!(func.metrics.distinct_operands > 0);
        assert!(func.metrics.volume > 0.0);
    }

    #[test]
    fn test_complex_python_function() {
        let source = r#"
def process(items, threshold):
    result = []
    for item in items:
        if item > threshold:
            result.append(item * 2)
        elif item == threshold:
            result.append(item)
    return result
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_halstead(file.path(), true);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        let func = &analysis.functions[0];

        // More complex function should have higher metrics
        assert!(func.metrics.volume > 50.0);
        assert!(func.metrics.difficulty > 1.0);
    }

    #[test]
    fn test_typescript_function() {
        let source = r#"
function greet(name: string): string {
    if (name === "") {
        return "Hello, stranger!";
    }
    return `Hello, ${name}!`;
}
"#;
        let file = create_temp_file(source, ".ts");
        let result = analyze_file_halstead(file.path(), true);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert!(!analysis.functions.is_empty());
    }

    #[test]
    fn test_rust_function() {
        let source = r#"
fn factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}
"#;
        let file = create_temp_file(source, ".rs");
        let result = analyze_file_halstead(file.path(), true);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        let func = &analysis.functions[0];
        assert_eq!(func.function_name, "factorial");
    }

    #[test]
    fn test_class_methods() {
        let source = r#"
class Calculator:
    def add(self, a, b):
        return a + b

    def multiply(self, a, b):
        return a * b
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_halstead(file.path(), false);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 2);

        let add = analysis.functions.iter().find(|f| f.function_name == "Calculator.add");
        let mul = analysis.functions.iter().find(|f| f.function_name == "Calculator.multiply");

        assert!(add.is_some());
        assert!(mul.is_some());
    }

    #[test]
    fn test_aggregate_statistics() {
        let source = r#"
def simple():
    return 1

def complex(a, b, c):
    result = a + b
    if result > c:
        return result * 2
    else:
        return result - c
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_halstead(file.path(), false);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.stats.total_functions, 2);
        assert!(analysis.stats.avg_volume > 0.0);
        assert!(analysis.stats.max_volume >= analysis.stats.avg_volume);
    }

    #[test]
    fn test_empty_file() {
        let source = "# Just a comment\n";
        let file = create_temp_file(source, ".py");
        let result = analyze_file_halstead(file.path(), false);

        assert!(result.is_ok());
        let analysis = result.unwrap();
        assert_eq!(analysis.functions.len(), 0);
        assert_eq!(analysis.stats.total_functions, 0);
    }

    #[test]
    fn test_nonexistent_file() {
        let result = analyze_file_halstead("/nonexistent/path/file.py", false);
        assert!(result.is_err());
    }

    #[test]
    fn test_go_operators() {
        let collector = TokenCollector::new("go");

        // Check Go-specific operators
        assert!(collector.operator_set.contains(":="));
        assert!(collector.operator_set.contains("<-"));
        assert!(collector.operator_set.contains("..."));
        assert!(collector.operator_set.contains("range"));

        // Check value keywords
        assert!(collector.value_keywords.contains("nil"));
        assert!(collector.value_keywords.contains("iota"));
    }

    #[test]
    fn test_java_operators() {
        let collector = TokenCollector::new("java");

        // Check Java-specific operators
        assert!(collector.operator_set.contains("instanceof"));
        assert!(collector.operator_set.contains("->"));
        assert!(collector.operator_set.contains("synchronized"));

        // Check value keywords
        assert!(collector.value_keywords.contains("null"));
        assert!(collector.value_keywords.contains("this"));
        assert!(collector.value_keywords.contains("super"));
    }

    #[test]
    fn test_calculated_length_accuracy() {
        // Test the calculated length formula: N^ = n1 * log2(n1) + n2 * log2(n2)
        let metrics = HalsteadMetrics::from_counts(10, 20, 50, 100);

        // n1 * log2(n1) = 10 * 3.32 = 33.2
        // n2 * log2(n2) = 20 * 4.32 = 86.4
        // Total = 119.6 approximately
        assert!(metrics.calculated_length > 100.0 && metrics.calculated_length < 150.0);
    }

    #[test]
    fn test_time_and_bugs_estimates() {
        let metrics = HalsteadMetrics::from_counts(20, 30, 100, 150);

        // Time should be positive and reasonable
        assert!(metrics.time_seconds > 0.0);

        // Bugs estimate should be small fraction of volume
        assert!(metrics.bugs > 0.0);
        assert!(metrics.bugs < metrics.volume / 1000.0);
    }
}
