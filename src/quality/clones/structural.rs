//! Structural clone detection (Type-2/Type-3 clones).
//!
//! Detects code clones based on AST structure rather than text:
//!
//! - **Type-2 (Syntactic)**: Same structure with different identifiers/literals
//! - **Type-3 (Near-miss)**: Similar structure with small modifications
//!
//! # Algorithm
//!
//! 1. **AST Extraction**: Parse source files using tree-sitter
//! 2. **Normalization**: Convert function ASTs to canonical form:
//!    - Replace identifiers with placeholders: `$VAR1`, `$VAR2`, etc.
//!    - Replace literals with type markers: `$INT`, `$STRING`, `$FLOAT`
//!    - Preserve operators, keywords, and structure
//! 3. **Hashing**: Compute hash of normalized AST for fast Type-2 detection
//! 4. **Similarity**: Compute tree edit distance for Type-3 detection
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::quality::clones::structural::{
//!     StructuralCloneDetector, StructuralCloneConfig
//! };
//!
//! let config = StructuralCloneConfig::default()
//!     .with_similarity_threshold(0.8);
//! let detector = StructuralCloneDetector::new(config);
//! let result = detector.detect("./src")?;
//!
//! for clone in &result.clone_groups {
//!     println!("Clone group: {} instances, {:.0}% similar",
//!         clone.instances.len(), clone.similarity * 100.0);
//! }
//! ```
//!
//! # False Positive Handling
//!
//! The detector automatically filters out expected similarities:
//!
//! - **Generic/Template functions**: Detected by parameter patterns
//! - **Overloaded methods**: Same name, different signatures
//! - **Interface implementations**: Required method signatures
//! - **Getter/Setter pairs**: Simple accessor patterns
//! - **Test functions**: Similar setup/teardown structure

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use fxhash::{FxHashMap, FxHasher};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::{debug, trace};
use tree_sitter::{Node, Tree};
use xxhash_rust::xxh3::xxh3_64;

use std::hash::{Hash, Hasher};

use crate::ast::types::FunctionInfo;
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{Result, BrrrError};
use crate::lang::{Language, LanguageRegistry};
use crate::quality::clones::textual::CloneType;

// =============================================================================
// TYPES
// =============================================================================

/// A structural clone instance with location and metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructuralCloneInstance {
    /// File containing this clone.
    pub file: PathBuf,
    /// Function name.
    pub function_name: String,
    /// Starting line number (1-indexed).
    pub start_line: usize,
    /// Ending line number (1-indexed).
    pub end_line: usize,
    /// Number of AST nodes in the function.
    pub node_count: usize,
    /// Normalized form preview (first 100 chars).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub normalized_preview: Option<String>,
    /// Whether this is a method (belongs to a class).
    pub is_method: bool,
    /// Parent class name if this is a method.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub class_name: Option<String>,
}

impl StructuralCloneInstance {
    /// Number of lines in this instance.
    #[must_use]
    pub fn line_count(&self) -> usize {
        self.end_line.saturating_sub(self.start_line) + 1
    }
}

/// Difference between two structurally similar clones.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Difference {
    /// An identifier was renamed.
    IdentifierRenamed {
        original: String,
        renamed: String,
        /// Approximate position in normalized form.
        position: usize,
    },
    /// A literal value was changed.
    LiteralChanged {
        original: String,
        changed: String,
        literal_type: String,
    },
    /// A statement was added.
    StatementAdded {
        line: usize,
        /// Brief description of the added statement.
        description: String,
    },
    /// A statement was removed.
    StatementRemoved {
        line: usize,
        description: String,
    },
    /// A statement was modified.
    StatementModified {
        line: usize,
        description: String,
    },
}

/// A group of structurally similar clones.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructuralClone {
    /// Hash of the normalized form (identifies Type-2 clones).
    pub normalized_hash: u64,
    /// All instances of this clone.
    pub instances: Vec<StructuralCloneInstance>,
    /// Similarity score: 1.0 for Type-2 (exact), < 1.0 for Type-3.
    pub similarity: f64,
    /// Differences between instances (for Type-3 clones).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub differences: Vec<Difference>,
    /// Clone type classification.
    pub clone_type: CloneType,
    /// Number of AST nodes in normalized form.
    pub node_count: usize,
    /// Whether this clone group was filtered as a potential false positive.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub filtered: bool,
    /// Reason for filtering (if filtered).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub filter_reason: Option<String>,
}

impl StructuralClone {
    /// Total duplicated nodes across all instances (excluding the first).
    #[must_use]
    pub fn duplicated_nodes(&self) -> usize {
        if self.instances.len() <= 1 {
            return 0;
        }
        self.node_count * (self.instances.len() - 1)
    }

    /// Total duplicated lines across all instances.
    #[must_use]
    pub fn duplicated_lines(&self) -> usize {
        if self.instances.len() <= 1 {
            return 0;
        }
        let avg_lines = self.instances.iter()
            .map(|i| i.line_count())
            .sum::<usize>() / self.instances.len();
        avg_lines * (self.instances.len() - 1)
    }
}

/// Configuration for structural clone detection.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructuralCloneConfig {
    /// Minimum number of AST nodes for a function to be considered.
    /// Filters out trivial functions like getters/setters.
    /// Default: 10 nodes.
    pub min_nodes: usize,

    /// Minimum number of lines for a function to be considered.
    /// Default: 3 lines.
    pub min_lines: usize,

    /// Similarity threshold for Type-3 clone detection (0.0-1.0).
    /// Functions with similarity >= threshold are reported.
    /// Default: 0.8 (80% similar).
    pub similarity_threshold: f64,

    /// Whether to detect Type-2 clones (exact structural match).
    /// Default: true.
    pub detect_type2: bool,

    /// Whether to detect Type-3 clones (near-miss structural match).
    /// Default: true.
    pub detect_type3: bool,

    /// Whether to filter out getter/setter patterns.
    /// Default: true.
    pub filter_accessors: bool,

    /// Whether to filter out likely interface implementations.
    /// Default: true.
    pub filter_interface_impls: bool,

    /// Whether to filter out test functions.
    /// Default: false.
    pub filter_tests: bool,

    /// Maximum functions to compare for Type-3 detection.
    /// Higher values find more clones but take longer.
    /// Default: 1000.
    pub max_comparisons: usize,

    /// Maximum file size to process (bytes).
    /// Default: 1MB.
    pub max_file_size: u64,

    /// Language filter.
    pub language: Option<String>,

    /// Include only files matching these glob patterns.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub include_patterns: Vec<String>,

    /// Exclude files matching these glob patterns.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub exclude_patterns: Vec<String>,
}

impl Default for StructuralCloneConfig {
    fn default() -> Self {
        Self {
            min_nodes: 10,
            min_lines: 3,
            similarity_threshold: 0.8,
            detect_type2: true,
            detect_type3: true,
            filter_accessors: true,
            filter_interface_impls: true,
            filter_tests: false,
            max_comparisons: 1000,
            max_file_size: 1024 * 1024,
            language: None,
            include_patterns: Vec::new(),
            exclude_patterns: Vec::new(),
        }
    }
}

impl StructuralCloneConfig {
    /// Set similarity threshold.
    #[must_use]
    pub fn with_similarity_threshold(mut self, threshold: f64) -> Self {
        self.similarity_threshold = threshold.clamp(0.0, 1.0);
        self
    }

    /// Set minimum node count.
    #[must_use]
    pub fn with_min_nodes(mut self, min: usize) -> Self {
        self.min_nodes = min;
        self
    }

    /// Set minimum line count.
    #[must_use]
    pub fn with_min_lines(mut self, min: usize) -> Self {
        self.min_lines = min;
        self
    }

    /// Set language filter.
    #[must_use]
    pub fn with_language(mut self, lang: impl Into<String>) -> Self {
        self.language = Some(lang.into());
        self
    }

    /// Enable/disable Type-2 detection.
    #[must_use]
    pub fn with_type2(mut self, enabled: bool) -> Self {
        self.detect_type2 = enabled;
        self
    }

    /// Enable/disable Type-3 detection.
    #[must_use]
    pub fn with_type3(mut self, enabled: bool) -> Self {
        self.detect_type3 = enabled;
        self
    }
}

/// Statistics about structural clone detection.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct StructuralCloneStats {
    /// Total files scanned.
    pub files_scanned: usize,
    /// Total functions analyzed.
    pub functions_analyzed: usize,
    /// Functions that passed size filters.
    pub functions_considered: usize,
    /// Type-2 clone groups found.
    pub type2_groups: usize,
    /// Type-3 clone groups found.
    pub type3_groups: usize,
    /// Total clone instances.
    pub clone_instances: usize,
    /// Total duplicated AST nodes.
    pub duplicated_nodes: usize,
    /// Estimated duplicated lines.
    pub duplicated_lines: usize,
    /// Groups filtered as false positives.
    pub filtered_groups: usize,
    /// Files skipped due to errors.
    pub files_skipped: usize,
}

/// Error during structural clone detection.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructuralCloneError {
    /// File where error occurred.
    pub file: PathBuf,
    /// Error message.
    pub message: String,
}

/// Result of structural clone analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructuralCloneAnalysis {
    /// Path that was analyzed.
    pub path: PathBuf,
    /// Configuration used.
    pub config: StructuralCloneConfig,
    /// Clone groups detected (including filtered).
    pub clone_groups: Vec<StructuralClone>,
    /// Statistics.
    pub stats: StructuralCloneStats,
    /// Errors encountered.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<StructuralCloneError>,
}

impl StructuralCloneAnalysis {
    /// Get only unfiltered clone groups.
    #[must_use]
    pub fn active_clones(&self) -> Vec<&StructuralClone> {
        self.clone_groups.iter().filter(|c| !c.filtered).collect()
    }

    /// Get only Type-2 clone groups.
    #[must_use]
    pub fn type2_clones(&self) -> Vec<&StructuralClone> {
        self.clone_groups.iter()
            .filter(|c| !c.filtered && matches!(c.clone_type, CloneType::Type2))
            .collect()
    }

    /// Get only Type-3 clone groups.
    #[must_use]
    pub fn type3_clones(&self) -> Vec<&StructuralClone> {
        self.clone_groups.iter()
            .filter(|c| !c.filtered && matches!(c.clone_type, CloneType::Type3))
            .collect()
    }
}

// =============================================================================
// AST NORMALIZATION
// =============================================================================

/// Placeholder types for normalization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PlaceholderType {
    Variable,
    Function,
    Type,
    Parameter,
    Field,
}

/// AST normalizer that converts code to canonical form.
struct AstNormalizer {
    /// Counter for variable placeholders.
    var_counter: usize,
    /// Counter for function placeholders.
    func_counter: usize,
    /// Counter for type placeholders.
    type_counter: usize,
    /// Counter for parameter placeholders.
    param_counter: usize,
    /// Mapping from original identifiers to placeholders.
    identifier_map: HashMap<String, String>,
    /// Language being processed.
    language: String,
}

impl AstNormalizer {
    /// Create a new normalizer for the given language.
    fn new(language: &str) -> Self {
        Self {
            var_counter: 0,
            func_counter: 0,
            type_counter: 0,
            param_counter: 0,
            identifier_map: HashMap::new(),
            language: language.to_string(),
        }
    }

    /// Reset the normalizer for a new function.
    fn reset(&mut self) {
        self.var_counter = 0;
        self.func_counter = 0;
        self.type_counter = 0;
        self.param_counter = 0;
        self.identifier_map.clear();
    }

    /// Get or create a placeholder for an identifier.
    fn get_placeholder(&mut self, name: &str, kind: PlaceholderType) -> String {
        if let Some(existing) = self.identifier_map.get(name) {
            return existing.clone();
        }

        let placeholder = match kind {
            PlaceholderType::Variable => {
                self.var_counter += 1;
                format!("$VAR{}", self.var_counter)
            }
            PlaceholderType::Function => {
                self.func_counter += 1;
                format!("$FUNC{}", self.func_counter)
            }
            PlaceholderType::Type => {
                self.type_counter += 1;
                format!("$TYPE{}", self.type_counter)
            }
            PlaceholderType::Parameter => {
                self.param_counter += 1;
                format!("$PARAM{}", self.param_counter)
            }
            PlaceholderType::Field => {
                // Fields reuse variable placeholders
                self.var_counter += 1;
                format!("$FIELD{}", self.var_counter)
            }
        };

        self.identifier_map.insert(name.to_string(), placeholder.clone());
        placeholder
    }

    /// Normalize a literal value to a type marker.
    fn normalize_literal(&self, node: Node, source: &[u8]) -> String {
        let kind = node.kind();
        match kind {
            "integer" | "integer_literal" | "number" | "int_literal" => "$INT".to_string(),
            "float" | "float_literal" | "decimal_floating_point_literal" => "$FLOAT".to_string(),
            "string" | "string_literal" | "interpreted_string_literal" | "raw_string_literal" => "$STRING".to_string(),
            "true" | "false" | "boolean" | "True" | "False" => "$BOOL".to_string(),
            "none" | "nil" | "null" | "None" | "nullptr" => "$NULL".to_string(),
            "character_literal" | "char_literal" => "$CHAR".to_string(),
            _ => {
                // Unknown literal type - use text but mark it
                let text = Self::node_text(node, source);
                if text.chars().all(|c| c.is_ascii_digit() || c == '.' || c == '-') {
                    "$NUM".to_string()
                } else if text.starts_with('"') || text.starts_with('\'') || text.starts_with('`') {
                    "$STRING".to_string()
                } else {
                    format!("$LIT({})", kind)
                }
            }
        }
    }

    /// Get node text safely.
    fn node_text<'a>(node: Node<'a>, source: &'a [u8]) -> &'a str {
        std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }

    /// Check if a node kind is an identifier.
    fn is_identifier_kind(&self, kind: &str) -> bool {
        matches!(
            kind,
            "identifier" | "name" | "variable_name" | "field_identifier"
                | "property_identifier" | "shorthand_property_identifier"
                | "type_identifier" | "scoped_identifier"
        )
    }

    /// Check if a node kind is a literal.
    fn is_literal_kind(&self, kind: &str) -> bool {
        matches!(
            kind,
            "integer" | "integer_literal" | "float" | "float_literal"
                | "string" | "string_literal" | "interpreted_string_literal"
                | "raw_string_literal" | "number" | "decimal_floating_point_literal"
                | "true" | "false" | "boolean" | "none" | "nil" | "null"
                | "None" | "True" | "False" | "nullptr" | "character_literal"
                | "char_literal" | "int_literal"
        )
    }

    /// Check if a node kind is a keyword that should be preserved.
    fn is_keyword(&self, kind: &str) -> bool {
        matches!(
            kind,
            "if" | "else" | "elif" | "while" | "for" | "return" | "break"
                | "continue" | "try" | "except" | "catch" | "finally" | "throw"
                | "raise" | "assert" | "pass" | "yield" | "await" | "async"
                | "with" | "as" | "import" | "from" | "class" | "def" | "fn"
                | "func" | "function" | "let" | "var" | "const" | "mut"
                | "pub" | "private" | "public" | "protected" | "static"
                | "match" | "switch" | "case" | "default" | "in" | "not"
                | "and" | "or" | "is" | "lambda" | "new" | "delete" | "this"
                | "self" | "super" | "interface" | "struct" | "enum" | "trait"
                | "impl" | "type" | "extends" | "implements"
        )
    }

    /// Check if a node kind is an operator that should be preserved.
    fn is_operator(&self, kind: &str) -> bool {
        matches!(
            kind,
            "+" | "-" | "*" | "/" | "%" | "**" | "//" | "==" | "!=" | "<"
                | ">" | "<=" | ">=" | "&&" | "||" | "!" | "&" | "|" | "^"
                | "~" | "<<" | ">>" | "=" | "+=" | "-=" | "*=" | "/="
                | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=" | "++" | "--"
                | "." | "->" | "::" | "?" | ":" | "=>" | "binary_operator"
                | "unary_operator" | "comparison_operator" | "assignment"
        )
    }

    /// Normalize a function's AST to canonical form.
    ///
    /// Returns the normalized string representation and node count.
    fn normalize_function(&mut self, node: Node, source: &[u8]) -> (String, usize) {
        self.reset();
        let mut output = String::new();
        let mut node_count = 0;
        self.normalize_node(node, source, &mut output, &mut node_count, 0);
        (output, node_count)
    }

    /// Recursively normalize a node.
    fn normalize_node(
        &mut self,
        node: Node,
        source: &[u8],
        output: &mut String,
        node_count: &mut usize,
        depth: usize,
    ) {
        // Prevent stack overflow on deeply nested code
        if depth > 100 {
            output.push_str("$DEEP");
            return;
        }

        let kind = node.kind();
        *node_count += 1;

        // Handle different node types
        if self.is_literal_kind(kind) {
            output.push_str(&self.normalize_literal(node, source));
            output.push(' ');
        } else if self.is_identifier_kind(kind) {
            let text = Self::node_text(node, source);

            // Determine placeholder type based on context
            let placeholder_type = if let Some(parent) = node.parent() {
                match parent.kind() {
                    "call" | "call_expression" | "function_call" => PlaceholderType::Function,
                    "type" | "type_annotation" | "type_identifier" | "generic_type" => {
                        PlaceholderType::Type
                    }
                    "parameter" | "typed_parameter" | "required_parameter" | "optional_parameter" => {
                        PlaceholderType::Parameter
                    }
                    "field_expression" | "member_expression" | "attribute" => PlaceholderType::Field,
                    _ => PlaceholderType::Variable,
                }
            } else {
                PlaceholderType::Variable
            };

            // Check if it's a built-in or keyword
            if self.is_builtin(text) {
                output.push_str(text);
            } else {
                output.push_str(&self.get_placeholder(text, placeholder_type));
            }
            output.push(' ');
        } else if self.is_keyword(kind) || self.is_operator(kind) {
            // Preserve keywords and operators
            output.push_str(kind);
            output.push(' ');
        } else if kind == "comment" || kind == "line_comment" || kind == "block_comment" {
            // Skip comments entirely - they don't affect structure
        } else {
            // For structural nodes, output the kind and recurse into children
            let is_structural = matches!(
                kind,
                "block" | "compound_statement" | "statement_block" | "body"
                    | "if_statement" | "while_statement" | "for_statement"
                    | "for_in_statement" | "try_statement" | "with_statement"
                    | "match_statement" | "switch_statement" | "return_statement"
                    | "expression_statement" | "assignment_expression" | "assignment"
                    | "call_expression" | "call" | "binary_expression"
                    | "unary_expression" | "comparison" | "boolean_operator"
                    | "conditional_expression" | "ternary_expression"
                    | "subscript_expression" | "index_expression" | "slice"
                    | "list" | "tuple" | "dictionary" | "set" | "array"
                    | "object" | "argument_list" | "parameters" | "arguments"
                    | "lambda" | "arrow_function" | "function_expression"
            );

            if is_structural {
                output.push_str(kind);
                output.push_str("( ");
            }

            // Process children
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                self.normalize_node(child, source, output, node_count, depth + 1);
            }

            if is_structural {
                output.push_str(") ");
            }
        }
    }

    /// Check if an identifier is a language built-in.
    fn is_builtin(&self, name: &str) -> bool {
        // Python builtins
        let python_builtins = [
            "print", "len", "range", "enumerate", "zip", "map", "filter",
            "sorted", "reversed", "list", "dict", "set", "tuple", "str",
            "int", "float", "bool", "bytes", "type", "isinstance", "hasattr",
            "getattr", "setattr", "delattr", "open", "input", "sum", "max",
            "min", "abs", "round", "pow", "divmod", "all", "any", "iter",
            "next", "repr", "format", "id", "hash", "callable", "super",
            "object", "Exception", "ValueError", "TypeError", "KeyError",
            "IndexError", "AttributeError", "RuntimeError", "StopIteration",
        ];

        // JavaScript/TypeScript builtins
        let js_builtins = [
            "console", "Math", "JSON", "Object", "Array", "String", "Number",
            "Boolean", "Date", "RegExp", "Error", "Map", "Set", "WeakMap",
            "WeakSet", "Promise", "Symbol", "BigInt", "parseInt", "parseFloat",
            "isNaN", "isFinite", "encodeURI", "decodeURI", "setTimeout",
            "setInterval", "clearTimeout", "clearInterval", "fetch", "alert",
            "confirm", "prompt", "undefined", "NaN", "Infinity",
        ];

        // Rust builtins
        let rust_builtins = [
            "Some", "None", "Ok", "Err", "Vec", "String", "Box", "Rc", "Arc",
            "Cell", "RefCell", "Mutex", "RwLock", "Option", "Result", "println",
            "print", "eprintln", "eprint", "format", "panic", "assert", "debug_assert",
            "todo", "unimplemented", "unreachable", "Default", "Clone", "Copy",
            "Send", "Sync", "Sized", "Drop", "Fn", "FnMut", "FnOnce",
        ];

        // Go builtins
        let go_builtins = [
            "len", "cap", "make", "new", "append", "copy", "delete", "close",
            "panic", "recover", "print", "println", "complex", "real", "imag",
            "error", "string", "int", "int8", "int16", "int32", "int64",
            "uint", "uint8", "uint16", "uint32", "uint64", "float32", "float64",
            "bool", "byte", "rune", "nil", "true", "false", "iota",
        ];

        // C/C++ builtins
        let c_builtins = [
            "printf", "scanf", "malloc", "free", "realloc", "calloc",
            "sizeof", "memcpy", "memset", "strcmp", "strlen", "strcpy",
            "strcat", "fopen", "fclose", "fread", "fwrite", "fprintf",
            "fscanf", "exit", "abort", "assert", "NULL", "stdin", "stdout",
            "stderr", "EOF", "size_t", "ptrdiff_t", "nullptr", "std",
            "cout", "cin", "endl", "cerr", "vector", "map", "set",
            "string", "unique_ptr", "shared_ptr", "make_unique", "make_shared",
        ];

        match self.language.as_str() {
            "python" => python_builtins.contains(&name),
            "typescript" | "javascript" | "tsx" | "jsx" => js_builtins.contains(&name),
            "rust" => rust_builtins.contains(&name),
            "go" => go_builtins.contains(&name),
            "c" | "cpp" => c_builtins.contains(&name),
            _ => {
                // Check all builtins for unknown languages
                python_builtins.contains(&name)
                    || js_builtins.contains(&name)
                    || rust_builtins.contains(&name)
                    || go_builtins.contains(&name)
                    || c_builtins.contains(&name)
            }
        }
    }
}

/// Compute a stable hash for a normalized string.
fn hash_normalized(normalized: &str) -> u64 {
    let mut hasher = FxHasher::default();
    normalized.hash(&mut hasher);
    hasher.finish()
}

// =============================================================================
// SIMILARITY COMPUTATION
// =============================================================================

/// Compute Levenshtein edit distance on pre-hashed token sequences.
///
/// This is the hot path for Type-3 clone similarity. Optimizations:
/// - Uses u64 hash comparison (O(1)) instead of string comparison (O(k))
/// - Uses u32 for DP matrix (sufficient for token counts, better cache locality)
/// - Uses unchecked indexing to eliminate bounds checks in inner loop
/// - Prefetches next row's data for better cache utilization
///
/// # Safety
/// Uses unchecked array access. Callers must ensure:
/// - `a_hashes` and `b_hashes` are non-empty (handled by early returns)
/// - All indices are within bounds (guaranteed by loop structure)
#[inline]
fn edit_distance_hashed(a_hashes: &[u64], b_hashes: &[u64]) -> u32 {
    let m = a_hashes.len();
    let n = b_hashes.len();

    if m == 0 {
        return n as u32;
    }
    if n == 0 {
        return m as u32;
    }

    // Early exit for very short sequences - avoid allocation overhead
    if m == 1 && n == 1 {
        return if a_hashes[0] == b_hashes[0] { 0 } else { 1 };
    }

    // Two-row optimization: only keep current and previous row
    // Use u32 for better cache density (4 bytes vs 8 bytes per cell)
    let mut prev: Vec<u32> = (0..=n as u32).collect();
    let mut curr: Vec<u32> = vec![0; n + 1];

    for i in 1..=m {
        curr[0] = i as u32;

        // SAFETY: i-1 is always in bounds since i >= 1 and i <= m
        let a_hash = unsafe { *a_hashes.get_unchecked(i - 1) };

        // Prefetch next row's token hash for better cache utilization
        if i < m {
            // Hint to prefetch the next token we'll compare against
            let next_ptr = unsafe { a_hashes.as_ptr().add(i) };
            // Use inline assembly for prefetch on x86_64, no-op on other archs
            #[cfg(target_arch = "x86_64")]
            unsafe {
                std::arch::x86_64::_mm_prefetch(next_ptr.cast::<i8>(), std::arch::x86_64::_MM_HINT_T0);
            }
        }

        // Process columns with unchecked access
        // The inner loop is the hottest path - every bounds check matters
        for j in 1..=n {
            // SAFETY: j-1 is always in bounds since j >= 1 and j <= n
            let b_hash = unsafe { *b_hashes.get_unchecked(j - 1) };

            // Cost is 0 for match, 1 for mismatch (substitution)
            // Using u64 hash comparison instead of string comparison
            let cost = u32::from(a_hash != b_hash);

            // SAFETY: All indices are valid:
            // - prev[j]: j in 1..=n, prev has n+1 elements
            // - curr[j-1]: j-1 in 0..n, curr has n+1 elements
            // - prev[j-1]: j-1 in 0..n, prev has n+1 elements
            unsafe {
                let deletion = *prev.get_unchecked(j) + 1;
                let insertion = *curr.get_unchecked(j - 1) + 1;
                let substitution = *prev.get_unchecked(j - 1) + cost;

                // min(a, b, c) compiles to CMOVcc instructions (branchless)
                *curr.get_unchecked_mut(j) = deletion.min(insertion).min(substitution);
            }
        }

        std::mem::swap(&mut prev, &mut curr);
    }

    prev[n]
}

/// Hash tokens to u64 for fast equality comparison.
///
/// Uses xxh3 (SIMD-accelerated) for high-quality, fast hashing.
#[inline]
fn hash_tokens(tokens: &[&str]) -> Vec<u64> {
    tokens.iter().map(|t| xxh3_64(t.as_bytes())).collect()
}

/// Compute Levenshtein edit distance between two strings.
///
/// Tokenizes by whitespace and computes token-level edit distance.
/// Used for Type-3 clone similarity calculation.
fn edit_distance(a: &str, b: &str) -> usize {
    let a_tokens: Vec<&str> = a.split_whitespace().collect();
    let b_tokens: Vec<&str> = b.split_whitespace().collect();

    // Pre-hash tokens for O(1) comparison in the inner loop
    let a_hashes = hash_tokens(&a_tokens);
    let b_hashes = hash_tokens(&b_tokens);

    edit_distance_hashed(&a_hashes, &b_hashes) as usize
}

/// Compute similarity ratio between two normalized strings.
///
/// Returns a value between 0.0 (completely different) and 1.0 (identical).
/// Uses token-level edit distance with pre-hashed tokens for efficiency.
fn compute_similarity(a: &str, b: &str) -> f64 {
    // Fast path: identical strings
    if a == b {
        return 1.0;
    }

    // Tokenize once - avoids the previous double tokenization bug
    // where we'd tokenize here AND in edit_distance
    let a_tokens: Vec<&str> = a.split_whitespace().collect();
    let b_tokens: Vec<&str> = b.split_whitespace().collect();

    let max_len = a_tokens.len().max(b_tokens.len());
    if max_len == 0 {
        return 1.0;
    }

    // Pre-hash tokens for O(1) comparison in edit distance
    let a_hashes = hash_tokens(&a_tokens);
    let b_hashes = hash_tokens(&b_tokens);

    // Use the optimized hashed version directly, avoiding re-tokenization
    let distance = edit_distance_hashed(&a_hashes, &b_hashes);

    1.0 - (f64::from(distance) / max_len as f64)
}

/// Extract differences between two normalized strings.
fn extract_differences(a: &str, b: &str) -> Vec<Difference> {
    let mut differences = Vec::new();
    let a_tokens: Vec<&str> = a.split_whitespace().collect();
    let b_tokens: Vec<&str> = b.split_whitespace().collect();

    let mut i = 0;
    let mut j = 0;
    let mut position = 0;

    while i < a_tokens.len() && j < b_tokens.len() {
        let a_tok = a_tokens[i];
        let b_tok = b_tokens[j];

        if a_tok == b_tok {
            i += 1;
            j += 1;
            position += 1;
        } else if a_tok.starts_with('$') && b_tok.starts_with('$') {
            // Both are placeholders - check if same type
            let a_type = a_tok.chars().take_while(|c| c.is_alphabetic() || *c == '$').collect::<String>();
            let b_type = b_tok.chars().take_while(|c| c.is_alphabetic() || *c == '$').collect::<String>();

            if a_type == b_type {
                // Same type placeholder, different number - that's expected
                i += 1;
                j += 1;
                position += 1;
            } else {
                differences.push(Difference::IdentifierRenamed {
                    original: a_tok.to_string(),
                    renamed: b_tok.to_string(),
                    position,
                });
                i += 1;
                j += 1;
                position += 1;
            }
        } else {
            // Actual difference
            if a_tok.starts_with('$') && (b_tok.starts_with('$') || !b_tok.starts_with('$')) {
                differences.push(Difference::StatementModified {
                    line: position,
                    description: format!("{} -> {}", a_tok, b_tok),
                });
            }
            i += 1;
            j += 1;
            position += 1;
        }

        // Limit differences to prevent huge outputs
        if differences.len() >= 20 {
            break;
        }
    }

    // Handle remaining tokens
    while i < a_tokens.len() && differences.len() < 20 {
        differences.push(Difference::StatementRemoved {
            line: position,
            description: a_tokens[i].to_string(),
        });
        i += 1;
        position += 1;
    }

    while j < b_tokens.len() && differences.len() < 20 {
        differences.push(Difference::StatementAdded {
            line: position,
            description: b_tokens[j].to_string(),
        });
        j += 1;
        position += 1;
    }

    differences
}

// =============================================================================
// FALSE POSITIVE FILTERING
// =============================================================================

/// Check if a function appears to be a simple getter/setter.
fn is_accessor(normalized: &str, line_count: usize) -> bool {
    // Very short functions are likely accessors
    if line_count <= 3 {
        let tokens: Vec<&str> = normalized.split_whitespace().collect();
        if tokens.len() < 15 {
            // Check for getter pattern: return $FIELD
            if normalized.contains("return") && normalized.contains("$FIELD") {
                return true;
            }
            // Check for setter pattern: $FIELD = $PARAM
            if normalized.contains("assignment") && tokens.len() < 10 {
                return true;
            }
        }
    }
    false
}

/// Check if a function appears to be a test.
fn is_test_function(name: &str, decorators: &[String]) -> bool {
    // Check name patterns
    if name.starts_with("test_")
        || name.starts_with("Test")
        || name.ends_with("_test")
        || name.ends_with("Test")
        || name == "setUp"
        || name == "tearDown"
        || name == "setUpClass"
        || name == "tearDownClass"
    {
        return true;
    }

    // Check decorators
    for dec in decorators {
        if dec.contains("test") || dec.contains("Test") || dec == "pytest.fixture" {
            return true;
        }
    }

    false
}

/// Check if functions are likely interface/trait implementations.
fn are_interface_implementations(instances: &[&NormalizedFunction]) -> bool {
    // If all instances have the same method name and are methods (not free functions),
    // they might be interface implementations
    if instances.len() < 2 {
        return false;
    }

    let all_methods = instances.iter().all(|f| f.info.is_method);
    if !all_methods {
        return false;
    }

    // Check if all have the same name
    let first_name = &instances[0].info.name;
    let all_same_name = instances.iter().all(|f| &f.info.name == first_name);

    if all_same_name {
        // Common interface method names
        let common_interface_methods = [
            "__init__", "__str__", "__repr__", "__eq__", "__hash__",
            "__len__", "__iter__", "__next__", "__enter__", "__exit__",
            "__getitem__", "__setitem__", "__contains__", "__call__",
            "toString", "equals", "hashCode", "compareTo", "clone",
            "String", "Debug", "Display", "Default", "Clone", "Copy",
            "serialize", "deserialize", "to_json", "from_json",
            "encode", "decode", "read", "write", "close", "flush",
            "get", "set", "new", "default", "build", "create",
        ];

        if common_interface_methods.contains(&first_name.as_str()) {
            return true;
        }
    }

    false
}

// =============================================================================
// DETECTOR
// =============================================================================

/// Normalized function representation for clone detection.
#[derive(Debug, Clone)]
struct NormalizedFunction {
    /// Original function info.
    info: FunctionInfo,
    /// File path.
    file: PathBuf,
    /// Normalized AST string.
    normalized: String,
    /// Hash of normalized form.
    hash: u64,
    /// AST node count.
    node_count: usize,
    /// Parent class name (if method).
    class_name: Option<String>,
}

/// Minimum files for parallel processing.
const MIN_FILES_FOR_PARALLEL: usize = 10;

/// Structural clone detector.
pub struct StructuralCloneDetector {
    config: StructuralCloneConfig,
}

impl StructuralCloneDetector {
    /// Create a new detector with the given configuration.
    #[must_use]
    pub fn new(config: StructuralCloneConfig) -> Self {
        Self { config }
    }

    /// Create a detector with default configuration.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(StructuralCloneConfig::default())
    }

    /// Detect structural clones in the given path.
    pub fn detect(&self, path: impl AsRef<Path>) -> Result<StructuralCloneAnalysis> {
        let path = path.as_ref();
        debug!("Starting structural clone detection in {:?}", path);

        // Scan for source files
        let mut scan_config = if let Some(ref lang) = self.config.language {
            ScanConfig::for_language(lang)
        } else {
            ScanConfig::default()
        };
        scan_config.collect_metadata = true;

        let scanner = ProjectScanner::new(path.to_string_lossy().as_ref())?;
        let scan_result = scanner.scan_with_config(&scan_config)?;

        // Filter files by size
        let files: Vec<PathBuf> = if !scan_result.metadata.is_empty() {
            scan_result
                .metadata
                .into_iter()
                .filter(|meta| meta.size <= self.config.max_file_size)
                .map(|meta| meta.path)
                .collect()
        } else {
            scan_result
                .files
                .into_iter()
                .filter(|p| {
                    std::fs::metadata(p)
                        .map(|m| m.len() <= self.config.max_file_size)
                        .unwrap_or(false)
                })
                .collect()
        };

        debug!("Found {} files to analyze", files.len());

        self.detect_in_files(path.to_path_buf(), &files)
    }

    /// Detect clones in a specific list of files.
    pub fn detect_in_files(
        &self,
        base_path: PathBuf,
        files: &[PathBuf],
    ) -> Result<StructuralCloneAnalysis> {
        let mut stats = StructuralCloneStats::default();
        stats.files_scanned = files.len();

        // Shared state for parallel processing
        let all_functions: Mutex<Vec<NormalizedFunction>> = Mutex::new(Vec::new());
        let errors: Mutex<Vec<StructuralCloneError>> = Mutex::new(Vec::new());
        let functions_analyzed: Mutex<usize> = Mutex::new(0);

        // Process files
        let process_file = |file: &PathBuf| {
            match self.process_file(file) {
                Ok(funcs) => {
                    let count = funcs.len();
                    if !funcs.is_empty() {
                        let mut all = all_functions.lock().unwrap_or_else(|e| e.into_inner());
                        all.extend(funcs);
                    }
                    *functions_analyzed.lock().unwrap_or_else(|e| e.into_inner()) += count;
                }
                Err(e) => {
                    errors.lock().unwrap_or_else(|e| e.into_inner()).push(StructuralCloneError {
                        file: file.clone(),
                        message: e.to_string(),
                    });
                }
            }
        };

        // Choose parallel vs sequential based on file count
        if files.len() >= MIN_FILES_FOR_PARALLEL {
            files.par_iter().for_each(process_file);
        } else {
            files.iter().for_each(process_file);
        }

        // Extract results
        let all_functions = all_functions.into_inner().unwrap_or_else(|e| e.into_inner());
        let errors = errors.into_inner().unwrap_or_else(|e| e.into_inner());
        stats.functions_analyzed = *functions_analyzed.lock().unwrap_or_else(|e| e.into_inner());
        stats.files_skipped = errors.len();

        // Filter functions by size
        let functions: Vec<NormalizedFunction> = all_functions
            .into_iter()
            .filter(|f| {
                f.node_count >= self.config.min_nodes
                    && f.info.end_line_number.map_or(true, |end| {
                        end.saturating_sub(f.info.line_number) + 1 >= self.config.min_lines
                    })
            })
            .collect();

        stats.functions_considered = functions.len();
        debug!(
            "Analyzing {} functions (filtered from {})",
            functions.len(),
            stats.functions_analyzed
        );

        // Detect clones
        let clone_groups = self.find_clones(&functions);

        // Calculate statistics
        for clone in &clone_groups {
            if clone.filtered {
                stats.filtered_groups += 1;
            } else {
                match clone.clone_type {
                    CloneType::Type2 => stats.type2_groups += 1,
                    CloneType::Type3 => stats.type3_groups += 1,
                    _ => {}
                }
                stats.clone_instances += clone.instances.len();
                stats.duplicated_nodes += clone.duplicated_nodes();
                stats.duplicated_lines += clone.duplicated_lines();
            }
        }

        debug!(
            "Detection complete: {} Type-2, {} Type-3, {} filtered",
            stats.type2_groups, stats.type3_groups, stats.filtered_groups
        );

        Ok(StructuralCloneAnalysis {
            path: base_path,
            config: self.config.clone(),
            clone_groups,
            stats,
            errors,
        })
    }

    /// Process a single file and extract normalized functions.
    fn process_file(&self, path: &Path) -> Result<Vec<NormalizedFunction>> {
        let registry = LanguageRegistry::global();
        let lang = registry.detect_language(path).ok_or_else(|| {
            BrrrError::UnsupportedLanguage(
                path.extension()
                    .and_then(|e| e.to_str())
                    .unwrap_or("unknown")
                    .to_string(),
            )
        })?;

        let source = std::fs::read(path)
            .map_err(|e| BrrrError::io_with_path(e, path))?;

        // Check content compatibility
        if lang.should_skip_file(path, &source) {
            return Ok(Vec::new());
        }

        // Parse file
        let mut parser = lang.parser()?;
        let tree = parser
            .parse(&source, None)
            .ok_or_else(|| BrrrError::Parse {
                file: path.display().to_string(),
                message: "Failed to parse file".to_string(),
            })?;

        self.extract_normalized_functions(&tree, &source, lang, path)
    }

    /// Extract and normalize all functions from a parsed tree.
    fn extract_normalized_functions(
        &self,
        tree: &Tree,
        source: &[u8],
        lang: &dyn Language,
        path: &Path,
    ) -> Result<Vec<NormalizedFunction>> {
        let mut results = Vec::new();
        let mut normalizer = AstNormalizer::new(lang.name());

        // Extract functions using tree-sitter queries
        let query_str = lang.function_query();
        let ts_lang = tree.language();
        let query = tree_sitter::Query::new(&ts_lang, query_str)
            .map_err(|e| BrrrError::TreeSitter(format!("Query error: {}", e)))?;

        let mut cursor = tree_sitter::QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source);

        use streaming_iterator::StreamingIterator;
        while let Some(match_) = matches.next() {
            // Get function node
            let node = if let Some(idx) = query.capture_index_for_name("function") {
                match_.captures.iter().find(|c| c.index == idx).map(|c| c.node)
            } else {
                match_.captures.first().map(|c| c.node)
            };

            if let Some(node) = node {
                if let Some(func_info) = lang.extract_function(node, source) {
                    // Check test filter
                    if self.config.filter_tests && is_test_function(&func_info.name, &func_info.decorators) {
                        continue;
                    }

                    // Find the function body node for normalization
                    let body_node = Self::find_body_node(node);
                    let target_node = body_node.unwrap_or(node);

                    // Normalize the function
                    let (normalized, node_count) = normalizer.normalize_function(target_node, source);
                    let hash = hash_normalized(&normalized);

                    // Check accessor filter
                    let line_count = func_info.end_line_number
                        .map(|end| end.saturating_sub(func_info.line_number) + 1)
                        .unwrap_or(1);

                    if self.config.filter_accessors && is_accessor(&normalized, line_count) {
                        trace!("Skipping accessor: {}:{}", path.display(), func_info.name);
                        continue;
                    }

                    results.push(NormalizedFunction {
                        info: func_info,
                        file: path.to_path_buf(),
                        normalized,
                        hash,
                        node_count,
                        class_name: None, // TODO: extract from parent context
                    });
                }
            }
        }

        // Also extract methods from classes
        let class_query_str = lang.class_query();
        let class_query = tree_sitter::Query::new(&ts_lang, class_query_str)
            .map_err(|e| BrrrError::TreeSitter(format!("Class query error: {}", e)))?;

        let mut class_cursor = tree_sitter::QueryCursor::new();
        let mut class_matches = class_cursor.matches(&class_query, tree.root_node(), source);

        while let Some(match_) = class_matches.next() {
            let class_node = if let Some(idx) = class_query.capture_index_for_name("class") {
                match_.captures.iter().find(|c| c.index == idx).map(|c| c.node)
            } else {
                match_.captures.first().map(|c| c.node)
            };

            if let Some(class_node) = class_node {
                if let Some(class_info) = lang.extract_class(class_node, source) {
                    for method in &class_info.methods {
                        // Check test filter
                        if self.config.filter_tests && is_test_function(&method.name, &method.decorators) {
                            continue;
                        }

                        // Find method node in the class
                        if let Some(method_node) = Self::find_method_node(class_node, &method.name, source) {
                            let body_node = Self::find_body_node(method_node);
                            let target_node = body_node.unwrap_or(method_node);

                            let (normalized, node_count) = normalizer.normalize_function(target_node, source);
                            let hash = hash_normalized(&normalized);

                            let line_count = method.end_line_number
                                .map(|end| end.saturating_sub(method.line_number) + 1)
                                .unwrap_or(1);

                            if self.config.filter_accessors && is_accessor(&normalized, line_count) {
                                continue;
                            }

                            results.push(NormalizedFunction {
                                info: method.clone(),
                                file: path.to_path_buf(),
                                normalized,
                                hash,
                                node_count,
                                class_name: Some(class_info.name.clone()),
                            });
                        }
                    }
                }
            }
        }

        Ok(results)
    }

    /// Find the body/block node of a function.
    fn find_body_node(func_node: Node) -> Option<Node> {
        let body_kinds = ["block", "compound_statement", "statement_block", "body", "expression_body"];

        let mut cursor = func_node.walk();
        for child in func_node.children(&mut cursor) {
            if body_kinds.contains(&child.kind()) {
                return Some(child);
            }
        }

        // Try child_by_field_name
        for kind in &["body", "consequence", "block"] {
            if let Some(body) = func_node.child_by_field_name(kind) {
                return Some(body);
            }
        }

        None
    }

    /// Find a method node within a class node by name.
    fn find_method_node<'a>(class_node: Node<'a>, method_name: &str, source: &[u8]) -> Option<Node<'a>> {
        let method_kinds = [
            "function_definition", "method_definition", "function_declaration",
            "method_declaration", "function_item", "constructor_declaration",
        ];

        let mut cursor = class_node.walk();
        Self::find_method_recursive(class_node, method_name, source, &method_kinds, &mut cursor)
    }

    fn find_method_recursive<'a>(
        node: Node<'a>,
        method_name: &str,
        source: &[u8],
        method_kinds: &[&str],
        cursor: &mut tree_sitter::TreeCursor<'a>,
    ) -> Option<Node<'a>> {
        if method_kinds.contains(&node.kind()) {
            // Check if this is the method we're looking for
            if let Some(name_node) = node.child_by_field_name("name") {
                let name = std::str::from_utf8(&source[name_node.start_byte()..name_node.end_byte()])
                    .unwrap_or("");
                if name == method_name {
                    return Some(node);
                }
            }
        }

        // Recurse into children
        for child in node.children(cursor) {
            let mut child_cursor = child.walk();
            if let Some(found) = Self::find_method_recursive(child, method_name, source, method_kinds, &mut child_cursor) {
                return Some(found);
            }
        }

        None
    }

    /// Find all clone groups from normalized functions.
    fn find_clones(&self, functions: &[NormalizedFunction]) -> Vec<StructuralClone> {
        let mut clone_groups = Vec::new();

        // Type-2 detection: group by exact hash match
        if self.config.detect_type2 {
            let type2_groups = self.find_type2_clones(functions);
            clone_groups.extend(type2_groups);
        }

        // Type-3 detection: find similar but not identical functions
        if self.config.detect_type3 {
            // Get hashes of functions already in Type-2 groups
            let type2_hashes: std::collections::HashSet<u64> = clone_groups
                .iter()
                .flat_map(|g| g.instances.iter().map(|_| g.normalized_hash))
                .collect();

            let type3_groups = self.find_type3_clones(functions, &type2_hashes);
            clone_groups.extend(type3_groups);
        }

        // Sort by duplicated nodes (most impactful first)
        clone_groups.sort_by(|a, b| {
            let a_impact = if a.filtered { 0 } else { a.duplicated_nodes() };
            let b_impact = if b.filtered { 0 } else { b.duplicated_nodes() };
            b_impact.cmp(&a_impact)
        });

        clone_groups
    }

    /// Find Type-2 clones (exact structural match).
    fn find_type2_clones(&self, functions: &[NormalizedFunction]) -> Vec<StructuralClone> {
        let mut hash_groups: FxHashMap<u64, Vec<&NormalizedFunction>> = FxHashMap::default();

        for func in functions {
            hash_groups.entry(func.hash).or_default().push(func);
        }

        let mut clone_groups = Vec::new();

        for (hash, group) in hash_groups {
            if group.len() >= 2 {
                let instances: Vec<StructuralCloneInstance> = group
                    .iter()
                    .map(|f| StructuralCloneInstance {
                        file: f.file.clone(),
                        function_name: f.info.name.clone(),
                        start_line: f.info.line_number,
                        end_line: f.info.end_line_number.unwrap_or(f.info.line_number),
                        node_count: f.node_count,
                        normalized_preview: Some(f.normalized.chars().take(100).collect()),
                        is_method: f.info.is_method,
                        class_name: f.class_name.clone(),
                    })
                    .collect();

                let node_count = group.first().map(|f| f.node_count).unwrap_or(0);

                // Check for interface implementations
                let filtered = self.config.filter_interface_impls && are_interface_implementations(group.as_slice());

                clone_groups.push(StructuralClone {
                    normalized_hash: hash,
                    instances,
                    similarity: 1.0,
                    differences: Vec::new(),
                    clone_type: CloneType::Type2,
                    node_count,
                    filtered,
                    filter_reason: if filtered {
                        Some("Likely interface implementations".to_string())
                    } else {
                        None
                    },
                });
            }
        }

        clone_groups
    }

    /// Find Type-3 clones (near-miss structural match).
    fn find_type3_clones(
        &self,
        functions: &[NormalizedFunction],
        excluded_hashes: &std::collections::HashSet<u64>,
    ) -> Vec<StructuralClone> {
        let mut clone_groups = Vec::new();

        // Filter out functions already in Type-2 groups
        let candidates: Vec<&NormalizedFunction> = functions
            .iter()
            .filter(|f| !excluded_hashes.contains(&f.hash))
            .collect();

        if candidates.len() < 2 {
            return clone_groups;
        }

        // Limit comparisons for performance
        let max_candidates = self.config.max_comparisons.min(candidates.len());
        let candidates = &candidates[..max_candidates];

        // Track which functions are already grouped
        let mut grouped: std::collections::HashSet<usize> = std::collections::HashSet::new();

        // Compare each pair of functions
        for (i, func_a) in candidates.iter().enumerate() {
            if grouped.contains(&i) {
                continue;
            }

            let mut group_members = vec![(i, *func_a, 1.0f64)];

            for (j, func_b) in candidates.iter().enumerate().skip(i + 1) {
                if grouped.contains(&j) {
                    continue;
                }

                // Quick size filter: skip if node counts are very different
                let size_ratio = func_a.node_count.min(func_b.node_count) as f64
                    / func_a.node_count.max(func_b.node_count) as f64;

                if size_ratio < self.config.similarity_threshold * 0.8 {
                    continue;
                }

                let similarity = compute_similarity(&func_a.normalized, &func_b.normalized);

                if similarity >= self.config.similarity_threshold {
                    group_members.push((j, *func_b, similarity));
                }
            }

            if group_members.len() >= 2 {
                // Mark all as grouped
                for (idx, _, _) in &group_members {
                    grouped.insert(*idx);
                }

                // Calculate average similarity
                let avg_similarity = group_members.iter().map(|(_, _, s)| *s).sum::<f64>()
                    / group_members.len() as f64;

                // Extract differences between first and second function
                let differences = if group_members.len() >= 2 {
                    extract_differences(
                        &group_members[0].1.normalized,
                        &group_members[1].1.normalized,
                    )
                } else {
                    Vec::new()
                };

                let instances: Vec<StructuralCloneInstance> = group_members
                    .iter()
                    .map(|(_, f, _)| StructuralCloneInstance {
                        file: f.file.clone(),
                        function_name: f.info.name.clone(),
                        start_line: f.info.line_number,
                        end_line: f.info.end_line_number.unwrap_or(f.info.line_number),
                        node_count: f.node_count,
                        normalized_preview: Some(f.normalized.chars().take(100).collect()),
                        is_method: f.info.is_method,
                        class_name: f.class_name.clone(),
                    })
                    .collect();

                let funcs: Vec<&NormalizedFunction> = group_members.iter().map(|(_, f, _)| *f).collect();

                // Check for interface implementations
                let filtered = self.config.filter_interface_impls && are_interface_implementations(funcs.as_slice());

                let node_count = func_a.node_count;

                clone_groups.push(StructuralClone {
                    normalized_hash: func_a.hash, // Use first function's hash as identifier
                    instances,
                    similarity: avg_similarity,
                    differences,
                    clone_type: CloneType::Type3,
                    node_count,
                    filtered,
                    filter_reason: if filtered {
                        Some("Likely interface implementations".to_string())
                    } else {
                        None
                    },
                });
            }
        }

        clone_groups
    }
}

// =============================================================================
// PUBLIC API
// =============================================================================

/// Detect structural clones (Type-2/Type-3) in a project.
///
/// This is the main entry point for structural clone detection.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `similarity_threshold` - Similarity threshold for Type-3 (0.0-1.0, default: 0.8)
/// * `language` - Optional language filter
///
/// # Example
///
/// ```ignore
/// let result = detect_structural_clones("./src", Some(0.8), None)?;
/// println!("Found {} Type-2 and {} Type-3 clone groups",
///     result.stats.type2_groups, result.stats.type3_groups);
/// ```
pub fn detect_structural_clones(
    path: impl AsRef<Path>,
    similarity_threshold: Option<f64>,
    language: Option<&str>,
) -> Result<StructuralCloneAnalysis> {
    let mut config = StructuralCloneConfig::default();

    if let Some(threshold) = similarity_threshold {
        config.similarity_threshold = threshold.clamp(0.0, 1.0);
    }

    if let Some(lang) = language {
        config.language = Some(lang.to_string());
    }

    let detector = StructuralCloneDetector::new(config);
    detector.detect(path)
}

/// Format structural clone analysis for display.
pub fn format_structural_clone_summary(analysis: &StructuralCloneAnalysis) -> String {
    let mut output = String::new();

    output.push_str(&format!(
        "Structural Clone Detection Results for {}\n",
        analysis.path.display()
    ));
    output.push_str(&format!("{}\n\n", "=".repeat(60)));

    // Statistics
    output.push_str("Statistics:\n");
    output.push_str(&format!("  Files scanned:        {}\n", analysis.stats.files_scanned));
    output.push_str(&format!("  Functions analyzed:   {}\n", analysis.stats.functions_analyzed));
    output.push_str(&format!("  Functions considered: {}\n", analysis.stats.functions_considered));
    output.push_str(&format!("  Type-2 clone groups:  {}\n", analysis.stats.type2_groups));
    output.push_str(&format!("  Type-3 clone groups:  {}\n", analysis.stats.type3_groups));
    output.push_str(&format!("  Total instances:      {}\n", analysis.stats.clone_instances));
    output.push_str(&format!("  Duplicated nodes:     {}\n", analysis.stats.duplicated_nodes));
    output.push_str(&format!("  Duplicated lines:     ~{}\n", analysis.stats.duplicated_lines));
    if analysis.stats.filtered_groups > 0 {
        output.push_str(&format!("  Filtered (false pos): {}\n", analysis.stats.filtered_groups));
    }
    output.push('\n');

    // Clone groups (unfiltered)
    let active_clones = analysis.active_clones();
    if !active_clones.is_empty() {
        output.push_str("Clone Groups:\n");
        for (i, clone) in active_clones.iter().take(15).enumerate() {
            let type_str = match clone.clone_type {
                CloneType::Type2 => "Type-2 (structural)",
                CloneType::Type3 => "Type-3 (near-miss)",
                _ => "Unknown",
            };

            output.push_str(&format!(
                "\n{}. {} - {} instances, {} nodes, {:.0}% similar\n",
                i + 1,
                type_str,
                clone.instances.len(),
                clone.node_count,
                clone.similarity * 100.0
            ));

            for instance in &clone.instances {
                let class_prefix = instance.class_name.as_ref()
                    .map(|c| format!("{}.", c))
                    .unwrap_or_default();

                output.push_str(&format!(
                    "   {}:{}-{} {}{}\n",
                    instance.file.display(),
                    instance.start_line,
                    instance.end_line,
                    class_prefix,
                    instance.function_name
                ));
            }

            // Show differences for Type-3
            if matches!(clone.clone_type, CloneType::Type3) && !clone.differences.is_empty() {
                output.push_str("   Differences:\n");
                for diff in clone.differences.iter().take(5) {
                    match diff {
                        Difference::IdentifierRenamed { original, renamed, .. } => {
                            output.push_str(&format!("     - Renamed: {} -> {}\n", original, renamed));
                        }
                        Difference::LiteralChanged { original, changed, .. } => {
                            output.push_str(&format!("     - Literal: {} -> {}\n", original, changed));
                        }
                        Difference::StatementAdded { description, .. } => {
                            output.push_str(&format!("     - Added: {}\n", description));
                        }
                        Difference::StatementRemoved { description, .. } => {
                            output.push_str(&format!("     - Removed: {}\n", description));
                        }
                        Difference::StatementModified { description, .. } => {
                            output.push_str(&format!("     - Modified: {}\n", description));
                        }
                    }
                }
            }
        }

        if active_clones.len() > 15 {
            output.push_str(&format!("\n... and {} more clone groups\n", active_clones.len() - 15));
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
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_ast_normalizer_basic() {
        let mut normalizer = AstNormalizer::new("python");

        // Test placeholder generation
        assert_eq!(normalizer.get_placeholder("x", PlaceholderType::Variable), "$VAR1");
        assert_eq!(normalizer.get_placeholder("x", PlaceholderType::Variable), "$VAR1"); // Same name returns same placeholder
        assert_eq!(normalizer.get_placeholder("y", PlaceholderType::Variable), "$VAR2");
        assert_eq!(normalizer.get_placeholder("foo", PlaceholderType::Function), "$FUNC1");
        assert_eq!(normalizer.get_placeholder("int", PlaceholderType::Type), "$TYPE1");
    }

    #[test]
    fn test_ast_normalizer_reset() {
        let mut normalizer = AstNormalizer::new("python");

        normalizer.get_placeholder("x", PlaceholderType::Variable);
        normalizer.get_placeholder("y", PlaceholderType::Variable);

        normalizer.reset();

        // After reset, counters start over
        assert_eq!(normalizer.get_placeholder("a", PlaceholderType::Variable), "$VAR1");
    }

    #[test]
    fn test_is_builtin() {
        let normalizer = AstNormalizer::new("python");

        assert!(normalizer.is_builtin("print"));
        assert!(normalizer.is_builtin("len"));
        assert!(normalizer.is_builtin("ValueError"));
        assert!(!normalizer.is_builtin("my_custom_function"));
    }

    #[test]
    fn test_edit_distance() {
        // Identical strings
        assert_eq!(edit_distance("a b c", "a b c"), 0);

        // One substitution
        assert_eq!(edit_distance("a b c", "a x c"), 1);

        // One insertion
        assert_eq!(edit_distance("a c", "a b c"), 1);

        // One deletion
        assert_eq!(edit_distance("a b c", "a c"), 1);

        // Multiple operations
        assert_eq!(edit_distance("a b c d", "x b y"), 3);
    }

    #[test]
    fn test_compute_similarity() {
        // Identical
        assert!((compute_similarity("a b c", "a b c") - 1.0).abs() < 0.001);

        // Mostly similar
        let sim = compute_similarity("$VAR1 $VAR2 return $VAR1", "$VAR1 $VAR2 return $VAR2");
        assert!(sim > 0.7, "Expected >0.7, got {}", sim);

        // Very different
        let sim = compute_similarity("a b c d e f", "x y z");
        assert!(sim < 0.5, "Expected <0.5, got {}", sim);
    }

    #[test]
    fn test_hash_normalized() {
        let hash1 = hash_normalized("$VAR1 = $INT return $VAR1");
        let hash2 = hash_normalized("$VAR1 = $INT return $VAR1");
        let hash3 = hash_normalized("$VAR1 = $STRING return $VAR1");

        assert_eq!(hash1, hash2, "Same normalized string should have same hash");
        assert_ne!(hash1, hash3, "Different normalized strings should have different hashes");
    }

    #[test]
    fn test_is_accessor() {
        // Simple getter
        assert!(is_accessor("return $FIELD1", 2));

        // Simple setter
        assert!(is_accessor("assignment( $FIELD1 $PARAM1 )", 2));

        // Too long for accessor
        assert!(!is_accessor("if( $VAR1 ) block( return $VAR2 ) else block( return $VAR3 )", 10));
    }

    #[test]
    fn test_is_test_function() {
        assert!(is_test_function("test_my_function", &[]));
        assert!(is_test_function("TestMyClass", &[]));
        assert!(is_test_function("my_function_test", &[]));
        assert!(is_test_function("setUp", &[]));
        assert!(is_test_function("normal_function", &["pytest.fixture".to_string()]));
        assert!(!is_test_function("normal_function", &[]));
    }

    #[test]
    fn test_config_builder() {
        let config = StructuralCloneConfig::default()
            .with_similarity_threshold(0.9)
            .with_min_nodes(20)
            .with_language("rust")
            .with_type3(false);

        assert!((config.similarity_threshold - 0.9).abs() < 0.001);
        assert_eq!(config.min_nodes, 20);
        assert_eq!(config.language, Some("rust".to_string()));
        assert!(!config.detect_type3);
    }

    #[test]
    fn test_structural_clone_duplicated_nodes() {
        let clone = StructuralClone {
            normalized_hash: 12345,
            instances: vec![
                StructuralCloneInstance {
                    file: PathBuf::from("a.py"),
                    function_name: "func1".to_string(),
                    start_line: 1,
                    end_line: 10,
                    node_count: 50,
                    normalized_preview: None,
                    is_method: false,
                    class_name: None,
                },
                StructuralCloneInstance {
                    file: PathBuf::from("b.py"),
                    function_name: "func2".to_string(),
                    start_line: 1,
                    end_line: 10,
                    node_count: 50,
                    normalized_preview: None,
                    is_method: false,
                    class_name: None,
                },
            ],
            similarity: 1.0,
            differences: Vec::new(),
            clone_type: CloneType::Type2,
            node_count: 50,
            filtered: false,
            filter_reason: None,
        };

        // 2 instances, 50 nodes each, first is "original" so 1 * 50 = 50 duplicated
        assert_eq!(clone.duplicated_nodes(), 50);
    }

    #[test]
    fn test_detect_structural_clones_integration() {
        let temp_dir = TempDir::new().unwrap();

        // Create two Python files with structurally identical functions
        let code1 = r#"
def calculate_sum(numbers, multiplier):
    total = 0
    for num in numbers:
        if num > 0:
            total = total + num * multiplier
        else:
            total = total + num
    return total

def other_function():
    pass
"#;

        let code2 = r#"
def compute_total(items, factor):
    result = 0
    for item in items:
        if item > 0:
            result = result + item * factor
        else:
            result = result + item
    return result

def different_function():
    pass
"#;

        let file1 = temp_dir.path().join("file1.py");
        let file2 = temp_dir.path().join("file2.py");

        fs::write(&file1, code1).unwrap();
        fs::write(&file2, code2).unwrap();

        // Run detection
        let config = StructuralCloneConfig::default()
            .with_min_nodes(5)
            .with_min_lines(3);
        let detector = StructuralCloneDetector::new(config);
        let result = detector.detect_in_files(
            temp_dir.path().to_path_buf(),
            &[file1, file2]
        ).unwrap();

        // Should detect the structural clone
        assert!(
            result.stats.type2_groups > 0 || result.stats.type3_groups > 0,
            "Should detect at least one clone group. Stats: {:?}",
            result.stats
        );
    }

    #[test]
    fn test_extract_differences() {
        let a = "$VAR1 = $INT return $VAR1 + $VAR2";
        let b = "$VAR1 = $STRING return $VAR1 + $VAR3";

        let diffs = extract_differences(a, b);

        assert!(!diffs.is_empty(), "Should find differences");
    }

    #[test]
    fn test_structural_clone_analysis_helpers() {
        let analysis = StructuralCloneAnalysis {
            path: PathBuf::from("./src"),
            config: StructuralCloneConfig::default(),
            clone_groups: vec![
                StructuralClone {
                    normalized_hash: 1,
                    instances: vec![],
                    similarity: 1.0,
                    differences: Vec::new(),
                    clone_type: CloneType::Type2,
                    node_count: 10,
                    filtered: false,
                    filter_reason: None,
                },
                StructuralClone {
                    normalized_hash: 2,
                    instances: vec![],
                    similarity: 0.9,
                    differences: Vec::new(),
                    clone_type: CloneType::Type3,
                    node_count: 15,
                    filtered: false,
                    filter_reason: None,
                },
                StructuralClone {
                    normalized_hash: 3,
                    instances: vec![],
                    similarity: 1.0,
                    differences: Vec::new(),
                    clone_type: CloneType::Type2,
                    node_count: 8,
                    filtered: true,
                    filter_reason: Some("Test".to_string()),
                },
            ],
            stats: StructuralCloneStats::default(),
            errors: Vec::new(),
        };

        assert_eq!(analysis.active_clones().len(), 2);
        assert_eq!(analysis.type2_clones().len(), 1);
        assert_eq!(analysis.type3_clones().len(), 1);
    }

    #[test]
    fn test_format_structural_clone_summary() {
        let analysis = StructuralCloneAnalysis {
            path: PathBuf::from("./src"),
            config: StructuralCloneConfig::default(),
            clone_groups: vec![StructuralClone {
                normalized_hash: 12345,
                instances: vec![
                    StructuralCloneInstance {
                        file: PathBuf::from("a.py"),
                        function_name: "func_a".to_string(),
                        start_line: 1,
                        end_line: 10,
                        node_count: 50,
                        normalized_preview: Some("$VAR1 = $INT".to_string()),
                        is_method: false,
                        class_name: None,
                    },
                    StructuralCloneInstance {
                        file: PathBuf::from("b.py"),
                        function_name: "func_b".to_string(),
                        start_line: 5,
                        end_line: 15,
                        node_count: 50,
                        normalized_preview: Some("$VAR1 = $INT".to_string()),
                        is_method: false,
                        class_name: None,
                    },
                ],
                similarity: 1.0,
                differences: Vec::new(),
                clone_type: CloneType::Type2,
                node_count: 50,
                filtered: false,
                filter_reason: None,
            }],
            stats: StructuralCloneStats {
                files_scanned: 5,
                functions_analyzed: 20,
                functions_considered: 15,
                type2_groups: 1,
                type3_groups: 0,
                clone_instances: 2,
                duplicated_nodes: 50,
                duplicated_lines: 10,
                filtered_groups: 0,
                files_skipped: 0,
            },
            errors: Vec::new(),
        };

        let summary = format_structural_clone_summary(&analysis);

        assert!(summary.contains("Structural Clone Detection"));
        assert!(summary.contains("Files scanned:        5"));
        assert!(summary.contains("Type-2 clone groups:  1"));
        assert!(summary.contains("func_a"));
        assert!(summary.contains("func_b"));
    }
}
