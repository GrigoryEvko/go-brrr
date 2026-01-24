//! Semantic search type definitions.
//!
//! Core data structures for semantic code search and embedding.
//! Mirrors the Python implementation in brrr/semantic.py.

use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

// =============================================================================
// Token Budget Constants
// =============================================================================

/// Maximum tokens for embedding text (conservative limit for good retrieval quality).
/// Qwen3 supports 32K, TEI configured for 16K, but 8K gives best results.
pub const MAX_EMBEDDING_TOKENS: usize = 8192;

/// Maximum tokens for code preview, leaving room for metadata in embedding text.
pub const MAX_CODE_PREVIEW_TOKENS: usize = 6000;

/// Token overlap between chunks for context continuity.
pub const CHUNK_OVERLAP_TOKENS: usize = 200;

// =============================================================================
// Semantic Pattern Definitions
// =============================================================================

/// Semantic pattern categories for automatic code tagging.
/// Each pattern is a regex that matches code containing that semantic concept.
#[derive(Debug, Clone)]
pub struct SemanticPattern {
    /// Pattern category name (e.g., "crud", "validation")
    pub name: &'static str,
    /// Regex pattern to match
    pub pattern: &'static str,
}

/// All semantic patterns for code tagging.
/// These patterns detect common code categories for semantic enrichment.
pub static SEMANTIC_PATTERNS: &[SemanticPattern] = &[
    // Data operations
    SemanticPattern {
        name: "crud",
        pattern: r"\b(create|read|update|delete|insert|select|save|load|fetch|store|persist|get|set|add|remove)\b",
    },
    SemanticPattern {
        name: "validation",
        pattern: r"\b(valid|validate|check|verify|assert|ensure|sanitize|normalize|parse|format)\b",
    },
    SemanticPattern {
        name: "transform",
        pattern: r"\b(convert|transform|map|reduce|filter|sort|merge|split|join|serialize|deserialize)\b",
    },
    // Control flow patterns
    SemanticPattern {
        name: "error_handling",
        pattern: r"\b(try|catch|except|raise|throw|error|exception|fail|panic)\b",
    },
    SemanticPattern {
        name: "async_ops",
        pattern: r"\b(async|await|promise|future|callback|then|concurrent|parallel|thread)\b",
    },
    SemanticPattern {
        name: "iteration",
        pattern: r"\b(for|while|loop|iterate|each|map|reduce|filter)\b",
    },
    // Architecture patterns
    SemanticPattern {
        name: "api_endpoint",
        pattern: r"\b(route|endpoint|handler|controller|get|post|put|delete|patch|request|response)\b",
    },
    SemanticPattern {
        name: "database",
        pattern: r"\b(query|sql|select|insert|update|delete|table|schema|migration|model|entity)\b",
    },
    SemanticPattern {
        name: "auth",
        pattern: r"\b(auth|login|logout|session|token|jwt|oauth|permission|role|access)\b",
    },
    SemanticPattern {
        name: "cache",
        pattern: r"\b(cache|memoize|memo|store|redis|memcache|ttl|expire|invalidate)\b",
    },
    // Code quality
    SemanticPattern {
        name: "test",
        pattern: r"\b(test|spec|mock|stub|assert|expect|should|describe|it)\b",
    },
    SemanticPattern {
        name: "logging",
        pattern: r"\b(log|logger|debug|info|warn|error|trace|print|console)\b",
    },
    SemanticPattern {
        name: "config",
        pattern: r"\b(config|setting|option|env|environment|parameter|argument)\b",
    },
];

// =============================================================================
// Core Types
// =============================================================================

/// Kind of code unit for embedding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum UnitKind {
    /// Top-level function
    Function,
    /// Class method
    Method,
    /// Class or struct definition
    Class,
    /// Module-level code or file summary
    Module,
    /// Chunk of an oversized unit
    Chunk,
}

impl UnitKind {
    /// Convert to string representation.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Function => "function",
            Self::Method => "method",
            Self::Class => "class",
            Self::Module => "module",
            Self::Chunk => "chunk",
        }
    }
}

impl std::fmt::Display for UnitKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Code complexity metrics (heuristic analysis without full AST parsing).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CodeComplexity {
    /// Maximum nesting depth
    pub depth: usize,
    /// Number of branch statements (if, elif, else, case, switch, match)
    pub branches: usize,
    /// Number of loop statements (for, while, loop)
    pub loops: usize,
}

impl CodeComplexity {
    /// Create empty complexity metrics.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Check if the code has notable complexity.
    #[must_use]
    pub fn is_complex(&self) -> bool {
        self.depth > 3 || self.branches > 5 || self.loops > 2
    }

    /// Generate a natural language description of complexity.
    #[must_use]
    pub fn describe(&self) -> Option<String> {
        let mut parts = Vec::new();
        if self.depth > 3 {
            parts.push("deep nesting");
        }
        if self.branches > 5 {
            parts.push("many branches");
        }
        if self.loops > 2 {
            parts.push("multiple loops");
        }
        if parts.is_empty() {
            None
        } else {
            Some(parts.join(", "))
        }
    }
}

/// A code unit for semantic embedding.
///
/// Contains information from all 5 brrr analysis layers plus semantic enrichment.
/// This is the primary unit of indexing and retrieval in semantic search.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingUnit {
    /// Unique identifier (typically file::qualified_name or file::name#chunkN)
    pub id: String,

    /// Source file path (relative to project root)
    pub file: String,

    /// Simple name (function/class/method name)
    pub name: String,

    /// Kind of code unit
    pub kind: UnitKind,

    /// Full code content (may be truncated for large units)
    pub code: String,

    /// Function/method signature or class declaration
    pub signature: String,

    /// Docstring or documentation comment
    pub docstring: Option<String>,

    /// Starting line number (1-indexed)
    pub start_line: usize,

    /// Ending line number (1-indexed)
    pub end_line: usize,

    /// Token count for this unit's code
    pub token_count: usize,

    /// Semantic tags detected from code patterns
    pub semantic_tags: Vec<String>,

    /// Parent unit name (for chunks and methods)
    pub parent: Option<String>,

    // ==========================================================================
    // Extended metadata from brrr layers
    // ==========================================================================
    /// L1: Programming language
    pub language: String,

    /// L2: Functions this unit calls
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub calls: Vec<String>,

    /// L2: Functions that call this unit
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub called_by: Vec<String>,

    /// L3: CFG summary (complexity, block count)
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub cfg_summary: String,

    /// L4: DFG summary (variable count, def-use chains)
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub dfg_summary: String,

    /// L5: Dependencies (imported modules)
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub dependencies: String,

    /// Code complexity metrics
    #[serde(default)]
    pub complexity: CodeComplexity,

    /// Chunk index (0-indexed, for chunked units)
    #[serde(default)]
    pub chunk_index: usize,

    /// Total number of chunks (1 for non-chunked units)
    #[serde(default = "default_chunk_total")]
    pub chunk_total: usize,
}

fn default_chunk_total() -> usize {
    1
}

impl EmbeddingUnit {
    /// Create a new embedding unit with minimal required fields.
    #[must_use]
    pub fn new(
        file: impl Into<String>,
        name: impl Into<String>,
        kind: UnitKind,
        code: impl Into<String>,
        start_line: usize,
        language: impl Into<String>,
    ) -> Self {
        let name = name.into();
        let file = file.into();
        let code = code.into();

        Self {
            id: format!("{}::{}", file, name),
            file,
            name,
            kind,
            code,
            signature: String::new(),
            docstring: None,
            start_line,
            end_line: start_line,
            token_count: 0,
            semantic_tags: Vec::new(),
            parent: None,
            language: language.into(),
            calls: Vec::new(),
            called_by: Vec::new(),
            cfg_summary: String::new(),
            dfg_summary: String::new(),
            dependencies: String::new(),
            complexity: CodeComplexity::default(),
            chunk_index: 0,
            chunk_total: 1,
        }
    }

    /// Check if this unit is a chunk of a larger unit.
    #[must_use]
    pub fn is_chunk(&self) -> bool {
        self.chunk_total > 1
    }

    /// Check if this unit needs to be split into chunks based on token count.
    #[must_use]
    pub fn needs_chunking(&self) -> bool {
        self.token_count > MAX_EMBEDDING_TOKENS
    }

    /// Get the qualified name (file::name or file::parent.name for methods).
    #[must_use]
    pub fn qualified_name(&self) -> String {
        match &self.parent {
            Some(parent) if self.kind == UnitKind::Method => {
                format!("{}::{}.{}", self.file, parent, self.name)
            }
            _ => format!("{}::{}", self.file, self.name),
        }
    }

    /// Convert to a HashMap for JSON serialization.
    #[must_use]
    pub fn to_map(&self) -> HashMap<String, serde_json::Value> {
        serde_json::to_value(self)
            .ok()
            .and_then(|v| v.as_object().cloned())
            .map(|m| m.into_iter().collect())
            .unwrap_or_default()
    }
}

/// Result of a semantic search query.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    /// The matching code unit
    pub unit: EmbeddingUnit,

    /// Similarity score (0.0 to 1.0, higher is better)
    pub score: f32,

    /// Highlighted portions of code that matched (optional)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub highlights: Vec<String>,
}

impl SearchResult {
    /// Create a new search result.
    #[must_use]
    pub fn new(unit: EmbeddingUnit, score: f32) -> Self {
        Self {
            unit,
            score,
            highlights: Vec::new(),
        }
    }

    /// Create a search result with highlights.
    #[must_use]
    pub fn with_highlights(unit: EmbeddingUnit, score: f32, highlights: Vec<String>) -> Self {
        Self {
            unit,
            score,
            highlights,
        }
    }
}

/// Information about a chunk split from an oversized unit.
#[derive(Debug, Clone)]
pub struct ChunkInfo {
    /// Chunk text content
    pub text: String,
    /// Start character offset in original code
    pub start_char: usize,
    /// End character offset in original code
    pub end_char: usize,
}

impl ChunkInfo {
    /// Create a new chunk info.
    #[must_use]
    pub fn new(text: String, start_char: usize, end_char: usize) -> Self {
        Self {
            text,
            start_char,
            end_char,
        }
    }
}

// =============================================================================
// Content-Hashed Index for Deduplication
// =============================================================================

/// Location information for a code unit (file, function name, line).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeLocation {
    /// Source file path
    pub file: String,
    /// Function or code unit name
    pub name: String,
    /// Line number (1-indexed)
    pub line: usize,
}

impl CodeLocation {
    /// Create a new code location.
    #[must_use]
    pub fn new(file: impl Into<String>, name: impl Into<String>, line: usize) -> Self {
        Self {
            file: file.into(),
            name: name.into(),
            line,
        }
    }
}

/// Content-hashed index for deduplication of code units.
///
/// Used to avoid indexing identical code multiple times. The index normalizes
/// whitespace before hashing, so code with different formatting but identical
/// content will be detected as duplicates.
///
/// # Examples
///
/// ```
/// use go_brrr::semantic::ContentHashedIndex;
///
/// let mut index = ContentHashedIndex::new();
///
/// // First occurrence is added
/// assert!(index.add("def foo(): pass", "src/a.py", "foo", 10));
///
/// // Identical content is detected as duplicate
/// assert!(!index.add("def foo(): pass", "src/b.py", "foo", 20));
///
/// // Check stats
/// let (unique, duplicates) = index.stats();
/// assert_eq!(unique, 1);
/// assert_eq!(duplicates, 1);
/// ```
#[derive(Debug, Clone, Default)]
pub struct ContentHashedIndex {
    /// Hash -> original location (file, function_name, line)
    seen: HashMap<u64, CodeLocation>,
    /// Number of duplicate items detected
    pub duplicates_found: usize,
    /// Number of unique items indexed
    pub unique_items: usize,
}

impl ContentHashedIndex {
    /// Create a new empty content-hashed index.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Compute content hash for code with whitespace normalization.
    ///
    /// Normalizes code by:
    /// - Trimming each line
    /// - Removing empty lines
    /// - Joining with single newlines
    ///
    /// This ensures code with different indentation or blank lines
    /// but identical content produces the same hash.
    fn hash_content(content: &str) -> u64 {
        let mut hasher = DefaultHasher::new();
        let normalized: String = content
            .lines()
            .map(|l| l.trim())
            .filter(|l| !l.is_empty())
            .collect::<Vec<_>>()
            .join("\n");
        normalized.hash(&mut hasher);
        hasher.finish()
    }

    /// Check if content is a duplicate, returning the original location if so.
    ///
    /// # Arguments
    ///
    /// * `content` - Code content to check
    ///
    /// # Returns
    ///
    /// `Some(&CodeLocation)` if this content was already seen, `None` otherwise.
    #[must_use]
    pub fn check_duplicate(&self, content: &str) -> Option<&CodeLocation> {
        let hash = Self::hash_content(content);
        self.seen.get(&hash)
    }

    /// Add content to the index.
    ///
    /// # Arguments
    ///
    /// * `content` - Code content to add
    /// * `file` - Source file path
    /// * `function_name` - Name of the function or code unit
    /// * `line` - Line number (1-indexed)
    ///
    /// # Returns
    ///
    /// `true` if this is new content (was added), `false` if duplicate (was not added).
    pub fn add(&mut self, content: &str, file: &str, function_name: &str, line: usize) -> bool {
        let hash = Self::hash_content(content);

        if self.seen.contains_key(&hash) {
            self.duplicates_found += 1;
            false
        } else {
            self.seen
                .insert(hash, CodeLocation::new(file, function_name, line));
            self.unique_items += 1;
            true
        }
    }

    /// Get deduplication statistics.
    ///
    /// # Returns
    ///
    /// Tuple of (unique_items, duplicates_found).
    #[must_use]
    pub fn stats(&self) -> (usize, usize) {
        (self.unique_items, self.duplicates_found)
    }

    /// Get the number of unique items in the index.
    #[must_use]
    pub fn len(&self) -> usize {
        self.seen.len()
    }

    /// Check if the index is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.seen.is_empty()
    }

    /// Clear the index and reset statistics.
    pub fn clear(&mut self) {
        self.seen.clear();
        self.duplicates_found = 0;
        self.unique_items = 0;
    }

    /// Get the deduplication ratio (duplicates / total).
    ///
    /// Returns 0.0 if no items have been processed.
    #[must_use]
    pub fn dedup_ratio(&self) -> f64 {
        let total = self.unique_items + self.duplicates_found;
        if total == 0 {
            0.0
        } else {
            self.duplicates_found as f64 / total as f64
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unit_kind_as_str() {
        assert_eq!(UnitKind::Function.as_str(), "function");
        assert_eq!(UnitKind::Method.as_str(), "method");
        assert_eq!(UnitKind::Class.as_str(), "class");
        assert_eq!(UnitKind::Module.as_str(), "module");
        assert_eq!(UnitKind::Chunk.as_str(), "chunk");
    }

    #[test]
    fn test_unit_kind_display() {
        assert_eq!(format!("{}", UnitKind::Function), "function");
    }

    #[test]
    fn test_code_complexity_describe() {
        let simple = CodeComplexity {
            depth: 2,
            branches: 3,
            loops: 1,
        };
        assert!(simple.describe().is_none());

        let complex = CodeComplexity {
            depth: 5,
            branches: 10,
            loops: 4,
        };
        let desc = complex.describe().unwrap();
        assert!(desc.contains("deep nesting"));
        assert!(desc.contains("many branches"));
        assert!(desc.contains("multiple loops"));
    }

    #[test]
    fn test_embedding_unit_new() {
        let unit = EmbeddingUnit::new(
            "src/main.py",
            "process_data",
            UnitKind::Function,
            "def process_data(): pass",
            10,
            "python",
        );

        assert_eq!(unit.id, "src/main.py::process_data");
        assert_eq!(unit.file, "src/main.py");
        assert_eq!(unit.name, "process_data");
        assert_eq!(unit.kind, UnitKind::Function);
        assert_eq!(unit.start_line, 10);
        assert_eq!(unit.language, "python");
        assert!(!unit.is_chunk());
    }

    #[test]
    fn test_embedding_unit_qualified_name() {
        let mut unit = EmbeddingUnit::new(
            "src/model.py",
            "save",
            UnitKind::Method,
            "def save(self): pass",
            20,
            "python",
        );
        unit.parent = Some("User".to_string());

        assert_eq!(unit.qualified_name(), "src/model.py::User.save");
    }

    #[test]
    fn test_embedding_unit_is_chunk() {
        let mut unit = EmbeddingUnit::new(
            "src/large.py",
            "big_function[1/3]",
            UnitKind::Chunk,
            "# chunk 1",
            1,
            "python",
        );
        unit.chunk_index = 0;
        unit.chunk_total = 3;

        assert!(unit.is_chunk());
    }

    #[test]
    fn test_search_result() {
        let unit = EmbeddingUnit::new(
            "test.py",
            "test_fn",
            UnitKind::Function,
            "def test_fn(): pass",
            1,
            "python",
        );
        let result = SearchResult::new(unit.clone(), 0.95);

        assert_eq!(result.score, 0.95);
        assert!(result.highlights.is_empty());

        let result_with_highlights =
            SearchResult::with_highlights(unit, 0.95, vec!["highlighted text".to_string()]);
        assert_eq!(result_with_highlights.highlights.len(), 1);
    }

    #[test]
    fn test_semantic_patterns_defined() {
        assert!(!SEMANTIC_PATTERNS.is_empty());

        // Check some key patterns exist
        let pattern_names: Vec<_> = SEMANTIC_PATTERNS.iter().map(|p| p.name).collect();
        assert!(pattern_names.contains(&"crud"));
        assert!(pattern_names.contains(&"validation"));
        assert!(pattern_names.contains(&"error_handling"));
        assert!(pattern_names.contains(&"async_ops"));
    }

    #[test]
    fn test_constants() {
        assert!(MAX_EMBEDDING_TOKENS > 0);
        assert!(MAX_CODE_PREVIEW_TOKENS < MAX_EMBEDDING_TOKENS);
        assert!(CHUNK_OVERLAP_TOKENS < MAX_CODE_PREVIEW_TOKENS);
    }

    #[test]
    fn test_code_location_new() {
        let loc = CodeLocation::new("src/main.py", "process", 42);
        assert_eq!(loc.file, "src/main.py");
        assert_eq!(loc.name, "process");
        assert_eq!(loc.line, 42);
    }

    #[test]
    fn test_content_hashed_index_new() {
        let index = ContentHashedIndex::new();
        assert!(index.is_empty());
        assert_eq!(index.len(), 0);
        assert_eq!(index.unique_items, 0);
        assert_eq!(index.duplicates_found, 0);
    }

    #[test]
    fn test_content_hashed_index_add_unique() {
        let mut index = ContentHashedIndex::new();

        // First item should be added
        assert!(index.add("def foo(): pass", "src/a.py", "foo", 10));
        assert_eq!(index.unique_items, 1);
        assert_eq!(index.duplicates_found, 0);
        assert_eq!(index.len(), 1);

        // Different content should also be added
        assert!(index.add("def bar(): return 1", "src/b.py", "bar", 20));
        assert_eq!(index.unique_items, 2);
        assert_eq!(index.duplicates_found, 0);
        assert_eq!(index.len(), 2);
    }

    #[test]
    fn test_content_hashed_index_detect_duplicate() {
        let mut index = ContentHashedIndex::new();

        // Add first occurrence
        assert!(index.add("def foo(): pass", "src/a.py", "foo", 10));

        // Same content in different file is duplicate
        assert!(!index.add("def foo(): pass", "src/b.py", "foo", 20));
        assert_eq!(index.unique_items, 1);
        assert_eq!(index.duplicates_found, 1);
    }

    #[test]
    fn test_content_hashed_index_whitespace_normalization() {
        let mut index = ContentHashedIndex::new();

        // Add with specific indentation
        let code1 = "def foo():\n    return 1";
        assert!(index.add(code1, "src/a.py", "foo", 10));

        // Same code with different indentation is duplicate
        let code2 = "  def foo():\n        return 1  ";
        assert!(!index.add(code2, "src/b.py", "foo", 20));

        // Same code with extra blank lines is duplicate
        let code3 = "def foo():\n\n    return 1\n\n";
        assert!(!index.add(code3, "src/c.py", "foo", 30));

        assert_eq!(index.unique_items, 1);
        assert_eq!(index.duplicates_found, 2);
    }

    #[test]
    fn test_content_hashed_index_check_duplicate() {
        let mut index = ContentHashedIndex::new();

        // Initially nothing is duplicate
        assert!(index.check_duplicate("def foo(): pass").is_none());

        // Add content
        index.add("def foo(): pass", "src/a.py", "foo", 10);

        // Now it should be detected
        let loc = index.check_duplicate("def foo(): pass").unwrap();
        assert_eq!(loc.file, "src/a.py");
        assert_eq!(loc.name, "foo");
        assert_eq!(loc.line, 10);
    }

    #[test]
    fn test_content_hashed_index_stats() {
        let mut index = ContentHashedIndex::new();

        index.add("code1", "f1.py", "fn1", 1);
        index.add("code2", "f2.py", "fn2", 2);
        index.add("code1", "f3.py", "fn1", 3); // duplicate
        index.add("code3", "f4.py", "fn3", 4);
        index.add("code2", "f5.py", "fn2", 5); // duplicate

        let (unique, dups) = index.stats();
        assert_eq!(unique, 3);
        assert_eq!(dups, 2);
    }

    #[test]
    fn test_content_hashed_index_dedup_ratio() {
        let mut index = ContentHashedIndex::new();

        // Empty index has 0 ratio
        assert_eq!(index.dedup_ratio(), 0.0);

        // 3 unique, 2 duplicates = 2/5 = 0.4
        index.add("code1", "f1.py", "fn1", 1);
        index.add("code2", "f2.py", "fn2", 2);
        index.add("code1", "f3.py", "fn1", 3);
        index.add("code3", "f4.py", "fn3", 4);
        index.add("code2", "f5.py", "fn2", 5);

        assert!((index.dedup_ratio() - 0.4).abs() < 0.001);
    }

    #[test]
    fn test_content_hashed_index_clear() {
        let mut index = ContentHashedIndex::new();

        index.add("code1", "f1.py", "fn1", 1);
        index.add("code1", "f2.py", "fn1", 2);

        assert!(!index.is_empty());
        assert_eq!(index.unique_items, 1);
        assert_eq!(index.duplicates_found, 1);

        index.clear();

        assert!(index.is_empty());
        assert_eq!(index.unique_items, 0);
        assert_eq!(index.duplicates_found, 0);

        // After clear, same content is unique again
        assert!(index.add("code1", "f1.py", "fn1", 1));
    }
}
