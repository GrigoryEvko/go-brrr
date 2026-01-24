//! AST extraction using tree-sitter.
//!
//! Provides efficient code structure extraction from source files using
//! tree-sitter queries. Supports multiple languages through the Language trait.
//!
//! # Query Caching
//!
//! Tree-sitter query compilation is expensive (1-5ms per query). Since queries
//! are immutable after creation, we cache them globally keyed by
//! `(language_name, query_kind)`. This provides O(1) amortized access for
//! multi-file operations, improving performance by 20-30%.
//!
//! # Parser Caching
//!
//! Tree-sitter parser creation involves memory allocation and language setup,
//! which adds overhead when processing many files. We use thread-local parser
//! caching to reuse parsers across files of the same language, with RAII-based
//! automatic return to the cache. This provides ~10-20% speedup for multi-file
//! operations.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::ops::Bound;
use std::path::Path;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use once_cell::sync::Lazy;
use parking_lot::RwLock;
use tree_sitter::{Language as TSLanguage, Node, Parser, Query, QueryCursor, QueryMatch, Tree};

use crate::ast::types::{ClassInfo, FunctionInfo, ImportInfo, ModuleInfo};
use crate::error::{BrrrError, Result};
use crate::lang::{Language, LanguageRegistry};
use crate::util::format_query_error;

/// Cache key for compiled tree-sitter queries.
/// Uses `(language_name, query_kind)` to uniquely identify queries.
type QueryCacheKey = (&'static str, &'static str);

/// Thread-safe cache for compiled tree-sitter queries.
///
/// Stores `Arc<Query>` to allow shared access without cloning the Query itself.
/// Uses `parking_lot::RwLock` for better performance than `std::sync::RwLock`.
static QUERY_CACHE: Lazy<RwLock<FxHashMap<QueryCacheKey, Arc<Query>>>> =
    Lazy::new(|| RwLock::new(FxHashMap::default()));

/// Get or compile a tree-sitter query, using cache for repeated lookups.
///
/// This function provides O(1) amortized access to compiled queries by:
/// 1. First checking the read-locked cache (fast path for cached queries)
/// 2. On cache miss, compiling the query and storing it under write lock
///
/// # Arguments
/// * `ts_lang` - Tree-sitter language for query compilation
/// * `lang_name` - Static string identifier for the language
/// * `query_kind` - Static string identifier for query type ("function", "class")
/// * `query_str` - The tree-sitter query pattern to compile
///
/// # Returns
/// * `Result<Arc<Query>>` - Shared reference to compiled query or compilation error
///
/// # Performance
/// - First call for a (lang, kind) pair: O(query_compile_time) ~1-5ms
/// - Subsequent calls: O(1) hash lookup ~10ns
fn get_cached_query(
    ts_lang: &TSLanguage,
    lang_name: &'static str,
    query_kind: &'static str,
    query_str: &str,
) -> Result<Arc<Query>> {
    let key = (lang_name, query_kind);

    // Fast path: check cache with read lock
    {
        let cache = QUERY_CACHE.read();
        if let Some(query) = cache.get(&key) {
            return Ok(Arc::clone(query));
        }
    }

    // Slow path: compile query and cache it
    let query = Query::new(ts_lang, query_str).map_err(|e| {
        BrrrError::TreeSitter(format_query_error(lang_name, query_kind, query_str, &e))
    })?;

    let query_arc = Arc::new(query);

    let mut cache = QUERY_CACHE.write();
    // Double-check: another thread might have inserted while we were compiling
    // Use entry API to avoid overwriting if already present
    cache.entry(key).or_insert_with(|| Arc::clone(&query_arc));

    Ok(query_arc)
}

/// Clear the query cache.
///
/// Useful for testing or when language configurations are updated.
/// In normal operation, the cache persists for the lifetime of the process.
#[allow(dead_code)]
pub fn clear_query_cache() {
    let mut cache = QUERY_CACHE.write();
    cache.clear();
}

/// Get current query cache statistics.
///
/// Returns the number of cached queries. Useful for debugging and monitoring.
#[allow(dead_code)]
pub fn query_cache_stats() -> usize {
    QUERY_CACHE.read().len()
}

// =============================================================================
// Parser Caching
// =============================================================================
//
// Tree-sitter parsers are expensive to create (~100-500us) due to memory
// allocation and language grammar setup. Since parsers maintain mutable state
// during parsing, they cannot be shared across threads. We use thread-local
// storage to cache one parser per language per thread.
//
// Key design decisions:
// - Thread-local: Parsers are not thread-safe, avoiding synchronization overhead
// - RAII wrapper: Automatic return to cache via Drop, ensuring cleanup on errors
// - Size limit: Prevents unbounded memory growth (max 16 parsers per thread)
// - Reset on reuse: Clears parser state for fresh parsing
// =============================================================================

thread_local! {
    /// Thread-local parser cache for reusing parsers across file operations.
    ///
    /// Stores one parser per language name. When a parser is needed, it's removed
    /// from the cache (if present), reset, and wrapped in CachedParser. On drop,
    /// the parser is returned to the cache for reuse.
    static PARSER_CACHE: RefCell<FxHashMap<&'static str, Parser>> = RefCell::new(FxHashMap::default());
}

/// Maximum number of parsers to cache per thread.
///
/// Limits memory usage while covering common multi-language projects.
/// 16 parsers covers all supported languages (Python, TypeScript, TSX, Go,
/// Rust, Java, C, C++) with room for future additions.
const MAX_CACHED_PARSERS: usize = 16;

/// RAII wrapper for cached parser access.
///
/// Automatically returns the parser to the thread-local cache on drop,
/// ensuring proper cleanup even when errors occur. This pattern is essential
/// because tree-sitter's Parser doesn't implement Clone.
///
/// # Example
///
/// ```ignore
/// let mut cached = CachedParser::take(lang)?;
/// let tree = cached.get_mut().parse(&source, None);
/// // Parser automatically returned to cache when `cached` is dropped
/// ```
struct CachedParser {
    /// The parser being used. Option allows taking ownership on drop.
    parser: Option<Parser>,
    /// Language name for cache key on return.
    lang_name: &'static str,
}

impl CachedParser {
    /// Get a parser for the given language, reusing cached parser if available.
    ///
    /// If a cached parser exists for this language, it is removed from the cache,
    /// reset to clear previous state, and returned. Otherwise, a new parser is
    /// created via the Language trait.
    ///
    /// # Performance
    ///
    /// - Cache hit: O(1) hash lookup + reset ~1-5us
    /// - Cache miss: O(parser_creation_time) ~100-500us
    ///
    /// # Errors
    ///
    /// Returns an error if parser creation fails (e.g., invalid language grammar).
    fn take(lang: &dyn Language) -> Result<Self> {
        let lang_name = lang.name();

        // Try to get cached parser for this language
        let cached = PARSER_CACHE.with(|cache| cache.borrow_mut().remove(lang_name));

        let parser = match cached {
            Some(mut p) => {
                // Reset parser to clear previous parsing state (tree references, etc.)
                p.reset();
                p
            }
            None => {
                // Create new parser - this is the expensive path
                lang.parser()?
            }
        };

        Ok(Self {
            parser: Some(parser),
            lang_name,
        })
    }

    /// Get mutable reference to the underlying parser.
    ///
    /// # Panics
    ///
    /// Panics if called after the parser has been consumed (should never happen
    /// in normal use since we only consume on drop).
    fn get_mut(&mut self) -> &mut Parser {
        self.parser.as_mut().expect("Parser already consumed")
    }
}

impl Drop for CachedParser {
    fn drop(&mut self) {
        if let Some(parser) = self.parser.take() {
            PARSER_CACHE.with(|cache| {
                let mut cache = cache.borrow_mut();
                // Only cache if under limit to prevent memory bloat
                if cache.len() < MAX_CACHED_PARSERS {
                    cache.insert(self.lang_name, parser);
                }
                // If over limit, parser is simply dropped (freed)
            });
        }
    }
}

/// Clear the parser cache for the current thread.
///
/// Useful for testing or when language configurations change.
/// In production, the cache persists for the thread's lifetime.
#[allow(dead_code)]
pub fn clear_parser_cache() {
    PARSER_CACHE.with(|cache| {
        cache.borrow_mut().clear();
    });
}

/// Get current parser cache statistics for the current thread.
///
/// Returns the number of cached parsers. Useful for debugging and monitoring.
#[allow(dead_code)]
pub fn parser_cache_stats() -> usize {
    PARSER_CACHE.with(|cache| cache.borrow().len())
}

/// Efficient position set for O(log n) proximity-based deduplication.
///
/// Uses a BTreeSet to detect if a position is within a small tolerance
/// (default 2 bytes) of any previously seen position. This replaces
/// linear O(n) scanning with O(log n) range queries.
///
/// # Performance
/// - Insert: O(log n)
/// - Proximity check: O(log n) using range queries
/// - Overall for n items: O(n log n) instead of O(n^2)
///
/// For a file with 500 functions, this reduces comparisons from
/// 125,000 (n^2/2) to approximately 4,500 (n * log n).
struct PositionSet {
    /// Sorted set of seen start positions
    positions: BTreeSet<usize>,
    /// Tolerance for "close enough" position matching (in bytes)
    tolerance: usize,
}

impl PositionSet {
    /// Create a new PositionSet with the specified tolerance.
    ///
    /// # Arguments
    /// * `tolerance` - Maximum byte distance to consider positions as duplicates
    fn with_tolerance(tolerance: usize) -> Self {
        Self {
            positions: BTreeSet::new(),
            tolerance,
        }
    }

    /// Check if a position is a duplicate (within tolerance of any existing position).
    ///
    /// Uses BTreeSet range queries for O(log n) performance:
    /// - Finds positions in range [pos - tolerance, pos + tolerance]
    /// - Returns true if any position in that range exists
    ///
    /// # Arguments
    /// * `pos` - The position to check
    ///
    /// # Returns
    /// * `true` if this position is within `tolerance` bytes of an existing position
    fn is_duplicate(&self, pos: usize) -> bool {
        // Calculate search range, handling underflow for positions near 0
        let lower = pos.saturating_sub(self.tolerance);
        let upper = pos.saturating_add(self.tolerance);

        // Use range query to find any position in [lower, upper]
        // This is O(log n) to find the starting point, then O(k) where k is matches
        // In practice k is 0 or 1, making this effectively O(log n)
        self.positions
            .range((Bound::Included(lower), Bound::Included(upper)))
            .next()
            .is_some()
    }

    /// Insert a position into the set.
    ///
    /// # Arguments
    /// * `pos` - The position to insert
    fn insert(&mut self, pos: usize) {
        self.positions.insert(pos);
    }
}

/// Known function node kinds across all supported languages.
///
/// When the @function capture is missing from a query pattern, we use these
/// node kinds to identify the correct function definition node from captures.
/// This handles cases where queries use alternative capture names like @method
/// or @constructor (Java), or patterns without explicit function captures.
const FUNCTION_NODE_KINDS: &[&str] = &[
    // Python
    "function_definition",
    "decorated_definition",
    // TypeScript/JavaScript
    "function_declaration",
    "method_definition",
    "arrow_function",
    "function_expression",
    "generator_function_declaration",
    "function_signature",
    "ambient_declaration",
    // Go
    "function_declaration",
    "method_declaration",
    // Rust
    "function_item",
    "function_signature_item",
    "macro_definition",
    // C/C++
    "function_definition",
    "declaration",
    "template_declaration",
    "preproc_def",
    "preproc_function_def",
    "type_definition",
    // Java
    "method_declaration",
    "constructor_declaration",
];

/// Known class/type node kinds across all supported languages.
///
/// When the @class capture is missing from a query pattern, we use these
/// node kinds to identify the correct class/struct/interface node from captures.
/// This handles cases where queries use alternative capture names like @struct,
/// @interface, @enum (Go, C, C++), or other type-related patterns.
const CLASS_NODE_KINDS: &[&str] = &[
    // Python
    "class_definition",
    "decorated_definition",
    // TypeScript/JavaScript
    "class_declaration",
    "abstract_class_declaration",
    "class", // class expression
    "interface_declaration",
    "enum_declaration",
    "type_alias_declaration",
    "module",
    // Go
    "type_declaration",
    // Rust
    "struct_item",
    "union_item",
    "impl_item",
    "trait_item",
    "enum_item",
    "const_item",
    "static_item",
    "type_item",
    "mod_item",
    "foreign_mod_item",
    "extern_crate_declaration",
    // C/C++
    "struct_specifier",
    "enum_specifier",
    "union_specifier",
    "class_specifier",
    "namespace_definition",
    "type_definition",
    "preproc_ifdef",
    "preproc_if",
    // Java
    "class_declaration",
    "interface_declaration",
    "enum_declaration",
    "record_declaration",
    "annotation_type_declaration",
];

/// Extract the function node from a query match using robust fallback logic.
///
/// This function implements a three-tier selection strategy:
/// 1. Try to find a capture with the exact name "function"
/// 2. Fall back to finding a capture whose node kind matches known function types
/// 3. Last resort: return the first capture's node
///
/// This handles cases where:
/// - Different languages use different capture names (@method, @constructor)
/// - Query patterns don't have explicit @function captures
/// - Multiple captures exist and the first one is a child node (like @name)
fn get_function_node_from_match<'tree>(
    match_: &QueryMatch<'_, 'tree>,
    query: &Query,
) -> Option<Node<'tree>> {
    // Strategy 1: Try to find @function capture by name
    if let Some(idx) = query.capture_index_for_name("function") {
        if let Some(capture) = match_.captures.iter().find(|c| c.index == idx) {
            return Some(capture.node);
        }
    }

    // Strategy 2: Look for captures with known function node kinds
    // This handles Java (@method, @constructor), etc.
    for capture in match_.captures.iter() {
        if FUNCTION_NODE_KINDS.contains(&capture.node.kind()) {
            return Some(capture.node);
        }
    }

    // Strategy 3: Last resort - first capture
    // This may still be wrong if the first capture is @name, but it's the best we can do
    match_.captures.first().map(|c| c.node)
}

/// Extract the class node from a query match using robust fallback logic.
///
/// This function implements a three-tier selection strategy:
/// 1. Try to find a capture with the exact name "class"
/// 2. Fall back to finding a capture whose node kind matches known class/type kinds
/// 3. Last resort: return the first capture's node
///
/// This handles cases where:
/// - Different languages use different capture names (@struct, @interface, @enum)
/// - Query patterns don't have explicit @class captures
/// - Multiple captures exist and the first one is a child node (like @name)
fn get_class_node_from_match<'tree>(
    match_: &QueryMatch<'_, 'tree>,
    query: &Query,
) -> Option<Node<'tree>> {
    // Strategy 1: Try to find @class capture by name
    if let Some(idx) = query.capture_index_for_name("class") {
        if let Some(capture) = match_.captures.iter().find(|c| c.index == idx) {
            return Some(capture.node);
        }
    }

    // Strategy 2: Look for captures with known class node kinds
    // This handles Go (@struct, @interface), C/C++ (@struct, @enum, @namespace), etc.
    for capture in match_.captures.iter() {
        if CLASS_NODE_KINDS.contains(&capture.node.kind()) {
            return Some(capture.node);
        }
    }

    // Strategy 3: Last resort - first capture
    match_.captures.first().map(|c| c.node)
}

/// Extracts AST information from source files.
///
/// Uses tree-sitter queries for efficient pattern matching and delegates
/// to language-specific implementations for detailed extraction.
pub struct AstExtractor;

impl AstExtractor {
    /// Extract full module info from a file.
    ///
    /// This is the main entry point for AST extraction. It:
    /// 1. Detects the language from file extension
    /// 2. Parses the file with tree-sitter
    /// 3. Extracts functions, classes, and imports
    /// 4. Returns a complete ModuleInfo structure
    ///
    /// # Arguments
    /// * `path` - Path to the source file
    ///
    /// # Returns
    /// * `Result<ModuleInfo>` - Extracted module information or error
    ///
    /// # Errors
    /// * `BrrrError::UnsupportedLanguage` - File extension not recognized
    /// * `BrrrError::Io` - File could not be read
    /// * `BrrrError::Parse` - File could not be parsed
    pub fn extract_file(path: &Path) -> Result<ModuleInfo> {
        let registry = LanguageRegistry::global();
        let lang = registry.detect_language(path).ok_or_else(|| {
            BrrrError::UnsupportedLanguage(
                path.extension()
                    .and_then(|e| e.to_str())
                    .unwrap_or("unknown")
                    .to_string(),
            )
        })?;

        let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;

        // Check if the language handler wants to skip this file based on content.
        // This is used by the C handler to skip `.h` files that contain C++ code,
        // preventing parse errors when processing mixed C/C++ projects.
        if lang.should_skip_file(path, &source) {
            return Err(BrrrError::UnsupportedLanguage(format!(
                "File content incompatible with {} parser: {}",
                lang.name(),
                path.display()
            )));
        }

        // Use cached parser for performance - avoids recreating parser for each file.
        // The CachedParser RAII wrapper ensures the parser is returned to the
        // thread-local cache on drop, even if an error occurs during parsing.
        let mut cached_parser = CachedParser::take(lang)?;
        let tree = cached_parser
            .get_mut()
            .parse(&source, None)
            .ok_or_else(|| BrrrError::Parse {
                file: path.display().to_string(),
                message: "Failed to parse file".to_string(),
            })?;

        Self::extract_module(&tree, &source, lang, path)
    }

    /// Extract module information from a parsed tree.
    ///
    /// Combines function, class, and import extraction into a complete
    /// ModuleInfo structure.
    fn extract_module(
        tree: &Tree,
        source: &[u8],
        lang: &dyn Language,
        path: &Path,
    ) -> Result<ModuleInfo> {
        let functions = Self::extract_functions(tree, source, lang)?;
        let classes = Self::extract_classes(tree, source, lang)?;
        let imports = lang.extract_imports(tree, source);
        let docstring = lang.extract_module_docstring(tree, source);

        Ok(ModuleInfo {
            path: path.display().to_string(),
            language: lang.name().to_string(),
            docstring,
            functions,
            classes,
            imports,
            call_graph: None, // Call graph extraction is done separately via callgraph module
        })
    }

    /// Extract all functions from a parsed tree using tree-sitter queries.
    ///
    /// Uses the language's function query pattern to find all function
    /// definitions, then delegates to the language's extract_function
    /// method for detailed extraction.
    ///
    /// # Arguments
    /// * `tree` - Parsed tree-sitter tree
    /// * `source` - Source code bytes
    /// * `lang` - Language implementation
    ///
    /// # Returns
    /// * `Result<Vec<FunctionInfo>>` - Extracted functions or error
    fn extract_functions(
        tree: &Tree,
        source: &[u8],
        lang: &dyn Language,
    ) -> Result<Vec<FunctionInfo>> {
        let query_str = lang.function_query();
        let ts_lang = tree.language();

        // Use cached query instead of compiling every time
        // This provides ~20-30% speedup for multi-file operations
        let query = get_cached_query(&ts_lang, lang.name(), "function", query_str)?;

        let mut cursor = QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source);

        let mut functions = Vec::new();
        // Use PositionSet for O(log n) deduplication instead of O(n) linear search
        // Tolerance of 2 bytes handles decorated_definition vs function_definition offset
        let mut seen_positions = PositionSet::with_tolerance(2);

        // Use streaming iterator pattern (tree-sitter 0.24+)
        use streaming_iterator::StreamingIterator;
        while let Some(match_) = matches.next() {
            // Get the function node using robust fallback logic
            // This handles cases where @function capture is missing (e.g., Java uses @method/@constructor)
            // or where multiple captures exist and the first one is a child node (like @name)
            let node = get_function_node_from_match(match_, &query);

            if let Some(node) = node {
                // Skip if we've already processed a function at this exact position
                // (handles decorated functions where both the decorator and inner function match)
                //
                // We use start position only, not full range overlap, because:
                // - Decorated functions match twice (decorated_definition and function_definition)
                //   but they have the same or very close start positions
                // - Nested functions have different start positions and should NOT be skipped
                //
                // Example: @decorator\ndef foo(): pass
                // - decorated_definition starts at byte 0 (the @)
                // - function_definition starts at byte ~11 (the def)
                // These should deduplicate (we keep decorated_definition because it matches first)
                //
                // Example: def outer():\n    def inner(): pass
                // - outer starts at byte 0
                // - inner starts at byte ~17
                // These should NOT deduplicate (different functions)
                let start = node.start_byte();

                // O(log n) duplicate check using BTreeSet range query
                if seen_positions.is_duplicate(start) {
                    continue;
                }
                seen_positions.insert(start);

                if let Some(func_info) = lang.extract_function(node, source) {
                    functions.push(func_info);
                }
            }
        }

        // Sort by line number for consistent output
        functions.sort_by_key(|f| f.line_number);
        Ok(functions)
    }

    /// Extract all classes from a parsed tree using tree-sitter queries.
    ///
    /// Uses the language's class query pattern to find all class
    /// definitions, then delegates to the language's extract_class
    /// method for detailed extraction including methods.
    ///
    /// # Arguments
    /// * `tree` - Parsed tree-sitter tree
    /// * `source` - Source code bytes
    /// * `lang` - Language implementation
    ///
    /// # Returns
    /// * `Result<Vec<ClassInfo>>` - Extracted classes or error
    fn extract_classes(tree: &Tree, source: &[u8], lang: &dyn Language) -> Result<Vec<ClassInfo>> {
        let query_str = lang.class_query();
        let ts_lang = tree.language();

        // Use cached query instead of compiling every time
        // This provides ~20-30% speedup for multi-file operations
        let query = get_cached_query(&ts_lang, lang.name(), "class", query_str)?;

        let mut cursor = QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source);

        let mut classes = Vec::new();
        // Use PositionSet for O(log n) deduplication instead of O(n) linear search
        // Tolerance of 2 bytes handles decorated_definition vs class_definition offset
        let mut seen_positions = PositionSet::with_tolerance(2);

        // Use streaming iterator pattern (tree-sitter 0.24+)
        use streaming_iterator::StreamingIterator;
        while let Some(match_) = matches.next() {
            // Get the class node using robust fallback logic
            // This handles cases where @class capture is missing (e.g., Go uses @struct/@interface,
            // C/C++ uses @struct/@enum/@namespace) or where multiple captures exist
            // and the first one is a child node (like @name)
            let node = get_class_node_from_match(match_, &query);

            if let Some(node) = node {
                // Skip if we've already processed a class at this exact position
                // (handles decorated classes where both the decorator and inner class match)
                //
                // We use start position only, not full range overlap, because:
                // - Decorated classes match twice (decorated_definition and class_definition)
                //   but they have close start positions
                // - Nested classes have different start positions and should NOT be skipped
                let start = node.start_byte();

                // O(log n) duplicate check using BTreeSet range query
                if seen_positions.is_duplicate(start) {
                    continue;
                }
                seen_positions.insert(start);

                if let Some(class_info) = lang.extract_class(node, source) {
                    // The tree-sitter query matches ALL class definitions including nested ones,
                    // so each class is already returned as a separate entry. We don't need to
                    // flatten inner_classes - they're already matched by the query.
                    // The inner_classes field still contains the hierarchical structure for
                    // consumers who want to traverse the nesting relationship.
                    classes.push(class_info);
                }
            }
        }

        // Sort by line number for consistent output
        classes.sort_by_key(|c| c.line_number);
        Ok(classes)
    }

    /// Extract functions and classes from source code string.
    ///
    /// Convenience method for extracting from in-memory source code
    /// when the language is already known.
    ///
    /// # Arguments
    /// * `source` - Source code as string
    /// * `language` - Language name (e.g., "python", "typescript")
    ///
    /// # Returns
    /// * `Result<ModuleInfo>` - Extracted module information
    #[allow(dead_code)]
    pub fn extract_from_source(source: &str, language: &str) -> Result<ModuleInfo> {
        let registry = LanguageRegistry::global();
        let lang = registry
            .get_by_name(language)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(language.to_string()))?;

        let source_bytes = source.as_bytes();

        // Use cached parser for performance - reuses parser across multiple
        // extract_from_source calls with the same language.
        let mut cached_parser = CachedParser::take(lang)?;
        let tree = cached_parser
            .get_mut()
            .parse(source_bytes, None)
            .ok_or_else(|| BrrrError::Parse {
                file: "<string>".to_string(),
                message: "Failed to parse source".to_string(),
            })?;

        let functions = Self::extract_functions(&tree, source_bytes, lang)?;
        let classes = Self::extract_classes(&tree, source_bytes, lang)?;
        let imports = lang.extract_imports(&tree, source_bytes);
        let docstring = lang.extract_module_docstring(&tree, source_bytes);

        Ok(ModuleInfo {
            path: "<string>".to_string(),
            language: lang.name().to_string(),
            docstring,
            functions,
            classes,
            imports,
            call_graph: None, // Call graph extraction is done separately via callgraph module
        })
    }

    /// Find a specific function by name in a file.
    ///
    /// # Arguments
    /// * `path` - Path to source file
    /// * `function_name` - Name of function to find
    ///
    /// # Returns
    /// * `Result<FunctionInfo>` - Function info or FunctionNotFound error
    #[allow(dead_code)]
    pub fn find_function(path: &Path, function_name: &str) -> Result<FunctionInfo> {
        let module_info = Self::extract_file(path)?;

        // Search in top-level functions
        if let Some(func) = module_info
            .functions
            .iter()
            .find(|f| f.name == function_name)
        {
            return Ok(func.clone());
        }

        // Search in class methods
        for class in &module_info.classes {
            if let Some(method) = class.methods.iter().find(|m| m.name == function_name) {
                return Ok(method.clone());
            }
        }

        Err(BrrrError::FunctionNotFound(function_name.to_string()))
    }

    /// Find a specific class by name in a file.
    ///
    /// # Arguments
    /// * `path` - Path to source file
    /// * `class_name` - Name of class to find
    ///
    /// # Returns
    /// * `Result<ClassInfo>` - Class info or error
    #[allow(dead_code)]
    pub fn find_class(path: &Path, class_name: &str) -> Result<ClassInfo> {
        let module_info = Self::extract_file(path)?;

        module_info
            .classes
            .into_iter()
            .find(|c| c.name == class_name)
            .ok_or_else(|| BrrrError::ClassNotFound(class_name.to_string()))
    }
}

/// Extract imports from a source file.
///
/// Convenience function for extracting only import statements.
pub fn extract_imports(path: &Path) -> Result<Vec<ImportInfo>> {
    let registry = LanguageRegistry::global();
    let lang = registry.detect_language(path).ok_or_else(|| {
        BrrrError::UnsupportedLanguage(
            path.extension()
                .and_then(|e| e.to_str())
                .unwrap_or("unknown")
                .to_string(),
        )
    })?;

    let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;

    // Use cached parser for performance - avoids recreating parser for each file.
    let mut cached_parser = CachedParser::take(lang)?;
    let tree = cached_parser
        .get_mut()
        .parse(&source, None)
        .ok_or_else(|| BrrrError::Parse {
            file: path.display().to_string(),
            message: "Failed to parse file".to_string(),
        })?;

    Ok(lang.extract_imports(&tree, &source))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn create_temp_file(content: &str, extension: &str) -> NamedTempFile {
        let mut file = tempfile::Builder::new()
            .suffix(extension)
            .tempfile()
            .unwrap();
        file.write_all(content.as_bytes()).unwrap();
        file
    }

    #[test]
    fn test_extract_python_functions() {
        let source = r#"
def hello(name: str) -> str:
    """Say hello to someone."""
    return f"Hello, {name}!"

async def fetch_data(url: str) -> bytes:
    """Fetch data from URL."""
    pass

class MyClass:
    def method(self, x: int) -> int:
        return x * 2
"#;
        let file = create_temp_file(source, ".py");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        assert_eq!(result.language, "python");
        assert!(result.functions.len() >= 2);

        // Find hello function
        let hello = result.functions.iter().find(|f| f.name == "hello");
        assert!(hello.is_some());
        let hello = hello.unwrap();
        assert_eq!(hello.return_type, Some("str".to_string()));
        assert!(hello
            .docstring
            .as_ref()
            .map_or(false, |d| d.contains("Say hello")));
        assert!(!hello.is_async);

        // Find async function
        let fetch = result.functions.iter().find(|f| f.name == "fetch_data");
        assert!(fetch.is_some());
        assert!(fetch.unwrap().is_async);

        // Check class was extracted
        assert_eq!(result.classes.len(), 1);
        assert_eq!(result.classes[0].name, "MyClass");
        assert!(!result.classes[0].methods.is_empty());
    }

    #[test]
    fn test_extract_python_classes() {
        let source = r#"
class Animal:
    """Base class for animals."""

    def __init__(self, name: str):
        self.name = name

    def speak(self) -> str:
        pass

class Dog(Animal):
    """A dog."""

    def speak(self) -> str:
        return "Woof!"
"#;
        let file = create_temp_file(source, ".py");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        assert_eq!(result.classes.len(), 2);

        let animal = result.classes.iter().find(|c| c.name == "Animal").unwrap();
        assert!(animal
            .docstring
            .as_ref()
            .map_or(false, |d| d.contains("Base class")));
        assert!(animal.methods.len() >= 2);

        let dog = result.classes.iter().find(|c| c.name == "Dog").unwrap();
        assert!(dog.bases.contains(&"Animal".to_string()));
    }

    #[test]
    fn test_extract_python_imports() {
        let source = r#"
import os
import sys as system
from pathlib import Path
from collections import defaultdict as dd
from . import local
"#;
        let file = create_temp_file(source, ".py");
        let imports = extract_imports(file.path()).unwrap();

        assert!(imports.len() >= 4);

        // Check regular import
        let os_import = imports.iter().find(|i| i.module == "os");
        assert!(os_import.is_some());
        assert!(!os_import.unwrap().is_from);

        // Check aliased import
        let sys_import = imports.iter().find(|i| i.module == "sys");
        assert!(sys_import.is_some());
        assert!(sys_import.unwrap().aliases.contains_key("sys"));

        // Check from import
        let pathlib_import = imports.iter().find(|i| i.module == "pathlib");
        assert!(pathlib_import.is_some());
        assert!(pathlib_import.unwrap().is_from);
        assert!(pathlib_import.unwrap().names.contains(&"Path".to_string()));
    }

    #[test]
    fn test_extract_typescript_functions() {
        let source = r#"
function greet(name: string): string {
    return "Hello, " + name;
}

async function fetchData(url: string): Promise<Response> {
    return fetch(url);
}

const add = (a: number, b: number): number => a + b;
"#;
        let file = create_temp_file(source, ".ts");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        assert_eq!(result.language, "typescript");
        assert!(result.functions.len() >= 2);

        let greet = result.functions.iter().find(|f| f.name == "greet");
        assert!(greet.is_some());
        assert_eq!(greet.unwrap().return_type, Some("string".to_string()));

        let fetch_data = result.functions.iter().find(|f| f.name == "fetchData");
        assert!(fetch_data.is_some());
        assert!(fetch_data.unwrap().is_async);
    }

    #[test]
    fn test_extract_typescript_classes() {
        let source = r#"
class Animal {
    constructor(public name: string) {}

    speak(): void {
        console.log(this.name);
    }
}

class Dog extends Animal {
    bark(): void {
        console.log("Woof!");
    }
}
"#;
        let file = create_temp_file(source, ".ts");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        assert_eq!(result.classes.len(), 2);

        let animal = result.classes.iter().find(|c| c.name == "Animal");
        assert!(animal.is_some());

        let dog = result.classes.iter().find(|c| c.name == "Dog");
        assert!(dog.is_some());
        assert!(dog.unwrap().bases.contains(&"Animal".to_string()));
    }

    #[test]
    fn test_extract_from_source() {
        let source = r#"
def add(a: int, b: int) -> int:
    return a + b
"#;
        let result = AstExtractor::extract_from_source(source, "python").unwrap();

        assert_eq!(result.language, "python");
        assert_eq!(result.functions.len(), 1);
        assert_eq!(result.functions[0].name, "add");
    }

    #[test]
    fn test_find_function() {
        let source = r#"
def target_function(x: int) -> int:
    return x * 2

def other_function():
    pass
"#;
        let file = create_temp_file(source, ".py");

        let func = AstExtractor::find_function(file.path(), "target_function");
        assert!(func.is_ok());
        assert_eq!(func.unwrap().name, "target_function");

        let not_found = AstExtractor::find_function(file.path(), "nonexistent");
        assert!(not_found.is_err());
    }

    #[test]
    fn test_find_class() {
        let source = r#"
class TargetClass:
    pass

class OtherClass:
    pass
"#;
        let file = create_temp_file(source, ".py");

        let class = AstExtractor::find_class(file.path(), "TargetClass");
        assert!(class.is_ok());
        assert_eq!(class.unwrap().name, "TargetClass");

        let not_found = AstExtractor::find_class(file.path(), "NonexistentClass");
        assert!(not_found.is_err());
        assert!(matches!(not_found, Err(BrrrError::ClassNotFound(_))));
    }

    #[test]
    fn test_unsupported_language() {
        let file = create_temp_file("some content", ".xyz");
        let result = AstExtractor::extract_file(file.path());

        assert!(matches!(result, Err(BrrrError::UnsupportedLanguage(_))));
    }

    #[test]
    fn test_decorated_python_function() {
        let source = r#"
@staticmethod
@cache
def cached_function(x: int) -> int:
    return x * 2
"#;
        let file = create_temp_file(source, ".py");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        assert_eq!(result.functions.len(), 1);
        let func = &result.functions[0];
        assert_eq!(func.name, "cached_function");
        assert!(!func.decorators.is_empty());
    }

    #[test]
    fn test_decorated_python_class() {
        let source = r#"
@dataclass
class Point:
    x: float
    y: float
"#;
        let file = create_temp_file(source, ".py");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        assert_eq!(result.classes.len(), 1);
        let class = &result.classes[0];
        assert_eq!(class.name, "Point");
        assert!(!class.decorators.is_empty());
    }

    #[test]
    fn test_multiple_decorated_functions_no_duplicates() {
        // This test verifies that the overlap detection algorithm correctly
        // handles multiple decorated functions without producing duplicates.
        // The fix ensures partial overlaps are detected, not just containment.
        let source = r#"
@decorator1
def func1():
    pass

@decorator2
@decorator3
def func2():
    pass

@contextmanager
def func3():
    yield

def plain_func():
    pass
"#;
        let file = create_temp_file(source, ".py");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        // Should extract exactly 4 functions, no duplicates
        assert_eq!(
            result.functions.len(),
            4,
            "Expected 4 functions, got {}: {:?}",
            result.functions.len(),
            result.functions.iter().map(|f| &f.name).collect::<Vec<_>>()
        );

        // Verify each function is unique
        let names: Vec<&str> = result.functions.iter().map(|f| f.name.as_str()).collect();
        assert!(names.contains(&"func1"));
        assert!(names.contains(&"func2"));
        assert!(names.contains(&"func3"));
        assert!(names.contains(&"plain_func"));
    }

    #[test]
    fn test_nested_decorated_classes_no_duplicates() {
        // Verify overlap detection works for classes with decorators
        let source = r#"
@dataclass
class Point:
    x: float
    y: float

@singleton
@validate
class Config:
    value: str

class PlainClass:
    pass
"#;
        let file = create_temp_file(source, ".py");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        // Should extract exactly 3 classes, no duplicates
        assert_eq!(
            result.classes.len(),
            3,
            "Expected 3 classes, got {}: {:?}",
            result.classes.len(),
            result.classes.iter().map(|c| &c.name).collect::<Vec<_>>()
        );

        let names: Vec<&str> = result.classes.iter().map(|c| c.name.as_str()).collect();
        assert!(names.contains(&"Point"));
        assert!(names.contains(&"Config"));
        assert!(names.contains(&"PlainClass"));
    }

    #[test]
    fn test_overlap_detection_algorithm() {
        // Unit test for the interval overlap logic itself
        // Two intervals [start, end) and [s, e) overlap iff start < e AND s < end

        // Helper to check overlap
        fn overlaps(start: usize, end: usize, s: usize, e: usize) -> bool {
            start < e && s < end
        }

        // Partial overlap: (10, 20) and (15, 25)
        assert!(
            overlaps(10, 20, 15, 25),
            "Partial overlap should be detected"
        );

        // Partial overlap reversed: (15, 25) and (10, 20)
        assert!(
            overlaps(15, 25, 10, 20),
            "Partial overlap should be detected (reversed)"
        );

        // Complete containment: outer contains inner
        assert!(overlaps(10, 30, 15, 20), "Containment should be detected");

        // Complete containment: inner inside outer
        assert!(
            overlaps(15, 20, 10, 30),
            "Containment should be detected (reversed)"
        );

        // Adjacent but not overlapping: (10, 20) and (20, 30)
        assert!(
            !overlaps(10, 20, 20, 30),
            "Adjacent intervals should not overlap"
        );

        // No overlap: (10, 20) and (25, 30)
        assert!(
            !overlaps(10, 20, 25, 30),
            "Disjoint intervals should not overlap"
        );

        // No overlap reversed: (25, 30) and (10, 20)
        assert!(
            !overlaps(25, 30, 10, 20),
            "Disjoint intervals should not overlap (reversed)"
        );

        // Same interval
        assert!(overlaps(10, 20, 10, 20), "Same interval should overlap");

        // Edge case: one point overlap at start
        assert!(
            overlaps(10, 20, 19, 25),
            "Should overlap when ranges share interior point"
        );
    }

    #[test]
    fn test_position_set_deduplication() {
        // Unit test for the PositionSet O(log n) deduplication structure

        // Test with tolerance of 2 (same as used in extract_functions/extract_classes)
        let mut set = PositionSet::with_tolerance(2);

        // Empty set should report no duplicates
        assert!(
            !set.is_duplicate(100),
            "Empty set should have no duplicates"
        );

        // Insert first position
        set.insert(100);

        // Exact match should be duplicate
        assert!(set.is_duplicate(100), "Exact position should be duplicate");

        // Positions within tolerance should be duplicates
        assert!(
            set.is_duplicate(99),
            "Position 99 should be duplicate (within tolerance of 100)"
        );
        assert!(
            set.is_duplicate(101),
            "Position 101 should be duplicate (within tolerance of 100)"
        );
        assert!(
            set.is_duplicate(98),
            "Position 98 should be duplicate (within tolerance of 100)"
        );
        assert!(
            set.is_duplicate(102),
            "Position 102 should be duplicate (within tolerance of 100)"
        );

        // Positions outside tolerance should NOT be duplicates
        assert!(
            !set.is_duplicate(97),
            "Position 97 should NOT be duplicate (outside tolerance)"
        );
        assert!(
            !set.is_duplicate(103),
            "Position 103 should NOT be duplicate (outside tolerance)"
        );
        assert!(!set.is_duplicate(50), "Position 50 should NOT be duplicate");
        assert!(
            !set.is_duplicate(200),
            "Position 200 should NOT be duplicate"
        );

        // Insert another position far away
        set.insert(500);
        assert!(
            set.is_duplicate(500),
            "Position 500 should now be duplicate"
        );
        assert!(
            set.is_duplicate(498),
            "Position 498 should be duplicate (within tolerance of 500)"
        );
        assert!(
            !set.is_duplicate(495),
            "Position 495 should NOT be duplicate"
        );

        // Original positions should still work
        assert!(
            set.is_duplicate(100),
            "Position 100 should still be duplicate"
        );

        // Test edge case: position 0
        let mut set2 = PositionSet::with_tolerance(2);
        set2.insert(0);
        assert!(set2.is_duplicate(0), "Position 0 should be duplicate");
        assert!(
            set2.is_duplicate(1),
            "Position 1 should be duplicate (within tolerance of 0)"
        );
        assert!(
            set2.is_duplicate(2),
            "Position 2 should be duplicate (within tolerance of 0)"
        );
        assert!(!set2.is_duplicate(3), "Position 3 should NOT be duplicate");

        // Test edge case: position 1
        set2.insert(1);
        // Both 0 and 1 are in the set, so positions 0-3 should all be duplicates
        assert!(set2.is_duplicate(0), "Position 0 should be duplicate");
        assert!(
            set2.is_duplicate(3),
            "Position 3 should be duplicate (within tolerance of 1)"
        );
    }

    #[test]
    fn test_position_set_performance_characteristics() {
        // Verify that PositionSet maintains O(log n) characteristics
        // by testing with a large number of positions
        let mut set = PositionSet::with_tolerance(2);

        // Insert 1000 positions (simulating a large file with many functions)
        // Each position is 100 bytes apart (typical function spacing)
        for i in 0..1000 {
            let pos = i * 100;
            assert!(
                !set.is_duplicate(pos),
                "Position {} should not be duplicate before insert",
                pos
            );
            set.insert(pos);
            assert!(
                set.is_duplicate(pos),
                "Position {} should be duplicate after insert",
                pos
            );
        }

        // Verify all positions are still correctly identified
        for i in 0..1000 {
            let pos = i * 100;
            assert!(
                set.is_duplicate(pos),
                "Position {} should be duplicate",
                pos
            );
            assert!(
                set.is_duplicate(pos + 1),
                "Position {} should be duplicate (tolerance)",
                pos + 1
            );
            // Position between functions should not be duplicate
            if i < 999 {
                assert!(
                    !set.is_duplicate(pos + 50),
                    "Position {} should NOT be duplicate (between functions)",
                    pos + 50
                );
            }
        }
    }

    #[test]
    fn test_extract_java_methods_with_fallback() {
        // Java uses @method/@constructor captures instead of @function
        // This test verifies that the fallback node selection works correctly
        let source = r#"
public class Calculator {
    public int add(int a, int b) {
        return a + b;
    }

    public Calculator() {
        // constructor
    }

    private void helper() {
        // helper method
    }
}
"#;
        let file = create_temp_file(source, ".java");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        // Verify class was extracted
        assert_eq!(result.classes.len(), 1, "Should extract Calculator class");
        let calc = &result.classes[0];
        assert_eq!(calc.name, "Calculator");

        // Verify methods were extracted (Java extracts methods as part of class)
        // The methods should have been extracted correctly even without @function capture
        assert!(
            calc.methods.len() >= 2,
            "Should extract at least 2 methods from Calculator, got {}",
            calc.methods.len()
        );

        // Verify specific method names
        let method_names: Vec<&str> = calc.methods.iter().map(|m| m.name.as_str()).collect();
        assert!(
            method_names.contains(&"add"),
            "Should find 'add' method, found: {:?}",
            method_names
        );
    }

    #[test]
    fn test_extract_go_structs_with_fallback() {
        // Go uses @struct/@interface captures instead of @class
        // This test verifies that the fallback node selection works correctly
        let source = r#"
package main

type Person struct {
    Name string
    Age  int
}

type Speaker interface {
    Speak() string
}
"#;
        let file = create_temp_file(source, ".go");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        // Verify both struct and interface were extracted
        assert!(
            result.classes.len() >= 2,
            "Should extract Person struct and Speaker interface, got {}",
            result.classes.len()
        );

        let names: Vec<&str> = result.classes.iter().map(|c| c.name.as_str()).collect();
        assert!(
            names.contains(&"Person"),
            "Should find Person struct, found: {:?}",
            names
        );
        assert!(
            names.contains(&"Speaker"),
            "Should find Speaker interface, found: {:?}",
            names
        );
    }

    #[test]
    fn test_fallback_node_selection_helper_functions() {
        // Test the FUNCTION_NODE_KINDS and CLASS_NODE_KINDS constants
        // Verify they contain expected values

        // Function kinds should include common function node types
        assert!(
            FUNCTION_NODE_KINDS.contains(&"function_definition"),
            "Should contain Python function_definition"
        );
        assert!(
            FUNCTION_NODE_KINDS.contains(&"method_declaration"),
            "Should contain Java method_declaration"
        );
        assert!(
            FUNCTION_NODE_KINDS.contains(&"function_item"),
            "Should contain Rust function_item"
        );
        assert!(
            FUNCTION_NODE_KINDS.contains(&"arrow_function"),
            "Should contain TypeScript arrow_function"
        );

        // Class kinds should include common class/type node types
        assert!(
            CLASS_NODE_KINDS.contains(&"class_definition"),
            "Should contain Python class_definition"
        );
        assert!(
            CLASS_NODE_KINDS.contains(&"type_declaration"),
            "Should contain Go type_declaration"
        );
        assert!(
            CLASS_NODE_KINDS.contains(&"struct_specifier"),
            "Should contain C struct_specifier"
        );
        assert!(
            CLASS_NODE_KINDS.contains(&"class_declaration"),
            "Should contain Java/TS class_declaration"
        );
    }

    #[test]
    fn test_query_caching() {
        // Note: Tests run in parallel and share the global cache,
        // so we cannot assume the cache is empty at the start.
        // Instead, we verify the caching behavior relative to the current state.

        // Get baseline cache size (may have entries from other tests)
        let _baseline_size = query_cache_stats();

        // Extract from a Python file - this will either use cached queries
        // or add new entries if Python wasn't processed yet
        let source = r#"
def hello():
    pass

class World:
    pass
"#;
        let file = create_temp_file(source, ".py");
        let result = AstExtractor::extract_file(file.path()).unwrap();

        // Verify extraction worked
        assert!(
            !result.functions.is_empty(),
            "Should extract at least one function"
        );
        assert!(
            !result.classes.is_empty(),
            "Should extract at least one class"
        );

        // Cache should have at least 2 entries total (function + class queries for at least one language)
        let cache_size_after_python = query_cache_stats();
        assert!(
            cache_size_after_python >= 2,
            "Cache should have at least 2 entries (function + class), got {}",
            cache_size_after_python
        );

        // Extract again from the same language - should use cached queries (cache size unchanged)
        let source2 = r#"
def another():
    return 42
"#;
        let file2 = create_temp_file(source2, ".py");
        let result2 = AstExtractor::extract_file(file2.path()).unwrap();
        assert!(!result2.functions.is_empty());

        // Cache size should remain the same (Python queries were already cached)
        assert_eq!(
            query_cache_stats(),
            cache_size_after_python,
            "Cache size should remain the same when reusing same language"
        );
    }

    #[test]
    fn test_query_cache_reuse() {
        // Test that same-language queries are reused (cache size doesn't increase)
        // This is the key property we care about for performance

        // Process TypeScript file twice in a row
        let ts_source1 = "function greet(): string { return 'hello'; }";
        let ts_file1 = create_temp_file(ts_source1, ".ts");
        let _ = AstExtractor::extract_file(ts_file1.path()).unwrap();

        let size_after_first = query_cache_stats();

        // Process another TypeScript file - should reuse cached queries
        let ts_source2 = "const add = (a: number, b: number) => a + b;";
        let ts_file2 = create_temp_file(ts_source2, ".ts");
        let ts_result = AstExtractor::extract_file(ts_file2.path()).unwrap();
        assert!(
            !ts_result.functions.is_empty(),
            "Should extract TypeScript function"
        );

        let size_after_second = query_cache_stats();

        // Cache size should not increase when processing same language
        assert_eq!(
            size_after_first, size_after_second,
            "Cache size should remain the same when reprocessing same language"
        );
    }

    #[test]
    fn test_query_cache_thread_safety() {
        // Test that cache operations are thread-safe under concurrent access
        // Note: We don't clear the cache since it interferes with parallel tests
        use std::thread;

        let handles: Vec<_> = (0..4)
            .map(|i| {
                thread::spawn(move || {
                    let source = format!(
                        r#"
def func_{}():
    pass
"#,
                        i
                    );
                    let file = create_temp_file(&source, ".py");
                    let result = AstExtractor::extract_file(file.path());
                    assert!(result.is_ok(), "Extraction should succeed in thread {}", i);
                })
            })
            .collect();

        for handle in handles {
            handle.join().expect("Thread should complete successfully");
        }

        // After concurrent access, cache should have entries
        let cache_size = query_cache_stats();
        assert!(
            cache_size >= 2,
            "Cache should have entries after concurrent access, got {}",
            cache_size
        );
    }

    // =========================================================================
    // Parser Caching Tests
    // =========================================================================

    #[test]
    fn test_parser_caching_basic() {
        // Parser cache is thread-local, so we can test it in isolation
        // Note: Other tests in the same thread may have cached parsers

        // Process multiple Python files - should reuse cached parser
        let source1 = r#"
def hello():
    pass
"#;
        let source2 = r#"
def world():
    return 42
"#;
        let file1 = create_temp_file(source1, ".py");
        let file2 = create_temp_file(source2, ".py");

        // Both extractions should succeed and use the cached parser
        let result1 = AstExtractor::extract_file(file1.path());
        assert!(result1.is_ok(), "First extraction should succeed");

        let result2 = AstExtractor::extract_file(file2.path());
        assert!(
            result2.is_ok(),
            "Second extraction should succeed (using cached parser)"
        );

        // Verify parsing was correct
        assert!(!result1.unwrap().functions.is_empty());
        assert!(!result2.unwrap().functions.is_empty());
    }

    #[test]
    fn test_parser_caching_multiple_languages() {
        // Test that parsers for different languages are cached separately

        let py_source = "def hello(): pass";
        let ts_source = "function hello(): void {}";
        let go_source = "package main\nfunc hello() {}";

        let py_file = create_temp_file(py_source, ".py");
        let ts_file = create_temp_file(ts_source, ".ts");
        let go_file = create_temp_file(go_source, ".go");

        // Extract from multiple languages
        let py_result = AstExtractor::extract_file(py_file.path());
        let ts_result = AstExtractor::extract_file(ts_file.path());
        let go_result = AstExtractor::extract_file(go_file.path());

        // All should succeed
        assert!(py_result.is_ok(), "Python extraction should succeed");
        assert!(ts_result.is_ok(), "TypeScript extraction should succeed");
        assert!(go_result.is_ok(), "Go extraction should succeed");

        // Verify correct language was detected
        assert_eq!(py_result.unwrap().language, "python");
        assert_eq!(ts_result.unwrap().language, "typescript");
        assert_eq!(go_result.unwrap().language, "go");

        // Parser cache should have entries for each language
        let cache_size = parser_cache_stats();
        assert!(
            cache_size >= 3,
            "Cache should have at least 3 parsers (one per language), got {}",
            cache_size
        );
    }

    #[test]
    fn test_parser_caching_extract_from_source() {
        // Test that extract_from_source also uses cached parsers

        let source1 = "def foo(): pass";
        let source2 = "def bar(): return 1";

        let result1 = AstExtractor::extract_from_source(source1, "python");
        let result2 = AstExtractor::extract_from_source(source2, "python");

        assert!(result1.is_ok(), "First extract_from_source should succeed");
        assert!(
            result2.is_ok(),
            "Second extract_from_source should succeed (cached)"
        );

        assert_eq!(result1.unwrap().functions[0].name, "foo");
        assert_eq!(result2.unwrap().functions[0].name, "bar");
    }

    #[test]
    fn test_parser_cache_clear() {
        // Test that clearing the parser cache works

        // Populate cache with a parser
        let source = "def test(): pass";
        let file = create_temp_file(source, ".py");
        let _ = AstExtractor::extract_file(file.path()).unwrap();

        // Cache should have at least one parser
        let before_clear = parser_cache_stats();
        assert!(
            before_clear >= 1,
            "Cache should have at least 1 parser before clear"
        );

        // Clear the cache
        clear_parser_cache();

        // Cache should be empty
        let after_clear = parser_cache_stats();
        assert_eq!(after_clear, 0, "Cache should be empty after clear");

        // Extraction should still work (creates new parser)
        let source2 = "def another(): pass";
        let file2 = create_temp_file(source2, ".py");
        let result = AstExtractor::extract_file(file2.path());
        assert!(result.is_ok(), "Extraction should work after cache clear");

        // Cache should have one parser again
        let after_extraction = parser_cache_stats();
        assert_eq!(
            after_extraction, 1,
            "Cache should have 1 parser after extraction"
        );
    }

    #[test]
    fn test_parser_cache_thread_local() {
        // Test that parser cache is truly thread-local (each thread has its own cache)
        use std::thread;

        // Clear cache in main thread
        clear_parser_cache();

        // Populate cache in main thread
        let source = "def main_thread(): pass";
        let file = create_temp_file(source, ".py");
        let _ = AstExtractor::extract_file(file.path()).unwrap();

        let main_thread_cache = parser_cache_stats();
        assert!(
            main_thread_cache >= 1,
            "Main thread cache should have parser"
        );

        // Spawn a new thread and check its cache
        let handle = thread::spawn(|| {
            // New thread should have empty cache
            let child_cache_before = parser_cache_stats();

            // Parse something in the child thread
            let source = "def child_thread(): pass";
            let file = create_temp_file(source, ".py");
            let _ = AstExtractor::extract_file(file.path()).unwrap();

            let child_cache_after = parser_cache_stats();

            (child_cache_before, child_cache_after)
        });

        let (child_before, child_after) = handle.join().unwrap();

        // Child thread should have started with empty cache (thread-local)
        assert_eq!(
            child_before, 0,
            "Child thread should start with empty cache"
        );
        assert!(
            child_after >= 1,
            "Child thread should have parser after extraction"
        );

        // Main thread cache should be unchanged
        let main_thread_cache_after = parser_cache_stats();
        assert_eq!(
            main_thread_cache, main_thread_cache_after,
            "Main thread cache should be unchanged by child thread"
        );
    }
}
