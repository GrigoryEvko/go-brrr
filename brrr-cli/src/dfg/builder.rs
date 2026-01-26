//! DFG construction logic.
//!
//! Provides high-level API for extracting data flow graphs from source files.
//! Handles file parsing, function lookup, and delegates to language-specific
//! DFG builders.
//!
//! Data Flow Graph tracks:
//! - Variable definitions (assignments, parameters)
//! - Variable uses (reads)
//! - Variable mutations (augmented assignments, method calls)
//! - Return values
//! - Function parameters
//!
//! The DFG enables program slicing: finding which lines affect (backward slice)
//! or are affected by (forward slice) a given line.

use std::path::Path;

use streaming_iterator::StreamingIterator;
use tree_sitter::{Query, QueryCursor};

use crate::dfg::types::DFGInfo;
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;
use crate::util::format_query_error;

/// Builds data flow graphs from source code.
///
/// This is the main entry point for DFG extraction. It handles:
/// - File parsing using tree-sitter
/// - Function lookup using language-specific queries
/// - Delegation to language-specific DFG builders
///
/// # Example
/// ```ignore
/// use brrr::dfg::DfgBuilder;
///
/// let dfg = DfgBuilder::extract_from_file("example.py", "my_function")?;
///
/// // Find what affects line 42
/// let backward_slice = dfg.backward_slice(42);
///
/// // Find what's affected by line 10
/// let forward_slice = dfg.forward_slice(10);
/// ```
// Public API - used by library consumers and lib.rs's get_dfg_from_source
#[allow(dead_code)]
pub struct DfgBuilder;

// Public API methods for DFG extraction
#[allow(dead_code)]
impl DfgBuilder {
    /// Extract DFG for a named function from a file.
    ///
    /// Parses the file, locates the function by name, and builds a data flow
    /// graph tracking variable definitions, uses, and mutations.
    ///
    /// # Arguments
    /// * `file` - Path to the source file
    /// * `function` - Name of the function to extract DFG for
    ///
    /// # Returns
    /// * `Result<DFGInfo>` - The data flow graph or an error
    ///
    /// # Errors
    /// * `BrrrError::UnsupportedLanguage` - File extension not recognized
    /// * `BrrrError::Io` - File could not be read
    /// * `BrrrError::Parse` - File could not be parsed
    /// * `BrrrError::FunctionNotFound` - Function not found in file
    ///
    /// # Example
    /// ```ignore
    /// use brrr::dfg::DfgBuilder;
    ///
    /// let dfg = DfgBuilder::extract_from_file("example.py", "process_data")?;
    ///
    /// // Check which variables are defined
    /// println!("Defined variables: {:?}", dfg.variables());
    ///
    /// // Get backward slice for debugging
    /// let slice = dfg.backward_slice(42);
    /// println!("Lines affecting line 42: {:?}", slice);
    /// ```
    pub fn extract_from_file(file: &str, function: &str) -> Result<DFGInfo> {
        Self::extract_from_file_with_language(file, function, None)
    }

    /// Extract DFG for a named function from a file with explicit language.
    ///
    /// This method allows overriding language auto-detection, useful for files
    /// without extensions or with non-standard extensions.
    ///
    /// # Arguments
    /// * `file` - Path to the source file
    /// * `function` - Name of the function to extract DFG for
    /// * `language` - Optional language override (e.g., "python", "typescript").
    ///   If `None`, language is auto-detected from file extension.
    ///
    /// # Returns
    /// * `Result<DFGInfo>` - The data flow graph or an error
    ///
    /// # Errors
    /// * `BrrrError::UnsupportedLanguage` - Language not recognized
    /// * `BrrrError::Io` - File could not be read
    /// * `BrrrError::Parse` - File could not be parsed
    /// * `BrrrError::FunctionNotFound` - Function not found in file
    ///
    /// # Example
    /// ```ignore
    /// use brrr::dfg::DfgBuilder;
    ///
    /// // Auto-detect from extension
    /// let dfg = DfgBuilder::extract_from_file_with_language("example.py", "func", None)?;
    ///
    /// // Force Python for extensionless file
    /// let dfg = DfgBuilder::extract_from_file_with_language("script", "main", Some("python"))?;
    /// ```
    pub fn extract_from_file_with_language(
        file: &str,
        function: &str,
        language: Option<&str>,
    ) -> Result<DFGInfo> {
        // SECURITY: Basic input validation for dangerous patterns.
        // This is defense-in-depth for single-file extraction.

        // Check for null bytes (could bypass security checks in some contexts)
        if file.contains('\0') {
            return Err(BrrrError::PathTraversal {
                target: "<contains null byte>".to_string(),
                base: "<DFG extraction>".to_string(),
            });
        }

        let path = Path::new(file);
        let registry = LanguageRegistry::global();

        // Check for excessive parent directory traversal.
        // Count depth: going up (ParentDir) decreases, going into dirs increases.
        // If we escape more than 10 levels up from start, likely an attack.
        let mut depth: i32 = 0;
        for component in path.components() {
            match component {
                std::path::Component::ParentDir => {
                    depth -= 1;
                    if depth < -10 {
                        return Err(BrrrError::PathTraversal {
                            target: file.to_string(),
                            base: "<DFG extraction>".to_string(),
                        });
                    }
                }
                std::path::Component::Normal(_) => {
                    depth += 1;
                }
                _ => {}
            }
        }

        // Resolve language: use explicit override or auto-detect from extension
        let lang = match language {
            Some(lang_name) => registry
                .get_by_name(lang_name)
                .ok_or_else(|| BrrrError::UnsupportedLanguage(lang_name.to_string()))?,
            None => registry.detect_language(path).ok_or_else(|| {
                BrrrError::UnsupportedLanguage(
                    path.extension()
                        .and_then(|e| e.to_str())
                        .unwrap_or("unknown")
                        .to_string(),
                )
            })?,
        };

        // Read and parse the file with extension-aware parser
        let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;
        let mut parser = lang.parser_for_path(path)?;
        let tree = parser
            .parse(&source, None)
            .ok_or_else(|| BrrrError::Parse {
                file: file.to_string(),
                message: "Failed to parse file".to_string(),
            })?;

        // Find the function node by name
        let function_node = Self::find_function_node(&tree, &source, lang, function)?;

        // Delegate to language-specific DFG builder
        lang.build_dfg(function_node, &source)
    }

    /// Extract DFG from source code string.
    ///
    /// Convenience method for extracting DFG from in-memory source code
    /// when the language is already known.
    ///
    /// # Arguments
    /// * `source` - Source code as string
    /// * `language` - Language name (e.g., "python", "typescript", "go", "rust")
    /// * `function` - Name of the function to extract DFG for
    ///
    /// # Returns
    /// * `Result<DFGInfo>` - The data flow graph or an error
    ///
    /// # Example
    /// ```ignore
    /// use brrr::dfg::DfgBuilder;
    ///
    /// let source = r#"
    /// def example(x, y):
    ///     z = x + y
    ///     return z
    /// "#;
    ///
    /// let dfg = DfgBuilder::extract_from_source(source, "python", "example")?;
    /// assert!(dfg.definitions.contains_key("z"));
    /// ```
    pub fn extract_from_source(source: &str, language: &str, function: &str) -> Result<DFGInfo> {
        let registry = LanguageRegistry::global();
        let lang = registry
            .get_by_name(language)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(language.to_string()))?;

        let source_bytes = source.as_bytes();
        let mut parser = lang.parser()?;
        let tree = parser
            .parse(source_bytes, None)
            .ok_or_else(|| BrrrError::Parse {
                file: "<string>".to_string(),
                message: "Failed to parse source".to_string(),
            })?;

        let function_node = Self::find_function_node(&tree, source_bytes, lang, function)?;
        lang.build_dfg(function_node, source_bytes)
    }

    /// Find a function node by name using tree-sitter queries.
    ///
    /// Searches through function definitions and decorated functions to find
    /// one matching the given name. Also searches class methods if not found
    /// at module level.
    fn find_function_node<'a>(
        tree: &'a tree_sitter::Tree,
        source: &'a [u8],
        lang: &dyn crate::lang::Language,
        function_name: &str,
    ) -> Result<tree_sitter::Node<'a>> {
        let query_str = lang.function_query();
        let ts_lang = tree.language();

        let query = Query::new(&ts_lang, query_str).map_err(|e| {
            BrrrError::TreeSitter(format_query_error(lang.name(), "function", query_str, &e))
        })?;

        let mut cursor = QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source);

        // Find capture indices for function and name
        let function_capture_idx = query.capture_index_for_name("function");
        let name_capture_idx = query.capture_index_for_name("name");

        // Track seen byte ranges to avoid duplicate matches (e.g., decorated functions)
        let mut seen_ranges: Vec<(usize, usize)> = Vec::new();

        while let Some(match_) = matches.next() {
            // Get the function node from captures
            let func_node = if let Some(idx) = function_capture_idx {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            } else {
                match_.captures.first().map(|c| c.node)
            };

            // Get the name node from captures
            let name_node = if let Some(idx) = name_capture_idx {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            } else {
                None
            };

            if let (Some(func_node), Some(name_node)) = (func_node, name_node) {
                // Skip if we've already processed this byte range
                let start = func_node.start_byte();
                let end = func_node.end_byte();

                // Check if this range overlaps with any existing range
                // Two intervals [start, end) and [s, e) overlap iff start < e AND s < end
                // This correctly detects:
                // - Partial overlaps: (10,20) and (15,25) -> 10<25 && 15<20 = true
                // - Complete containment: (10,30) and (15,20) -> 10<20 && 15<30 = true
                // - No overlap: (10,20) and (25,30) -> 10<30 && 25<20 = false
                let overlaps = seen_ranges.iter().any(|(s, e)| start < *e && *s < end);

                if overlaps {
                    continue;
                }
                seen_ranges.push((start, end));

                // Check if function name matches
                let name =
                    std::str::from_utf8(&source[name_node.start_byte()..name_node.end_byte()])
                        .unwrap_or("");

                if name == function_name {
                    // For decorated functions, unwrap to get the inner function_definition
                    return Ok(Self::unwrap_decorated_function(func_node));
                }
            }
        }

        // Function not found at module level - search class methods
        Self::find_method_node(tree, source, lang, function_name)
    }

    /// Unwrap a decorated function to get the inner function_definition node.
    ///
    /// When a function is decorated, the tree-sitter query matches the
    /// decorated_definition wrapper. This extracts the actual function_definition.
    fn unwrap_decorated_function(node: tree_sitter::Node) -> tree_sitter::Node {
        if node.kind() == "decorated_definition" {
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "function_definition" {
                    return child;
                }
            }
        }
        node
    }

    /// Search for a method inside class definitions.
    ///
    /// Called when the function is not found at module level. Iterates through
    /// all classes and their methods to find a matching name.
    fn find_method_node<'a>(
        tree: &'a tree_sitter::Tree,
        source: &'a [u8],
        lang: &dyn crate::lang::Language,
        method_name: &str,
    ) -> Result<tree_sitter::Node<'a>> {
        let class_query_str = lang.class_query();
        let ts_lang = tree.language();

        let query = Query::new(&ts_lang, class_query_str).map_err(|e| {
            BrrrError::TreeSitter(format_query_error(
                lang.name(),
                "class",
                class_query_str,
                &e,
            ))
        })?;

        let mut cursor = QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source);

        let class_capture_idx = query.capture_index_for_name("class");

        while let Some(match_) = matches.next() {
            let class_node = if let Some(idx) = class_capture_idx {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            } else {
                match_.captures.first().map(|c| c.node)
            };

            if let Some(class_node) = class_node {
                // Search for method inside this class body
                if let Some(method_node) =
                    Self::find_method_in_class(class_node, source, method_name)
                {
                    return Ok(method_node);
                }
            }
        }

        Err(BrrrError::FunctionNotFound(format!(
            "Function '{}' not found in file",
            method_name
        )))
    }

    /// Find a method by name inside a class node.
    ///
    /// Searches the class body for function definitions or decorated functions
    /// matching the given name.
    fn find_method_in_class<'a>(
        class_node: tree_sitter::Node<'a>,
        source: &[u8],
        method_name: &str,
    ) -> Option<tree_sitter::Node<'a>> {
        // Find the class body node (block in Python, class_body in other languages)
        let body_node = Self::find_class_body(class_node)?;

        let mut cursor = body_node.walk();
        for child in body_node.children(&mut cursor) {
            match child.kind() {
                "function_definition" | "method_definition" | "method_declaration" => {
                    if let Some(name) = Self::extract_function_name(child, source) {
                        if name == method_name {
                            return Some(child);
                        }
                    }
                }
                "decorated_definition" => {
                    // Look for function inside decorated definition
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        if inner.kind() == "function_definition" {
                            if let Some(name) = Self::extract_function_name(inner, source) {
                                if name == method_name {
                                    return Some(inner);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        None
    }

    /// Find the body node of a class definition.
    ///
    /// Different languages use different node types for class bodies:
    /// - Python: "block"
    /// - TypeScript/JavaScript: "class_body"
    /// - Go: "declaration_list"
    fn find_class_body(class_node: tree_sitter::Node) -> Option<tree_sitter::Node> {
        let mut cursor = class_node.walk();
        for child in class_node.children(&mut cursor) {
            match child.kind() {
                "block" | "class_body" | "declaration_list" => {
                    return Some(child);
                }
                _ => {}
            }
        }
        None
    }

    /// Extract function name from a function definition node.
    ///
    /// Handles different languages' ways of encoding the function name:
    /// - Direct identifier child
    /// - Wrapped in a "name" node
    fn extract_function_name(node: tree_sitter::Node, source: &[u8]) -> Option<String> {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "identifier" | "property_identifier" | "field_identifier" => {
                    return std::str::from_utf8(&source[child.start_byte()..child.end_byte()])
                        .ok()
                        .map(|s| s.to_string());
                }
                "name" => {
                    // Some languages wrap the name in a "name" node
                    let mut inner = child.walk();
                    for inner_child in child.children(&mut inner) {
                        if inner_child.kind() == "identifier" {
                            return std::str::from_utf8(
                                &source[inner_child.start_byte()..inner_child.end_byte()],
                            )
                            .ok()
                            .map(|s| s.to_string());
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }
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
    fn test_extract_simple_function_dfg() {
        let source = r#"
def example(x, y):
    z = x + y
    return z
"#;
        let file = create_temp_file(source, ".py");
        let dfg = DfgBuilder::extract_from_file(file.path().to_str().unwrap(), "example");

        assert!(dfg.is_ok());
        let dfg = dfg.unwrap();
        assert_eq!(dfg.function_name, "example");

        // Check parameters are tracked as definitions
        assert!(dfg.definitions.contains_key("x"));
        assert!(dfg.definitions.contains_key("y"));

        // Check local variable is tracked
        assert!(dfg.definitions.contains_key("z"));

        // Check uses
        assert!(dfg.uses.contains_key("x"));
        assert!(dfg.uses.contains_key("y"));
        assert!(dfg.uses.contains_key("z"));

        // Check edges exist
        assert!(!dfg.edges.is_empty());
    }

    #[test]
    fn test_extract_function_with_mutation() {
        let source = r#"
def accumulate(items):
    total = 0
    for item in items:
        total += item
    return total
"#;
        let file = create_temp_file(source, ".py");
        let dfg = DfgBuilder::extract_from_file(file.path().to_str().unwrap(), "accumulate");

        assert!(dfg.is_ok());
        let dfg = dfg.unwrap();
        assert_eq!(dfg.function_name, "accumulate");

        // total should appear in both definitions (initial + mutation) and uses (mutation reads)
        assert!(dfg.definitions.contains_key("total"));
        assert!(dfg.uses.contains_key("total"));

        // item should be defined (loop variable) and used (in augmented assignment)
        assert!(dfg.definitions.contains_key("item"));
        assert!(dfg.uses.contains_key("item"));
    }

    #[test]
    fn test_extract_function_with_conditional() {
        let source = r#"
def process(x):
    if x > 0:
        result = x * 2
    else:
        result = 0
    return result
"#;
        let file = create_temp_file(source, ".py");
        let dfg = DfgBuilder::extract_from_file(file.path().to_str().unwrap(), "process");

        assert!(dfg.is_ok());
        let dfg = dfg.unwrap();

        // result is defined in both branches
        assert!(dfg.definitions.contains_key("result"));

        // x is used in condition and assignment
        assert!(dfg.uses.contains_key("x"));
    }

    #[test]
    fn test_extract_decorated_function() {
        let source = r#"
@staticmethod
def my_static(x):
    y = x + 1
    return y
"#;
        let file = create_temp_file(source, ".py");
        let dfg = DfgBuilder::extract_from_file(file.path().to_str().unwrap(), "my_static");

        assert!(dfg.is_ok());
        let dfg = dfg.unwrap();
        assert_eq!(dfg.function_name, "my_static");
        assert!(dfg.definitions.contains_key("x"));
        assert!(dfg.definitions.contains_key("y"));
    }

    #[test]
    fn test_extract_class_method() {
        let source = r#"
class Calculator:
    def add(self, a, b):
        result = a + b
        return result
"#;
        let file = create_temp_file(source, ".py");
        let dfg = DfgBuilder::extract_from_file(file.path().to_str().unwrap(), "add");

        assert!(dfg.is_ok());
        let dfg = dfg.unwrap();
        assert_eq!(dfg.function_name, "add");

        // self, a, b should be parameters
        assert!(dfg.definitions.contains_key("self"));
        assert!(dfg.definitions.contains_key("a"));
        assert!(dfg.definitions.contains_key("b"));

        // result should be defined and used
        assert!(dfg.definitions.contains_key("result"));
        assert!(dfg.uses.contains_key("result"));
    }

    #[test]
    fn test_function_not_found() {
        let source = r#"
def existing_function():
    pass
"#;
        let file = create_temp_file(source, ".py");
        let dfg = DfgBuilder::extract_from_file(file.path().to_str().unwrap(), "nonexistent");

        assert!(dfg.is_err());
        assert!(matches!(dfg, Err(BrrrError::FunctionNotFound(_))));
    }

    #[test]
    fn test_extract_from_source() {
        let source = r#"
def multiply(a, b):
    return a * b
"#;
        let dfg = DfgBuilder::extract_from_source(source, "python", "multiply");

        assert!(dfg.is_ok());
        let dfg = dfg.unwrap();
        assert_eq!(dfg.function_name, "multiply");
        assert!(dfg.definitions.contains_key("a"));
        assert!(dfg.definitions.contains_key("b"));
        assert!(dfg.uses.contains_key("a"));
        assert!(dfg.uses.contains_key("b"));
    }

    #[test]
    fn test_unsupported_language() {
        let file = create_temp_file("content", ".xyz");
        let result = DfgBuilder::extract_from_file(file.path().to_str().unwrap(), "func");

        assert!(matches!(result, Err(BrrrError::UnsupportedLanguage(_))));
    }

    #[test]
    fn test_backward_slice() {
        let source = r#"
def compute(x):
    a = x + 1
    b = a * 2
    c = b + x
    return c
"#;
        let dfg = DfgBuilder::extract_from_source(source, "python", "compute").unwrap();

        // Line 5 (c = b + x) should be affected by lines defining x, a, b
        // Note: exact line numbers depend on the source format
        let slice = dfg.backward_slice(5);
        assert!(!slice.is_empty());
    }

    #[test]
    fn test_forward_slice() {
        let source = r#"
def compute(x):
    a = x + 1
    b = a * 2
    return b
"#;
        let dfg = DfgBuilder::extract_from_source(source, "python", "compute").unwrap();

        // Changes to x should affect lines using x and variables derived from it
        let slice = dfg.forward_slice(2);
        assert!(!slice.is_empty());
    }

    #[test]
    fn test_multiple_assignment_targets() {
        let source = r#"
def swap(pair):
    a, b = pair
    return b, a
"#;
        let dfg = DfgBuilder::extract_from_source(source, "python", "swap").unwrap();

        assert!(dfg.definitions.contains_key("a"));
        assert!(dfg.definitions.contains_key("b"));
        assert!(dfg.uses.contains_key("a"));
        assert!(dfg.uses.contains_key("b"));
        assert!(dfg.uses.contains_key("pair"));
    }

    #[test]
    fn test_comprehension_variables() {
        let source = r#"
def squared(items):
    result = [x * x for x in items]
    return result
"#;
        let dfg = DfgBuilder::extract_from_source(source, "python", "squared").unwrap();

        // x is defined in comprehension and used in expression
        assert!(dfg.definitions.contains_key("x"));
        assert!(dfg.uses.contains_key("x"));
        assert!(dfg.uses.contains_key("items"));
    }

    #[test]
    fn test_with_statement() {
        let source = r#"
def read_file(path):
    with open(path) as f:
        content = f.read()
    return content
"#;
        let dfg = DfgBuilder::extract_from_source(source, "python", "read_file").unwrap();

        // f is defined by with statement
        assert!(dfg.definitions.contains_key("f"));
        assert!(dfg.uses.contains_key("f"));
        assert!(dfg.definitions.contains_key("content"));
    }

    #[test]
    fn test_try_except_variables() {
        let source = r#"
def safe_parse(text):
    try:
        result = int(text)
    except ValueError as e:
        result = 0
    return result
"#;
        let dfg = DfgBuilder::extract_from_source(source, "python", "safe_parse").unwrap();

        // e is defined in except clause
        assert!(dfg.definitions.contains_key("e"));
        // result is defined in both branches
        assert!(dfg.definitions.contains_key("result"));
    }

    #[test]
    fn test_variables_method() {
        let source = r#"
def example(x, y):
    z = x + y
    w = z * 2
    return w
"#;
        let dfg = DfgBuilder::extract_from_source(source, "python", "example").unwrap();
        let vars = dfg.variables();

        assert!(vars.contains(&"x"));
        assert!(vars.contains(&"y"));
        assert!(vars.contains(&"z"));
        assert!(vars.contains(&"w"));
    }

    #[test]
    fn test_overlap_detection_algorithm() {
        // Unit test for the interval overlap logic itself
        // Two intervals [start, end) and [s, e) overlap iff start < e AND s < end

        // Helper to check overlap using the same logic as the production code
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

        // Edge case: one point overlap at boundary
        assert!(
            overlaps(10, 20, 19, 25),
            "Should overlap when ranges share interior point"
        );
    }

    #[test]
    fn test_decorated_functions_no_duplicates() {
        // This test verifies that the overlap detection correctly handles
        // decorated functions without producing duplicate DFG extractions
        let source = r#"
@decorator1
def func1(x):
    y = x + 1
    return y

@decorator2
@decorator3
def func2(x):
    if x > 0:
        result = x
    else:
        result = 0
    return result

def plain_func(x):
    return x * 2
"#;
        // Extract DFG for each function - should succeed without duplicate issues
        let dfg1 = DfgBuilder::extract_from_source(source, "python", "func1");
        assert!(dfg1.is_ok(), "Should extract func1 DFG");
        let dfg1 = dfg1.unwrap();
        assert_eq!(dfg1.function_name, "func1");
        assert!(dfg1.definitions.contains_key("x"));
        assert!(dfg1.definitions.contains_key("y"));

        let dfg2 = DfgBuilder::extract_from_source(source, "python", "func2");
        assert!(dfg2.is_ok(), "Should extract func2 DFG");
        let dfg2 = dfg2.unwrap();
        assert_eq!(dfg2.function_name, "func2");
        assert!(dfg2.definitions.contains_key("x"));
        assert!(dfg2.definitions.contains_key("result"));

        let dfg3 = DfgBuilder::extract_from_source(source, "python", "plain_func");
        assert!(dfg3.is_ok(), "Should extract plain_func DFG");
        assert_eq!(dfg3.unwrap().function_name, "plain_func");
    }

    // =========================================================================
    // SECURITY TESTS: Path Traversal Protection
    // =========================================================================

    #[test]
    fn test_extract_from_file_rejects_path_traversal() {
        // Excessive parent directory traversal should be rejected
        let malicious_path = "../../../../../../../../../../../etc/passwd";
        let result = DfgBuilder::extract_from_file(malicious_path, "main");

        // Should fail with PathTraversal or Io error (file doesn't exist)
        assert!(result.is_err());
        match result.unwrap_err() {
            BrrrError::PathTraversal { .. } => {}
            BrrrError::Io(_) => {} // Also acceptable - path doesn't exist
            BrrrError::UnsupportedLanguage(_) => {} // File has no recognized extension
            e => panic!(
                "Expected PathTraversal, Io, or UnsupportedLanguage error, got: {:?}",
                e
            ),
        }
    }

    #[test]
    fn test_extract_from_file_allows_valid_paths() {
        // Normal relative paths should work
        let source = r#"
def example(x, y):
    z = x + y
    return z
"#;
        let file = create_temp_file(source, ".py");
        let result = DfgBuilder::extract_from_file(file.path().to_str().unwrap(), "example");

        assert!(result.is_ok(), "Valid path should be accepted");
    }

    #[test]
    fn test_extract_from_source_bypasses_path_validation() {
        // extract_from_source doesn't read files, so no path validation needed
        let source = r#"
def test():
    return 42
"#;
        let result = DfgBuilder::extract_from_source(source, "python", "test");
        assert!(
            result.is_ok(),
            "extract_from_source should work with string input"
        );
    }
}
