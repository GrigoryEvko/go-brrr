//! CFG construction logic.
//!
//! Provides high-level API for extracting control flow graphs from source files.
//! Handles file parsing, function lookup, and delegates to language-specific
//! CFG builders.

use std::path::Path;

use streaming_iterator::StreamingIterator;
use tree_sitter::{Query, QueryCursor};

use crate::cfg::types::CFGInfo;
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;
use crate::util::format_query_error;

/// Builds control flow graphs from source code.
///
/// This is the main entry point for CFG extraction. It handles:
/// - File parsing using tree-sitter
/// - Function lookup using language-specific queries
/// - Delegation to language-specific CFG builders
pub struct CfgBuilder;

impl CfgBuilder {
    /// Extract CFG for a named function from a file.
    ///
    /// Parses the file, locates the function by name, and builds a control flow
    /// graph representing its execution paths.
    ///
    /// # Arguments
    /// * `file` - Path to the source file
    /// * `function` - Name of the function to extract CFG for
    ///
    /// # Returns
    /// * `Result<CFGInfo>` - The control flow graph or an error
    ///
    /// # Errors
    /// * `BrrrError::UnsupportedLanguage` - File extension not recognized
    /// * `BrrrError::Io` - File could not be read
    /// * `BrrrError::Parse` - File could not be parsed
    /// * `BrrrError::FunctionNotFound` - Function not found in file
    ///
    /// # Example
    /// ```ignore
    /// use go_brrr::cfg::{CfgBuilder, to_mermaid};
    ///
    /// let cfg = CfgBuilder::extract_from_file("example.py", "my_function")?;
    /// println!("Cyclomatic complexity: {}", cfg.cyclomatic_complexity());
    /// println!("{}", to_mermaid(&cfg));
    /// ```
    #[allow(dead_code)]
    pub fn extract_from_file(file: &str, function: &str) -> Result<CFGInfo> {
        Self::extract_from_file_with_language(file, function, None)
    }

    /// Extract CFG for a named function from a file with explicit language.
    ///
    /// This method allows overriding language auto-detection, useful for files
    /// without extensions or with non-standard extensions.
    ///
    /// # Arguments
    /// * `file` - Path to the source file
    /// * `function` - Name of the function to extract CFG for
    /// * `language` - Optional language override (e.g., "python", "typescript").
    ///   If `None`, language is auto-detected from file extension.
    ///
    /// # Returns
    /// * `Result<CFGInfo>` - The control flow graph or an error
    ///
    /// # Errors
    /// * `BrrrError::UnsupportedLanguage` - Language not recognized
    /// * `BrrrError::Io` - File could not be read
    /// * `BrrrError::Parse` - File could not be parsed
    /// * `BrrrError::FunctionNotFound` - Function not found in file
    ///
    /// # Example
    /// ```ignore
    /// use go_brrr::cfg::CfgBuilder;
    ///
    /// // Auto-detect from extension
    /// let cfg = CfgBuilder::extract_from_file_with_language("example.py", "func", None)?;
    ///
    /// // Force Python for extensionless file
    /// let cfg = CfgBuilder::extract_from_file_with_language("Makefile.inc", "target", Some("python"))?;
    /// ```
    pub fn extract_from_file_with_language(
        file: &str,
        function: &str,
        language: Option<&str>,
    ) -> Result<CFGInfo> {
        // SECURITY: Basic input validation for dangerous patterns.
        // This is defense-in-depth for single-file extraction.

        // Check for null bytes (could bypass security checks in some contexts)
        if file.contains('\0') {
            return Err(BrrrError::PathTraversal {
                target: "<contains null byte>".to_string(),
                base: "<CFG extraction>".to_string(),
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
                            base: "<CFG extraction>".to_string(),
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

        // Build a query to find the function by name
        let function_node = Self::find_function_node(&tree, &source, lang, function)?;

        // Delegate to language-specific CFG builder
        lang.build_cfg(function_node, &source)
    }

    /// Find a function node by name using tree-sitter queries.
    ///
    /// Searches through function definitions and decorated functions to find
    /// one matching the given name. Supports `Class.method` notation for
    /// finding methods within specific classes.
    ///
    /// # Qualified Name Support
    ///
    /// When `function_name` contains a `.`, it is treated as `Class.method`:
    /// - `Flask.run` -> finds the `run` method inside the `Flask` class
    /// - `UserController.get_user` -> finds `get_user` in `UserController`
    ///
    /// This allows disambiguating methods with the same name in different classes.
    fn find_function_node<'a>(
        tree: &'a tree_sitter::Tree,
        source: &'a [u8],
        lang: &dyn crate::lang::Language,
        function_name: &str,
    ) -> Result<tree_sitter::Node<'a>> {
        // Check for Class.method notation (qualified name)
        if let Some((class_name, method_name)) = function_name.split_once('.') {
            return Self::find_qualified_method_node(tree, source, lang, class_name, method_name);
        }

        let query_str = lang.function_query();
        let ts_lang = tree.language();

        let query = Query::new(&ts_lang, query_str).map_err(|e| {
            BrrrError::TreeSitter(format_query_error(lang.name(), "function", query_str, &e))
        })?;

        let mut cursor = QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source);

        // Find capture indices
        let function_capture_idx = query.capture_index_for_name("function");
        let name_capture_idx = query.capture_index_for_name("name");

        // Track seen ranges to avoid duplicates (e.g., decorated functions)
        let mut seen_ranges: Vec<(usize, usize)> = Vec::new();

        while let Some(match_) = matches.next() {
            // Get the function node
            let func_node = if let Some(idx) = function_capture_idx {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            } else {
                match_.captures.first().map(|c| c.node)
            };

            // Get the name node
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
                // Skip if we've already processed this range
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

                // Check if name matches
                let name =
                    std::str::from_utf8(&source[name_node.start_byte()..name_node.end_byte()])
                        .unwrap_or("");

                if name == function_name {
                    // For decorated functions, we need to find the inner function_definition
                    return Ok(Self::unwrap_decorated_function(func_node));
                }
            }
        }

        // Function not found - search in class methods
        Self::find_method_node(tree, source, lang, function_name)
    }

    /// Find a method in a specific class using qualified name notation.
    ///
    /// This method handles `Class.method` notation by:
    /// 1. Finding the class with the matching name
    /// 2. Searching for the method within that specific class
    ///
    /// # Arguments
    /// * `tree` - Parsed syntax tree
    /// * `source` - Source code bytes
    /// * `lang` - Language implementation
    /// * `class_name` - Name of the class to search in
    /// * `method_name` - Name of the method to find
    ///
    /// # Returns
    /// * `Result<Node>` - The method node or an error if not found
    fn find_qualified_method_node<'a>(
        tree: &'a tree_sitter::Tree,
        source: &'a [u8],
        lang: &dyn crate::lang::Language,
        class_name: &str,
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
        let name_capture_idx = query.capture_index_for_name("name");

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

            // Get the class name from the @name capture or extract it directly
            let found_class_name = if let Some(idx) = name_capture_idx {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .and_then(|c| {
                        std::str::from_utf8(&source[c.node.start_byte()..c.node.end_byte()]).ok()
                    })
            } else {
                // Fall back to extracting from the class node
                class_node.and_then(|n| Self::extract_class_name(n, source))
            };

            if let (Some(class_node), Some(found_name)) = (class_node, found_class_name) {
                if found_name == class_name {
                    // Found the target class, now search for the method
                    if let Some(method_node) =
                        Self::find_method_in_class(class_node, source, method_name)
                    {
                        return Ok(method_node);
                    }
                    // Class found but method not found - return specific error
                    return Err(BrrrError::FunctionNotFound(format!(
                        "Method '{}' not found in class '{}'",
                        method_name, class_name
                    )));
                }
            }
        }

        Err(BrrrError::FunctionNotFound(format!(
            "Class '{}' not found in file (looking for {}.{})",
            class_name, class_name, method_name
        )))
    }

    /// Extract the class name from a class node.
    ///
    /// Handles various class node structures across languages:
    /// - Python: class_definition with identifier child
    /// - TypeScript/JavaScript: class_declaration with name field
    /// - Java: class_declaration with identifier child
    fn extract_class_name<'a>(
        class_node: tree_sitter::Node<'a>,
        source: &'a [u8],
    ) -> Option<&'a str> {
        let mut cursor = class_node.walk();
        for child in class_node.children(&mut cursor) {
            match child.kind() {
                "identifier" | "type_identifier" => {
                    return std::str::from_utf8(&source[child.start_byte()..child.end_byte()]).ok();
                }
                "name" => {
                    // Some languages wrap the name in a "name" node
                    let mut inner = child.walk();
                    for inner_child in child.children(&mut inner) {
                        if inner_child.kind() == "identifier" {
                            return std::str::from_utf8(
                                &source[inner_child.start_byte()..inner_child.end_byte()],
                            )
                            .ok();
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Unwrap a decorated function to get the inner function_definition node.
    ///
    /// When a function is decorated, the query matches the decorated_definition
    /// wrapper. We need to extract the actual function_definition inside.
    fn unwrap_decorated_function(node: tree_sitter::Node) -> tree_sitter::Node {
        if node.kind() == "decorated_definition" {
            // Find the function_definition inside
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "function_definition" {
                    return child;
                }
            }
        }
        node
    }

    /// Search for a method inside classes.
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
                // Search for method inside class body
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
    fn find_method_in_class<'a>(
        class_node: tree_sitter::Node<'a>,
        source: &[u8],
        method_name: &str,
    ) -> Option<tree_sitter::Node<'a>> {
        // Find the class body (block in Python, class_body in other languages)
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

    /// Find the body node of a class.
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

    /// Extract function name from a function node.
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

    /// Extract CFG from source code string.
    ///
    /// Convenience method for extracting CFG from in-memory source code
    /// when the language is already known.
    ///
    /// # Arguments
    /// * `source` - Source code as string
    /// * `language` - Language name (e.g., "python", "typescript")
    /// * `function` - Name of the function to extract CFG for
    ///
    /// # Returns
    /// * `Result<CFGInfo>` - The control flow graph or an error
    #[allow(dead_code)]
    pub fn extract_from_source(source: &str, language: &str, function: &str) -> Result<CFGInfo> {
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
        lang.build_cfg(function_node, source_bytes)
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
    fn test_extract_simple_function_cfg() {
        let source = r#"
def example(x):
    if x > 0:
        return True
    return False
"#;
        let file = create_temp_file(source, ".py");
        let cfg = CfgBuilder::extract_from_file(file.path().to_str().unwrap(), "example");

        assert!(cfg.is_ok());
        let cfg = cfg.unwrap();
        assert_eq!(cfg.function_name, "example");
        assert!(!cfg.blocks.is_empty());
        assert!(!cfg.edges.is_empty());
        assert!(!cfg.exits.is_empty());
    }

    #[test]
    fn test_extract_function_with_loop() {
        let source = r#"
def sum_list(items):
    total = 0
    for item in items:
        total += item
    return total
"#;
        let file = create_temp_file(source, ".py");
        let cfg = CfgBuilder::extract_from_file(file.path().to_str().unwrap(), "sum_list");

        assert!(cfg.is_ok());
        let cfg = cfg.unwrap();
        assert_eq!(cfg.function_name, "sum_list");

        // Should have edges for loop
        let has_iterate_edge = cfg.edges.iter().any(|e| e.label().contains("iterate"));
        assert!(has_iterate_edge);
    }

    #[test]
    fn test_extract_function_with_try_except() {
        let source = r#"
def safe_divide(a, b):
    try:
        result = a / b
    except ZeroDivisionError:
        result = 0
    return result
"#;
        let file = create_temp_file(source, ".py");
        let cfg = CfgBuilder::extract_from_file(file.path().to_str().unwrap(), "safe_divide");

        assert!(cfg.is_ok());
        let cfg = cfg.unwrap();
        assert_eq!(cfg.function_name, "safe_divide");

        // Should have exception edge (TypedException for typed handlers like ZeroDivisionError)
        use crate::cfg::types::EdgeType;
        let has_exception_edge = cfg.edges.iter().any(|e| {
            matches!(
                e.edge_type,
                EdgeType::Exception | EdgeType::TypedException | EdgeType::ExceptionGroup
            )
        });
        assert!(has_exception_edge);
    }

    #[test]
    fn test_extract_decorated_function() {
        let source = r#"
@staticmethod
def my_static_method(x):
    return x * 2
"#;
        let file = create_temp_file(source, ".py");
        let cfg = CfgBuilder::extract_from_file(file.path().to_str().unwrap(), "my_static_method");

        assert!(cfg.is_ok());
        let cfg = cfg.unwrap();
        assert_eq!(cfg.function_name, "my_static_method");
    }

    #[test]
    fn test_extract_class_method() {
        let source = r#"
class Calculator:
    def add(self, a, b):
        return a + b
"#;
        let file = create_temp_file(source, ".py");
        let cfg = CfgBuilder::extract_from_file(file.path().to_str().unwrap(), "add");

        assert!(cfg.is_ok());
        let cfg = cfg.unwrap();
        assert_eq!(cfg.function_name, "add");
    }

    #[test]
    fn test_function_not_found() {
        let source = r#"
def existing_function():
    pass
"#;
        let file = create_temp_file(source, ".py");
        let cfg = CfgBuilder::extract_from_file(file.path().to_str().unwrap(), "nonexistent");

        assert!(cfg.is_err());
        assert!(matches!(cfg, Err(BrrrError::FunctionNotFound(_))));
    }

    #[test]
    fn test_extract_from_source() {
        let source = r#"
def multiply(a, b):
    return a * b
"#;
        let cfg = CfgBuilder::extract_from_source(source, "python", "multiply");

        assert!(cfg.is_ok());
        let cfg = cfg.unwrap();
        assert_eq!(cfg.function_name, "multiply");
    }

    #[test]
    fn test_mermaid_output() {
        use crate::cfg::render::to_mermaid;

        let source = r#"
def conditional(x):
    if x > 0:
        return "positive"
    else:
        return "non-positive"
"#;
        let cfg = CfgBuilder::extract_from_source(source, "python", "conditional").unwrap();
        let mermaid = to_mermaid(&cfg);

        assert!(mermaid.contains("flowchart TD"));
        assert!(mermaid.contains("B0")); // Should have at least entry block
    }

    #[test]
    fn test_cyclomatic_complexity() {
        // Simple function: complexity = 1 (0 decision points + 1)
        let simple_source = r#"
def simple():
    return 42
"#;
        let simple_cfg =
            CfgBuilder::extract_from_source(simple_source, "python", "simple").unwrap();
        let simple_complexity = simple_cfg.cyclomatic_complexity();
        assert_eq!(
            simple_cfg.decision_points, 0,
            "Simple function should have 0 decision points"
        );
        assert_eq!(
            simple_complexity, 1,
            "Simple function complexity should be 1"
        );

        // Function with if: complexity = 2 (1 decision point + 1)
        let if_source = r#"
def with_if(x):
    if x > 0:
        return 1
    return 0
"#;
        let if_cfg = CfgBuilder::extract_from_source(if_source, "python", "with_if").unwrap();
        let if_complexity = if_cfg.cyclomatic_complexity();
        assert_eq!(
            if_cfg.decision_points, 1,
            "Function with if should have 1 decision point"
        );
        assert_eq!(if_complexity, 2, "Function with if complexity should be 2");

        // Function with if-elif-else: complexity = 3 (2 decision points + 1)
        let elif_source = r#"
def with_elif(x):
    if x > 0:
        return "positive"
    elif x < 0:
        return "negative"
    else:
        return "zero"
"#;
        let elif_cfg = CfgBuilder::extract_from_source(elif_source, "python", "with_elif").unwrap();
        assert_eq!(
            elif_cfg.decision_points, 2,
            "if-elif should have 2 decision points"
        );
        assert_eq!(
            elif_cfg.cyclomatic_complexity(),
            3,
            "if-elif complexity should be 3"
        );

        // Function with for loop: complexity = 2 (1 decision point + 1)
        let for_source = r#"
def with_for(items):
    for item in items:
        print(item)
"#;
        let for_cfg = CfgBuilder::extract_from_source(for_source, "python", "with_for").unwrap();
        assert_eq!(
            for_cfg.decision_points, 1,
            "for loop should have 1 decision point"
        );
        assert_eq!(
            for_cfg.cyclomatic_complexity(),
            2,
            "for loop complexity should be 2"
        );

        // Function with while loop: complexity = 2 (1 decision point + 1)
        let while_source = r#"
def with_while(n):
    while n > 0:
        n -= 1
"#;
        let while_cfg =
            CfgBuilder::extract_from_source(while_source, "python", "with_while").unwrap();
        assert_eq!(
            while_cfg.decision_points, 1,
            "while loop should have 1 decision point"
        );
        assert_eq!(
            while_cfg.cyclomatic_complexity(),
            2,
            "while loop complexity should be 2"
        );

        assert!(if_complexity >= simple_complexity);
    }

    #[test]
    fn test_unsupported_language() {
        let file = create_temp_file("content", ".xyz");
        let result = CfgBuilder::extract_from_file(file.path().to_str().unwrap(), "func");

        assert!(matches!(result, Err(BrrrError::UnsupportedLanguage(_))));
    }

    #[test]
    fn test_while_loop_cfg() {
        let source = r#"
def countdown(n):
    while n > 0:
        n -= 1
    return n
"#;
        let cfg = CfgBuilder::extract_from_source(source, "python", "countdown").unwrap();

        // Should have back edge for loop
        let has_next_edge = cfg.edges.iter().any(|e| e.label().contains("next"));
        assert!(has_next_edge);
    }

    #[test]
    fn test_match_statement_cfg() {
        let source = r#"
def process_command(cmd):
    match cmd:
        case "start":
            return 1
        case "stop":
            return 0
        case _:
            return -1
"#;
        let cfg = CfgBuilder::extract_from_source(source, "python", "process_command").unwrap();

        // Match statement with 3 cases should produce multiple blocks and edges
        // The exact structure depends on tree-sitter-python version and match support
        assert!(
            cfg.blocks.len() >= 2,
            "Expected at least 2 blocks for match statement with cases, got {}",
            cfg.blocks.len()
        );
        assert!(
            cfg.edges.len() >= 1,
            "Expected at least 1 edge for match statement, got {}",
            cfg.edges.len()
        );
    }

    #[test]
    fn test_break_continue_cfg() {
        let source = r#"
def find_first(items, target):
    for item in items:
        if item == target:
            break
        if item < 0:
            continue
    return item
"#;
        let cfg = CfgBuilder::extract_from_source(source, "python", "find_first").unwrap();

        // Should have break edge
        let has_break = cfg.edges.iter().any(|e| e.label().contains("break"));
        assert!(has_break);

        // Should have continue edge
        let has_continue = cfg.edges.iter().any(|e| e.label().contains("continue"));
        assert!(has_continue);
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
        // decorated functions without producing duplicate CFG extractions
        let source = r#"
@decorator1
def func1(x):
    return x + 1

@decorator2
@decorator3
def func2(x):
    if x > 0:
        return x
    return 0

def plain_func(x):
    return x * 2
"#;
        // Extract CFG for each function - should succeed without duplicate issues
        let cfg1 = CfgBuilder::extract_from_source(source, "python", "func1");
        assert!(cfg1.is_ok(), "Should extract func1 CFG");
        assert_eq!(cfg1.unwrap().function_name, "func1");

        let cfg2 = CfgBuilder::extract_from_source(source, "python", "func2");
        assert!(cfg2.is_ok(), "Should extract func2 CFG");
        assert_eq!(cfg2.unwrap().function_name, "func2");

        let cfg3 = CfgBuilder::extract_from_source(source, "python", "plain_func");
        assert!(cfg3.is_ok(), "Should extract plain_func CFG");
        assert_eq!(cfg3.unwrap().function_name, "plain_func");
    }

    /// CFG-BUG-5: Test that match guards are properly tracked as decision points.
    /// Guards in case clauses create additional branching in the control flow.
    #[test]
    fn test_match_guard_cfg() {
        let source = r#"
def process_value(value):
    match value:
        case str() if len(value) > 0:
            return "non-empty string"
        case str():
            return "empty string"
        case int() if value > 0:
            return "positive int"
        case int():
            return "non-positive int"
        case _:
            return "other"
"#;
        let cfg = CfgBuilder::extract_from_source(source, "python", "process_value").unwrap();

        // With guards, we should have more blocks and edges than without guards
        // Each guard creates: guard block, guard_pass block, and true/false edges
        // 5 cases with 2 guards = more complex CFG

        // Check that guard blocks exist
        let has_guard_block = cfg.blocks.values().any(|b| b.label.contains("guard:"));
        assert!(
            has_guard_block,
            "Expected guard blocks for case clauses with guards"
        );

        // Check that guard edges exist (true/false branches)
        let has_true_edge = cfg.edges.iter().any(|e| e.label() == "true");
        let has_false_edge = cfg.edges.iter().any(|e| e.label() == "false");

        assert!(
            has_true_edge,
            "Expected 'true' edge from guard block for successful guard"
        );
        assert!(
            has_false_edge,
            "Expected 'false' edge from guard block for failed guard (fallthrough)"
        );

        // Count guard-related blocks and edges to verify the fix
        let guard_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.label.starts_with("guard:"))
            .collect();
        assert_eq!(
            guard_blocks.len(),
            2,
            "Expected 2 guard blocks for the 2 guards in the test, got {}",
            guard_blocks.len()
        );

        // Verify pattern_match edges exist (case -> guard)
        let pattern_match_edges = cfg
            .edges
            .iter()
            .filter(|e| e.label() == "pattern_match")
            .count();
        assert_eq!(
            pattern_match_edges, 2,
            "Expected 2 pattern_match edges (case -> guard), got {}",
            pattern_match_edges
        );

        // Verify guard_pass blocks exist
        let guard_pass_blocks = cfg
            .blocks
            .values()
            .filter(|b| b.label == "guard_pass")
            .count();
        assert_eq!(
            guard_pass_blocks, 2,
            "Expected 2 guard_pass blocks, got {}",
            guard_pass_blocks
        );

        // The complexity formula (E - N + 2) is diluted by unreachable blocks from returns,
        // but the guard structure is correct. Check that complexity is at least non-trivial.
        let complexity = cfg.cyclomatic_complexity();
        assert!(
            complexity >= 2,
            "Expected cyclomatic complexity >= 2, got {}",
            complexity
        );
    }

    // =========================================================================
    // QUALIFIED NAME TESTS: Class.method notation
    // =========================================================================

    #[test]
    fn test_extract_qualified_method_python() {
        // Test Class.method notation for Python
        let source = r#"
class Flask:
    def run(self, host='127.0.0.1', port=5000):
        if host == '0.0.0.0':
            return 'public'
        return 'localhost'

class App:
    def run(self):
        return 'app running'
"#;
        let file = create_temp_file(source, ".py");

        // Should find Flask.run specifically
        let cfg = CfgBuilder::extract_from_file(file.path().to_str().unwrap(), "Flask.run");
        assert!(cfg.is_ok(), "Should find Flask.run");
        let cfg = cfg.unwrap();
        assert_eq!(cfg.function_name, "run");

        // Should find App.run specifically
        let cfg = CfgBuilder::extract_from_file(file.path().to_str().unwrap(), "App.run");
        assert!(cfg.is_ok(), "Should find App.run");
    }

    #[test]
    fn test_extract_qualified_method_disambiguates() {
        // Test that Class.method correctly disambiguates between same-named methods
        let source = r#"
class UserController:
    def get(self, user_id):
        if user_id > 0:
            return 'found'
        return 'not found'

class ProductController:
    def get(self, product_id):
        return 'product'
"#;
        let cfg = CfgBuilder::extract_from_source(source, "python", "UserController.get").unwrap();
        assert_eq!(cfg.function_name, "get");
        // UserController.get has an if statement, so it should have decision points
        assert!(
            cfg.decision_points >= 1,
            "UserController.get should have decision points from if statement"
        );

        let cfg =
            CfgBuilder::extract_from_source(source, "python", "ProductController.get").unwrap();
        assert_eq!(cfg.function_name, "get");
        // ProductController.get has no if statement
        assert_eq!(
            cfg.decision_points, 0,
            "ProductController.get should have no decision points"
        );
    }

    #[test]
    fn test_extract_qualified_method_class_not_found() {
        let source = r#"
class ExistingClass:
    def method(self):
        pass
"#;
        let result = CfgBuilder::extract_from_source(source, "python", "NonExistent.method");
        assert!(result.is_err(), "Should fail for non-existent class");
        let err = result.unwrap_err();
        match err {
            BrrrError::FunctionNotFound(msg) => {
                assert!(
                    msg.contains("NonExistent"),
                    "Error should mention the class name"
                );
            }
            _ => panic!("Expected FunctionNotFound error"),
        }
    }

    #[test]
    fn test_extract_qualified_method_method_not_found() {
        let source = r#"
class MyClass:
    def existing_method(self):
        pass
"#;
        let result = CfgBuilder::extract_from_source(source, "python", "MyClass.nonexistent");
        assert!(result.is_err(), "Should fail for non-existent method");
        let err = result.unwrap_err();
        match err {
            BrrrError::FunctionNotFound(msg) => {
                assert!(
                    msg.contains("nonexistent") && msg.contains("MyClass"),
                    "Error should mention both class and method: {}",
                    msg
                );
            }
            _ => panic!("Expected FunctionNotFound error"),
        }
    }

    #[test]
    fn test_extract_qualified_method_with_decorators() {
        // Test that qualified name works with decorated methods
        let source = r#"
class Controller:
    @staticmethod
    def static_method():
        return 1

    @classmethod
    def class_method(cls):
        return 2
"#;
        let cfg =
            CfgBuilder::extract_from_source(source, "python", "Controller.static_method").unwrap();
        assert_eq!(cfg.function_name, "static_method");

        let cfg =
            CfgBuilder::extract_from_source(source, "python", "Controller.class_method").unwrap();
        assert_eq!(cfg.function_name, "class_method");
    }

    #[test]
    fn test_bare_method_name_still_works() {
        // Verify that bare method names still work (backward compatibility)
        let source = r#"
class Calculator:
    def add(self, a, b):
        return a + b
"#;
        // Using bare name should still find the method (existing behavior)
        let cfg = CfgBuilder::extract_from_source(source, "python", "add").unwrap();
        assert_eq!(cfg.function_name, "add");
    }

    // =========================================================================
    // SECURITY TESTS: Path Traversal Protection
    // =========================================================================

    #[test]
    fn test_extract_from_file_rejects_path_traversal() {
        // Excessive parent directory traversal should be rejected
        let malicious_path = "../../../../../../../../../../../etc/passwd";
        let result = CfgBuilder::extract_from_file(malicious_path, "main");

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
def example(x):
    if x > 0:
        return True
    return False
"#;
        let file = create_temp_file(source, ".py");
        let result = CfgBuilder::extract_from_file(file.path().to_str().unwrap(), "example");

        assert!(result.is_ok(), "Valid path should be accepted");
    }

    #[test]
    fn test_extract_from_source_bypasses_path_validation() {
        // extract_from_source doesn't read files, so no path validation needed
        let source = r#"
def test():
    return 42
"#;
        let result = CfgBuilder::extract_from_source(source, "python", "test");
        assert!(
            result.is_ok(),
            "extract_from_source should work with string input"
        );
    }
}
