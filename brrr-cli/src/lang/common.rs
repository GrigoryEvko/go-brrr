//! Common utilities for language handlers.
//!
//! Provides shared functionality used across multiple language implementations:
//! - Node text extraction (safe UTF-8 handling)
//! - Child node traversal helpers
//! - Async function detection
//! - Common node type constants
//!
//! These utilities reduce code duplication across language handlers while
//! ensuring consistent behavior for tree-sitter node operations.

use tree_sitter::Node;

// =============================================================================
// Node Text Extraction
// =============================================================================

/// Extract text from a tree-sitter node as a `&str`.
///
/// Safely converts the byte range to UTF-8, returning an empty string
/// on invalid UTF-8 sequences rather than panicking.
///
/// # Arguments
/// * `node` - The tree-sitter node to extract text from
/// * `source` - The source code bytes
///
/// # Returns
/// The text content of the node, or empty string if UTF-8 conversion fails
///
/// # Example
/// ```ignore
/// let text = node_text(identifier_node, source);
/// ```
#[inline]
pub fn node_text<'a>(node: Node<'a>, source: &'a [u8]) -> &'a str {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
}

/// Extract text from a tree-sitter node as an owned `String`.
///
/// Similar to `node_text` but returns an owned String, useful when
/// the result needs to outlive the source reference.
///
/// # Arguments
/// * `node` - The tree-sitter node to extract text from
/// * `source` - The source code bytes
///
/// # Returns
/// The text content of the node as owned String
#[inline]
pub fn node_text_owned(node: Node, source: &[u8]) -> String {
    node_text(node, source).to_string()
}

// =============================================================================
// Child Node Traversal
// =============================================================================

/// Find a child node by its field name.
///
/// Uses tree-sitter's field-based access which is more efficient and
/// semantically correct than searching by node kind. Field names are
/// defined in the grammar and provide stable, named access to children.
///
/// # Arguments
/// * `node` - The parent node
/// * `field` - The field name to look up
///
/// # Returns
/// The child node at the named field, or None if not found
///
/// # Example
/// ```ignore
/// // Get the "name" field from a function definition
/// if let Some(name_node) = child_by_field(func_node, "name") {
///     let name = node_text(name_node, source);
/// }
/// ```
#[inline]
pub fn child_by_field<'a>(node: Node<'a>, field: &str) -> Option<Node<'a>> {
    node.child_by_field_name(field)
}

/// Find the first child node with a given kind.
///
/// Iterates through direct children to find the first one matching the
/// specified node kind. Use `child_by_field` when a field name is available,
/// as it's more precise and efficient.
///
/// # Arguments
/// * `node` - The parent node
/// * `kind` - The node kind to search for
///
/// # Returns
/// The first child with matching kind, or None if not found
///
/// # Example
/// ```ignore
/// // Find the parameters node
/// if let Some(params) = child_by_kind(func_node, "parameters") {
///     // Process parameters
/// }
/// ```
pub fn child_by_kind<'a>(node: Node<'a>, kind: &str) -> Option<Node<'a>> {
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == kind {
            return Some(child);
        }
    }
    None
}

/// Find all children with a given kind.
///
/// Returns a vector of all direct children matching the specified kind.
/// Useful when multiple children of the same type exist (e.g., multiple
/// parameters, statements, etc.).
///
/// # Arguments
/// * `node` - The parent node
/// * `kind` - The node kind to search for
///
/// # Returns
/// Vector of children matching the kind (may be empty)
pub fn children_by_kind<'a>(node: Node<'a>, kind: &str) -> Vec<Node<'a>> {
    let mut cursor = node.walk();
    node.children(&mut cursor)
        .filter(|child| child.kind() == kind)
        .collect()
}

/// Collect children matching a predicate.
///
/// Generic helper for filtering children by any criteria.
///
/// # Arguments
/// * `node` - The parent node
/// * `predicate` - Function returning true for children to include
///
/// # Returns
/// Vector of children passing the predicate
pub fn collect_children<'a, F>(node: Node<'a>, predicate: F) -> Vec<Node<'a>>
where
    F: Fn(&Node<'a>) -> bool,
{
    let mut cursor = node.walk();
    node.children(&mut cursor).filter(|n| predicate(n)).collect()
}

// =============================================================================
// Async Detection
// =============================================================================

/// Check if a function node has an async keyword.
///
/// Searches for an "async" keyword child node rather than using string matching,
/// which correctly handles:
/// - Comments before async: `/* comment */ async function foo() {}`
/// - Decorators before async: `@decorator async function foo() {}`
/// - Visibility modifiers: `class C { public async method() {} }`
///
/// Early exits when it reaches the function body since async always precedes it.
///
/// # Arguments
/// * `node` - The function/method declaration node
/// * `body_kinds` - Node kinds that indicate the function body (e.g., "statement_block", "block")
///
/// # Returns
/// `true` if the function has an async modifier
///
/// # Example
/// ```ignore
/// let is_async = has_async_keyword(func_node, &["statement_block", "block"]);
/// ```
pub fn has_async_keyword(node: Node, body_kinds: &[&str]) -> bool {
    for child in node.children(&mut node.walk()) {
        if child.kind() == "async" {
            return true;
        }
        // Early exit: async keyword always precedes the function body
        if body_kinds.contains(&child.kind()) {
            break;
        }
    }
    false
}

/// Check if a function node has an async keyword (simple version).
///
/// Uses common body node kinds: "statement_block", "block", "body".
/// For language-specific body detection, use `has_async_keyword` directly.
pub fn is_async_function(node: Node) -> bool {
    has_async_keyword(node, &["statement_block", "block", "body", "compound_statement"])
}

// =============================================================================
// Function Name Extraction
// =============================================================================

/// Extract function/method name from a declaration node.
///
/// Attempts to get the name using the "name" field, which is the standard
/// field name used by most tree-sitter grammars for function declarations.
///
/// # Arguments
/// * `node` - The function/method declaration node
/// * `source` - The source code bytes
///
/// # Returns
/// The function name if found, None otherwise
///
/// # Example
/// ```ignore
/// if let Some(name) = extract_function_name(func_node, source) {
///     println!("Function: {}", name);
/// }
/// ```
pub fn extract_function_name(node: Node, source: &[u8]) -> Option<String> {
    child_by_field(node, "name").map(|n| node_text_owned(n, source))
}

/// Extract function name with fallback to "declarator" field.
///
/// Some languages (C, C++) use a "declarator" field instead of "name".
/// This function tries "name" first, then falls back to "declarator".
///
/// For complex declarators (pointers, references), it recursively finds
/// the innermost identifier.
pub fn extract_function_name_with_declarator(node: Node, source: &[u8]) -> Option<String> {
    // Try "name" field first
    if let Some(name_node) = child_by_field(node, "name") {
        return Some(node_text_owned(name_node, source));
    }

    // Try "declarator" field (C/C++ style)
    if let Some(decl) = child_by_field(node, "declarator") {
        return extract_identifier_from_declarator(decl, source);
    }

    None
}

/// Extract the identifier from a possibly nested declarator.
///
/// C/C++ declarators can be nested: `*(*(*func)(int))(char)`
/// This recursively descends to find the innermost identifier.
fn extract_identifier_from_declarator(node: Node, source: &[u8]) -> Option<String> {
    match node.kind() {
        "identifier" => Some(node_text_owned(node, source)),
        "function_declarator" | "pointer_declarator" | "reference_declarator"
        | "array_declarator" | "parenthesized_declarator" => {
            child_by_field(node, "declarator")
                .and_then(|d| extract_identifier_from_declarator(d, source))
        }
        _ => None,
    }
}

// =============================================================================
// Parameter Extraction
// =============================================================================

/// Extract parameter names from a parameter list node.
///
/// Generic helper that iterates through parameter children and extracts
/// names. The actual parameter structure varies by language, so this
/// provides the iteration framework.
///
/// # Arguments
/// * `params_node` - The parameter list node (e.g., "formal_parameters", "parameter_list")
/// * `source` - The source code bytes
/// * `param_kinds` - Node kinds that represent parameters (e.g., &["parameter", "formal_parameter"])
///
/// # Returns
/// Vector of parameter representations as strings
pub fn extract_param_names(
    params_node: Node,
    source: &[u8],
    param_kinds: &[&str],
) -> Vec<String> {
    let mut params = Vec::new();
    let mut cursor = params_node.walk();

    for child in params_node.children(&mut cursor) {
        if param_kinds.contains(&child.kind()) {
            // Try to get just the name, fall back to full text
            let param_text = if let Some(name) = child_by_field(child, "name") {
                node_text_owned(name, source)
            } else {
                node_text_owned(child, source)
            };

            if !param_text.is_empty() {
                params.push(param_text);
            }
        }
    }

    params
}

// =============================================================================
// Common Node Type Constants
// =============================================================================

/// Common node types for function declarations across languages.
pub mod queries {
    /// Node types that represent function declarations in various languages.
    ///
    /// Note: Each language may use different subsets of these types.
    /// Use language-specific queries for precise matching.
    pub const FUNCTION_TYPES: &[&str] = &[
        // Python
        "function_definition",
        "decorated_definition",
        // JavaScript/TypeScript
        "function_declaration",
        "arrow_function",
        "method_definition",
        "function_expression",
        "generator_function_declaration",
        "generator_function",
        // Java
        "method_declaration",
        "constructor_declaration",
        // Go
        "function_declaration",
        "method_declaration",
        // Rust
        "function_item",
        // C/C++
        "function_definition",
    ];

    /// Node types that represent class/struct/interface declarations.
    pub const CLASS_TYPES: &[&str] = &[
        // Python
        "class_definition",
        "decorated_definition",
        // JavaScript/TypeScript
        "class_declaration",
        "interface_declaration",
        // Java
        "class_declaration",
        "interface_declaration",
        "enum_declaration",
        "record_declaration",
        // Go
        "type_declaration",
        // Rust
        "struct_item",
        "enum_item",
        "trait_item",
        "impl_item",
        // C/C++
        "struct_specifier",
        "class_specifier",
        "union_specifier",
    ];

    /// Node types that represent import/use statements.
    pub const IMPORT_TYPES: &[&str] = &[
        // Python
        "import_statement",
        "import_from_statement",
        // JavaScript/TypeScript
        "import_statement",
        "import_declaration",
        // Java
        "import_declaration",
        // Go
        "import_declaration",
        // Rust
        "use_declaration",
        "extern_crate_declaration",
        // C/C++
        "preproc_include",
    ];

    /// Common body node types that indicate function body start.
    /// Used for async keyword detection (async always precedes body).
    pub const BODY_TYPES: &[&str] = &[
        "statement_block",     // JavaScript/TypeScript
        "block",               // Python, Rust, many others
        "body",                // Some grammars use this
        "compound_statement",  // C/C++
    ];
}

// =============================================================================
// Line/Position Utilities
// =============================================================================

/// Get the 1-based line number for a node.
///
/// Tree-sitter uses 0-based line numbers internally; this converts to
/// 1-based for user-facing output.
#[inline]
pub fn node_line(node: Node) -> usize {
    node.start_position().row + 1
}

/// Get the end line number (1-based) for a node.
#[inline]
pub fn node_end_line(node: Node) -> usize {
    node.end_position().row + 1
}

/// Get the start column (0-based) for a node.
#[inline]
pub fn node_column(node: Node) -> usize {
    node.start_position().column
}

// =============================================================================
// Docstring Extraction Helpers
// =============================================================================

/// Find the previous sibling that is a comment.
///
/// Useful for finding doc comments that precede declarations.
/// Skips non-comment siblings and stops at the first comment found.
///
/// # Arguments
/// * `node` - The declaration node to find documentation for
///
/// # Returns
/// The preceding comment node if found
pub fn find_preceding_comment(node: Node) -> Option<Node> {
    let mut current = node.prev_sibling();
    while let Some(sibling) = current {
        if sibling.kind() == "comment" {
            return Some(sibling);
        }
        // Stop at any non-whitespace, non-comment node
        if !sibling.kind().contains("whitespace") && sibling.kind() != "comment" {
            break;
        }
        current = sibling.prev_sibling();
    }
    None
}

/// Extract text from a comment node, stripping comment markers.
///
/// Handles common comment formats:
/// - `// line comment` -> `line comment`
/// - `/* block comment */` -> `block comment`
/// - `# hash comment` -> `hash comment`
///
/// Does NOT handle JSDoc/Javadoc parsing - use language-specific handlers for those.
pub fn strip_comment_markers(comment_text: &str) -> String {
    let text = comment_text.trim();

    // Line comments
    if let Some(stripped) = text.strip_prefix("//") {
        return stripped.trim_start().to_string();
    }
    if let Some(stripped) = text.strip_prefix('#') {
        return stripped.trim_start().to_string();
    }

    // Block comments
    if text.starts_with("/*") && text.ends_with("*/") {
        let inner = &text[2..text.len() - 2];
        return inner.trim().to_string();
    }

    text.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strip_comment_markers_line() {
        assert_eq!(strip_comment_markers("// hello world"), "hello world");
        assert_eq!(strip_comment_markers("//no space"), "no space");
        assert_eq!(strip_comment_markers("# python comment"), "python comment");
    }

    #[test]
    fn test_strip_comment_markers_block() {
        assert_eq!(strip_comment_markers("/* block */"), "block");
        assert_eq!(strip_comment_markers("/* multi\nline */"), "multi\nline");
    }

    #[test]
    fn test_queries_constants() {
        assert!(queries::FUNCTION_TYPES.contains(&"function_definition"));
        assert!(queries::CLASS_TYPES.contains(&"class_declaration"));
        assert!(queries::IMPORT_TYPES.contains(&"import_statement"));
        assert!(queries::BODY_TYPES.contains(&"statement_block"));
    }
}
