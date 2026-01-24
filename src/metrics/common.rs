//! Common utilities and traits for metrics modules.
//!
//! This module provides shared functionality to reduce code duplication
//! across different metrics implementations.

use std::collections::HashSet;
use tree_sitter::Node;

// =============================================================================
// METRIC STATS TRAIT
// =============================================================================

/// Base trait for aggregate statistics across metrics modules.
///
/// Implementing this trait provides a consistent interface for statistics
/// and enables generic algorithms over different metric types.
pub trait MetricStats {
    /// Total count of items analyzed (functions, classes, etc.)
    fn count(&self) -> usize;

    /// Sum total of the primary metric value
    fn total(&self) -> f64;

    /// Average of the primary metric value
    fn average(&self) -> f64 {
        let count = self.count();
        if count == 0 {
            return 0.0;
        }
        self.total() / count as f64
    }

    /// Maximum value of the primary metric
    fn max(&self) -> f64;

    /// Minimum value of the primary metric
    fn min(&self) -> f64;
}

// =============================================================================
// AST UTILITIES
// =============================================================================

/// Safely extract text from an AST node.
///
/// Returns an empty string if the byte slice cannot be converted to UTF-8.
#[inline]
pub fn node_text<'a>(node: Node<'a>, source: &'a [u8]) -> &'a str {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
}

/// Find a class node by name and line number.
///
/// Searches recursively through the AST for class definitions
/// matching the given line number.
pub fn find_class_node<'a>(node: Node<'a>, _class_name: &str, line: usize) -> Option<Node<'a>> {
    let node_kind = node.kind();

    let is_class = matches!(
        node_kind,
        "class_definition"
            | "class_declaration"
            | "class"
            | "impl_item"
            | "struct_item"
            | "type_declaration"
    );

    if is_class {
        let node_line = node.start_position().row + 1;
        if node_line == line {
            return Some(node);
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(found) = find_class_node(child, _class_name, line) {
            return Some(found);
        }
    }

    None
}

/// Find a method node within a class by line number.
pub fn find_method_node<'a>(
    class_node: Node<'a>,
    _method_name: &str,
    line: usize,
    language: &str,
) -> Option<Node<'a>> {
    let method_kinds = get_method_node_kinds(language);
    find_method_recursive(class_node, &method_kinds, line)
}

/// Get the AST node kinds for method definitions in a language.
pub fn get_method_node_kinds(language: &str) -> Vec<&'static str> {
    match language {
        "python" => vec!["function_definition"],
        "typescript" | "javascript" | "tsx" | "jsx" => {
            vec!["method_definition", "function_declaration", "function"]
        }
        "rust" => vec!["function_item"],
        "go" => vec!["function_declaration", "method_declaration"],
        "java" | "kotlin" | "csharp" => vec!["method_declaration", "function_declaration"],
        "cpp" | "c" => vec!["function_definition", "function_declarator"],
        _ => vec!["function_definition", "method_definition"],
    }
}

/// Recursively find a method node by line number.
pub fn find_method_recursive<'a>(
    node: Node<'a>,
    method_kinds: &[&str],
    line: usize,
) -> Option<Node<'a>> {
    if method_kinds.contains(&node.kind()) {
        let node_line = node.start_position().row + 1;
        if node_line == line {
            return Some(node);
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(found) = find_method_recursive(child, method_kinds, line) {
            return Some(found);
        }
    }

    None
}

// =============================================================================
// ATTRIBUTE EXTRACTION
// =============================================================================

/// Extract instance attribute accesses from a method body.
///
/// Language-specific patterns:
/// - Python: `self.attr`
/// - TypeScript/JavaScript: `this.attr`
/// - Rust: `self.field`
/// - Go: receiver.field (where receiver is the struct type)
pub fn extract_attribute_accesses(node: Node, source: &[u8], language: &str) -> HashSet<String> {
    let mut attributes = HashSet::new();
    extract_attributes_recursive(node, source, language, &mut attributes);
    attributes
}

fn extract_attributes_recursive(
    node: Node,
    source: &[u8],
    language: &str,
    attributes: &mut HashSet<String>,
) {
    let node_kind = node.kind();

    match language {
        "python" => {
            if node_kind == "attribute" {
                if let Some(object) = node.child_by_field_name("object") {
                    let obj_text = node_text(object, source);
                    if obj_text == "self" {
                        if let Some(attr) = node.child_by_field_name("attribute") {
                            let attr_name = node_text(attr, source);
                            // Filter dunder methods
                            if !(attr_name.starts_with("__") && attr_name.ends_with("__")) {
                                attributes.insert(attr_name.to_string());
                            }
                        }
                    }
                }
            }
        }
        "typescript" | "javascript" | "tsx" | "jsx" => {
            if node_kind == "member_expression" {
                if let Some(object) = node.child_by_field_name("object") {
                    let obj_text = node_text(object, source);
                    if obj_text == "this" {
                        if let Some(prop) = node.child_by_field_name("property") {
                            let attr_name = node_text(prop, source);
                            attributes.insert(attr_name.to_string());
                        }
                    }
                }
            }
        }
        "rust" => {
            if node_kind == "field_expression" {
                if let Some(value) = node.child_by_field_name("value") {
                    let val_text = node_text(value, source);
                    if val_text == "self" {
                        if let Some(field) = node.child_by_field_name("field") {
                            let field_name = node_text(field, source);
                            attributes.insert(field_name.to_string());
                        }
                    }
                }
            }
        }
        "go" => {
            if node_kind == "selector_expression" {
                if let Some(operand) = node.child_by_field_name("operand") {
                    let operand_kind = operand.kind();
                    if operand_kind == "identifier" {
                        let var_name = node_text(operand, source);
                        // Common Go receiver patterns: single letter, or common names
                        if var_name.len() <= 3
                            || var_name.starts_with("this")
                            || var_name.starts_with("self")
                        {
                            if let Some(field) = node.child_by_field_name("field") {
                                let field_name = node_text(field, source);
                                attributes.insert(field_name.to_string());
                            }
                        }
                    }
                }
            }
        }
        "java" | "kotlin" | "csharp" => {
            if node_kind == "field_access" || node_kind == "member_access_expression" {
                if let Some(object) = node.child_by_field_name("object") {
                    let obj_text = node_text(object, source);
                    if obj_text == "this" {
                        if let Some(field) = node
                            .child_by_field_name("field")
                            .or_else(|| node.child_by_field_name("name"))
                        {
                            let field_name = node_text(field, source);
                            attributes.insert(field_name.to_string());
                        }
                    }
                }
            }
        }
        "cpp" | "c" => {
            if node_kind == "field_expression" {
                if let Some(argument) = node.child_by_field_name("argument") {
                    let arg_text = node_text(argument, source);
                    if arg_text == "this" {
                        if let Some(field) = node.child_by_field_name("field") {
                            let field_name = node_text(field, source);
                            attributes.insert(field_name.to_string());
                        }
                    }
                }
            }
        }
        _ => {}
    }

    // Recurse into children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        extract_attributes_recursive(child, source, language, attributes);
    }
}

// =============================================================================
// METHOD CALL EXTRACTION
// =============================================================================

/// Extract method calls within a method body (for LCOM4-style analysis).
///
/// Returns a set of method names from `class_methods` that are called
/// via self/this within the given node.
pub fn extract_method_calls(
    node: Node,
    source: &[u8],
    language: &str,
    class_methods: &HashSet<String>,
) -> HashSet<String> {
    let mut calls = HashSet::new();
    extract_calls_recursive(node, source, language, class_methods, &mut calls);
    calls
}

fn extract_calls_recursive(
    node: Node,
    source: &[u8],
    language: &str,
    class_methods: &HashSet<String>,
    calls: &mut HashSet<String>,
) {
    let node_kind = node.kind();

    match language {
        "python" => {
            // Python: self.method() calls
            if node_kind == "call" {
                if let Some(func) = node.child_by_field_name("function") {
                    if func.kind() == "attribute" {
                        if let Some(obj) = func.child_by_field_name("object") {
                            if node_text(obj, source) == "self" {
                                if let Some(attr) = func.child_by_field_name("attribute") {
                                    let method_name = node_text(attr, source);
                                    if class_methods.contains(method_name) {
                                        calls.insert(method_name.to_string());
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        "typescript" | "javascript" | "tsx" | "jsx" => {
            // this.method() calls
            if node_kind == "call_expression" {
                if let Some(func) = node.child_by_field_name("function") {
                    if func.kind() == "member_expression" {
                        if let Some(obj) = func.child_by_field_name("object") {
                            if node_text(obj, source) == "this" {
                                if let Some(prop) = func.child_by_field_name("property") {
                                    let method_name = node_text(prop, source);
                                    if class_methods.contains(method_name) {
                                        calls.insert(method_name.to_string());
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        "rust" => {
            // self.method() calls
            if node_kind == "call_expression" {
                if let Some(func) = node.child_by_field_name("function") {
                    if func.kind() == "field_expression" {
                        if let Some(val) = func.child_by_field_name("value") {
                            if node_text(val, source) == "self" {
                                if let Some(field) = func.child_by_field_name("field") {
                                    let method_name = node_text(field, source);
                                    if class_methods.contains(method_name) {
                                        calls.insert(method_name.to_string());
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        _ => {}
    }

    // Recurse
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        extract_calls_recursive(child, source, language, class_methods, calls);
    }
}

// =============================================================================
// STATISTICS HELPERS
// =============================================================================

/// Calculate median from a sorted slice of values.
pub fn calculate_median_u32(sorted: &[u32]) -> u32 {
    if sorted.is_empty() {
        return 0;
    }
    let len = sorted.len();
    if len % 2 == 0 {
        (sorted[len / 2 - 1] + sorted[len / 2]) / 2
    } else {
        sorted[len / 2]
    }
}

/// Calculate median from a sorted slice of f64 values.
pub fn calculate_median_f64(sorted: &[f64]) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let len = sorted.len();
    if len % 2 == 0 {
        (sorted[len / 2 - 1] + sorted[len / 2]) / 2.0
    } else {
        sorted[len / 2]
    }
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_calculate_median_u32() {
        assert_eq!(calculate_median_u32(&[]), 0);
        assert_eq!(calculate_median_u32(&[5]), 5);
        assert_eq!(calculate_median_u32(&[1, 2, 3]), 2);
        assert_eq!(calculate_median_u32(&[1, 2, 3, 4]), 2); // (2+3)/2 = 2.5 -> 2
        assert_eq!(calculate_median_u32(&[1, 3, 5, 7, 9]), 5);
    }

    #[test]
    fn test_calculate_median_f64() {
        assert!((calculate_median_f64(&[]) - 0.0).abs() < f64::EPSILON);
        assert!((calculate_median_f64(&[5.0]) - 5.0).abs() < f64::EPSILON);
        assert!((calculate_median_f64(&[1.0, 2.0, 3.0]) - 2.0).abs() < f64::EPSILON);
        assert!((calculate_median_f64(&[1.0, 2.0, 3.0, 4.0]) - 2.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_method_node_kinds() {
        let python_kinds = get_method_node_kinds("python");
        assert!(python_kinds.contains(&"function_definition"));

        let ts_kinds = get_method_node_kinds("typescript");
        assert!(ts_kinds.contains(&"method_definition"));

        let rust_kinds = get_method_node_kinds("rust");
        assert!(rust_kinds.contains(&"function_item"));
    }
}
