//! C++ language support.
//!
//! Implements extraction for C++ code including all C features plus:
//!
//! C++ specific features:
//! - Templates (class templates, function templates)
//! - Namespaces (namespace foo { } and namespace foo::bar { })
//! - Classes with access specifiers (public:, private:, protected:)
//! - Constructors and destructors
//! - Operator overloading (operator+, operator<<, etc.)
//! - Lambda expressions ([captures](params) { body })
//! - References (int&, const int&)
//! - Exception specifications (noexcept, throw())
//! - Virtual functions and pure virtual functions
//! - Override and final specifiers
//! - constexpr and consteval functions
//! - Static member functions
//! - Friend declarations
//!
//! C++11/14/17/20 features:
//! - Range-based for loops
//! - Auto type deduction
//! - Initializer lists
//! - Variadic templates
//! - Concepts (C++20)

use std::collections::HashMap;

use phf::phf_set;
use tree_sitter::{Node, Parser, Tree};

use crate::ast::types::{ClassInfo, FieldInfo, FunctionInfo, ImportInfo};
use crate::cfg::types::{BlockId, BlockType, CFGBlock, CFGEdge, CFGInfo, EdgeType};
use crate::dfg::types::{DFGInfo, DataflowEdge, DataflowKind};
use crate::error::{Result, BrrrError};
use crate::lang::traits::Language;

/// C++ keywords and reserved names that cannot be valid class names.
/// Uses compile-time perfect hashing for O(1) lookup instead of linear search.
static INVALID_CLASS_NAMES: phf::Set<&'static str> = phf_set! {
    "class", "struct", "public", "private", "protected",
    "virtual", "static", "const", "volatile", "template",
    "typename", "namespace", "using", "typedef", "enum",
    "union", "friend", "inline", "explicit", "extern",
    "return", "if", "else", "for", "while", "do", "switch",
    "case", "default", "break", "continue", "goto", "throw",
    "try", "catch", "new", "delete", "this", "nullptr",
};

/// C++ language implementation.
pub struct Cpp;

impl Cpp {
    /// Extract text from source bytes for a node.
    #[inline]
    fn get_text<'a>(&self, node: Node, source: &'a [u8]) -> &'a str {
        std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }

    /// Extract text as owned String.
    fn node_text(&self, node: Node, source: &[u8]) -> String {
        self.get_text(node, source).to_string()
    }

    /// Get child node by field name.
    fn child_by_field<'a>(&self, node: Node<'a>, field: &str) -> Option<Node<'a>> {
        node.child_by_field_name(field)
    }

    /// Extract preceding comment as documentation.
    ///
    /// Comments are considered adjacent if there is at most MAX_GAP blank lines
    /// between them and the declaration (or between consecutive comments).
    fn get_doc_comment(&self, node: Node, source: &[u8]) -> Option<String> {
        let mut comments = Vec::new();
        // Track the row we expect comments to end before.
        // Initially, this is the declaration's start row.
        let mut expected_before_row = node.start_position().row;

        // Maximum allowed gap (blank lines) between comment and declaration
        // or between consecutive comments. Setting to 1 allows a single blank line.
        const MAX_GAP: usize = 1;

        if let Some(parent) = node.parent() {
            let mut found_self = false;
            let child_count = parent.child_count();

            for i in (0..child_count).rev() {
                if let Some(sibling) = parent.child(i as u32) {
                    if sibling.id() == node.id() {
                        found_self = true;
                        continue;
                    }

                    if found_self && sibling.kind() == "comment" {
                        let comment_end_row = sibling.end_position().row;
                        // Calculate gap: number of blank lines between comment end and expected position
                        // Example: comment ends at row 8, function at row 10 -> gap = 10 - 9 = 1
                        let gap = expected_before_row.saturating_sub(comment_end_row + 1);

                        if gap <= MAX_GAP {
                            let text = self.get_text(sibling, source);
                            let cleaned = self.clean_comment(text);
                            if !cleaned.is_empty() {
                                comments.push(cleaned);
                            }
                            // Update: next comment should end before this one starts
                            expected_before_row = sibling.start_position().row;
                        } else {
                            break;
                        }
                    } else if found_self && sibling.kind() != "comment" {
                        break;
                    }
                }
            }
        }

        if comments.is_empty() {
            None
        } else {
            comments.reverse();
            Some(comments.join("\n"))
        }
    }

    /// Clean a comment string by removing comment markers.
    fn clean_comment(&self, text: &str) -> String {
        let text = text.trim();

        if text.starts_with("/*") {
            let inner = text
                .strip_prefix("/**")
                .or_else(|| text.strip_prefix("/*"))
                .unwrap_or(text);
            let inner = inner.strip_suffix("*/").unwrap_or(inner);

            return inner
                .lines()
                .map(|line| {
                    let line = line.trim();
                    line.strip_prefix('*').unwrap_or(line).trim()
                })
                .filter(|line| !line.is_empty())
                .collect::<Vec<_>>()
                .join(" ");
        }

        if text.starts_with("//") {
            return text.strip_prefix("//").unwrap_or(text).trim().to_string();
        }

        text.to_string()
    }

    /// Extract template parameters from a template_parameter_list node.
    /// Returns template parameter string like "typename T, typename U" or "class T, int N".
    fn extract_template_params(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut params = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "type_parameter_declaration" => {
                    // typename T or class T
                    let mut param_str = String::new();
                    let mut param_cursor = child.walk();
                    for param_child in child.children(&mut param_cursor) {
                        match param_child.kind() {
                            "typename" | "class" => {
                                param_str.push_str(self.get_text(param_child, source));
                                param_str.push(' ');
                            }
                            "type_identifier" => {
                                param_str.push_str(self.get_text(param_child, source));
                            }
                            _ => {}
                        }
                    }
                    if !param_str.is_empty() {
                        params.push(param_str.trim().to_string());
                    }
                }
                "parameter_declaration" => {
                    // Non-type template parameter like int N
                    params.push(self.node_text(child, source));
                }
                "variadic_type_parameter_declaration" => {
                    // typename... Args (parameter pack)
                    params.push(self.node_text(child, source));
                }
                "optional_type_parameter_declaration" => {
                    // typename T = default
                    params.push(self.node_text(child, source));
                }
                _ => {}
            }
        }

        params
    }

    /// Extract parameters from a parameter_list node.
    fn extract_params(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut params = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            if child.kind() == "parameter_declaration" {
                let param = self.extract_parameter(child, source);
                if !param.is_empty() {
                    params.push(param);
                }
            } else if child.kind() == "variadic_parameter_declaration" {
                params.push("...".to_string());
            } else if child.kind() == "optional_parameter_declaration" {
                let param = self.extract_parameter(child, source);
                if !param.is_empty() {
                    params.push(param);
                }
            }
        }

        params
    }

    /// Extract a single parameter declaration.
    fn extract_parameter(&self, node: Node, source: &[u8]) -> String {
        let mut type_parts = Vec::new();
        let mut name = String::new();
        let mut pointer_count = 0;
        let mut is_reference = false;
        let mut is_rvalue_ref = false;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "type_qualifier" => {
                    type_parts.push(self.node_text(child, source));
                }
                "primitive_type" | "type_identifier" | "sized_type_specifier" | "auto" => {
                    type_parts.push(self.node_text(child, source));
                }
                "template_type" => {
                    // Handle template types like vector<int>
                    type_parts.push(self.node_text(child, source));
                }
                "qualified_identifier" => {
                    // Handle qualified names like std::string
                    type_parts.push(self.node_text(child, source));
                }
                "pointer_declarator" => {
                    let (n, ptrs) = self.extract_pointer_declarator(child, source);
                    name = n;
                    pointer_count = ptrs;
                }
                "reference_declarator" => {
                    let (n, is_rval) = self.extract_reference_declarator(child, source);
                    name = n;
                    if is_rval {
                        is_rvalue_ref = true;
                    } else {
                        is_reference = true;
                    }
                }
                "identifier" => {
                    name = self.node_text(child, source);
                }
                "array_declarator" => {
                    let (n, suffix) = self.extract_array_declarator(child, source);
                    name = format!("{}{}", n, suffix);
                }
                _ => {}
            }
        }

        let type_str = type_parts.join(" ");
        let pointers = "*".repeat(pointer_count);
        let ref_suffix = if is_rvalue_ref {
            "&&"
        } else if is_reference {
            "&"
        } else {
            ""
        };

        if name.is_empty() {
            format!("{}{}{}", type_str, pointers, ref_suffix)
        } else {
            format!("{}{}{} {}", type_str, pointers, ref_suffix, name)
        }
    }

    /// Extract identifier and pointer count from a pointer_declarator.
    fn extract_pointer_declarator(&self, node: Node, source: &[u8]) -> (String, usize) {
        let mut pointer_count = 0;
        let mut current = node;

        loop {
            if current.kind() == "pointer_declarator" {
                pointer_count += 1;
                if let Some(declarator) = self.child_by_field(current, "declarator") {
                    current = declarator;
                } else {
                    let mut cursor = current.walk();
                    let mut found = false;
                    for child in current.children(&mut cursor) {
                        if child.kind() != "*" {
                            current = child;
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        break;
                    }
                }
            } else if current.kind() == "identifier" || current.kind() == "field_identifier" {
                return (self.node_text(current, source), pointer_count);
            } else if current.kind() == "function_declarator" {
                if let Some(decl) = self.child_by_field(current, "declarator") {
                    return self.extract_pointer_declarator(decl, source);
                }
                break;
            } else {
                break;
            }
        }

        (String::new(), pointer_count)
    }

    /// Extract identifier and whether it's rvalue reference from a reference_declarator.
    fn extract_reference_declarator(&self, node: Node, source: &[u8]) -> (String, bool) {
        let text = self.node_text(node, source);
        let is_rvalue = text.contains("&&");

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "identifier" {
                return (self.node_text(child, source), is_rvalue);
            }
        }

        (String::new(), is_rvalue)
    }

    /// Extract identifier and array suffix from an array_declarator.
    fn extract_array_declarator(&self, node: Node, source: &[u8]) -> (String, String) {
        let mut name = String::new();
        let mut suffix = String::new();

        if let Some(declarator) = self.child_by_field(node, "declarator") {
            name = self.node_text(declarator, source);
        }

        if let Some(size) = self.child_by_field(node, "size") {
            suffix = format!("[{}]", self.node_text(size, source));
        } else {
            suffix = "[]".to_string();
        }

        (name, suffix)
    }

    /// Extract return type from a function definition or declaration.
    fn extract_return_type(&self, node: Node, source: &[u8]) -> Option<String> {
        // For C++, return type can be in "type" field or as trailing return type
        if let Some(type_node) = self.child_by_field(node, "type") {
            return Some(self.node_text(type_node, source));
        }

        // Check for trailing return type (auto f() -> int)
        if let Some(trailing) = self.child_by_field(node, "trailing_return_type") {
            return Some(self.node_text(trailing, source));
        }

        let mut type_parts = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "storage_class_specifier" | "virtual" | "explicit" | "inline" | "constexpr" | "consteval" => {
                    // Skip these for return type
                }
                "type_qualifier" => {
                    type_parts.push(self.node_text(child, source));
                }
                "primitive_type" | "type_identifier" | "sized_type_specifier" | "auto" => {
                    type_parts.push(self.node_text(child, source));
                }
                "template_type" | "qualified_identifier" => {
                    type_parts.push(self.node_text(child, source));
                }
                "function_declarator" | "pointer_declarator" | "reference_declarator" => {
                    break;
                }
                _ => {}
            }
        }

        if type_parts.is_empty() {
            None
        } else {
            Some(type_parts.join(" "))
        }
    }

    /// Extract function name from a function_declarator.
    fn extract_function_name(&self, node: Node, source: &[u8]) -> Option<String> {
        if let Some(declarator) = self.child_by_field(node, "declarator") {
            return self.extract_name_from_declarator(declarator, source);
        }

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "identifier" | "field_identifier" => {
                    return Some(self.node_text(child, source));
                }
                "destructor_name" => {
                    return Some(self.node_text(child, source));
                }
                "operator_name" => {
                    return Some(self.node_text(child, source));
                }
                "qualified_identifier" => {
                    return Some(self.node_text(child, source));
                }
                "template_function" => {
                    // Handle template instantiation in function name
                    return Some(self.node_text(child, source));
                }
                "pointer_declarator" => {
                    let (name, _) = self.extract_pointer_declarator(child, source);
                    if !name.is_empty() {
                        return Some(name);
                    }
                }
                _ => {}
            }
        }

        None
    }

    /// Extract name from a declarator node.
    fn extract_name_from_declarator(&self, node: Node, source: &[u8]) -> Option<String> {
        match node.kind() {
            "identifier" | "field_identifier" => Some(self.node_text(node, source)),
            "destructor_name" => Some(self.node_text(node, source)),
            "operator_name" => Some(self.node_text(node, source)),
            "qualified_identifier" => Some(self.node_text(node, source)),
            "template_function" => Some(self.node_text(node, source)),
            "pointer_declarator" => {
                let (name, _) = self.extract_pointer_declarator(node, source);
                if name.is_empty() { None } else { Some(name) }
            }
            "reference_declarator" => {
                let (name, _) = self.extract_reference_declarator(node, source);
                if name.is_empty() { None } else { Some(name) }
            }
            "function_declarator" => self.extract_function_name(node, source),
            _ => None,
        }
    }

    /// Check if a function has a specific storage class specifier.
    fn has_storage_class(&self, node: Node, source: &[u8], specifier: &str) -> bool {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "storage_class_specifier" {
                if self.get_text(child, source).trim() == specifier {
                    return true;
                }
            }
        }
        false
    }

    /// Check if a function has a specific specifier (virtual, inline, etc.).
    fn has_specifier(&self, node: Node, kind: &str) -> bool {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == kind {
                return true;
            }
        }
        false
    }

    /// Check if a node is inside a class/struct body (field_declaration_list).
    /// This is used to determine if a function is a method.
    fn is_inside_class(&self, node: Node) -> bool {
        let mut current = node;
        while let Some(parent) = current.parent() {
            match parent.kind() {
                // If we hit a class/struct specifier, we're inside a class
                "class_specifier" | "struct_specifier" => return true,
                // If we hit another function definition first, we're not a method
                // (could be a nested function inside a lambda)
                "function_definition" if parent.id() != node.id() => return false,
                // If we hit namespace or translation unit, we're not inside a class
                "namespace_definition" | "translation_unit" => return false,
                _ => {}
            }
            current = parent;
        }
        false
    }

    /// Check if a string looks like a C/C++ macro name (ALL_CAPS with underscores).
    fn is_macro_identifier(&self, text: &str) -> bool {
        let trimmed = text.trim();
        !trimmed.is_empty()
            && trimmed.len() > 3  // Avoid short names like "FOO"
            && trimmed.chars().next().map_or(false, |c| c.is_ascii_uppercase())
            && trimmed.chars().all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
    }

    /// Attempt to extract a class from a misparsed function_definition.
    /// This handles cases like:
    /// ```cpp
    /// MACRO_TEMPLATE_DECLARATION
    /// class ClassName { ... }
    /// ```
    /// Where tree-sitter misparses it as a function_definition because
    /// the macro looks like a return type.
    fn extract_macro_preceded_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        if node.kind() != "function_definition" {
            return None;
        }

        // Check if the "type" is a macro-like identifier
        let type_node = self.child_by_field(node, "type")?;
        let type_text = self.node_text(type_node, source);
        if !self.is_macro_identifier(&type_text) {
            return None;
        }

        // Extract class name from misparsed tree structure.
        // Tree-sitter parses "MACRO\nclass Name : base { }" in different ways:
        //
        // Case 1 (no inheritance):
        //   declarator: identifier ("Name")
        //   ERROR: contains "class Name" text
        //
        // Case 2 (with inheritance, relative namespace):
        //   declarator: identifier ("class")  <- keyword becomes declarator!
        //   ERROR: identifier ("Name") + inheritance info
        //
        // Case 3 (with inheritance, global namespace like ::ns::Base):
        //   declarator: qualified_identifier
        //     scope: namespace_identifier ("class")  <- keyword!
        //     ERROR: identifier ("Name") + ": public"
        //     :: and name: qualified path to base class
        //
        let mut class_name = None;
        let mut cursor = node.walk();

        // Check if declarator is "class" or "struct" (Case 2)
        // Or if declarator is a qualified_identifier with "class"/"struct" scope (Case 3)
        // We MUST have evidence of "class" or "struct" keyword to avoid matching namespace macros
        if let Some(decl) = self.child_by_field(node, "declarator") {
            let decl_text = self.node_text(decl, source).trim().to_string();
            let is_class_keyword = decl_text == "class" || decl_text == "struct";
            let starts_with_class = decl_text.starts_with("class ") || decl_text.starts_with("struct ");

            // For qualified_identifier, check if it contains "class" somewhere
            let qualified_has_class = if decl.kind() == "qualified_identifier" {
                decl_text.contains("class") || decl_text.contains("struct")
            } else {
                false
            };

            if is_class_keyword || starts_with_class || qualified_has_class {
                // Look for ERROR node containing the class name
                // The ERROR might be a direct child of function_definition (Case 2)
                // or a child of the qualified_identifier (Case 3)
                let error_search_roots = if decl.kind() == "qualified_identifier" {
                    vec![decl, node]  // Search both qualified_identifier and function_definition
                } else {
                    vec![node]
                };

                for search_root in error_search_roots {
                    if class_name.is_some() {
                        break;
                    }
                    let mut search_cursor = search_root.walk();
                    for child in search_root.children(&mut search_cursor) {
                        if child.kind() == "ERROR" {
                            // Find the first identifier child in the ERROR node
                            let mut err_cursor = child.walk();
                            for err_child in child.children(&mut err_cursor) {
                                if err_child.kind() == "identifier" {
                                    class_name = Some(self.node_text(err_child, source));
                                    break;
                                }
                            }
                            if class_name.is_some() {
                                break;
                            }
                        }
                    }
                }
            }
        }

        // Case 1: Look for "class Name" or "struct Name" in ERROR node text
        if class_name.is_none() {
            cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "ERROR" {
                    let text = self.node_text(child, source);
                    if text.contains("class ") || text.contains("struct ") {
                        let stripped = text
                            .trim()
                            .strip_prefix("class ")
                            .or_else(|| text.trim().strip_prefix("struct "));
                        if let Some(rest) = stripped {
                            class_name = rest.split_whitespace().next().map(|s| s.to_string());
                        }
                    }
                }
            }
        }

        // Fallback: Use declarator if it's not "class"/"struct" and looks like a name
        if class_name.is_none() {
            if let Some(decl) = self.child_by_field(node, "declarator") {
                let decl_text = self.node_text(decl, source);
                if decl_text != "class" && decl_text != "struct"
                    && !decl_text.contains('(') && !decl_text.contains('{')
                {
                    class_name = Some(decl_text.trim().to_string());
                }
            }
        }

        let name = class_name?;

        // Reject C++ keywords and invalid names (O(1) lookup via PHF)
        if INVALID_CLASS_NAMES.contains(name.as_str()) || name.len() < 2 {
            return None;
        }

        // Check if body looks like a class body (has access specifiers as labels)
        let body = self.child_by_field(node, "body")?;
        let has_access_specifiers = body.children(&mut body.walk())
            .any(|c| {
                if c.kind() == "labeled_statement" {
                    let text = self.node_text(c, source);
                    text.contains("public") || text.contains("private") || text.contains("protected")
                } else {
                    false
                }
            });

        if !has_access_specifiers {
            return None;
        }

        // Extract what we can - this is a best-effort extraction
        let docstring = self.get_doc_comment(node, source);

        // Mark as template class since it had a macro (likely template macro)
        let decorators = vec![
            "class".to_string(),
            format!("macro:{}", type_text),
        ];

        Some(ClassInfo {
            name,
            bases: Vec::new(),  // Hard to extract from misparsed tree
            docstring,
            methods: Vec::new(),  // Would need more complex extraction
            fields: Vec::new(),
            inner_classes: Vec::new(),
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "cpp".to_string(),
        })
    }

    /// Extract lambda expression information.
    /// Returns FunctionInfo with decorator "lambda" and captures in decorators.
    fn extract_lambda(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        if node.kind() != "lambda_expression" {
            return None;
        }

        // Extract captures from lambda_capture_specifier
        let mut captures = Vec::new();
        if let Some(capture_list) = node.children(&mut node.walk())
            .find(|c| c.kind() == "lambda_capture_specifier")
        {
            let capture_text = self.node_text(capture_list, source);
            captures.push(format!("captures:{}", capture_text));
        }

        // Extract parameters
        let params = self.child_by_field(node, "declarator")
            .and_then(|d| self.child_by_field(d, "parameters"))
            .map(|p| self.extract_params(p, source))
            .unwrap_or_default();

        // Extract return type (trailing return type)
        let return_type = self.child_by_field(node, "declarator")
            .and_then(|d| d.children(&mut d.walk())
                .find(|c| c.kind() == "trailing_return_type"))
            .map(|t| self.node_text(t, source));

        let mut decorators = vec!["lambda".to_string()];
        decorators.extend(captures);

        // Check for mutable
        if node.children(&mut node.walk()).any(|c| c.kind() == "mutable") {
            decorators.push("mutable".to_string());
        }

        Some(FunctionInfo {
            name: "<lambda>".to_string(),
            params,
            return_type,
            docstring: None,
            is_method: false,
            is_async: false,
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "cpp".to_string(),
        })
    }

    /// Extract template declaration.
    /// Returns the decorated FunctionInfo or ClassInfo with template parameters.
    fn extract_template_declaration<'a>(&self, node: Node<'a>, source: &[u8]) -> Option<(Vec<String>, Node<'a>)> {
        if node.kind() != "template_declaration" {
            return None;
        }

        // Extract template parameters
        let template_params = node.children(&mut node.walk())
            .find(|c| c.kind() == "template_parameter_list")
            .map(|p| self.extract_template_params(p, source))
            .unwrap_or_default();

        // Build template decorator
        let template_decorator = format!("template<{}>", template_params.join(", "));

        // Find the templated declaration (function_definition, class_specifier, etc.)
        let inner = node.children(&mut node.walk())
            .find(|c| matches!(c.kind(),
                "function_definition" | "declaration" | "class_specifier" |
                "struct_specifier" | "alias_declaration"));

        inner.map(move |n| (vec![template_decorator], n))
    }

    /// Extract namespace declaration.
    fn extract_namespace(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        if node.kind() != "namespace_definition" {
            return None;
        }

        // Get namespace name (could be qualified like foo::bar)
        let name = self.child_by_field(node, "name")
            .map(|n| self.node_text(n, source))
            .unwrap_or_else(|| "<anonymous>".to_string());

        let docstring = self.get_doc_comment(node, source);

        // Extract nested classes, functions from namespace body
        let mut methods = Vec::new();
        let mut inner_classes = Vec::new();

        if let Some(body) = self.child_by_field(node, "body") {
            let mut cursor = body.walk();
            for child in body.children(&mut cursor) {
                match child.kind() {
                    "function_definition" | "declaration" | "template_declaration" => {
                        if let Some(func) = self.extract_function(child, source) {
                            methods.push(func);
                        }
                    }
                    "class_specifier" | "struct_specifier" | "enum_specifier" |
                    "namespace_definition" => {
                        if let Some(class) = self.extract_class(child, source) {
                            inner_classes.push(class);
                        }
                    }
                    _ => {}
                }
            }
        }

        Some(ClassInfo {
            name,
            bases: Vec::new(),
            docstring,
            methods,
            fields: Vec::new(),
            inner_classes,
            decorators: vec!["namespace".to_string()],
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "cpp".to_string(),
        })
    }

    /// Extract class fields with visibility tracking.
    fn extract_class_fields(&self, node: Node, source: &[u8]) -> Vec<FieldInfo> {
        let mut fields = Vec::new();
        let mut current_visibility = "private".to_string(); // Default for classes

        // Check if this is a struct (default public) or class (default private)
        if node.kind() == "struct_specifier" {
            current_visibility = "public".to_string();
        }

        let body = match self.child_by_field(node, "body") {
            Some(b) => b,
            None => return fields,
        };

        let mut cursor = body.walk();
        for child in body.children(&mut cursor) {
            match child.kind() {
                "access_specifier" => {
                    // Update current visibility: public:, private:, protected:
                    let spec_text = self.node_text(child, source);
                    if spec_text.contains("public") {
                        current_visibility = "public".to_string();
                    } else if spec_text.contains("protected") {
                        current_visibility = "protected".to_string();
                    } else if spec_text.contains("private") {
                        current_visibility = "private".to_string();
                    }
                }
                "field_declaration" => {
                    // Extract field with current visibility
                    if let Some(field) = self.extract_single_field(child, source, &current_visibility) {
                        fields.push(field);
                    }
                }
                _ => {}
            }
        }

        fields
    }

    /// Extract a single field declaration.
    fn extract_single_field(&self, node: Node, source: &[u8], visibility: &str) -> Option<FieldInfo> {
        let mut type_parts = Vec::new();
        let mut field_name = String::new();
        let mut is_static = false;
        let mut is_const = false;
        let mut annotations = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "storage_class_specifier" => {
                    let text = self.node_text(child, source);
                    if text == "static" {
                        is_static = true;
                    } else if text == "mutable" {
                        annotations.push("mutable".to_string());
                    }
                }
                "type_qualifier" => {
                    let text = self.node_text(child, source);
                    if text == "const" {
                        is_const = true;
                    }
                    type_parts.push(text);
                }
                "primitive_type" | "type_identifier" | "sized_type_specifier" | "auto" => {
                    type_parts.push(self.node_text(child, source));
                }
                "template_type" | "qualified_identifier" => {
                    type_parts.push(self.node_text(child, source));
                }
                "field_identifier" => {
                    field_name = self.node_text(child, source);
                }
                "pointer_declarator" => {
                    let (name, ptrs) = self.extract_pointer_declarator(child, source);
                    if !name.is_empty() {
                        field_name = name;
                    }
                    type_parts.push("*".repeat(ptrs));
                }
                "reference_declarator" => {
                    let (name, is_rval) = self.extract_reference_declarator(child, source);
                    if !name.is_empty() {
                        field_name = name;
                    }
                    type_parts.push(if is_rval { "&&" } else { "&" }.to_string());
                }
                "bitfield_clause" => {
                    let mut bf_cursor = child.walk();
                    for bf_child in child.children(&mut bf_cursor) {
                        if bf_child.kind() == "number_literal" {
                            annotations.push(format!("bitfield:{}", self.node_text(bf_child, source)));
                            break;
                        }
                    }
                }
                _ => {}
            }
        }

        if field_name.is_empty() {
            return None;
        }

        let type_str = if type_parts.is_empty() {
            None
        } else {
            Some(type_parts.join(" "))
        };

        Some(FieldInfo {
            name: field_name,
            field_type: type_str,
            visibility: Some(visibility.to_string()),
            is_static,
            is_final: is_const,
            default_value: None,
            annotations,
            line_number: node.start_position().row + 1,
        })
    }

    /// Extract class methods with visibility tracking.
    fn extract_class_methods(&self, node: Node, source: &[u8], class_name: &str) -> Vec<FunctionInfo> {
        let mut methods = Vec::new();
        let mut current_visibility = "private".to_string();

        if node.kind() == "struct_specifier" {
            current_visibility = "public".to_string();
        }

        let body = match self.child_by_field(node, "body") {
            Some(b) => b,
            None => return methods,
        };

        let mut cursor = body.walk();
        for child in body.children(&mut cursor) {
            match child.kind() {
                "access_specifier" => {
                    let spec_text = self.node_text(child, source);
                    if spec_text.contains("public") {
                        current_visibility = "public".to_string();
                    } else if spec_text.contains("protected") {
                        current_visibility = "protected".to_string();
                    } else if spec_text.contains("private") {
                        current_visibility = "private".to_string();
                    }
                }
                "function_definition" | "declaration" | "template_declaration" => {
                    if let Some(mut func) = self.extract_cpp_function(child, source) {
                        func.is_method = true;
                        func.decorators.push(current_visibility.clone());

                        // Detect constructor/destructor
                        if func.name == class_name {
                            func.decorators.push("constructor".to_string());
                        } else if func.name == format!("~{}", class_name) || func.name.starts_with('~') {
                            func.decorators.push("destructor".to_string());
                        }

                        methods.push(func);
                    }
                }
                _ => {}
            }
        }

        methods
    }

    /// Extract base classes from a class specifier.
    fn extract_base_classes(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut bases = Vec::new();

        // Look for base_class_clause
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "base_class_clause" {
                let mut base_cursor = child.walk();
                for base_child in child.children(&mut base_cursor) {
                    if base_child.kind() == "base_class_specifier" {
                        // Extract the base class info including access specifier
                        bases.push(self.node_text(base_child, source));
                    }
                }
            }
        }

        bases
    }

    /// Extract C++ function with full feature support.
    fn extract_cpp_function(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        // Handle template declarations
        if node.kind() == "template_declaration" {
            if let Some((template_decorators, inner)) = self.extract_template_declaration(node, source) {
                if let Some(mut func) = self.extract_cpp_function(inner, source) {
                    func.decorators.extend(template_decorators);
                    // Update line numbers to template declaration
                    func.line_number = node.start_position().row + 1;
                    return Some(func);
                }
            }
            return None;
        }

        match node.kind() {
            "function_definition" => {
                let declarator = self.child_by_field(node, "declarator")?;
                let name = self.extract_function_name(declarator, source)?;

                let params = self.child_by_field(declarator, "parameters")
                    .map(|p| self.extract_params(p, source))
                    .unwrap_or_default();

                let return_type = self.extract_return_type(node, source);
                let docstring = self.get_doc_comment(node, source);

                let mut decorators = Vec::new();

                // Storage class specifiers
                if self.has_storage_class(node, source, "static") {
                    decorators.push("static".to_string());
                }
                if self.has_storage_class(node, source, "extern") {
                    decorators.push("extern".to_string());
                }

                // C++ specific specifiers
                if self.has_specifier(node, "virtual") {
                    decorators.push("virtual".to_string());
                }
                if self.has_specifier(node, "inline") {
                    decorators.push("inline".to_string());
                }
                if self.has_specifier(node, "constexpr") {
                    decorators.push("constexpr".to_string());
                }
                if self.has_specifier(node, "consteval") {
                    decorators.push("consteval".to_string());
                }
                if self.has_specifier(node, "explicit") {
                    decorators.push("explicit".to_string());
                }

                // Check for override/final in declarator
                let decl_text = self.node_text(declarator, source);
                if decl_text.contains("override") {
                    decorators.push("override".to_string());
                }
                if decl_text.contains("final") {
                    decorators.push("final".to_string());
                }
                if decl_text.contains("noexcept") {
                    decorators.push("noexcept".to_string());
                }
                if decl_text.contains("= 0") {
                    decorators.push("pure_virtual".to_string());
                }
                if decl_text.contains("= default") {
                    decorators.push("default".to_string());
                }
                if decl_text.contains("= delete") {
                    decorators.push("deleted".to_string());
                }

                // Detect operator overloading
                if name.starts_with("operator") {
                    decorators.push("operator".to_string());
                }

                // Check if this function is inside a class/struct body
                let is_method = self.is_inside_class(node);

                Some(FunctionInfo {
                    name,
                    params,
                    return_type,
                    docstring,
                    is_method,
                    is_async: false,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "cpp".to_string(),
                })
            }
            "declaration" => {
                // Function declaration (prototype) or variable declaration
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "function_declarator" {
                        let name = self.extract_function_name(child, source)?;
                        let params = self.child_by_field(child, "parameters")
                            .map(|p| self.extract_params(p, source))
                            .unwrap_or_default();
                        let return_type = self.extract_return_type(node, source);
                        let docstring = self.get_doc_comment(node, source);

                        let mut decorators = vec!["declaration".to_string()];

                        if self.has_storage_class(node, source, "static") {
                            decorators.push("static".to_string());
                        }
                        if self.has_storage_class(node, source, "extern") {
                            decorators.push("extern".to_string());
                        }
                        if self.has_specifier(node, "virtual") {
                            decorators.push("virtual".to_string());
                        }

                        // Check for pure virtual
                        let node_text = self.node_text(node, source);
                        if node_text.contains("= 0") {
                            decorators.push("pure_virtual".to_string());
                        }

                        // Detect operator overloading
                        if name.starts_with("operator") {
                            decorators.push("operator".to_string());
                        }

                        // Check if this declaration is inside a class/struct body
                        let is_method = self.is_inside_class(node);

                        return Some(FunctionInfo {
                            name,
                            params,
                            return_type,
                            docstring,
                            is_method,
                            is_async: false,
                            decorators,
                            line_number: node.start_position().row + 1,
                            end_line_number: Some(node.end_position().row + 1),
                            language: "cpp".to_string(),
                        });
                    }
                }
                None
            }
            "lambda_expression" => self.extract_lambda(node, source),
            _ => None,
        }
    }

    /// Extract C++ class or struct with full feature support.
    fn extract_cpp_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        // Handle template declarations
        if node.kind() == "template_declaration" {
            if let Some((template_decorators, inner)) = self.extract_template_declaration(node, source) {
                if let Some(mut class) = self.extract_cpp_class(inner, source) {
                    class.decorators.extend(template_decorators);
                    class.line_number = node.start_position().row + 1;
                    return Some(class);
                }
            }
            return None;
        }

        match node.kind() {
            "class_specifier" | "struct_specifier" => {
                let name = self.child_by_field(node, "name")
                    .map(|n| self.node_text(n, source))?;

                let docstring = self.get_doc_comment(node, source);
                let bases = self.extract_base_classes(node, source);
                let fields = self.extract_class_fields(node, source);
                let methods = self.extract_class_methods(node, source, &name);

                // Extract nested classes
                let mut inner_classes = Vec::new();
                if let Some(body) = self.child_by_field(node, "body") {
                    let mut cursor = body.walk();
                    for child in body.children(&mut cursor) {
                        if child.kind() == "class_specifier" || child.kind() == "struct_specifier"
                            || child.kind() == "enum_specifier" {
                            if let Some(inner) = self.extract_cpp_class(child, source) {
                                inner_classes.push(inner);
                            }
                        }
                    }
                }

                let mut decorators = Vec::new();
                if node.kind() == "struct_specifier" {
                    decorators.push("struct".to_string());
                } else {
                    decorators.push("class".to_string());
                }

                // Check for final class
                let node_text = self.node_text(node, source);
                if node_text.contains(" final ") || node_text.contains(" final:") {
                    decorators.push("final".to_string());
                }

                Some(ClassInfo {
                    name,
                    bases,
                    docstring,
                    methods,
                    fields,
                    inner_classes,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "cpp".to_string(),
                })
            }
            "enum_specifier" => {
                let name = self.child_by_field(node, "name")
                    .map(|n| self.node_text(n, source))?;

                let docstring = self.get_doc_comment(node, source);

                // Check for enum class (C++11 scoped enum)
                let mut decorators = vec!["enum".to_string()];
                let node_text = self.node_text(node, source);
                if node_text.starts_with("enum class") || node_text.starts_with("enum struct") {
                    decorators.push("scoped".to_string());
                }

                Some(ClassInfo {
                    name,
                    bases: Vec::new(),
                    docstring,
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "cpp".to_string(),
                })
            }
            "namespace_definition" => self.extract_namespace(node, source),
            "type_definition" => {
                // typedef or using declaration
                let mut typedef_name = None;
                let mut cursor = node.walk();

                for child in node.children(&mut cursor) {
                    if child.kind() == "type_identifier" {
                        typedef_name = Some(self.node_text(child, source));
                    }
                }

                let name = typedef_name?;
                let docstring = self.get_doc_comment(node, source);

                Some(ClassInfo {
                    name,
                    bases: Vec::new(),
                    docstring,
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: Vec::new(),
                    decorators: vec!["typedef".to_string()],
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "cpp".to_string(),
                })
            }
            "alias_declaration" => {
                // using Name = Type;
                let name = self.child_by_field(node, "name")
                    .map(|n| self.node_text(n, source))?;

                let docstring = self.get_doc_comment(node, source);

                Some(ClassInfo {
                    name,
                    bases: Vec::new(),
                    docstring,
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: Vec::new(),
                    decorators: vec!["using".to_string(), "alias".to_string()],
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "cpp".to_string(),
                })
            }
            // Handle macro-preceded class definitions that tree-sitter misparses
            // as function_definitions (e.g., TEMPLATE_MACRO\nclass Name { ... })
            "function_definition" => self.extract_macro_preceded_class(node, source),
            _ => None,
        }
    }

    /// Build CFG for a C++ function.
    fn build_cpp_cfg(&self, node: Node, source: &[u8], func_name: &str) -> CFGInfo {
        let mut blocks = HashMap::new();
        let mut edges = Vec::new();
        let mut block_id = 0;
        let mut exits = Vec::new();

        let entry = BlockId(block_id);
        blocks.insert(
            entry,
            CFGBlock {
                id: entry,
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );
        block_id += 1;

        if let Some(body) = self.child_by_field(node, "body") {
            self.process_cfg_block(
                body,
                source,
                &mut blocks,
                &mut edges,
                &mut block_id,
                entry,
                &mut exits,
                &mut Vec::new(),
                &mut Vec::new(),
            );
        }

        if exits.is_empty() {
            exits.push(entry);
        }

        CFGInfo {
            function_name: func_name.to_string(),
            blocks,
            edges,
            entry,
            exits,
            decision_points: 0, // TODO: Calculate actual decision points for C++
            comprehension_decision_points: 0, // C++ doesn't have Python-style comprehensions
            nested_cfgs: HashMap::new(),      // TODO: Handle lambda expressions as nested CFGs
            is_async: false,                  // TODO: Track C++20 coroutines
            await_points: 0,                  // TODO: Track co_await points
            blocking_calls: Vec::new(),       // TODO: Track blocking calls in coroutines
            ..Default::default()
        }
    }

    /// Process a compound statement for CFG construction.
    #[allow(clippy::too_many_arguments)]
    fn process_cfg_block(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        loop_headers: &mut Vec<BlockId>,
        loop_exits: &mut Vec<BlockId>,
    ) -> BlockId {
        let mut last_block = current_block;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "return_statement" => {
                    *block_id += 1;
                    let ret_block = BlockId(*block_id);
                    let stmt = self.node_text(child, source);

                    blocks.insert(
                        ret_block,
                        CFGBlock {
                            id: ret_block,
                            label: "return".to_string(),
                            block_type: BlockType::Return,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::unconditional(last_block, ret_block));

                    exits.push(ret_block);
                    last_block = ret_block;
                }
                "throw_statement" => {
                    *block_id += 1;
                    let throw_block = BlockId(*block_id);
                    let stmt = self.node_text(child, source);

                    blocks.insert(
                        throw_block,
                        CFGBlock {
                            id: throw_block,
                            label: "throw".to_string(),
                            block_type: BlockType::Exception,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::unconditional(last_block, throw_block));

                    exits.push(throw_block);
                    last_block = throw_block;
                }
                "if_statement" => {
                    last_block = self.process_if_cfg(
                        child, source, blocks, edges, block_id,
                        last_block, exits, loop_headers, loop_exits,
                    );
                }
                "while_statement" | "for_statement" | "do_statement" | "for_range_loop" => {
                    last_block = self.process_loop_cfg(
                        child, source, blocks, edges, block_id,
                        last_block, exits, loop_headers, loop_exits,
                    );
                }
                "switch_statement" => {
                    last_block = self.process_switch_cfg(
                        child, source, blocks, edges, block_id,
                        last_block, exits, loop_headers, loop_exits,
                    );
                }
                "try_statement" => {
                    last_block = self.process_try_cfg(
                        child, source, blocks, edges, block_id,
                        last_block, exits, loop_headers, loop_exits,
                    );
                }
                "break_statement" => {
                    if let Some(&exit_block) = loop_exits.last() {
                        edges.push(CFGEdge::new(last_block, exit_block, EdgeType::Break));
                    }
                }
                "continue_statement" => {
                    if let Some(&header) = loop_headers.last() {
                        edges.push(CFGEdge::new(last_block, header, EdgeType::Continue));
                    }
                }
                "compound_statement" => {
                    last_block = self.process_cfg_block(
                        child, source, blocks, edges, block_id,
                        last_block, exits, loop_headers, loop_exits,
                    );
                }
                "declaration" | "expression_statement" | "labeled_statement" => {
                    if let Some(block) = blocks.get_mut(&last_block) {
                        let stmt = self.node_text(child, source);
                        block.statements.push(stmt);
                        block.end_line = child.end_position().row + 1;
                    }
                }
                _ => {}
            }
        }

        last_block
    }

    /// Process if statement for CFG.
    #[allow(clippy::too_many_arguments)]
    fn process_if_cfg(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        loop_headers: &mut Vec<BlockId>,
        loop_exits: &mut Vec<BlockId>,
    ) -> BlockId {
        *block_id += 1;
        let cond_block = BlockId(*block_id);
        let condition = self.child_by_field(node, "condition")
            .map(|n| self.node_text(n, source))
            .unwrap_or_else(|| "condition".to_string());

        blocks.insert(
            cond_block,
            CFGBlock {
                id: cond_block,
                label: format!("if ({})", condition),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(current_block, cond_block, None));

        // Process then branch
        *block_id += 1;
        let then_block = BlockId(*block_id);
        blocks.insert(
            then_block,
            CFGBlock {
                id: then_block,
                label: "then".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(cond_block, then_block, Some("true".to_string())));

        let then_end = if let Some(consequence) = self.child_by_field(node, "consequence") {
            self.process_cfg_block(
                consequence, source, blocks, edges, block_id,
                then_block, exits, loop_headers, loop_exits,
            )
        } else {
            then_block
        };

        // Merge block
        *block_id += 1;
        let merge_block = BlockId(*block_id);
        blocks.insert(
            merge_block,
            CFGBlock {
                id: merge_block,
                label: "merge".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(then_end, merge_block, None));

        // Process else branch if present
        if let Some(alternative) = self.child_by_field(node, "alternative") {
            *block_id += 1;
            let else_block = BlockId(*block_id);
            blocks.insert(
                else_block,
                CFGBlock {
                id: else_block,
                label: "else".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: alternative.start_position().row + 1,
                end_line: alternative.start_position().row + 1,
            },
            );

            edges.push(CFGEdge::from_label(cond_block, else_block, Some("false".to_string())));

            let else_end = self.process_cfg_block(
                alternative, source, blocks, edges, block_id,
                else_block, exits, loop_headers, loop_exits,
            );

            edges.push(CFGEdge::from_label(else_end, merge_block, None));
        } else {
            edges.push(CFGEdge::from_label(cond_block, merge_block, Some("false".to_string())));
        }

        merge_block
    }

    /// Process loop statement for CFG.
    #[allow(clippy::too_many_arguments)]
    fn process_loop_cfg(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        loop_headers: &mut Vec<BlockId>,
        loop_exits: &mut Vec<BlockId>,
    ) -> BlockId {
        *block_id += 1;
        let header_block = BlockId(*block_id);
        let label = match node.kind() {
            "while_statement" => {
                let cond = self.child_by_field(node, "condition")
                    .map(|n| self.node_text(n, source))
                    .unwrap_or_else(|| "condition".to_string());
                format!("while ({})", cond)
            }
            "for_statement" => "for".to_string(),
            "for_range_loop" => "for (range)".to_string(),
            "do_statement" => "do-while".to_string(),
            _ => "loop".to_string(),
        };

        blocks.insert(
            header_block,
            CFGBlock {
                id: header_block,
                label,
                block_type: BlockType::LoopHeader,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(current_block, header_block, None));

        // Exit block
        *block_id += 1;
        let exit_block = BlockId(*block_id);
        blocks.insert(
            exit_block,
            CFGBlock {
                id: exit_block,
                label: "loop_exit".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        loop_headers.push(header_block);
        loop_exits.push(exit_block);

        // Process body
        if let Some(body) = self.child_by_field(node, "body") {
            let body_end = self.process_cfg_block(
                body, source, blocks, edges, block_id,
                header_block, exits, loop_headers, loop_exits,
            );

            edges.push(CFGEdge::from_label(body_end, header_block, Some("loop".to_string())));
        }

        edges.push(CFGEdge::from_label(header_block, exit_block, Some("exit".to_string())));

        loop_headers.pop();
        loop_exits.pop();

        exit_block
    }

    /// Process switch statement for CFG.
    #[allow(clippy::too_many_arguments)]
    fn process_switch_cfg(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        loop_headers: &mut Vec<BlockId>,
        loop_exits: &mut Vec<BlockId>,
    ) -> BlockId {
        *block_id += 1;
        let switch_block = BlockId(*block_id);
        let condition = self.child_by_field(node, "condition")
            .map(|n| self.node_text(n, source))
            .unwrap_or_else(|| "expr".to_string());

        blocks.insert(
            switch_block,
            CFGBlock {
                id: switch_block,
                label: format!("switch ({})", condition),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(current_block, switch_block, None));

        // Exit block
        *block_id += 1;
        let exit_block = BlockId(*block_id);
        blocks.insert(
            exit_block,
            CFGBlock {
                id: exit_block,
                label: "switch_exit".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        loop_exits.push(exit_block);

        // Process case bodies
        if let Some(body) = self.child_by_field(node, "body") {
            let mut cursor = body.walk();
            for child in body.children(&mut cursor) {
                if child.kind() == "case_statement" {
                    *block_id += 1;
                    let case_block = BlockId(*block_id);

                    blocks.insert(
                        case_block,
                        CFGBlock {
                id: case_block,
                label: "case".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.end_position().row + 1,
            },
                    );

                    edges.push(CFGEdge::from_label(switch_block, case_block, Some("case".to_string())));

                    let case_end = self.process_cfg_block(
                        child, source, blocks, edges, block_id,
                        case_block, exits, loop_headers, loop_exits,
                    );

                    edges.push(CFGEdge::from_label(case_end, exit_block, None));
                }
            }
        }

        loop_exits.pop();
        exit_block
    }

    /// Process try-catch statement for CFG.
    #[allow(clippy::too_many_arguments)]
    fn process_try_cfg(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        loop_headers: &mut Vec<BlockId>,
        loop_exits: &mut Vec<BlockId>,
    ) -> BlockId {
        *block_id += 1;
        let try_block = BlockId(*block_id);

        blocks.insert(
            try_block,
            CFGBlock {
                id: try_block,
                label: "try".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(current_block, try_block, None));

        // Exit block
        *block_id += 1;
        let exit_block = BlockId(*block_id);
        blocks.insert(
            exit_block,
            CFGBlock {
                id: exit_block,
                label: "try_exit".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        // Process try body
        if let Some(body) = self.child_by_field(node, "body") {
            let try_end = self.process_cfg_block(
                body, source, blocks, edges, block_id,
                try_block, exits, loop_headers, loop_exits,
            );
            edges.push(CFGEdge::from_label(try_end, exit_block, None));
        }

        // Process catch clauses
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "catch_clause" {
                *block_id += 1;
                let catch_block = BlockId(*block_id);

                blocks.insert(
                    catch_block,
                    CFGBlock {
                id: catch_block,
                label: "catch".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.end_position().row + 1,
            },
                );

                edges.push(CFGEdge::from_label(try_block, catch_block, Some("exception".to_string())));

                if let Some(body) = self.child_by_field(child, "body") {
                    let catch_end = self.process_cfg_block(
                        body, source, blocks, edges, block_id,
                        catch_block, exits, loop_headers, loop_exits,
                    );
                    edges.push(CFGEdge::from_label(catch_end, exit_block, None));
                }
            }
        }

        exit_block
    }

    /// Build DFG for a C++ function.
    fn build_cpp_dfg(&self, node: Node, source: &[u8], func_name: &str) -> DFGInfo {
        let mut definitions: HashMap<String, Vec<usize>> = HashMap::new();
        let mut uses: HashMap<String, Vec<usize>> = HashMap::new();
        let mut edges = Vec::new();

        // Extract parameters as variable definitions
        if let Some(declarator) = self.child_by_field(node, "declarator") {
            if let Some(params) = self.child_by_field(declarator, "parameters") {
                let mut cursor = params.walk();
                for child in params.children(&mut cursor) {
                    if child.kind() == "parameter_declaration" {
                        if let Some(name_node) = child.children(&mut child.walk())
                            .find(|c| c.kind() == "identifier")
                        {
                            let name = self.node_text(name_node, source);
                            let line = child.start_position().row + 1;
                            definitions.entry(name.clone()).or_default().push(line);
                            edges.push(DataflowEdge {
                                variable: name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Param,
                            });
                        }
                    }
                }
            }
        }

        // Process function body
        if let Some(body) = self.child_by_field(node, "body") {
            self.process_dfg_block(body, source, &mut definitions, &mut uses, &mut edges);
        }

        DFGInfo::new(func_name.to_string(), edges, definitions, uses)
    }

    /// Process a block for DFG construction.
    fn process_dfg_block(
        &self,
        node: Node,
        source: &[u8],
        definitions: &mut HashMap<String, Vec<usize>>,
        uses: &mut HashMap<String, Vec<usize>>,
        edges: &mut Vec<DataflowEdge>,
    ) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "declaration" => {
                    self.process_dfg_declaration(child, source, definitions, uses, edges);
                }
                "expression_statement" => {
                    if let Some(expr) = child.children(&mut child.walk()).nth(0) {
                        self.process_dfg_expression(expr, source, definitions, uses, edges, child.start_position().row + 1);
                    }
                }
                "return_statement" => {
                    let line = child.start_position().row + 1;
                    // Collect uses from return expression
                    if let Some(expr) = child.children(&mut child.walk()).find(|c| c.kind() != "return") {
                        self.collect_dfg_uses(expr, source, line, definitions, uses, edges);
                    }
                }
                "if_statement" | "while_statement" | "for_statement" | "for_range_loop" => {
                    if let Some(body) = self.child_by_field(child, "body") {
                        self.process_dfg_block(body, source, definitions, uses, edges);
                    }
                    if let Some(alt) = self.child_by_field(child, "alternative") {
                        self.process_dfg_block(alt, source, definitions, uses, edges);
                    }
                }
                "compound_statement" => {
                    self.process_dfg_block(child, source, definitions, uses, edges);
                }
                _ => {}
            }
        }
    }

    /// Process a declaration for DFG.
    fn process_dfg_declaration(
        &self,
        node: Node,
        source: &[u8],
        definitions: &mut HashMap<String, Vec<usize>>,
        uses: &mut HashMap<String, Vec<usize>>,
        edges: &mut Vec<DataflowEdge>,
    ) {
        let line = node.start_position().row + 1;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "init_declarator" => {
                    if let Some(decl) = self.child_by_field(child, "declarator") {
                        let name = self.node_text(decl, source);
                        definitions.entry(name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: name.clone(),
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Definition,
                            });

                        // Check for initializer
                        if let Some(value) = self.child_by_field(child, "value") {
                            self.collect_dfg_uses(value, source, line, definitions, uses, edges);
                        }
                    }
                }
                "identifier" => {
                    let name = self.node_text(child, source);
                    definitions.entry(name.clone()).or_default().push(line);
                    edges.push(DataflowEdge {
                        variable: name,
                        from_line: line,
                        to_line: line,
                        kind: DataflowKind::Definition,
                            });
                }
                _ => {}
            }
        }
    }

    /// Process an expression for DFG.
    fn process_dfg_expression(
        &self,
        node: Node,
        source: &[u8],
        definitions: &mut HashMap<String, Vec<usize>>,
        uses: &mut HashMap<String, Vec<usize>>,
        edges: &mut Vec<DataflowEdge>,
        line: usize,
    ) {
        match node.kind() {
            "assignment_expression" | "compound_assignment_expr" => {
                if let Some(left) = self.child_by_field(node, "left") {
                    let target = self.node_text(left, source);

                    if let Some(right) = self.child_by_field(node, "right") {
                        self.collect_dfg_uses(right, source, line, definitions, uses, edges);
                    }

                    // Record mutation
                    definitions.entry(target.clone()).or_default().push(line);
                    edges.push(DataflowEdge {
                        variable: target,
                        from_line: line,
                        to_line: line,
                        kind: DataflowKind::Mutation,
                            });
                }
            }
            "update_expression" => {
                if let Some(arg) = self.child_by_field(node, "argument") {
                    let name = self.node_text(arg, source);

                    // Record use and mutation
                    uses.entry(name.clone()).or_default().push(line);
                    definitions.entry(name.clone()).or_default().push(line);
                    edges.push(DataflowEdge {
                        variable: name,
                        from_line: line,
                        to_line: line,
                        kind: DataflowKind::Mutation,
                            });
                }
            }
            _ => {}
        }
    }

    /// Collect variable uses from an expression for DFG.
    fn collect_dfg_uses(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        definitions: &HashMap<String, Vec<usize>>,
        uses: &mut HashMap<String, Vec<usize>>,
        edges: &mut Vec<DataflowEdge>,
    ) {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node, source);
                uses.entry(name.clone()).or_default().push(line);

                // Find most recent definition for this variable
                if let Some(def_lines) = definitions.get(&name) {
                    if let Some(&def_line) = def_lines.last() {
                        edges.push(DataflowEdge {
                            variable: name,
                            from_line: def_line,
                            to_line: line,
                            kind: DataflowKind::Use,
                            });
                    }
                }
            }
            _ => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.collect_dfg_uses(child, source, line, definitions, uses, edges);
                }
            }
        }
    }

    /// Extract a single #include directive.
    fn extract_include(&self, node: Node, source: &[u8]) -> Option<ImportInfo> {
        let mut path = String::new();
        let mut is_system = false;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "system_lib_string" => {
                    path = self.node_text(child, source);
                    path = path.trim_start_matches('<').trim_end_matches('>').to_string();
                    is_system = true;
                }
                "string_literal" => {
                    path = self.node_text(child, source);
                    path = path.trim_matches('"').to_string();
                    is_system = false;
                }
                _ => {}
            }
        }

        if path.is_empty() {
            return None;
        }

        Some(ImportInfo {
            module: path,
            names: Vec::new(),
            aliases: HashMap::new(),
            is_from: !is_system,
            level: if is_system { 0 } else { 1 },
            line_number: node.start_position().row + 1,
            visibility: None,
        })
    }

    /// Extract using declarations.
    fn extract_using(&self, node: Node, source: &[u8]) -> Option<ImportInfo> {
        if node.kind() != "using_declaration" {
            return None;
        }

        let mut names = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            if child.kind() == "qualified_identifier" || child.kind() == "identifier" {
                names.push(self.node_text(child, source));
            }
        }

        if names.is_empty() {
            return None;
        }

        Some(ImportInfo {
            module: names.join("::"),
            names: Vec::new(),
            aliases: HashMap::new(),
            is_from: true,
            level: 0,
            line_number: node.start_position().row + 1,
            visibility: None,
        })
    }
}

impl Language for Cpp {
    fn name(&self) -> &'static str {
        "cpp"
    }

    fn extensions(&self) -> &[&'static str] {
        &[".cpp", ".cc", ".cxx", ".hpp", ".hh", ".hxx", ".h++", ".c++"]
    }

    fn parser(&self) -> Result<Parser> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_cpp::LANGUAGE.into())
            .map_err(|e| BrrrError::TreeSitter(e.to_string()))?;
        Ok(parser)
    }

    fn extract_function(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        self.extract_cpp_function(node, source)
    }

    fn extract_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        self.extract_cpp_class(node, source)
    }

    fn extract_imports(&self, tree: &Tree, source: &[u8]) -> Vec<ImportInfo> {
        let mut imports = Vec::new();
        let root = tree.root_node();
        let mut cursor = root.walk();

        for child in root.children(&mut cursor) {
            match child.kind() {
                "preproc_include" => {
                    if let Some(import) = self.extract_include(child, source) {
                        imports.push(import);
                    }
                }
                "using_declaration" => {
                    if let Some(import) = self.extract_using(child, source) {
                        imports.push(import);
                    }
                }
                _ => {}
            }
        }

        imports
    }

    fn function_query(&self) -> &'static str {
        r#"[
            (function_definition
                declarator: (function_declarator
                    declarator: (identifier) @name)) @function
            (function_definition
                declarator: (function_declarator
                    declarator: (qualified_identifier) @name)) @function
            (function_definition
                declarator: (function_declarator
                    declarator: (destructor_name) @name)) @function
            (function_definition
                declarator: (function_declarator
                    declarator: (operator_name) @name)) @function
            (declaration
                declarator: (function_declarator
                    declarator: (identifier) @name)) @function
            (template_declaration
                (function_definition
                    declarator: (function_declarator
                        declarator: (identifier) @name))) @function
            (lambda_expression) @function
        ]"#
    }

    fn class_query(&self) -> &'static str {
        r#"[
            (class_specifier name: (type_identifier) @name) @class
            (struct_specifier name: (type_identifier) @name) @struct
            (enum_specifier name: (type_identifier) @name) @enum
            (namespace_definition name: (namespace_identifier) @name) @namespace
            (template_declaration
                (class_specifier name: (type_identifier) @name)) @class
            (template_declaration
                (struct_specifier name: (type_identifier) @name)) @struct
            (alias_declaration name: (type_identifier) @name) @alias
            (type_definition declarator: (type_identifier) @name) @typedef
            ; Match function_definitions that might be macro-preceded classes
            ; (e.g., NLOHMANN_BASIC_JSON_TPL_DECLARATION\nclass basic_json {...})
            ; The extraction code will filter out actual functions via extract_macro_preceded_class
            (function_definition
                type: (type_identifier) @macro_type) @class
        ]"#
    }

    fn call_query(&self) -> &'static str {
        r#"[
            (call_expression function: (identifier) @callee) @call
            (call_expression function: (qualified_identifier) @callee) @call
            (call_expression function: (field_expression field: (field_identifier) @callee)) @call
            (call_expression function: (template_function) @callee) @call
        ]"#
    }

    fn build_cfg(&self, node: Node, source: &[u8]) -> Result<CFGInfo> {
        if node.kind() != "function_definition" {
            return Err(BrrrError::UnsupportedLanguage(
                "Node is not a function definition".to_string(),
            ));
        }

        let func_name = self.child_by_field(node, "declarator")
            .and_then(|d| self.extract_function_name(d, source))
            .unwrap_or_else(|| "anonymous".to_string());

        Ok(self.build_cpp_cfg(node, source, &func_name))
    }

    fn build_dfg(&self, node: Node, source: &[u8]) -> Result<DFGInfo> {
        if node.kind() != "function_definition" {
            return Err(BrrrError::UnsupportedLanguage(
                "Node is not a function definition".to_string(),
            ));
        }

        let func_name = self.child_by_field(node, "declarator")
            .and_then(|d| self.extract_function_name(d, source))
            .unwrap_or_else(|| "anonymous".to_string());

        Ok(self.build_cpp_dfg(node, source, &func_name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_cpp(source: &str) -> Tree {
        let cpp = Cpp;
        let mut parser = cpp.parser().expect("Failed to create parser");
        parser.parse(source, None).expect("Failed to parse")
    }

    #[test]
    fn test_template_class() {
        let source = r#"
template<typename T>
class Container {
public:
    T value;
    void set(T v) { value = v; }
};
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;

        let root = tree.root_node();
        let mut found = false;

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "template_declaration" {
                if let Some(class) = cpp.extract_class(child, source.as_bytes()) {
                    assert_eq!(class.name, "Container");
                    assert!(class.decorators.iter().any(|d| d.contains("template")));
                    found = true;
                }
            }
        }

        assert!(found, "Template class not found");
    }

    #[test]
    fn test_namespace() {
        let source = r#"
namespace foo {
    void bar() {}
}
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;

        let root = tree.root_node();
        let mut found = false;

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "namespace_definition" {
                if let Some(ns) = cpp.extract_class(child, source.as_bytes()) {
                    assert_eq!(ns.name, "foo");
                    assert!(ns.decorators.contains(&"namespace".to_string()));
                    found = true;
                }
            }
        }

        assert!(found, "Namespace not found");
    }

    #[test]
    fn test_class_with_access_specifiers() {
        let source = r#"
class MyClass {
public:
    int public_field;
private:
    int private_field;
protected:
    int protected_field;
};
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;

        let root = tree.root_node();
        let mut cursor = root.walk();

        for child in root.children(&mut cursor) {
            if child.kind() == "class_specifier" {
                if let Some(class) = cpp.extract_class(child, source.as_bytes()) {
                    assert_eq!(class.name, "MyClass");
                    assert_eq!(class.fields.len(), 3);

                    let pub_field = class.fields.iter().find(|f| f.name == "public_field");
                    assert!(pub_field.is_some());
                    assert_eq!(pub_field.unwrap().visibility, Some("public".to_string()));

                    let priv_field = class.fields.iter().find(|f| f.name == "private_field");
                    assert!(priv_field.is_some());
                    assert_eq!(priv_field.unwrap().visibility, Some("private".to_string()));
                }
            }
        }
    }

    #[test]
    fn test_constructor_destructor() {
        let source = r#"
class MyClass {
public:
    MyClass() {}
    ~MyClass() {}
};
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;

        let root = tree.root_node();
        let mut cursor = root.walk();

        for child in root.children(&mut cursor) {
            if child.kind() == "class_specifier" {
                if let Some(class) = cpp.extract_class(child, source.as_bytes()) {
                    let ctor = class.methods.iter().find(|m| m.name == "MyClass");
                    assert!(ctor.is_some());
                    assert!(ctor.unwrap().decorators.contains(&"constructor".to_string()));

                    let dtor = class.methods.iter().find(|m| m.name.contains('~'));
                    assert!(dtor.is_some());
                    assert!(dtor.unwrap().decorators.contains(&"destructor".to_string()));
                }
            }
        }
    }

    #[test]
    fn test_operator_overloading() {
        let source = r#"
class Vector {
public:
    Vector operator+(const Vector& other) { return *this; }
};
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;

        let root = tree.root_node();
        let mut cursor = root.walk();

        for child in root.children(&mut cursor) {
            if child.kind() == "class_specifier" {
                if let Some(class) = cpp.extract_class(child, source.as_bytes()) {
                    let op = class.methods.iter().find(|m| m.name.contains("operator"));
                    assert!(op.is_some());
                    assert!(op.unwrap().decorators.contains(&"operator".to_string()));
                }
            }
        }
    }

    #[test]
    fn test_lambda_expression() {
        let source = r#"
void foo() {
    auto f = [x, &y](int a) -> int { return a + x + y; };
}
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;

        // Walk the tree to find lambda
        fn find_lambda(node: Node, cpp: &Cpp, source: &[u8]) -> Option<FunctionInfo> {
            if node.kind() == "lambda_expression" {
                return cpp.extract_lambda(node, source);
            }
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if let Some(lambda) = find_lambda(child, cpp, source) {
                    return Some(lambda);
                }
            }
            None
        }

        let lambda = find_lambda(tree.root_node(), &cpp, source.as_bytes());
        assert!(lambda.is_some());
        let lambda = lambda.unwrap();
        assert!(lambda.decorators.contains(&"lambda".to_string()));
        assert!(lambda.decorators.iter().any(|d| d.contains("captures")));
    }

    #[test]
    fn test_is_method_detection() {
        let source = r#"
class MyClass {
public:
    void method1() {}
    int method2(int x) { return x; }
};

void free_function() {}
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;

        let root = tree.root_node();
        let mut cursor = root.walk();
        let mut methods_found = 0;
        let mut free_functions_found = 0;

        fn walk_tree(node: Node, cpp: &Cpp, source: &[u8], methods: &mut i32, free_funcs: &mut i32) {
            if node.kind() == "function_definition" {
                if let Some(func) = cpp.extract_function(node, source) {
                    if func.is_method {
                        *methods += 1;
                    } else {
                        *free_funcs += 1;
                    }
                }
            }
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                walk_tree(child, cpp, source, methods, free_funcs);
            }
        }

        walk_tree(root, &cpp, source.as_bytes(), &mut methods_found, &mut free_functions_found);

        assert_eq!(methods_found, 2, "Should find 2 methods");
        assert_eq!(free_functions_found, 1, "Should find 1 free function");
    }

    #[test]
    fn test_macro_preceded_class_detection() {
        // This pattern mimics nlohmann/json's NLOHMANN_BASIC_JSON_TPL_DECLARATION
        let source = r#"
TEMPLATE_MACRO_DECLARATION
class basic_json
{
public:
    void foo() {}
private:
    int x;
};
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;

        let root = tree.root_node();
        let mut found = false;

        fn find_macro_class(node: Node, cpp: &Cpp, source: &[u8]) -> Option<ClassInfo> {
            if node.kind() == "function_definition" {
                if let Some(class) = cpp.extract_macro_preceded_class(node, source) {
                    return Some(class);
                }
            }
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if let Some(class) = find_macro_class(child, cpp, source) {
                    return Some(class);
                }
            }
            None
        }

        if let Some(class) = find_macro_class(root, &cpp, source.as_bytes()) {
            found = true;
            assert_eq!(class.name, "basic_json");
            assert!(class.decorators.iter().any(|d| d.contains("macro:")));
        }

        assert!(found, "Should detect macro-preceded class");
    }

    #[test]
    fn test_is_macro_identifier() {
        let cpp = Cpp;

        // Should be detected as macros
        assert!(cpp.is_macro_identifier("NLOHMANN_BASIC_JSON_TPL_DECLARATION"));
        assert!(cpp.is_macro_identifier("MY_MACRO"));
        assert!(cpp.is_macro_identifier("FOO_BAR_BAZ"));
        assert!(cpp.is_macro_identifier("API_EXPORT"));

        // Should NOT be detected as macros
        assert!(!cpp.is_macro_identifier("int")); // Too short
        assert!(!cpp.is_macro_identifier("FOO")); // Too short (len <= 3)
        assert!(!cpp.is_macro_identifier("MyClass")); // Has lowercase
        assert!(!cpp.is_macro_identifier("std::vector")); // Has special chars
        assert!(!cpp.is_macro_identifier("")); // Empty
    }
}
