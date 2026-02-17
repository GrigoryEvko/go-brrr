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

use phf::phf_set;
use rustc_hash::FxHashMap;
use tree_sitter::{Node, Parser, Tree};

use crate::ast::types::{ClassInfo, FieldInfo, FunctionInfo, ImportInfo};
use crate::cfg::types::{BlockId, BlockType, CFGBlock, CFGEdge, CFGInfo, EdgeType};
use crate::dfg::types::{DFGInfo, DataflowEdge, DataflowKind};
use crate::error::{BrrrError, Result};
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

/// CUDA/HIP function qualifiers that tree-sitter-cpp misparses as the return type.
/// These appear as `type_identifier` nodes because the C++ grammar doesn't know them.
/// When detected, the actual return type is recovered from the adjacent ERROR node.
static CUDA_QUALIFIERS: phf::Set<&'static str> = phf_set! {
    "__global__", "__device__", "__host__", "__forceinline__",
    "__launch_bounds__", "__noinline__", "__shared__",
    "__constant__", "__managed__", "__restrict__",
};

/// Check if an identifier looks like a function attribute macro rather than a type.
///
/// Heuristic: identifiers that are ALL_UPPER_CASE (with underscores) and at least
/// 4 characters are likely preprocessor macros used as function decorators
/// (e.g., C10_HOST_DEVICE, TORCH_API, C10_EXPORT). These get misidentified as
/// the return type by tree-sitter-cpp when they precede the actual return type.
fn is_likely_attribute_macro(name: &str) -> bool {
    if name.len() < 4 {
        return false;
    }
    // Must start with a letter or underscore
    let first = name.as_bytes()[0];
    if !first.is_ascii_alphabetic() && first != b'_' {
        return false;
    }
    // Check for ALL_UPPER_WITH_UNDERSCORES pattern
    name.bytes().all(|b| b.is_ascii_uppercase() || b.is_ascii_digit() || b == b'_')
}

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
    ///
    /// Handles CUDA/HIP qualifiers (`__global__`, `__device__`, etc.) and
    /// macro-style attributes (`C10_HOST_DEVICE`, `TORCH_API`, etc.) that
    /// tree-sitter-cpp misparses as the return type. When detected, the
    /// actual return type is recovered from the adjacent ERROR node.
    fn extract_return_type(&self, node: Node, source: &[u8]) -> Option<String> {
        if let Some(type_node) = self.child_by_field(node, "type") {
            let type_text = self.get_text(type_node, source);

            // tree-sitter-cpp treats CUDA qualifiers and macro attributes as
            // type_identifier (it thinks they're the return type). The real
            // return type ends up in an ERROR sibling node.
            if type_node.kind() == "type_identifier"
                && (CUDA_QUALIFIERS.contains(type_text) || is_likely_attribute_macro(type_text))
            {
                return self.recover_return_type_from_error(node, source);
            }

            return Some(type_text.to_string());
        }

        // Trailing return type: auto f() -> int
        if let Some(trailing) = self.child_by_field(node, "trailing_return_type") {
            return Some(self.node_text(trailing, source));
        }

        let mut type_parts = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "storage_class_specifier"
                | "virtual"
                | "explicit"
                | "inline"
                | "constexpr"
                | "consteval" => {}
                "type_qualifier" => {
                    type_parts.push(self.node_text(child, source));
                }
                "primitive_type" | "type_identifier" | "sized_type_specifier" | "auto" => {
                    let text = self.get_text(child, source);
                    if child.kind() == "type_identifier"
                        && (CUDA_QUALIFIERS.contains(text) || is_likely_attribute_macro(text))
                    {
                        continue;
                    }
                    type_parts.push(text.to_string());
                }
                "template_type" | "qualified_identifier" => {
                    type_parts.push(self.node_text(child, source));
                }
                "function_declarator" | "pointer_declarator" | "reference_declarator" => {
                    break;
                }
                "ERROR" => {
                    if type_parts.is_empty() {
                        if let Some(recovered) = self.extract_type_from_error_node(child, source) {
                            type_parts.push(recovered);
                        }
                    }
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

    /// Recover the actual return type when a CUDA qualifier was misidentified.
    ///
    /// Scans the function_definition's children for an ERROR node containing
    /// the real return type.
    fn recover_return_type_from_error(&self, node: Node, source: &[u8]) -> Option<String> {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "ERROR" {
                return self.extract_type_from_error_node(child, source);
            }
        }
        None
    }

    /// Extract a type name from an ERROR node's contents.
    ///
    /// Skips stacked CUDA qualifiers (e.g., `__device__ __forceinline__ float`)
    /// and returns the last non-qualifier token as the return type.
    fn extract_type_from_error_node(&self, error_node: Node, source: &[u8]) -> Option<String> {
        let mut cursor = error_node.walk();
        let mut last_type = None;

        for child in error_node.children(&mut cursor) {
            if child.kind() == "identifier" {
                let text = self.get_text(child, source);
                if !CUDA_QUALIFIERS.contains(text) && !is_likely_attribute_macro(text) {
                    last_type = Some(text.to_string());
                }
            }
        }

        // Fallback: parse raw ERROR text for the last non-qualifier token.
        // Handles primitives like "void" that may not appear as identifier nodes.
        if last_type.is_none() {
            let text = self.get_text(error_node, source).trim();
            for token in text.split_whitespace().rev() {
                if !CUDA_QUALIFIERS.contains(token) && !is_likely_attribute_macro(token) {
                    return Some(token.to_string());
                }
            }
        }

        last_type
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
                    return Some(self.node_text(child, source));
                }
                "pointer_declarator" => {
                    let (name, _) = self.extract_pointer_declarator(child, source);
                    if !name.is_empty() {
                        return Some(name);
                    }
                }
                // reference_declarator wrapping a function_declarator (e.g., T& operator=())
                "function_declarator" => {
                    return self.extract_function_name(child, source);
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
                if name.is_empty() {
                    None
                } else {
                    Some(name)
                }
            }
            "reference_declarator" => {
                // Reference-returning functions: reference_declarator -> & -> function_declarator
                // Look for function_declarator child first, then fall back to identifier.
                let mut ref_cursor = node.walk();
                for child in node.children(&mut ref_cursor) {
                    if child.kind() == "function_declarator" {
                        return self.extract_function_name(child, source);
                    }
                }
                let (name, _) = self.extract_reference_declarator(node, source);
                if name.is_empty() {
                    None
                } else {
                    Some(name)
                }
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

    /// Check if a type identifier is a CUDA execution space or attribute qualifier.
    ///
    /// tree-sitter-cpp does not understand CUDA qualifiers, so it misparses them as
    /// the return type. For example, `__global__ void kernel(...)` becomes:
    ///   type: type_identifier "__global__"
    ///   ERROR: identifier "void"
    ///   declarator: function_declarator ...
    ///
    /// This detects the CUDA qualifier so we can extract the real return type from
    /// the ERROR node and report the qualifier as a decorator.
    fn is_cuda_qualifier(text: &str) -> bool {
        CUDA_QUALIFIERS.contains(text)
    }

    /// Extract CUDA qualifiers and actual return type from a misparsed function_definition.
    ///
    /// When CUDA qualifiers are present, tree-sitter-cpp produces:
    ///   function_definition
    ///     type: type_identifier ("__global__")
    ///     ERROR (contains the actual return type and any extra qualifiers)
    ///     declarator: function_declarator
    ///
    /// Returns (cuda_decorators, actual_return_type) if CUDA qualifiers are detected,
    /// None otherwise.
    fn extract_cuda_info(&self, node: Node, source: &[u8]) -> Option<(Vec<String>, Option<String>)> {
        let type_node = self.child_by_field(node, "type")?;
        let type_text = self.get_text(type_node, source);

        // Detect both CUDA dunder qualifiers (__global__, __device__) and
        // macro-style attributes (C10_HOST_DEVICE, TORCH_API) that
        // tree-sitter-cpp misidentifies as the return type.
        if type_node.kind() != "type_identifier"
            || (!Self::is_cuda_qualifier(type_text) && !is_likely_attribute_macro(type_text))
        {
            return None;
        }

        let mut qualifiers = vec![type_text.to_string()];
        let mut actual_return_type = None;

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "ERROR" {
                let mut err_cursor = child.walk();
                for err_child in child.children(&mut err_cursor) {
                    match err_child.kind() {
                        "identifier" | "primitive_type" | "type_identifier"
                        | "sized_type_specifier" => {
                            let text = self.get_text(err_child, source);
                            if Self::is_cuda_qualifier(text) || is_likely_attribute_macro(text) {
                                qualifiers.push(text.to_string());
                            } else {
                                actual_return_type = Some(text.to_string());
                            }
                        }
                        _ => {}
                    }
                }
            }
            if matches!(
                child.kind(),
                "function_declarator" | "pointer_declarator" | "reference_declarator"
            ) {
                break;
            }
        }

        // Fallback: if no return type found in ERROR child nodes, try raw text
        if actual_return_type.is_none() {
            let mut cursor2 = node.walk();
            for child in node.children(&mut cursor2) {
                if child.kind() == "ERROR" {
                    let text = self.get_text(child, source).trim();
                    for token in text.split_whitespace().rev() {
                        if !Self::is_cuda_qualifier(token) && !is_likely_attribute_macro(token) {
                            actual_return_type = Some(token.to_string());
                            break;
                        }
                    }
                    break;
                }
            }
        }

        Some((qualifiers, actual_return_type))
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
            let starts_with_class =
                decl_text.starts_with("class ") || decl_text.starts_with("struct ");

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
                    vec![decl, node] // Search both qualified_identifier and function_definition
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
                if decl_text != "class"
                    && decl_text != "struct"
                    && !decl_text.contains('(')
                    && !decl_text.contains('{')
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
        let has_access_specifiers = body.children(&mut body.walk()).any(|c| {
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
        let decorators = vec!["class".to_string(), format!("macro:{}", type_text)];

        Some(ClassInfo {
            name,
            bases: Vec::new(), // Hard to extract from misparsed tree
            docstring,
            methods: Vec::new(), // Would need more complex extraction
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
        if let Some(capture_list) = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "lambda_capture_specifier")
        {
            let capture_text = self.node_text(capture_list, source);
            captures.push(format!("captures:{}", capture_text));
        }

        // Extract parameters
        let params = self
            .child_by_field(node, "declarator")
            .and_then(|d| self.child_by_field(d, "parameters"))
            .map(|p| self.extract_params(p, source))
            .unwrap_or_default();

        // Extract return type (trailing return type)
        let return_type = self
            .child_by_field(node, "declarator")
            .and_then(|d| {
                d.children(&mut d.walk())
                    .find(|c| c.kind() == "trailing_return_type")
            })
            .map(|t| self.node_text(t, source));

        let mut decorators = vec!["lambda".to_string()];
        decorators.extend(captures);

        // Check for mutable
        if node
            .children(&mut node.walk())
            .any(|c| c.kind() == "mutable")
        {
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
    fn extract_template_declaration<'a>(
        &self,
        node: Node<'a>,
        source: &[u8],
    ) -> Option<(Vec<String>, Node<'a>)> {
        if node.kind() != "template_declaration" {
            return None;
        }

        // Extract template parameters
        let template_params = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "template_parameter_list")
            .map(|p| self.extract_template_params(p, source))
            .unwrap_or_default();

        // Build template decorator
        let template_decorator = format!("template<{}>", template_params.join(", "));

        // Find the templated declaration (function_definition, class_specifier, etc.)
        let inner = node.children(&mut node.walk()).find(|c| {
            matches!(
                c.kind(),
                "function_definition"
                    | "declaration"
                    | "class_specifier"
                    | "struct_specifier"
                    | "alias_declaration"
            )
        });

        inner.map(move |n| (vec![template_decorator], n))
    }

    /// Extract namespace declaration.
    fn extract_namespace(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        if node.kind() != "namespace_definition" {
            return None;
        }

        // Get namespace name (could be qualified like foo::bar)
        let name = self
            .child_by_field(node, "name")
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
                    "class_specifier"
                    | "struct_specifier"
                    | "enum_specifier"
                    | "namespace_definition" => {
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
                    if let Some(field) =
                        self.extract_single_field(child, source, &current_visibility)
                    {
                        fields.push(field);
                    }
                }
                _ => {}
            }
        }

        fields
    }

    /// Extract a single field declaration.
    fn extract_single_field(
        &self,
        node: Node,
        source: &[u8],
        visibility: &str,
    ) -> Option<FieldInfo> {
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
                            annotations
                                .push(format!("bitfield:{}", self.node_text(bf_child, source)));
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
    fn extract_class_methods(
        &self,
        node: Node,
        source: &[u8],
        class_name: &str,
    ) -> Vec<FunctionInfo> {
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
                        } else if func.name == format!("~{}", class_name)
                            || func.name.starts_with('~')
                        {
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
            if let Some((template_decorators, inner)) =
                self.extract_template_declaration(node, source)
            {
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

                let params = self
                    .child_by_field(declarator, "parameters")
                    .map(|p| self.extract_params(p, source))
                    .unwrap_or_default();

                let docstring = self.get_doc_comment(node, source);

                let mut decorators = Vec::new();

                // CUDA qualifier detection: tree-sitter-cpp misparses __global__,
                // __device__, etc. as the return type. Detect and fix this.
                let return_type = if let Some((cuda_quals, real_ret)) =
                    self.extract_cuda_info(node, source)
                {
                    decorators.extend(cuda_quals);
                    real_ret
                } else {
                    self.extract_return_type(node, source)
                };

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

                // Check for override/final/noexcept in declarator text
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

                // = default, = delete, = 0 are sibling nodes of the declarator,
                // not children of it. Check tree-sitter child node kinds directly.
                if self.has_specifier(node, "default_method_clause") {
                    decorators.push("default".to_string());
                }
                if self.has_specifier(node, "delete_method_clause") {
                    decorators.push("deleted".to_string());
                }
                // Pure virtual = 0 (in declarations, not definitions typically)
                let func_text = self.node_text(node, source);
                if func_text.contains("= 0") {
                    decorators.push("pure_virtual".to_string());
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
                        let params = self
                            .child_by_field(child, "parameters")
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
            "preproc_function_def" => {
                let name = self
                    .child_by_field(node, "name")
                    .map(|n| self.node_text(n, source))?;
                let docstring = self.get_doc_comment(node, source);
                let params = self
                    .child_by_field(node, "parameters")
                    .map(|p| {
                        let mut params = Vec::new();
                        let mut cursor = p.walk();
                        for child in p.children(&mut cursor) {
                            if child.kind() == "identifier" {
                                params.push(self.node_text(child, source));
                            }
                        }
                        params
                    })
                    .unwrap_or_default();
                Some(FunctionInfo {
                    name,
                    params,
                    return_type: None,
                    docstring,
                    is_method: false,
                    is_async: false,
                    decorators: vec!["macro".to_string()],
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "cpp".to_string(),
                })
            }
            "preproc_def" => {
                let name = self
                    .child_by_field(node, "name")
                    .map(|n| self.node_text(n, source))?;
                let docstring = self.get_doc_comment(node, source);
                Some(FunctionInfo {
                    name,
                    params: Vec::new(),
                    return_type: None,
                    docstring,
                    is_method: false,
                    is_async: false,
                    decorators: vec!["macro".to_string()],
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "cpp".to_string(),
                })
            }
            _ => None,
        }
    }

    /// Extract C++ class or struct with full feature support.
    fn extract_cpp_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        // Handle template declarations
        if node.kind() == "template_declaration" {
            if let Some((template_decorators, inner)) =
                self.extract_template_declaration(node, source)
            {
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
                let name = self
                    .child_by_field(node, "name")
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
                        if child.kind() == "class_specifier"
                            || child.kind() == "struct_specifier"
                            || child.kind() == "enum_specifier"
                        {
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
                let name = self
                    .child_by_field(node, "name")
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
                let name = self
                    .child_by_field(node, "name")
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
        let mut blocks = FxHashMap::default();
        let mut edges = Vec::new();
        let mut block_id = 0;
        let mut exits = Vec::new();
        let mut decision_points: usize = 0;
        // label_name -> BlockId for goto targets
        let mut label_blocks: FxHashMap<String, BlockId> = FxHashMap::default();
        // (from_block, label_name) for unresolved gotos
        let mut pending_gotos: Vec<(BlockId, String)> = Vec::new();

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
                &mut decision_points,
                &mut label_blocks,
                &mut pending_gotos,
            );
        }

        // Resolve pending goto edges
        for (from_block, label_name) in &pending_gotos {
            if let Some(&target) = label_blocks.get(label_name) {
                edges.push(CFGEdge::with_condition(
                    *from_block,
                    target,
                    EdgeType::Goto,
                    format!("goto {}", label_name),
                ));
            }
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
            decision_points,
            comprehension_decision_points: 0,
            nested_cfgs: FxHashMap::default(),
            is_async: false,
            await_points: 0,
            blocking_calls: Vec::new(),
            ..Default::default()
        }
    }

    /// Process a compound statement for CFG construction.
    #[allow(clippy::too_many_arguments)]
    fn process_cfg_block(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        loop_headers: &mut Vec<BlockId>,
        loop_exits: &mut Vec<BlockId>,
        decision_points: &mut usize,
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
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
                        child, source, blocks, edges, block_id, last_block, exits,
                        loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
                    );
                }
                "while_statement" | "for_statement" | "do_statement" | "for_range_loop" => {
                    last_block = self.process_loop_cfg(
                        child, source, blocks, edges, block_id, last_block, exits,
                        loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
                    );
                }
                "switch_statement" => {
                    last_block = self.process_switch_cfg(
                        child, source, blocks, edges, block_id, last_block, exits,
                        loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
                    );
                }
                "try_statement" => {
                    last_block = self.process_try_cfg(
                        child, source, blocks, edges, block_id, last_block, exits,
                        loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
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
                "goto_statement" => {
                    // Extract the label name from the goto statement
                    let mut gc = child.walk();
                    for gchild in child.children(&mut gc) {
                        if gchild.kind() == "statement_identifier" || gchild.kind() == "identifier" {
                            let label_name = self.node_text(gchild, source);
                            pending_gotos.push((last_block, label_name));
                            break;
                        }
                    }
                }
                "labeled_statement" => {
                    // Create a new block for the label target
                    let mut label_name = None;
                    let mut inner_cursor = child.walk();
                    for lchild in child.children(&mut inner_cursor) {
                        if lchild.kind() == "statement_identifier" || lchild.kind() == "identifier" {
                            label_name = Some(self.node_text(lchild, source));
                            break;
                        }
                    }

                    if let Some(name) = label_name {
                        *block_id += 1;
                        let label_block = BlockId(*block_id);
                        blocks.insert(
                            label_block,
                            CFGBlock {
                                id: label_block,
                                label: format!("label: {}", name),
                                block_type: BlockType::Body,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: child.start_position().row + 1,
                                end_line: child.end_position().row + 1,
                            },
                        );
                        edges.push(CFGEdge::unconditional(last_block, label_block));
                        label_blocks.insert(name, label_block);

                        // Process the labeled statement's body (child statements)
                        last_block = self.process_cfg_block(
                            child, source, blocks, edges, block_id, label_block, exits,
                            loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
                        );
                    } else {
                        // No label found, treat as regular statement
                        if let Some(block) = blocks.get_mut(&last_block) {
                            let stmt = self.node_text(child, source);
                            block.statements.push(stmt);
                            block.end_line = child.end_position().row + 1;
                        }
                    }
                }
                "compound_statement" => {
                    last_block = self.process_cfg_block(
                        child, source, blocks, edges, block_id, last_block, exits,
                        loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
                    );
                }
                "declaration" | "expression_statement" => {
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
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        loop_headers: &mut Vec<BlockId>,
        loop_exits: &mut Vec<BlockId>,
        decision_points: &mut usize,
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
    ) -> BlockId {
        *decision_points += 1;
        *block_id += 1;
        let cond_block = BlockId(*block_id);
        let condition = self
            .child_by_field(node, "condition")
            .map(|n| self.node_text(n, source))
            .unwrap_or_else(|| "condition".to_string());

        blocks.insert(
            cond_block,
            CFGBlock {
                id: cond_block,
                label: format!("if ({})", condition),
                block_type: BlockType::Branch,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::unconditional(current_block, cond_block));

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

        edges.push(CFGEdge::new(cond_block, then_block, EdgeType::True));

        let then_end = if let Some(consequence) = self.child_by_field(node, "consequence") {
            self.process_cfg_block(
                consequence, source, blocks, edges, block_id, then_block, exits,
                loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
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

        edges.push(CFGEdge::unconditional(then_end, merge_block));

        // Process else branch if present
        if let Some(alternative) = self.child_by_field(node, "alternative") {
            // Check if this is an "else if" (the alternative is itself an if_statement)
            if alternative.kind() == "if_statement" {
                // "else if" is another decision point; recurse
                let elif_end = self.process_if_cfg(
                    alternative, source, blocks, edges, block_id, cond_block, exits,
                    loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
                );
                edges.push(CFGEdge::unconditional(elif_end, merge_block));
            } else {
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

                edges.push(CFGEdge::new(cond_block, else_block, EdgeType::False));

                let else_end = self.process_cfg_block(
                    alternative, source, blocks, edges, block_id, else_block, exits,
                    loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
                );

                edges.push(CFGEdge::unconditional(else_end, merge_block));
            }
        } else {
            edges.push(CFGEdge::new(cond_block, merge_block, EdgeType::False));
        }

        merge_block
    }

    /// Process loop statement for CFG.
    #[allow(clippy::too_many_arguments)]
    fn process_loop_cfg(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        loop_headers: &mut Vec<BlockId>,
        loop_exits: &mut Vec<BlockId>,
        decision_points: &mut usize,
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
    ) -> BlockId {
        *decision_points += 1;
        *block_id += 1;
        let header_block = BlockId(*block_id);
        let label = match node.kind() {
            "while_statement" => {
                let cond = self
                    .child_by_field(node, "condition")
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

        edges.push(CFGEdge::unconditional(current_block, header_block));

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
                body, source, blocks, edges, block_id, header_block, exits,
                loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
            );

            edges.push(CFGEdge::new(body_end, header_block, EdgeType::Loop));
        }

        edges.push(CFGEdge::new(header_block, exit_block, EdgeType::Exit));

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
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        loop_headers: &mut Vec<BlockId>,
        loop_exits: &mut Vec<BlockId>,
        decision_points: &mut usize,
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
    ) -> BlockId {
        *block_id += 1;
        let switch_block = BlockId(*block_id);
        let condition = self
            .child_by_field(node, "condition")
            .map(|n| self.node_text(n, source))
            .unwrap_or_else(|| "expr".to_string());

        blocks.insert(
            switch_block,
            CFGBlock {
                id: switch_block,
                label: format!("switch ({})", condition),
                block_type: BlockType::Branch,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::unconditional(current_block, switch_block));

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
                    *decision_points += 1;
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

                    edges.push(CFGEdge::new(switch_block, case_block, EdgeType::Case));

                    let case_end = self.process_cfg_block(
                        child, source, blocks, edges, block_id, case_block, exits,
                        loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
                    );

                    edges.push(CFGEdge::unconditional(case_end, exit_block));
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
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        loop_headers: &mut Vec<BlockId>,
        loop_exits: &mut Vec<BlockId>,
        decision_points: &mut usize,
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
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

        edges.push(CFGEdge::unconditional(current_block, try_block));

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
                body, source, blocks, edges, block_id, try_block, exits,
                loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
            );
            edges.push(CFGEdge::unconditional(try_end, exit_block));
        }

        // Process catch clauses
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "catch_clause" {
                *decision_points += 1;
                *block_id += 1;
                let catch_block = BlockId(*block_id);

                blocks.insert(
                    catch_block,
                    CFGBlock {
                        id: catch_block,
                        label: "catch".to_string(),
                        block_type: BlockType::Exception,
                        statements: Vec::new(),
                        func_calls: Vec::new(),
                        start_line: child.start_position().row + 1,
                        end_line: child.end_position().row + 1,
                    },
                );

                edges.push(CFGEdge::new(try_block, catch_block, EdgeType::Exception));

                if let Some(body) = self.child_by_field(child, "body") {
                    let catch_end = self.process_cfg_block(
                        body, source, blocks, edges, block_id, catch_block, exits,
                        loop_headers, loop_exits, decision_points, label_blocks, pending_gotos,
                    );
                    edges.push(CFGEdge::unconditional(catch_end, exit_block));
                }
            }
        }

        exit_block
    }

    /// Build DFG for a C++ function.
    // =========================================================================
    // DFG (Data Flow Graph) construction for C++
    //
    // Extends C DFG with: references (T&), this->, range-for, templates,
    // pointer/struct/array tracking, compound assignments, conditions.
    // =========================================================================

    fn build_cpp_dfg(&self, node: Node, source: &[u8], func_name: &str) -> DFGInfo {
        let mut definitions: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        let mut uses: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        let mut edges = Vec::new();

        // Extract parameters (handle pointer_declarator, reference_declarator)
        if let Some(declarator) = self.child_by_field(node, "declarator") {
            if let Some(params) = self.child_by_field(declarator, "parameters") {
                let mut cursor = params.walk();
                for child in params.children(&mut cursor) {
                    if child.kind() == "parameter_declaration"
                        || child.kind() == "optional_parameter_declaration"
                    {
                        let line = child.start_position().row + 1;
                        self.cpp_dfg_extract_param(child, source, line, &mut edges, &mut definitions);
                    }
                }
            }
        }

        if let Some(body) = self.child_by_field(node, "body") {
            self.cpp_dfg_process_block(body, source, &mut edges, &mut definitions, &mut uses);
        }

        DFGInfo::new(
            func_name.to_string(),
            edges,
            definitions.into_iter().collect(),
            uses.into_iter().collect(),
        )
    }

    /// Extract parameter name from declaration, handling pointer/reference declarators.
    fn cpp_dfg_extract_param(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
    ) {
        // Walk children to find the declarator name
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    let name = self.node_text(child, source);
                    if !name.is_empty() {
                        definitions.entry(name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Param,
                        });
                    }
                }
                "pointer_declarator" => {
                    if let Some(name) = self.cpp_dfg_declarator_name(child, source) {
                        definitions.entry(name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Param,
                        });
                    }
                }
                "reference_declarator" => {
                    if let Some(name) = self.cpp_dfg_declarator_name(child, source) {
                        definitions.entry(name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Param,
                        });
                    }
                }
                _ => {}
            }
        }
    }

    /// Extract the identifier name from a declarator node (recursive unwrap).
    fn cpp_dfg_declarator_name(&self, node: Node, source: &[u8]) -> Option<String> {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node, source);
                if name.is_empty() { None } else { Some(name) }
            }
            "pointer_declarator" | "reference_declarator" => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "identifier" {
                        let name = self.node_text(child, source);
                        if !name.is_empty() {
                            return Some(name);
                        }
                    }
                    if let Some(name) = self.cpp_dfg_declarator_name(child, source) {
                        return Some(name);
                    }
                }
                None
            }
            "array_declarator" => {
                self.child_by_field(node, "declarator")
                    .and_then(|d| self.cpp_dfg_declarator_name(d, source))
            }
            _ => None,
        }
    }

    /// Recursively process a block for C++ DFG.
    fn cpp_dfg_process_block(
        &self,
        node: Node,
        source: &[u8],
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            let line = child.start_position().row + 1;
            match child.kind() {
                "declaration" => {
                    self.cpp_dfg_process_declaration(child, source, line, edges, definitions, uses);
                }
                "expression_statement" => {
                    self.cpp_dfg_process_expr_stmt(child, source, line, edges, definitions, uses);
                }
                "return_statement" => {
                    self.cpp_dfg_process_return(child, source, line, edges, definitions, uses);
                }
                "if_statement" => {
                    if let Some(cond) = self.child_by_field(child, "condition") {
                        self.cpp_dfg_collect_uses(cond, source, line, edges, definitions, uses);
                    }
                    if let Some(consequence) = self.child_by_field(child, "consequence") {
                        self.cpp_dfg_process_block(consequence, source, edges, definitions, uses);
                    }
                    if let Some(alt) = self.child_by_field(child, "alternative") {
                        self.cpp_dfg_process_block(alt, source, edges, definitions, uses);
                    }
                }
                "while_statement" | "do_statement" => {
                    if let Some(cond) = self.child_by_field(child, "condition") {
                        let cl = cond.start_position().row + 1;
                        self.cpp_dfg_collect_uses(cond, source, cl, edges, definitions, uses);
                    }
                    if let Some(body) = self.child_by_field(child, "body") {
                        self.cpp_dfg_process_block(body, source, edges, definitions, uses);
                    }
                }
                "for_statement" => {
                    if let Some(init) = self.child_by_field(child, "initializer") {
                        let il = init.start_position().row + 1;
                        if init.kind() == "declaration" {
                            self.cpp_dfg_process_declaration(init, source, il, edges, definitions, uses);
                        } else {
                            self.cpp_dfg_process_top_expr(init, source, il, edges, definitions, uses);
                        }
                    }
                    if let Some(cond) = self.child_by_field(child, "condition") {
                        let cl = cond.start_position().row + 1;
                        self.cpp_dfg_collect_uses(cond, source, cl, edges, definitions, uses);
                    }
                    if let Some(update) = self.child_by_field(child, "update") {
                        let ul = update.start_position().row + 1;
                        self.cpp_dfg_process_top_expr(update, source, ul, edges, definitions, uses);
                    }
                    if let Some(body) = self.child_by_field(child, "body") {
                        self.cpp_dfg_process_block(body, source, edges, definitions, uses);
                    }
                }
                "for_range_loop" => {
                    // for (auto& x : container)
                    if let Some(decl) = self.child_by_field(child, "declarator") {
                        if let Some(name) = self.cpp_dfg_declarator_name(decl, source) {
                            definitions.entry(name.clone()).or_default().push(line);
                            edges.push(DataflowEdge {
                                variable: name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Definition,
                            });
                        }
                    }
                    if let Some(right) = self.child_by_field(child, "right") {
                        self.cpp_dfg_collect_uses(right, source, line, edges, definitions, uses);
                    }
                    if let Some(body) = self.child_by_field(child, "body") {
                        self.cpp_dfg_process_block(body, source, edges, definitions, uses);
                    }
                }
                "switch_statement" => {
                    if let Some(cond) = self.child_by_field(child, "condition") {
                        self.cpp_dfg_collect_uses(cond, source, line, edges, definitions, uses);
                    }
                    if let Some(body) = self.child_by_field(child, "body") {
                        self.cpp_dfg_process_block(body, source, edges, definitions, uses);
                    }
                }
                "try_statement" => {
                    if let Some(body) = self.child_by_field(child, "body") {
                        self.cpp_dfg_process_block(body, source, edges, definitions, uses);
                    }
                    // Process catch clauses
                    let mut inner = child.walk();
                    for inner_child in child.children(&mut inner) {
                        if inner_child.kind() == "catch_clause" {
                            if let Some(body) = self.child_by_field(inner_child, "body") {
                                self.cpp_dfg_process_block(body, source, edges, definitions, uses);
                            }
                        }
                    }
                }
                "compound_statement" | "case_statement" | "labeled_statement" => {
                    self.cpp_dfg_process_block(child, source, edges, definitions, uses);
                }
                _ => {}
            }
        }
    }

    fn cpp_dfg_process_declaration(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "init_declarator" => {
                    if let Some(decl) = self.child_by_field(child, "declarator") {
                        if let Some(name) = self.cpp_dfg_lvalue_name(decl, source) {
                            definitions.entry(name.clone()).or_default().push(line);
                            edges.push(DataflowEdge {
                                variable: name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Definition,
                            });
                        }
                    }
                    if let Some(value) = self.child_by_field(child, "value") {
                        self.cpp_dfg_collect_uses(value, source, line, edges, definitions, uses);
                    }
                }
                "identifier" | "pointer_declarator" | "reference_declarator" | "array_declarator" => {
                    if let Some(name) = self.cpp_dfg_lvalue_name(child, source) {
                        definitions.entry(name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Definition,
                        });
                    }
                }
                _ => {}
            }
        }
    }

    fn cpp_dfg_process_expr_stmt(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.is_named() {
                self.cpp_dfg_process_top_expr(child, source, line, edges, definitions, uses);
            }
        }
    }

    fn cpp_dfg_process_top_expr(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "assignment_expression" | "compound_assignment_expr" | "augmented_assignment_expression" => {
                // Check if this is a compound assignment (+=, -=, etc.)
                // tree-sitter-cpp parses compound assignments as assignment_expression
                // with an operator field like "+=", "-=", "*=", etc.
                let is_compound = node.child_by_field_name("operator")
                    .map(|op| {
                        let op_text = self.get_text(op, source);
                        op_text != "="
                    })
                    .unwrap_or(node.kind() != "assignment_expression");

                if let Some(right) = self.child_by_field(node, "right") {
                    self.cpp_dfg_collect_uses(right, source, line, edges, definitions, uses);
                }
                if let Some(left) = self.child_by_field(node, "left") {
                    if is_compound {
                        self.cpp_dfg_collect_uses(left, source, line, edges, definitions, uses);
                    }
                    self.cpp_dfg_process_lvalue_mutation(left, source, line, edges, definitions, uses);
                }
            }
            "update_expression" => {
                if let Some(arg) = self.child_by_field(node, "argument") {
                    self.cpp_dfg_collect_uses(arg, source, line, edges, definitions, uses);
                    self.cpp_dfg_process_lvalue_mutation(arg, source, line, edges, definitions, uses);
                }
            }
            "comma_expression" => {
                if let Some(left) = self.child_by_field(node, "left") {
                    self.cpp_dfg_process_top_expr(left, source, line, edges, definitions, uses);
                }
                if let Some(right) = self.child_by_field(node, "right") {
                    self.cpp_dfg_process_top_expr(right, source, line, edges, definitions, uses);
                }
            }
            _ => {
                self.cpp_dfg_collect_uses(node, source, line, edges, definitions, uses);
            }
        }
    }

    fn cpp_dfg_process_lvalue_mutation(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "pointer_expression" => {
                if let Some(arg) = self.child_by_field(node, "argument") {
                    self.cpp_dfg_collect_uses(arg, source, line, edges, definitions, uses);
                    if let Some(base) = self.cpp_dfg_lvalue_name(arg, source) {
                        let deref_name = format!("(*{})", base);
                        definitions.entry(deref_name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: deref_name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Mutation,
                        });
                    }
                }
            }
            "field_expression" => {
                if let Some(name) = self.cpp_dfg_field_expr_name(node, source) {
                    definitions.entry(name.clone()).or_default().push(line);
                    edges.push(DataflowEdge {
                        variable: name,
                        from_line: line,
                        to_line: line,
                        kind: DataflowKind::Mutation,
                    });
                }
                if let Some(arg) = self.child_by_field(node, "argument") {
                    if let Some(base) = self.cpp_dfg_lvalue_name(arg, source) {
                        definitions.entry(base.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: base,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Mutation,
                        });
                    }
                }
            }
            "subscript_expression" => {
                if let Some(arg) = self.child_by_field(node, "argument") {
                    if let Some(base) = self.cpp_dfg_lvalue_name(arg, source) {
                        definitions.entry(base.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: base,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Mutation,
                        });
                    }
                }
                if let Some(idx) = self.child_by_field(node, "index") {
                    self.cpp_dfg_collect_uses(idx, source, line, edges, definitions, uses);
                }
            }
            "parenthesized_expression" => {
                let mut inner_cursor = node.walk();
                for child in node.children(&mut inner_cursor) {
                    if child.is_named() {
                        self.cpp_dfg_process_lvalue_mutation(child, source, line, edges, definitions, uses);
                        return;
                    }
                }
            }
            _ => {
                if let Some(name) = self.cpp_dfg_lvalue_name(node, source) {
                    definitions.entry(name.clone()).or_default().push(line);
                    edges.push(DataflowEdge {
                        variable: name,
                        from_line: line,
                        to_line: line,
                        kind: DataflowKind::Mutation,
                    });
                }
            }
        }
    }

    fn cpp_dfg_lvalue_name(&self, node: Node, source: &[u8]) -> Option<String> {
        match node.kind() {
            "identifier" | "this" => {
                let name = self.node_text(node, source);
                if name.is_empty() { None } else { Some(name) }
            }
            "pointer_declarator" | "reference_declarator" => {
                self.cpp_dfg_declarator_name(node, source)
            }
            "array_declarator" => {
                self.child_by_field(node, "declarator")
                    .and_then(|d| self.cpp_dfg_lvalue_name(d, source))
            }
            "field_expression" => self.cpp_dfg_field_expr_name(node, source),
            "subscript_expression" => {
                self.child_by_field(node, "argument")
                    .and_then(|arg| self.cpp_dfg_lvalue_name(arg, source))
            }
            "pointer_expression" => {
                self.child_by_field(node, "argument")
                    .and_then(|arg| self.cpp_dfg_lvalue_name(arg, source))
            }
            "parenthesized_expression" => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.is_named() {
                        return self.cpp_dfg_lvalue_name(child, source);
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn cpp_dfg_field_expr_name(&self, node: Node, source: &[u8]) -> Option<String> {
        let arg = self.child_by_field(node, "argument")?;
        let field = self.child_by_field(node, "field")?;
        let base = self.cpp_dfg_lvalue_name(arg, source)?;
        let field_name = self.node_text(field, source);
        let op = self.cpp_dfg_field_operator(node, source);
        Some(format!("{}{}{}", base, op, field_name))
    }

    fn cpp_dfg_field_operator(&self, node: Node, source: &[u8]) -> &'static str {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if !child.is_named() {
                let text = self.get_text(child, source);
                if text == "->" {
                    return "->";
                }
                if text == "." {
                    return ".";
                }
            }
        }
        "."
    }

    fn cpp_dfg_process_return(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.is_named() && child.kind() != "return" {
                self.cpp_dfg_collect_return_uses(child, source, line, edges, definitions, uses);
            }
        }
    }

    fn cpp_dfg_collect_return_uses(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "identifier" | "this" => {
                let name = self.node_text(node, source);
                uses.entry(name.clone()).or_default().push(line);
                if let Some(def_lines) = definitions.get(&name) {
                    if let Some(&def_line) = def_lines.last() {
                        edges.push(DataflowEdge {
                            variable: name,
                            from_line: def_line,
                            to_line: line,
                            kind: DataflowKind::Return,
                        });
                    }
                }
            }
            "field_expression" => {
                if let Some(name) = self.cpp_dfg_field_expr_name(node, source) {
                    uses.entry(name.clone()).or_default().push(line);
                    if let Some(def_lines) = definitions.get(&name) {
                        if let Some(&def_line) = def_lines.last() {
                            edges.push(DataflowEdge {
                                variable: name,
                                from_line: def_line,
                                to_line: line,
                                kind: DataflowKind::Return,
                            });
                        }
                    }
                }
                if let Some(arg) = self.child_by_field(node, "argument") {
                    self.cpp_dfg_collect_return_uses(arg, source, line, edges, definitions, uses);
                }
            }
            _ => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.is_named() {
                        self.cpp_dfg_collect_return_uses(child, source, line, edges, definitions, uses);
                    }
                }
            }
        }
    }

    /// Recursively collect variable uses from a C++ expression.
    fn cpp_dfg_collect_uses(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "identifier" | "this" => {
                let name = self.node_text(node, source);
                if name.is_empty() {
                    return;
                }
                uses.entry(name.clone()).or_default().push(line);
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
            "field_expression" => {
                if let Some(name) = self.cpp_dfg_field_expr_name(node, source) {
                    uses.entry(name.clone()).or_default().push(line);
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
                if let Some(arg) = self.child_by_field(node, "argument") {
                    self.cpp_dfg_collect_uses(arg, source, line, edges, definitions, uses);
                }
            }
            "pointer_expression" => {
                if let Some(arg) = self.child_by_field(node, "argument") {
                    self.cpp_dfg_collect_uses(arg, source, line, edges, definitions, uses);
                    if let Some(base) = self.cpp_dfg_lvalue_name(arg, source) {
                        let deref_name = format!("(*{})", base);
                        if definitions.contains_key(&deref_name) {
                            uses.entry(deref_name.clone()).or_default().push(line);
                            if let Some(def_lines) = definitions.get(&deref_name) {
                                if let Some(&def_line) = def_lines.last() {
                                    edges.push(DataflowEdge {
                                        variable: deref_name,
                                        from_line: def_line,
                                        to_line: line,
                                        kind: DataflowKind::Use,
                                    });
                                }
                            }
                        }
                    }
                }
            }
            "subscript_expression" => {
                if let Some(arg) = self.child_by_field(node, "argument") {
                    self.cpp_dfg_collect_uses(arg, source, line, edges, definitions, uses);
                }
                if let Some(idx) = self.child_by_field(node, "index") {
                    self.cpp_dfg_collect_uses(idx, source, line, edges, definitions, uses);
                }
            }
            "sizeof_expression" | "alignof_expression" => {}
            "cast_expression" => {
                if let Some(value) = self.child_by_field(node, "value") {
                    self.cpp_dfg_collect_uses(value, source, line, edges, definitions, uses);
                }
            }
            "template_function" | "template_method" | "qualified_identifier" => {
                // For qualified names like std::move(x), recurse into arguments
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.is_named() {
                        self.cpp_dfg_collect_uses(child, source, line, edges, definitions, uses);
                    }
                }
            }
            "lambda_expression" => {
                // Track captured variables
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "lambda_capture_specifier" {
                        let mut cap_cursor = child.walk();
                        for cap in child.children(&mut cap_cursor) {
                            if cap.kind() == "identifier" {
                                let name = self.node_text(cap, source);
                                uses.entry(name.clone()).or_default().push(line);
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
                        }
                    }
                }
            }
            _ => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.is_named() {
                        self.cpp_dfg_collect_uses(child, source, line, edges, definitions, uses);
                    }
                }
            }
        }
    }

    /// Recursively collect all import-like constructs from C++ source.
    ///
    /// Walks into preprocessor conditional blocks (`#ifdef`, `#ifndef`, `#if`, `#elif`, `#else`),
    /// namespace definitions, and linkage specifications (`extern "C"`) to find:
    /// - `#include` directives (both `<>` and `""`)
    /// - `using` declarations (`using std::vector;`)
    /// - `using namespace` directives (`using namespace std;`)
    fn collect_cpp_imports_recursive(
        &self,
        node: Node,
        source: &[u8],
        imports: &mut Vec<ImportInfo>,
        depth: usize,
    ) {
        if depth > 100 {
            return;
        }
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
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
                // Recurse into containers that can hold includes/using decls
                "preproc_ifdef" | "preproc_ifndef" | "preproc_if" | "preproc_else"
                | "preproc_elif" | "namespace_definition" | "declaration_list"
                | "linkage_specification" | "translation_unit" => {
                    self.collect_cpp_imports_recursive(child, source, imports, depth + 1);
                }
                _ => {
                    // Also recurse into nodes that have children and might contain includes
                    if child.child_count() > 0 && child.is_named() {
                        self.collect_cpp_imports_recursive(child, source, imports, depth + 1);
                    }
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
                    path = path
                        .trim_start_matches('<')
                        .trim_end_matches('>')
                        .to_string();
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
            aliases: FxHashMap::default(),
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
            aliases: FxHashMap::default(),
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
        &[".cpp", ".cc", ".cxx", ".hpp", ".hh", ".hxx", ".h++", ".c++", ".cu", ".cuh", ".h"]
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
        self.collect_cpp_imports_recursive(tree.root_node(), source, &mut imports, 0);
        imports
    }

    fn function_query(&self) -> &'static str {
        r#"[
            ; --- Direct function definitions ---
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
            (function_definition
                declarator: (function_declarator
                    declarator: (field_identifier) @name)) @function

            ; --- Pointer-returning functions: T* foo() ---
            (function_definition
                declarator: (pointer_declarator
                    declarator: (function_declarator
                        declarator: (identifier) @name))) @function
            (function_definition
                declarator: (pointer_declarator
                    declarator: (function_declarator
                        declarator: (qualified_identifier) @name))) @function
            (function_definition
                declarator: (pointer_declarator
                    declarator: (function_declarator
                        declarator: (field_identifier) @name))) @function

            ; --- Reference-returning functions: T& foo() ---
            (function_definition
                declarator: (reference_declarator
                    (function_declarator
                        declarator: (identifier) @name))) @function
            (function_definition
                declarator: (reference_declarator
                    (function_declarator
                        declarator: (qualified_identifier) @name))) @function
            (function_definition
                declarator: (reference_declarator
                    (function_declarator
                        declarator: (operator_name) @name))) @function

            ; --- Forward declarations ---
            (declaration
                declarator: (function_declarator
                    declarator: (identifier) @name)) @function
            (declaration
                declarator: (function_declarator
                    declarator: (qualified_identifier) @name)) @function

            ; --- Template functions ---
            (template_declaration
                (function_definition
                    declarator: (function_declarator
                        declarator: (identifier) @name))) @function
            (template_declaration
                (function_definition
                    declarator: (function_declarator
                        declarator: (qualified_identifier) @name))) @function
            (template_declaration
                (function_definition
                    declarator: (function_declarator
                        declarator: (destructor_name) @name))) @function
            (template_declaration
                (function_definition
                    declarator: (function_declarator
                        declarator: (operator_name) @name))) @function
            (template_declaration
                (function_definition
                    declarator: (pointer_declarator
                        declarator: (function_declarator
                            declarator: (identifier) @name)))) @function
            (template_declaration
                (function_definition
                    declarator: (pointer_declarator
                        declarator: (function_declarator
                            declarator: (qualified_identifier) @name)))) @function
            (template_declaration
                (function_definition
                    declarator: (reference_declarator
                        (function_declarator
                            declarator: (identifier) @name)))) @function
            (template_declaration
                (function_definition
                    declarator: (reference_declarator
                        (function_declarator
                            declarator: (qualified_identifier) @name)))) @function

            ; --- Preprocessor macros ---
            (preproc_def
                name: (identifier) @name) @function
            (preproc_function_def
                name: (identifier) @name) @function

            ; --- Lambdas ---
            (lambda_expression) @function
        ]"#
    }

    fn class_query(&self) -> &'static str {
        r#"[
            (class_specifier name: (type_identifier) @name) @class
            (struct_specifier name: (type_identifier) @name) @struct
            (enum_specifier name: (type_identifier) @name) @enum
            (namespace_definition name: (namespace_identifier) @name) @namespace
            (namespace_definition name: (nested_namespace_specifier) @name) @namespace
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

        let func_name = self
            .child_by_field(node, "declarator")
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

        let func_name = self
            .child_by_field(node, "declarator")
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
                    assert!(ctor
                        .unwrap()
                        .decorators
                        .contains(&"constructor".to_string()));

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

        fn walk_tree(
            node: Node,
            cpp: &Cpp,
            source: &[u8],
            methods: &mut i32,
            free_funcs: &mut i32,
        ) {
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

        walk_tree(
            root,
            &cpp,
            source.as_bytes(),
            &mut methods_found,
            &mut free_functions_found,
        );

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

    #[test]
    fn test_cuda_global_kernel() {
        let source = r#"
__global__ void my_kernel(float* data, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) data[idx] *= 2.0f;
}
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                if let Some(func) = cpp.extract_function(child, source.as_bytes()) {
                    assert_eq!(func.name, "my_kernel");
                    assert!(
                        func.decorators.contains(&"__global__".to_string()),
                        "Should have __global__ decorator, got: {:?}",
                        func.decorators
                    );
                    assert_eq!(
                        func.return_type.as_deref(),
                        Some("void"),
                        "Return type should be 'void', got: {:?}",
                        func.return_type
                    );
                    found = true;
                }
            }
        }
        assert!(found, "CUDA kernel not found");
    }

    #[test]
    fn test_cuda_device_function() {
        let source = r#"
__device__ __forceinline__ float fast_sqrt(float x) {
    return __fsqrt_rn(x);
}
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                if let Some(func) = cpp.extract_function(child, source.as_bytes()) {
                    assert_eq!(func.name, "fast_sqrt");
                    assert!(
                        func.decorators.contains(&"__device__".to_string()),
                        "Should have __device__, got: {:?}",
                        func.decorators
                    );
                    assert!(
                        func.decorators.contains(&"__forceinline__".to_string()),
                        "Should have __forceinline__, got: {:?}",
                        func.decorators
                    );
                    assert_eq!(
                        func.return_type.as_deref(),
                        Some("float"),
                        "Return type should be 'float', got: {:?}",
                        func.return_type
                    );
                    found = true;
                }
            }
        }
        assert!(found, "CUDA device function not found");
    }

    #[test]
    fn test_cuda_host_device() {
        let source = r#"
__host__ __device__ int helper(int x) {
    return x + 1;
}
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                if let Some(func) = cpp.extract_function(child, source.as_bytes()) {
                    assert_eq!(func.name, "helper");
                    assert!(
                        func.decorators.contains(&"__host__".to_string()),
                        "Should have __host__, got: {:?}",
                        func.decorators
                    );
                    assert!(
                        func.decorators.contains(&"__device__".to_string()),
                        "Should have __device__, got: {:?}",
                        func.decorators
                    );
                    assert_eq!(
                        func.return_type.as_deref(),
                        Some("int"),
                        "Return type should be 'int', got: {:?}",
                        func.return_type
                    );
                    found = true;
                }
            }
        }
        assert!(found, "CUDA host/device function not found");
    }

    #[test]
    fn test_pointer_returning_function() {
        let source = r#"
ComputeBody* compute_body() const {
    return static_cast<ComputeBody*>(body);
}
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                if let Some(func) = cpp.extract_function(child, source.as_bytes()) {
                    assert_eq!(func.name, "compute_body");
                    found = true;
                }
            }
        }
        assert!(found, "Pointer-returning function not found");
    }

    #[test]
    fn test_out_of_class_method() {
        let source = r#"
void Graph::eliminate_dead_nodes() {
    for (int i = 0; i < num_nodes_; ++i) {}
}
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                if let Some(func) = cpp.extract_function(child, source.as_bytes()) {
                    assert_eq!(func.name, "Graph::eliminate_dead_nodes");
                    found = true;
                }
            }
        }
        assert!(found, "Out-of-class method not found");
    }

    #[test]
    fn test_preproc_function_def() {
        let source = r#"
#define MAX(a, b) ((a) > (b) ? (a) : (b))
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "preproc_function_def" {
                if let Some(func) = cpp.extract_function(child, source.as_bytes()) {
                    assert_eq!(func.name, "MAX");
                    assert!(
                        func.decorators.contains(&"macro".to_string()),
                        "Should have macro decorator, got: {:?}",
                        func.decorators
                    );
                    found = true;
                }
            }
        }
        assert!(found, "Preprocessor function macro not found");
    }

    #[test]
    fn test_preproc_object_macro() {
        let source = r#"
#define VERSION 42
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "preproc_def" {
                if let Some(func) = cpp.extract_function(child, source.as_bytes()) {
                    assert_eq!(func.name, "VERSION");
                    assert!(
                        func.decorators.contains(&"macro".to_string()),
                        "Should have macro decorator, got: {:?}",
                        func.decorators
                    );
                    found = true;
                }
            }
        }
        assert!(found, "Preprocessor object macro not found");
    }

    #[test]
    fn test_nested_namespace() {
        let source = r#"
namespace torch::conductor {
    void foo() {}
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
                    assert!(
                        ns.name.contains("torch") && ns.name.contains("conductor"),
                        "Should contain torch::conductor, got: {}",
                        ns.name
                    );
                    assert!(ns.decorators.contains(&"namespace".to_string()));
                    found = true;
                }
            }
        }
        assert!(found, "Nested namespace not found");
    }

    #[test]
    fn test_deleted_function() {
        let source = r#"
class Graph {
public:
    Graph(const Graph&) = delete;
};
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found_deleted = false;
        fn walk(node: Node, cpp: &Cpp, source: &[u8], found: &mut bool) {
            if node.kind() == "function_definition" {
                if let Some(func) = cpp.extract_function(node, source) {
                    if func.decorators.contains(&"deleted".to_string()) {
                        *found = true;
                    }
                }
            }
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                walk(child, cpp, source, found);
            }
        }
        walk(root, &cpp, source.as_bytes(), &mut found_deleted);
        assert!(found_deleted, "Deleted function not detected");
    }

    #[test]
    fn test_template_out_of_class_method() {
        let source = r#"
template<typename T>
void Container<T>::insert(const T& value) {
    data_.push_back(value);
}
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "template_declaration" {
                if let Some(func) = cpp.extract_function(child, source.as_bytes()) {
                    assert!(
                        func.name.contains("Container") && func.name.contains("insert"),
                        "Expected Container<T>::insert, got: {}",
                        func.name
                    );
                    assert!(
                        func.decorators.iter().any(|d| d.contains("template")),
                        "Should have template decorator, got: {:?}",
                        func.decorators
                    );
                    found = true;
                }
            }
        }
        assert!(found, "Template out-of-class method not found");
    }

    #[test]
    fn test_reference_returning_method_in_class() {
        let source = r#"
class Graph {
public:
    Graph& operator=(const Graph&) = delete;
};
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found = false;
        fn walk(node: Node, cpp: &Cpp, source: &[u8], found: &mut bool) {
            if node.kind() == "function_definition" {
                if let Some(func) = cpp.extract_function(node, source) {
                    if func.name.contains("operator") {
                        *found = true;
                    }
                }
            }
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                walk(child, cpp, source, found);
            }
        }
        walk(root, &cpp, source.as_bytes(), &mut found);
        assert!(found, "Reference-returning operator= not found in class");
    }

    #[test]
    fn test_enum_class_scoped() {
        let source = r#"
enum class NodeKind : uint8_t {
  INPUT,
  CONSTANT,
  POINTWISE,
};
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "enum_specifier" {
                if let Some(class) = cpp.extract_class(child, source.as_bytes()) {
                    assert_eq!(class.name, "NodeKind");
                    assert!(
                        class.decorators.contains(&"scoped".to_string()),
                        "Should have scoped decorator, got: {:?}",
                        class.decorators
                    );
                    found = true;
                }
            }
        }
        assert!(found, "Scoped enum not found");
    }

    /// End-to-end test: verify the query patterns match real C++ code and the
    /// full extraction pipeline produces correct results.
    #[test]
    fn test_e2e_query_pipeline() {
        use crate::ast::extractor::AstExtractor;

        let source = r#"
#pragma once
#include <cstdint>

#define GRAPH_VERSION 3
#define MAX_NODES(n) ((n) * 2)

namespace torch::conductor {

enum class NodeKind : uint8_t { INPUT, CONSTANT };

struct GraphNode {
  uint32_t id;
  NodeKind kind;
  bool is_dead() const { return false; }
  ComputeBody* compute_body() const { return nullptr; }
};

class Graph {
 public:
  explicit Graph(ExprPool* pool) : pool_(pool) {}
  Graph(const Graph&) = delete;
  Graph& operator=(const Graph&) = delete;

  GraphNode* add_input(int8_t dtype) { return nullptr; }

 private:
  void grow_(size_t cap) {}
  ExprPool* pool_;
};

template<typename T>
void Container<T>::insert(const T& value) {}

}
"#;
        let module = AstExtractor::extract_from_source(source, "cpp")
            .expect("Failed to extract C++ source");

        let func_names: Vec<&str> = module.functions.iter().map(|f| f.name.as_str()).collect();
        let class_names: Vec<&str> = module.classes.iter().map(|c| c.name.as_str()).collect();

        // Functions extracted via query patterns
        assert!(
            func_names.contains(&"GRAPH_VERSION"),
            "Should find object macro, got: {:?}",
            func_names
        );
        assert!(
            func_names.contains(&"MAX_NODES"),
            "Should find function macro, got: {:?}",
            func_names
        );

        // Classes extracted via query patterns
        assert!(
            class_names.iter().any(|n| n.contains("torch") || n.contains("conductor")),
            "Should find nested namespace, got: {:?}",
            class_names
        );
        assert!(
            class_names.contains(&"NodeKind"),
            "Should find enum class, got: {:?}",
            class_names
        );
        assert!(
            class_names.contains(&"GraphNode"),
            "Should find struct, got: {:?}",
            class_names
        );
        assert!(
            class_names.contains(&"Graph"),
            "Should find class, got: {:?}",
            class_names
        );
    }

    /// End-to-end test for CUDA kernels via the full extraction pipeline.
    #[test]
    fn test_e2e_cuda_kernels() {
        use crate::ast::extractor::AstExtractor;

        let source = r#"
__global__ void matmul_kernel(float* C, const float* A, const float* B, int N) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    if (row < N && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < N; ++k)
            sum += A[row * N + k] * B[k * N + col];
        C[row * N + col] = sum;
    }
}

__device__ float fast_exp(float x) { return __expf(x); }

__host__ __device__ int clamp(int x, int lo, int hi) {
    return x < lo ? lo : (x > hi ? hi : x);
}

template<typename T>
__global__ void fill_kernel(T* data, T value, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) data[idx] = value;
}
"#;
        let module = AstExtractor::extract_from_source(source, "cpp")
            .expect("Failed to extract CUDA source");

        let func_names: Vec<&str> = module.functions.iter().map(|f| f.name.as_str()).collect();

        assert!(
            func_names.contains(&"matmul_kernel"),
            "Should find __global__ kernel, got: {:?}",
            func_names
        );
        assert!(
            func_names.contains(&"fast_exp"),
            "Should find __device__ function, got: {:?}",
            func_names
        );
        assert!(
            func_names.contains(&"clamp"),
            "Should find __host__ __device__ function, got: {:?}",
            func_names
        );
        assert!(
            func_names.contains(&"fill_kernel"),
            "Should find template CUDA kernel, got: {:?}",
            func_names
        );

        // Verify CUDA qualifiers are extracted as decorators
        let matmul = module.functions.iter().find(|f| f.name == "matmul_kernel").unwrap();
        assert!(
            matmul.decorators.contains(&"__global__".to_string()),
            "matmul_kernel should have __global__ decorator, got: {:?}",
            matmul.decorators
        );
        assert_eq!(
            matmul.return_type.as_deref(),
            Some("void"),
            "matmul_kernel return type should be void"
        );

        let clamp_fn = module.functions.iter().find(|f| f.name == "clamp").unwrap();
        assert!(
            clamp_fn.decorators.contains(&"__host__".to_string()),
            "clamp should have __host__, got: {:?}",
            clamp_fn.decorators
        );
        assert!(
            clamp_fn.decorators.contains(&"__device__".to_string()),
            "clamp should have __device__, got: {:?}",
            clamp_fn.decorators
        );
    }

    #[test]
    fn test_extract_imports_includes() {
        let source = r#"
#include <iostream>
#include <vector>
#include "myheader.h"
#include "utils/helper.h"
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let imports = cpp.extract_imports(&tree, source.as_bytes());

        assert_eq!(imports.len(), 4, "Should find 4 includes");

        // System includes
        assert_eq!(imports[0].module, "iostream");
        assert!(!imports[0].is_from, "System include: is_from should be false");

        assert_eq!(imports[1].module, "vector");

        // Local includes
        assert_eq!(imports[2].module, "myheader.h");
        assert!(imports[2].is_from, "Local include: is_from should be true");

        assert_eq!(imports[3].module, "utils/helper.h");
    }

    #[test]
    fn test_extract_imports_using_declarations() {
        let source = r#"
#include <vector>
using std::vector;
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let imports = cpp.extract_imports(&tree, source.as_bytes());

        // Should find both the include and the using declaration
        assert!(imports.len() >= 2, "Should find at least 2 imports, got {}", imports.len());

        let has_vector_include = imports.iter().any(|i| i.module == "vector");
        assert!(has_vector_include, "Should find vector include");

        let has_using = imports.iter().any(|i| i.module.contains("std") && i.module.contains("vector"));
        assert!(has_using, "Should find using std::vector");
    }

    #[test]
    fn test_extract_imports_inside_ifdef() {
        let source = r#"
#include <cstdlib>
#ifdef __cplusplus
#include <string>
#include <memory>
#endif
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let imports = cpp.extract_imports(&tree, source.as_bytes());

        // Should find all 3 includes (cstdlib, string, memory) even those inside #ifdef
        let modules: Vec<&str> = imports.iter().map(|i| i.module.as_str()).collect();
        assert!(
            modules.contains(&"cstdlib"),
            "Should find cstdlib. Found: {:?}",
            modules
        );
        assert!(
            modules.contains(&"string"),
            "Should find string inside #ifdef. Found: {:?}",
            modules
        );
        assert!(
            modules.contains(&"memory"),
            "Should find memory inside #ifdef. Found: {:?}",
            modules
        );
    }

    #[test]
    fn test_extract_imports_inside_namespace() {
        // Note: includes inside namespace blocks are unusual but legal
        // More commonly, using declarations appear inside namespaces
        let source = r#"
#include <vector>
namespace mylib {
    #include "internal.h"
}
"#;
        let tree = parse_cpp(source);
        let cpp = Cpp;
        let imports = cpp.extract_imports(&tree, source.as_bytes());

        let modules: Vec<&str> = imports.iter().map(|i| i.module.as_str()).collect();
        assert!(
            modules.contains(&"vector"),
            "Should find top-level include"
        );
        assert!(
            modules.contains(&"internal.h"),
            "Should find include inside namespace. Found: {:?}",
            modules
        );
    }

    // =========================================================================
    // C++ CFG tests: decision_points, block types, control flow
    // =========================================================================

    #[test]
    fn test_cpp_cfg_if_decision_point() {
        let source = r#"
int f(int x) {
    if (x > 0) {
        return 1;
    }
    return 0;
}
"#;
        let cpp = Cpp;
        let cfg = crate::cfg::CfgBuilder::extract_from_source(source, "cpp", "f").unwrap();
        assert_eq!(cfg.decision_points, 1, "if should count as 1 decision point");
        assert_eq!(cfg.cyclomatic_complexity(), 2);
        let branch_blocks: Vec<_> = cfg.blocks.values()
            .filter(|b| b.block_type == BlockType::Branch)
            .collect();
        assert_eq!(branch_blocks.len(), 1, "Should have 1 branch block for if");
    }

    #[test]
    fn test_cpp_cfg_while_decision_point() {
        let source = r#"
void f(int n) {
    while (n > 0) {
        n--;
    }
}
"#;
        let cfg = crate::cfg::CfgBuilder::extract_from_source(source, "cpp", "f").unwrap();
        assert_eq!(cfg.decision_points, 1, "while should count as 1 decision point");
        let loop_headers: Vec<_> = cfg.blocks.values()
            .filter(|b| b.block_type == BlockType::LoopHeader)
            .collect();
        assert_eq!(loop_headers.len(), 1, "Should have 1 loop header for while");
    }

    #[test]
    fn test_cpp_cfg_for_decision_point() {
        let source = r#"
int f(int n) {
    int s = 0;
    for (int i = 0; i < n; i++) {
        s += i;
    }
    return s;
}
"#;
        let cfg = crate::cfg::CfgBuilder::extract_from_source(source, "cpp", "f").unwrap();
        assert_eq!(cfg.decision_points, 1, "for should count as 1 decision point");
    }

    #[test]
    fn test_cpp_cfg_switch_case_decision_points() {
        let source = r#"
int f(int x) {
    switch (x) {
        case 0: return 0;
        case 1: return 1;
        default: return -1;
    }
}
"#;
        let cfg = crate::cfg::CfgBuilder::extract_from_source(source, "cpp", "f").unwrap();
        assert_eq!(cfg.decision_points, 3, "3 case statements = 3 decision points");
        let branch_blocks: Vec<_> = cfg.blocks.values()
            .filter(|b| b.block_type == BlockType::Branch)
            .collect();
        assert_eq!(branch_blocks.len(), 1, "Should have 1 branch block for switch");
    }

    #[test]
    fn test_cpp_cfg_try_catch_decision_points() {
        let source = r#"
int f(int x) {
    try {
        return x / 2;
    } catch (const std::exception& e) {
        return -1;
    } catch (...) {
        return -2;
    }
}
"#;
        let cfg = crate::cfg::CfgBuilder::extract_from_source(source, "cpp", "f").unwrap();
        assert_eq!(cfg.decision_points, 2, "2 catch clauses = 2 decision points");
        let exception_blocks: Vec<_> = cfg.blocks.values()
            .filter(|b| b.block_type == BlockType::Exception)
            .collect();
        assert_eq!(exception_blocks.len(), 2, "Should have 2 exception blocks for catch");
    }

    #[test]
    fn test_cpp_cfg_goto_label() {
        let source = r#"
void f(int* data, int n) {
    for (int i = 0; i < n; i++) {
        if (data[i] < 0) {
            goto error;
        }
    }
    return;
error:
    data[0] = 0;
}
"#;
        let cfg = crate::cfg::CfgBuilder::extract_from_source(source, "cpp", "f").unwrap();

        // Check goto edge exists
        use crate::cfg::types::EdgeType;
        let goto_edges: Vec<_> = cfg.edges.iter()
            .filter(|e| e.edge_type == EdgeType::Goto)
            .collect();
        assert_eq!(goto_edges.len(), 1, "Should have 1 goto edge");

        // Check label block exists
        let label_blocks: Vec<_> = cfg.blocks.values()
            .filter(|b| b.label.contains("label:"))
            .collect();
        assert_eq!(label_blocks.len(), 1, "Should have 1 label block");
    }

    #[test]
    fn test_cpp_cfg_do_while() {
        let source = r#"
void f(int x) {
    do {
        x--;
    } while (x > 0);
}
"#;
        let cfg = crate::cfg::CfgBuilder::extract_from_source(source, "cpp", "f").unwrap();
        assert_eq!(cfg.decision_points, 1, "do-while counts as 1 decision point");
        let loop_headers: Vec<_> = cfg.blocks.values()
            .filter(|b| b.block_type == BlockType::LoopHeader)
            .collect();
        assert_eq!(loop_headers.len(), 1, "Should have 1 loop header for do-while");
    }

    #[test]
    fn test_cpp_cfg_complex_function() {
        let source = r#"
int f(int x) {
    if (x < 0) return -1;
    while (x > 10) {
        if (x % 2 == 0) {
            x /= 2;
        } else {
            x = x * 3 + 1;
        }
    }
    for (int i = 0; i < x; i++) {
        x++;
    }
    return x;
}
"#;
        let cfg = crate::cfg::CfgBuilder::extract_from_source(source, "cpp", "f").unwrap();
        // 1 if + 1 while + 1 if + 1 for = 4
        assert_eq!(cfg.decision_points, 4, "Complex function: 4 decision points");
        assert_eq!(cfg.cyclomatic_complexity(), 5);
    }

    // =========================================================================
    // C++ DFG tests: compound assignment, pointer, struct member
    // =========================================================================

    #[test]
    fn test_cpp_dfg_compound_assignment() {
        let source = r#"
int f(int a) {
    int x = 0;
    x += a;
    return x;
}
"#;
        let cfg = crate::cfg::CfgBuilder::extract_from_source(source, "cpp", "f").unwrap();
        let dfg = crate::dfg::extract_with_language(
            &"/dev/null", "f", Some("cpp"),
        );
        // Use extract_from_source via CfgBuilder approach
        let cpp = Cpp;
        let mut parser = cpp.parser().unwrap();
        let tree = parser.parse(source, None).unwrap();
        // Find the function node
        let root = tree.root_node();
        let mut func_node = None;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                func_node = Some(child);
            }
        }
        let dfg = cpp.build_dfg(func_node.unwrap(), source.as_bytes()).unwrap();

        // Check that x has both Use and Mutation for +=
        let x_uses: Vec<_> = dfg.edges.iter()
            .filter(|e| e.variable == "x" && e.kind == DataflowKind::Use)
            .collect();
        assert!(!x_uses.is_empty(), "x should have Use edge from compound assignment");

        let x_mutations: Vec<_> = dfg.edges.iter()
            .filter(|e| e.variable == "x" && e.kind == DataflowKind::Mutation)
            .collect();
        assert!(!x_mutations.is_empty(), "x should have Mutation edge from compound assignment");
    }

    #[test]
    fn test_cpp_dfg_struct_member() {
        let source = r#"
struct Point { int x; int y; };
void f(Point p) {
    p.x = 10;
    p.y = p.x + 1;
}
"#;
        let cpp = Cpp;
        let mut parser = cpp.parser().unwrap();
        let tree = parser.parse(source, None).unwrap();
        let root = tree.root_node();
        let mut func_node = None;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                func_node = Some(child);
            }
        }
        let dfg = cpp.build_dfg(func_node.unwrap(), source.as_bytes()).unwrap();

        // Check p.x is tracked
        let px_defs: Vec<_> = dfg.edges.iter()
            .filter(|e| e.variable == "p.x" && (e.kind == DataflowKind::Mutation || e.kind == DataflowKind::Definition))
            .collect();
        assert!(!px_defs.is_empty(), "p.x should have definition/mutation edges");
    }

    #[test]
    fn test_cpp_dfg_pointer_param() {
        let source = r#"
void f(int* arr, int n) {
    arr[0] = n;
}
"#;
        let cpp = Cpp;
        let mut parser = cpp.parser().unwrap();
        let tree = parser.parse(source, None).unwrap();
        let root = tree.root_node();
        let mut func_node = None;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                func_node = Some(child);
            }
        }
        let dfg = cpp.build_dfg(func_node.unwrap(), source.as_bytes()).unwrap();

        // Check arr parameter is tracked
        let arr_defs: Vec<_> = dfg.edges.iter()
            .filter(|e| e.variable == "arr")
            .collect();
        assert!(!arr_defs.is_empty(), "arr pointer param should be tracked in DFG");
    }

    #[test]
    fn test_cpp_dfg_for_loop_variable() {
        let source = r#"
void f() {
    for (int i = 0; i < 10; i++) {
        int x = i;
    }
}
"#;
        let cpp = Cpp;
        let mut parser = cpp.parser().unwrap();
        let tree = parser.parse(source, None).unwrap();
        let root = tree.root_node();
        let mut func_node = None;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                func_node = Some(child);
            }
        }
        let dfg = cpp.build_dfg(func_node.unwrap(), source.as_bytes()).unwrap();

        // Check i is defined
        assert!(dfg.definitions.contains_key("i"), "for loop variable i should be defined");
    }
}
