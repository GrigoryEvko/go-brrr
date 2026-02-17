//! C language support (also works for basic C++).
//!
//! Implements full extraction for C code including:
//! - Function definitions (function_definition)
//! - Function declarations (declaration with function_declarator)
//! - Structs (struct_specifier)
//! - Typedefs (type_definition)
//! - Includes (preproc_include with system and local paths)
//! - Macro definitions (preproc_def, preproc_function_def)
//! - Function pointer types (function_declarator in parenthesized_declarator)
//! - Preprocessor conditionals (#ifdef, #ifndef, #if, #elif, #else, #endif)
//! - Anonymous structs and unions (embedded within other structs)
//!
//! C11/C23 features:
//! - Static assertions (`_Static_assert`, `static_assert`) with decorator "static_assert"
//! - Thread-local storage (`__thread`) with decorator "thread_local"
//! - Inline assembly detection (`asm`, `__asm__`) with decorator "inline_assembly"
//!
//! C-specific patterns handled:
//! - Static functions (storage_class_specifier)
//! - Pointer types (pointer_declarator)
//! - Const qualifiers (type_qualifier)
//! - Header vs source file distinction
//! - Doc comments (/* */ and // style preceding declarations)
//! - Object-like macros (#define FOO 42)
//! - Function-like macros (#define MAX(a,b) ((a)>(b)?(a):(b)))
//! - Function pointer typedefs (typedef int (*fn_ptr)(int, int))
//! - Preprocessor conditional compilation blocks
//! - Anonymous struct/union members in composite types

use rustc_hash::FxHashMap;
use std::path::Path;
use tree_sitter::{Node, Parser, Tree};

use crate::ast::types::{ClassInfo, FunctionInfo, ImportInfo};
use crate::cfg::types::{BlockId, BlockType, CFGBlock, CFGEdge, CFGInfo, EdgeType};
use crate::dfg::types::{DFGInfo, DataflowEdge, DataflowKind};
use crate::error::{BrrrError, Result};
use crate::lang::traits::Language;

/// Detect if a `.h` header file contains C++ code.
///
/// This heuristic checks for C++ keywords and patterns that are not valid C.
/// Used to prevent the C parser from attempting to parse C++ headers,
/// which would result in parse errors or incorrect extraction.
///
/// # C++ Indicators Checked
///
/// - `template<` or `template <` - C++ templates
/// - `namespace ` followed by identifier - C++ namespaces
/// - `class ` followed by identifier (not typedef) - C++ classes
/// - `constexpr ` - C++11 constant expressions
/// - `consteval ` - C++20 immediate functions
/// - `nullptr` - C++11 null pointer literal
/// - `noexcept` - C++ exception specification
/// - `decltype` - C++11 type deduction
/// - `static_assert(` with no leading `_Static_assert` - C++11 static assertions
/// - `typename ` - C++ type parameter
/// - `using namespace` - C++ using directive
/// - `auto ` followed by identifier and `=` - C++11 type inference
/// - `private:`, `public:`, `protected:` - C++ access specifiers
///
/// # Arguments
///
/// * `content` - File content as bytes
///
/// # Returns
///
/// * `true` if C++ indicators are found, `false` otherwise
///
/// # Performance
///
/// Only scans the first 32KB of the file for efficiency.
/// Most C++ indicators appear near the top (includes, namespaces, templates).
fn is_cpp_header(content: &[u8]) -> bool {
    // Only scan the first 32KB for efficiency
    let scan_limit = content.len().min(32 * 1024);
    let content = match std::str::from_utf8(&content[..scan_limit]) {
        Ok(s) => s,
        Err(_) => return false, // Invalid UTF-8, likely binary - let parser handle it
    };

    // C++ keyword patterns that are definitively not valid C
    // Using simple substring search for performance (avoid regex overhead)

    // template<T> or template <T>
    if content.contains("template<") || content.contains("template <") {
        return true;
    }

    // namespace identifier { or namespace identifier::
    // Check for 'namespace' followed by a space and then an identifier
    if let Some(pos) = content.find("namespace ") {
        let after = &content[pos + 10..];
        // Check that it's followed by an identifier (letter or underscore)
        if let Some(first_char) = after.chars().next() {
            if first_char.is_alphabetic() || first_char == '_' {
                return true;
            }
        }
    }

    // class Foo : or class Foo { (but not 'enum class' which we need to distinguish)
    // Also avoid false positives from comments like "Every class is associated..."
    // A real C++ class declaration has: class Name { or class Name :
    for (idx, _) in content.match_indices("class ") {
        // Make sure it's not preceded by 'enum '
        let prefix_start = idx.saturating_sub(5);
        let prefix = &content[prefix_start..idx];
        if !prefix.ends_with("enum ") {
            // Check if followed by identifier
            let after = &content[idx + 6..];
            if let Some(first_char) = after.chars().next() {
                if first_char.is_alphabetic() || first_char == '_' {
                    // Look for class definition indicators: { or : within reasonable distance
                    // This avoids false positives from "class is" or "class configuration" in comments
                    let scan_ahead = &after[..after.len().min(100)];
                    // Check if we find { or : before a newline or semicolon (statement end)
                    let mut found_def = false;
                    for ch in scan_ahead.chars() {
                        match ch {
                            '{' | ':' => {
                                found_def = true;
                                break;
                            }
                            '\n' | ';' | '.' | ',' => {
                                // Statement/sentence ended without class definition
                                break;
                            }
                            _ => continue,
                        }
                    }
                    if found_def {
                        return true;
                    }
                }
            }
        }
    }

    // constexpr - C++11 constant expressions
    if content.contains("constexpr ") || content.contains("constexpr\n") {
        return true;
    }

    // consteval - C++20 immediate functions
    if content.contains("consteval ") {
        return true;
    }

    // nullptr - C++11 null pointer
    if content.contains("nullptr") {
        return true;
    }

    // noexcept - C++ exception specification
    if content.contains("noexcept") {
        return true;
    }

    // decltype - C++11 type deduction
    if content.contains("decltype(") || content.contains("decltype (") {
        return true;
    }

    // typename - C++ type parameter
    if content.contains("typename ") {
        return true;
    }

    // using namespace - C++ using directive
    if content.contains("using namespace") {
        return true;
    }

    // C++ access specifiers (public:, private:, protected:)
    // These inside struct/class definitions indicate C++
    if content.contains("public:") || content.contains("private:") || content.contains("protected:")
    {
        return true;
    }

    // C++ style casts
    if content.contains("static_cast<")
        || content.contains("dynamic_cast<")
        || content.contains("const_cast<")
        || content.contains("reinterpret_cast<")
    {
        return true;
    }

    // References with & in type declarations (tricky - avoid function address-of)
    // Look for patterns like "Type& name" or "const Type&"
    if content.contains("& ")
        && (content.contains("const ") || content.contains("int&") || content.contains("char&"))
    {
        // Additional check - C++ style reference in parameter/return
        for pattern in ["int& ", "char& ", "void& ", "bool& ", "auto& "] {
            if content.contains(pattern) {
                return true;
            }
        }
    }

    false
}

/// C language implementation.
pub struct C;

impl C {
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
    /// Supports both /* */ block comments and // line comments.
    ///
    /// Comments are considered adjacent if there is at most MAX_GAP blank lines
    /// between them and the declaration (or between consecutive comments).
    fn get_doc_comment(&self, node: Node, source: &[u8]) -> Option<String> {
        let mut comments = Vec::new();
        // Track the row we expect comments to end before.
        // Initially, this is the function's start row.
        let mut expected_before_row = node.start_position().row;

        // Maximum allowed gap (blank lines) between comment and declaration
        // or between consecutive comments. Setting to 1 allows a single blank line.
        const MAX_GAP: usize = 1;

        // Walk backwards through siblings to find comments
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

        // Block comment: /* ... */ or /** ... */
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

        // Line comment: // ...
        if text.starts_with("//") {
            return text.strip_prefix("//").unwrap_or(text).trim().to_string();
        }

        text.to_string()
    }

    /// Extract the full type from a type node, handling pointers and qualifiers.
    /// Reserved for future use in enhanced type extraction.
    #[allow(dead_code)]
    fn extract_type(&self, node: Node, source: &[u8]) -> String {
        let mut parts = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "type_qualifier" => {
                    parts.push(self.node_text(child, source));
                }
                "primitive_type" | "type_identifier" | "sized_type_specifier" => {
                    parts.push(self.node_text(child, source));
                }
                "struct_specifier" => {
                    // Handle struct Type
                    if let Some(name) = self.child_by_field(child, "name") {
                        parts.push(format!("struct {}", self.node_text(name, source)));
                    } else {
                        parts.push("struct".to_string());
                    }
                }
                "enum_specifier" => {
                    if let Some(name) = self.child_by_field(child, "name") {
                        parts.push(format!("enum {}", self.node_text(name, source)));
                    } else {
                        parts.push("enum".to_string());
                    }
                }
                "union_specifier" => {
                    if let Some(name) = self.child_by_field(child, "name") {
                        parts.push(format!("union {}", self.node_text(name, source)));
                    } else {
                        parts.push("union".to_string());
                    }
                }
                _ => {}
            }
        }

        // If no children matched, use the node text directly
        if parts.is_empty() {
            return self.node_text(node, source);
        }

        parts.join(" ")
    }

    /// Extract parameter list from a parameter_list node.
    fn extract_params(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut params = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            if child.kind() == "parameter_declaration" {
                let param = self.extract_parameter(child, source);
                if !param.is_empty() {
                    params.push(param);
                }
            } else if child.kind() == "variadic_parameter" {
                params.push("...".to_string());
            }
        }

        params
    }

    /// Extract a single parameter declaration.
    fn extract_parameter(&self, node: Node, source: &[u8]) -> String {
        let mut type_parts = Vec::new();
        let mut name = String::new();
        let mut pointer_count = 0;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "type_qualifier" => {
                    type_parts.push(self.node_text(child, source));
                }
                "primitive_type" | "type_identifier" | "sized_type_specifier" => {
                    type_parts.push(self.node_text(child, source));
                }
                "struct_specifier" => {
                    if let Some(n) = self.child_by_field(child, "name") {
                        type_parts.push(format!("struct {}", self.node_text(n, source)));
                    }
                }
                "pointer_declarator" => {
                    let (n, ptrs) = self.extract_pointer_declarator(child, source);
                    name = n;
                    pointer_count = ptrs;
                }
                "identifier" => {
                    name = self.node_text(child, source);
                }
                "array_declarator" => {
                    // Handle array parameters like int arr[]
                    let (n, suffix) = self.extract_array_declarator(child, source);
                    name = format!("{}{}", n, suffix);
                }
                "abstract_pointer_declarator" => {
                    // Handle unnamed pointer parameters like (const void*, int*)
                    // Count nested pointer levels for void**, int***, etc.
                    pointer_count += self.count_abstract_pointer_levels(child);
                }
                _ => {}
            }
        }

        let type_str = type_parts.join(" ");
        let pointers = "*".repeat(pointer_count);

        if name.is_empty() {
            // Unnamed parameter (just type)
            format!("{}{}", type_str, pointers)
        } else {
            format!("{}{} {}", type_str, pointers, name)
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
                    // Find the declarator child manually, skipping type qualifiers and pointer symbols.
                    // For `const int * const * ptr`, AST may have: const -> * -> const -> * -> identifier
                    // We must skip type_qualifier nodes to find the actual declarator.
                    let mut found = false;
                    let mut cursor = current.walk();
                    for child in current.children(&mut cursor) {
                        match child.kind() {
                            // Skip pointer symbols and type qualifiers
                            "*" | "type_qualifier" | "const" | "volatile" | "restrict"
                            | "_Atomic" => {
                                continue;
                            }
                            // Found a declarator or identifier - use it
                            "identifier"
                            | "field_identifier"
                            | "pointer_declarator"
                            | "array_declarator"
                            | "function_declarator" => {
                                current = child;
                                found = true;
                                break;
                            }
                            // For any other node type, try recursing into it
                            _ => {
                                current = child;
                                found = true;
                                break;
                            }
                        }
                    }
                    if !found {
                        break;
                    }
                }
            } else if current.kind() == "identifier" || current.kind() == "field_identifier" {
                return (self.node_text(current, source), pointer_count);
            } else if current.kind() == "function_declarator" {
                // Function pointer - extract the identifier from it
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

    /// Extract identifier and array suffix from an array_declarator.
    fn extract_array_declarator(&self, node: Node, source: &[u8]) -> (String, String) {
        let mut name = String::new();
        let mut suffix = String::new();

        if let Some(declarator) = self.child_by_field(node, "declarator") {
            name = self.node_text(declarator, source);
        }

        // Build array suffix
        if let Some(size) = self.child_by_field(node, "size") {
            suffix = format!("[{}]", self.node_text(size, source));
        } else {
            suffix = "[]".to_string();
        }

        (name, suffix)
    }

    /// Count pointer levels in an abstract_pointer_declarator.
    ///
    /// Handles nested pointers for types like `void**`, `int***`.
    /// The AST structure for `void**` is:
    /// ```text
    /// abstract_pointer_declarator
    ///   *
    ///   abstract_pointer_declarator
    ///     *
    /// ```
    fn count_abstract_pointer_levels(&self, node: Node) -> usize {
        let mut count = 1; // Current node is one pointer level
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            if child.kind() == "abstract_pointer_declarator" {
                count += self.count_abstract_pointer_levels(child);
            }
        }

        count
    }

    /// Extract object-like macro definition (#define FOO 42).
    /// Returns FunctionInfo with decorator "macro" and no params.
    fn extract_object_macro(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        // preproc_def has: name (identifier), value (preproc_arg)
        let name = self
            .child_by_field(node, "name")
            .map(|n| self.node_text(n, source))?;

        // Get the macro value/body if present
        let value = self
            .child_by_field(node, "value")
            .map(|v| self.node_text(v, source).trim().to_string());

        let docstring = self.get_doc_comment(node, source);

        Some(FunctionInfo {
            name,
            params: Vec::new(),
            return_type: value, // Store macro value in return_type field
            docstring,
            is_method: false,
            is_async: false,
            decorators: vec!["macro".to_string()],
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "c".to_string(),
        })
    }

    /// Extract function-like macro definition (#define MAX(a,b) ...).
    /// Returns FunctionInfo with decorator "macro" and params extracted from preproc_params.
    fn extract_function_macro(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        // preproc_function_def has: name (identifier), parameters (preproc_params), value (preproc_arg)
        let name = self
            .child_by_field(node, "name")
            .map(|n| self.node_text(n, source))?;

        // Extract macro parameters from preproc_params
        let params = self
            .child_by_field(node, "parameters")
            .map(|p| self.extract_macro_params(p, source))
            .unwrap_or_default();

        // Get the macro body if present
        let value = self
            .child_by_field(node, "value")
            .map(|v| self.node_text(v, source).trim().to_string());

        let docstring = self.get_doc_comment(node, source);

        Some(FunctionInfo {
            name,
            params,
            return_type: value, // Store macro body in return_type field
            docstring,
            is_method: false,
            is_async: false,
            decorators: vec!["macro".to_string()],
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "c".to_string(),
        })
    }

    /// Extract parameter names from a preproc_params node (for function-like macros).
    fn extract_macro_params(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut params = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            if child.kind() == "identifier" {
                params.push(self.node_text(child, source));
            } else if child.kind() == "..." {
                params.push("...".to_string());
            }
        }

        params
    }

    /// Extract preprocessor conditional (#ifdef, #ifndef, #if).
    /// Returns ClassInfo with decorator indicating the conditional type.
    fn extract_preproc_conditional(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        match node.kind() {
            "preproc_ifdef" => {
                // #ifdef or #ifndef - determined by first child
                let mut cursor = node.walk();
                let mut is_ifndef = false;

                for child in node.children(&mut cursor) {
                    if child.kind() == "#ifndef" {
                        is_ifndef = true;
                        break;
                    } else if child.kind() == "#ifdef" {
                        break;
                    }
                }

                let name = self
                    .child_by_field(node, "name")
                    .map(|n| self.node_text(n, source))?;

                let decorator = if is_ifndef {
                    "preproc_ifndef"
                } else {
                    "preproc_ifdef"
                };

                Some(ClassInfo {
                    name,
                    bases: Vec::new(),
                    docstring: self.get_doc_comment(node, source),
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: self.extract_nested_preproc_conditionals(node, source),
                    decorators: vec![decorator.to_string()],
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "c".to_string(),
                })
            }
            "preproc_if" => {
                // #if with condition expression
                let condition = self
                    .child_by_field(node, "condition")
                    .map(|n| self.node_text(n, source))
                    .unwrap_or_else(|| "unknown".to_string());

                // Extract nested conditionals from alternatives (elif/else chains)
                let mut inner = self.extract_nested_preproc_conditionals(node, source);

                // Also extract from alternative branch if present
                if let Some(alt) = self.child_by_field(node, "alternative") {
                    inner.extend(self.extract_preproc_alternative_chain(alt, source));
                }

                Some(ClassInfo {
                    name: condition,
                    bases: Vec::new(),
                    docstring: self.get_doc_comment(node, source),
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: inner,
                    decorators: vec!["preproc_if".to_string()],
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "c".to_string(),
                })
            }
            _ => None,
        }
    }

    /// Extract #elif and #else chains as nested ClassInfo entries.
    fn extract_preproc_alternative_chain(&self, node: Node, source: &[u8]) -> Vec<ClassInfo> {
        let mut results = Vec::new();

        match node.kind() {
            "preproc_elif" => {
                let condition = self
                    .child_by_field(node, "condition")
                    .map(|n| self.node_text(n, source))
                    .unwrap_or_else(|| "unknown".to_string());

                let mut inner = self.extract_nested_preproc_conditionals(node, source);

                // Continue chain if there's another alternative
                if let Some(alt) = self.child_by_field(node, "alternative") {
                    inner.extend(self.extract_preproc_alternative_chain(alt, source));
                }

                results.push(ClassInfo {
                    name: condition,
                    bases: Vec::new(),
                    docstring: None,
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: inner,
                    decorators: vec!["preproc_elif".to_string()],
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "c".to_string(),
                });
            }
            "preproc_else" => {
                results.push(ClassInfo {
                    name: "#else".to_string(),
                    bases: Vec::new(),
                    docstring: None,
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: self.extract_nested_preproc_conditionals(node, source),
                    decorators: vec!["preproc_else".to_string()],
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "c".to_string(),
                });
            }
            _ => {}
        }

        results
    }

    /// Extract nested preprocessor conditionals from a node's children.
    fn extract_nested_preproc_conditionals(&self, node: Node, source: &[u8]) -> Vec<ClassInfo> {
        let mut results = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "preproc_ifdef" | "preproc_if" => {
                    if let Some(cond) = self.extract_preproc_conditional(child, source) {
                        results.push(cond);
                    }
                }
                _ => {}
            }
        }

        results
    }

    /// Extract anonymous struct or union from a field_declaration.
    /// Returns ClassInfo with auto-generated name based on parent context.
    fn extract_anonymous_struct_or_union(
        &self,
        node: Node,
        source: &[u8],
        parent_name: &str,
        index: usize,
    ) -> Option<ClassInfo> {
        // node is a struct_specifier or union_specifier without a name
        let kind = node.kind();

        // Verify it has no name (anonymous)
        if self.child_by_field(node, "name").is_some() {
            return None;
        }

        // Verify it has a body (not just a forward reference)
        if self.child_by_field(node, "body").is_none() {
            return None;
        }

        let type_tag = if kind == "struct_specifier" {
            "struct"
        } else if kind == "union_specifier" {
            "union"
        } else {
            return None;
        };

        // Generate a synthetic name for the anonymous type
        let synthetic_name = format!("{}_anon_{}_{}", parent_name, type_tag, index);

        let decorator = format!("anonymous_{}", type_tag);

        // Extract nested anonymous types from this anonymous type's body
        let inner_classes = self.extract_anonymous_members_from_body(node, source, &synthetic_name);

        Some(ClassInfo {
            name: synthetic_name,
            bases: Vec::new(),
            docstring: self.get_doc_comment(node, source),
            methods: Vec::new(),
            fields: Vec::new(),
            inner_classes,
            decorators: vec![decorator],
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "c".to_string(),
        })
    }

    /// Extract all anonymous struct/union members from a struct/union body.
    fn extract_anonymous_members_from_body(
        &self,
        parent_node: Node,
        source: &[u8],
        parent_name: &str,
    ) -> Vec<ClassInfo> {
        let mut results = Vec::new();

        let body = match self.child_by_field(parent_node, "body") {
            Some(b) => b,
            None => return results,
        };

        let mut cursor = body.walk();
        let mut anon_index = 0;

        for child in body.children(&mut cursor) {
            if child.kind() == "field_declaration" {
                // Check if this field's type is an anonymous struct/union
                let mut field_cursor = child.walk();
                for field_child in child.children(&mut field_cursor) {
                    if field_child.kind() == "struct_specifier"
                        || field_child.kind() == "union_specifier"
                    {
                        // Check if it's anonymous (no name field)
                        if self.child_by_field(field_child, "name").is_none() {
                            if let Some(anon) = self.extract_anonymous_struct_or_union(
                                field_child,
                                source,
                                parent_name,
                                anon_index,
                            ) {
                                results.push(anon);
                                anon_index += 1;
                            }
                        }
                    }
                }
            }
        }

        results
    }

    /// Extract struct/union field declarations including bitfield information.
    ///
    /// Handles:
    /// - Regular fields: `int x;`
    /// - Pointer fields: `int *ptr;`
    /// - Array fields: `int arr[10];`
    /// - Bitfield fields: `unsigned int flag : 1;`
    ///
    /// Bitfield width is stored in the field's annotations as "bitfield:N".
    fn extract_struct_fields(
        &self,
        node: Node,
        source: &[u8],
    ) -> Vec<crate::ast::types::FieldInfo> {
        use crate::ast::types::FieldInfo;

        let mut fields = Vec::new();

        let body = match self.child_by_field(node, "body") {
            Some(b) => b,
            None => return fields,
        };

        let mut cursor = body.walk();

        for child in body.children(&mut cursor) {
            if child.kind() != "field_declaration" {
                continue;
            }

            // Extract field type
            let mut type_parts = Vec::new();
            let mut field_name = String::new();
            let mut pointer_count = 0;
            let mut array_suffix = String::new();
            let mut bitfield_width: Option<String> = None;

            let mut field_cursor = child.walk();
            for field_child in child.children(&mut field_cursor) {
                match field_child.kind() {
                    "type_qualifier" => {
                        type_parts.push(self.node_text(field_child, source));
                    }
                    "primitive_type" | "type_identifier" | "sized_type_specifier" => {
                        type_parts.push(self.node_text(field_child, source));
                    }
                    "struct_specifier" | "union_specifier" | "enum_specifier" => {
                        // Handle embedded type specifiers (including anonymous)
                        if let Some(name) = self.child_by_field(field_child, "name") {
                            let kind = if field_child.kind() == "struct_specifier" {
                                "struct"
                            } else if field_child.kind() == "union_specifier" {
                                "union"
                            } else {
                                "enum"
                            };
                            type_parts.push(format!("{} {}", kind, self.node_text(name, source)));
                        }
                    }
                    "field_identifier" => {
                        field_name = self.node_text(field_child, source);
                    }
                    "pointer_declarator" => {
                        let (name, ptrs) = self.extract_pointer_declarator(field_child, source);
                        if !name.is_empty() {
                            field_name = name;
                        }
                        pointer_count = ptrs;
                    }
                    "array_declarator" => {
                        let (name, suffix) = self.extract_array_declarator(field_child, source);
                        field_name = name;
                        array_suffix = suffix;
                    }
                    "bitfield_clause" => {
                        // Extract bit width from bitfield_clause
                        let mut bf_cursor = field_child.walk();
                        for bf_child in field_child.children(&mut bf_cursor) {
                            if bf_child.kind() == "number_literal" {
                                bitfield_width = Some(self.node_text(bf_child, source));
                                break;
                            }
                        }
                    }
                    _ => {}
                }
            }

            // Skip if no field name (shouldn't happen for valid C)
            if field_name.is_empty() {
                continue;
            }

            // Build the complete type string
            let pointers = "*".repeat(pointer_count);
            let type_str = if type_parts.is_empty() {
                None
            } else {
                Some(format!(
                    "{}{}{}",
                    type_parts.join(" "),
                    pointers,
                    array_suffix
                ))
            };

            // Build annotations including bitfield info
            let mut annotations = Vec::new();
            if let Some(width) = bitfield_width {
                annotations.push(format!("bitfield:{}", width));
            }

            fields.push(FieldInfo {
                name: field_name,
                field_type: type_str,
                visibility: None,
                is_static: false,
                is_final: false,
                default_value: None,
                annotations,
                line_number: child.start_position().row + 1,
            });
        }

        fields
    }

    /// Extract K&R style (old-style) parameter declarations.
    ///
    /// In K&R style, function parameters are declared without types in the
    /// parameter list, and type declarations follow:
    /// ```c
    /// int foo(a, b)
    /// int a;
    /// int b;
    /// { ... }
    /// ```
    ///
    /// Returns a map from parameter name to its full type string.
    fn extract_knr_params(
        &self,
        node: Node,
        source: &[u8],
    ) -> FxHashMap<String, String> {
        let mut type_map = FxHashMap::default();

        // K&R declarations are direct children of function_definition,
        // appearing between the declarator and the body
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() != "declaration" {
                continue;
            }

            // Extract type from the declaration
            let mut type_parts = Vec::new();
            let mut names = Vec::new();
            let mut decl_cursor = child.walk();

            for decl_child in child.children(&mut decl_cursor) {
                match decl_child.kind() {
                    "type_qualifier" => {
                        type_parts.push(self.node_text(decl_child, source));
                    }
                    "primitive_type" | "type_identifier" | "sized_type_specifier" => {
                        type_parts.push(self.node_text(decl_child, source));
                    }
                    "struct_specifier" => {
                        if let Some(name) = self.child_by_field(decl_child, "name") {
                            type_parts.push(format!("struct {}", self.node_text(name, source)));
                        }
                    }
                    "identifier" => {
                        names.push(self.node_text(decl_child, source));
                    }
                    "pointer_declarator" => {
                        let (name, ptrs) = self.extract_pointer_declarator(decl_child, source);
                        if !name.is_empty() {
                            let pointers = "*".repeat(ptrs);
                            // For K&R, store the full type with pointers
                            let base_type = type_parts.join(" ");
                            type_map.insert(name, format!("{}{}", base_type, pointers));
                        }
                    }
                    "array_declarator" => {
                        let (name, suffix) = self.extract_array_declarator(decl_child, source);
                        if !name.is_empty() {
                            let base_type = type_parts.join(" ");
                            type_map.insert(name, format!("{}{}", base_type, suffix));
                        }
                    }
                    _ => {}
                }
            }

            // Map each identifier to its type
            let base_type = type_parts.join(" ");
            for name in names {
                if !type_map.contains_key(&name) {
                    type_map.insert(name, base_type.clone());
                }
            }
        }

        type_map
    }

    /// Check if a function definition uses K&R style parameters.
    ///
    /// K&R style is detected when:
    /// 1. The parameter_list contains bare identifiers (no type specifiers)
    /// 2. There are declaration nodes between declarator and body
    fn is_knr_style(&self, node: Node) -> bool {
        if node.kind() != "function_definition" {
            return false;
        }

        // Check for declaration nodes that are direct children (K&R type declarations)
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            // If we find a declaration that's not inside the body, it's K&R style
            if child.kind() == "declaration" {
                return true;
            }
        }

        false
    }

    /// Extract GCC __attribute__ specifiers from a node.
    ///
    /// Handles attributes on:
    /// - Function declarations/definitions
    /// - Struct/union/enum specifiers
    /// - Variable declarations
    ///
    /// Returns a list of attribute strings like "packed", "aligned(4)", "noreturn".
    fn extract_attributes(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut attributes = Vec::new();

        // Look for attribute_specifier nodes in the current node and its children
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "attribute_specifier" {
                self.extract_attribute_content(child, source, &mut attributes);
            }
            // Also check in declarators (e.g., for function attributes)
            if child.kind() == "function_declarator" {
                let mut decl_cursor = child.walk();
                for decl_child in child.children(&mut decl_cursor) {
                    if decl_child.kind() == "attribute_specifier" {
                        self.extract_attribute_content(decl_child, source, &mut attributes);
                    }
                }
            }
        }

        attributes
    }

    /// Extract the content of an attribute_specifier node.
    fn extract_attribute_content(&self, node: Node, source: &[u8], attributes: &mut Vec<String>) {
        // attribute_specifier structure:
        // __attribute__ ( argument_list ( ... ) )
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "argument_list" {
                // The inner argument_list contains the actual attributes
                let mut inner_cursor = child.walk();
                for inner_child in child.children(&mut inner_cursor) {
                    match inner_child.kind() {
                        "argument_list" => {
                            // This is the ((...)) inner list
                            let mut attr_cursor = inner_child.walk();
                            for attr_child in inner_child.children(&mut attr_cursor) {
                                match attr_child.kind() {
                                    "identifier" => {
                                        // Simple attribute like "packed"
                                        let attr_name = self.node_text(attr_child, source);
                                        attributes.push(format!("__attribute__(({}))", attr_name));
                                    }
                                    "call_expression" => {
                                        // Attribute with arguments like "aligned(4)"
                                        let attr_text = self.node_text(attr_child, source);
                                        attributes.push(format!("__attribute__(({}))", attr_text));
                                    }
                                    _ => {}
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    /// Extract function pointer from a type_definition or declaration.
    /// Handles: typedef int (*fn_ptr)(int, int); or void (*callback)(void);
    fn extract_function_pointer(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        let is_typedef = node.kind() == "type_definition";

        // Find the function_declarator containing parenthesized_declarator
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "function_declarator" {
                return self.extract_fn_ptr_from_declarator(child, node, source, is_typedef);
            }
        }

        None
    }

    /// Extract function pointer details from a function_declarator node.
    fn extract_fn_ptr_from_declarator(
        &self,
        func_decl: Node,
        parent: Node,
        source: &[u8],
        is_typedef: bool,
    ) -> Option<FunctionInfo> {
        // Look for parenthesized_declarator containing pointer_declarator
        let paren_decl = self.child_by_field(func_decl, "declarator")?;

        if paren_decl.kind() != "parenthesized_declarator" {
            return None;
        }

        // Find the pointer_declarator inside parenthesized_declarator
        let mut cursor = paren_decl.walk();
        let mut fn_ptr_name = None;

        for child in paren_decl.children(&mut cursor) {
            if child.kind() == "pointer_declarator" {
                // Get the name - could be identifier or type_identifier
                if let Some(decl) = self.child_by_field(child, "declarator") {
                    fn_ptr_name = Some(self.node_text(decl, source));
                }
            }
        }

        let name = fn_ptr_name?;

        // Extract return type from parent node
        let return_type = self.extract_return_type(parent, source);

        // Extract parameters from function_declarator
        let params = self
            .child_by_field(func_decl, "parameters")
            .map(|p| self.extract_params(p, source))
            .unwrap_or_default();

        let docstring = self.get_doc_comment(parent, source);

        let mut decorators = vec!["function_pointer".to_string()];
        if is_typedef {
            decorators.push("typedef".to_string());
        }

        Some(FunctionInfo {
            name,
            params,
            return_type,
            docstring,
            is_method: false,
            is_async: false,
            decorators,
            line_number: parent.start_position().row + 1,
            end_line_number: Some(parent.end_position().row + 1),
            language: "c".to_string(),
        })
    }

    /// Extract return type from a function definition or declaration.
    fn extract_return_type(&self, node: Node, source: &[u8]) -> Option<String> {
        let mut type_parts = Vec::new();
        let mut pointer_count = 0;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "storage_class_specifier" => {
                    // Skip storage class (static, extern, etc.) for return type
                }
                "type_qualifier" => {
                    type_parts.push(self.node_text(child, source));
                }
                "primitive_type" | "type_identifier" | "sized_type_specifier" => {
                    type_parts.push(self.node_text(child, source));
                }
                "struct_specifier" => {
                    if let Some(name) = self.child_by_field(child, "name") {
                        type_parts.push(format!("struct {}", self.node_text(name, source)));
                    }
                }
                "pointer_declarator" => {
                    // Return type with pointer: int* func()
                    // Count asterisks at the start of the declarator chain
                    let mut current = child;
                    while current.kind() == "pointer_declarator" {
                        pointer_count += 1;
                        if let Some(decl) = self.child_by_field(current, "declarator") {
                            current = decl;
                        } else {
                            let mut c = current.walk();
                            let mut found = false;
                            for ch in current.children(&mut c) {
                                if ch.kind() != "*" {
                                    current = ch;
                                    found = true;
                                    break;
                                }
                            }
                            if !found {
                                break;
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        if type_parts.is_empty() {
            return None;
        }

        let pointers = "*".repeat(pointer_count);
        Some(format!("{}{}", type_parts.join(" "), pointers))
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

    /// Check if a function body contains inline assembly (gnu_asm_expression).
    ///
    /// Detects both `asm` and `__asm__` statements, including extended asm
    /// with volatile, goto, and operand specifications.
    fn contains_inline_assembly(&self, node: Node) -> bool {
        // Check current node
        if node.kind() == "gnu_asm_expression" {
            return true;
        }

        // Recursively check children
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if self.contains_inline_assembly(child) {
                return true;
            }
        }

        false
    }

    /// Extract a static assertion declaration.
    ///
    /// Handles both `_Static_assert` (C11) and `static_assert` (C23) forms.
    /// Since tree-sitter-c parses these as call_expression, we detect them
    /// by checking the function identifier name.
    ///
    /// Returns a FunctionInfo with decorator "static_assert" containing
    /// the condition expression and optional message.
    fn extract_static_assert(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        // Must be an expression_statement containing a call_expression
        if node.kind() != "expression_statement" {
            return None;
        }

        let call_expr = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "call_expression")?;

        // Check if function name is _Static_assert or static_assert
        let func_node = self.child_by_field(call_expr, "function")?;
        let func_name = self.node_text(func_node, source);

        if func_name != "_Static_assert" && func_name != "static_assert" {
            return None;
        }

        // Extract arguments
        let args_node = self.child_by_field(call_expr, "arguments")?;
        let mut params = Vec::new();
        let mut cursor = args_node.walk();

        for child in args_node.children(&mut cursor) {
            match child.kind() {
                "binary_expression" | "sizeof_expression" | "identifier" | "number_literal" => {
                    // The condition expression
                    params.push(self.node_text(child, source));
                }
                "string_literal" => {
                    // The message (optional in C23)
                    params.push(self.node_text(child, source));
                }
                _ => {}
            }
        }

        // Format: condition as first param, message as second (if present)
        let docstring = if params.len() > 1 {
            Some(params[1].trim_matches('"').to_string())
        } else {
            None
        };

        Some(FunctionInfo {
            name: format!(
                "static_assert({})",
                params.first().unwrap_or(&String::new())
            ),
            params: Vec::new(),
            return_type: None,
            docstring,
            is_method: false,
            is_async: false,
            decorators: vec!["static_assert".to_string()],
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "c".to_string(),
        })
    }

    /// Extract a thread-local variable declaration.
    ///
    /// Detects variables with `__thread` (GCC extension) or `_Thread_local` (C11)
    /// storage class specifier. Note: tree-sitter-c reliably parses `__thread`,
    /// but `_Thread_local` may produce parse errors in some tree-sitter versions.
    fn extract_thread_local_variable(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        if node.kind() != "declaration" {
            return None;
        }

        // Check for __thread storage class specifier
        let has_thread_local = self.has_storage_class(node, source, "__thread");
        if !has_thread_local {
            return None;
        }

        // Skip function declarations - they should be handled elsewhere
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "function_declarator" {
                return None;
            }
        }

        // Extract variable name from init_declarator or identifier
        let mut var_name = String::new();
        let mut var_type = String::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "primitive_type" | "type_identifier" | "sized_type_specifier" => {
                    var_type = self.node_text(child, source);
                }
                "init_declarator" => {
                    if let Some(decl) = self.child_by_field(child, "declarator") {
                        var_name = self.node_text(decl, source);
                    }
                }
                "identifier" => {
                    if var_name.is_empty() {
                        var_name = self.node_text(child, source);
                    }
                }
                "pointer_declarator" => {
                    let (name, ptr_count) = self.extract_pointer_declarator(child, source);
                    var_name = name;
                    var_type = format!("{}{}", var_type, "*".repeat(ptr_count));
                }
                _ => {}
            }
        }

        if var_name.is_empty() {
            return None;
        }

        let mut decorators = vec!["thread_local".to_string(), "variable".to_string()];

        // Check for other storage class specifiers
        if self.has_storage_class(node, source, "static") {
            decorators.push("static".to_string());
        }
        if self.has_storage_class(node, source, "extern") {
            decorators.push("extern".to_string());
        }

        let docstring = self.get_doc_comment(node, source);

        Some(FunctionInfo {
            name: var_name,
            params: Vec::new(),
            return_type: if var_type.is_empty() {
                None
            } else {
                Some(var_type)
            },
            docstring,
            is_method: false,
            is_async: false,
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "c".to_string(),
        })
    }

    /// Extract function name from a function_declarator.
    fn extract_function_name(&self, node: Node, source: &[u8]) -> Option<String> {
        // The declarator field contains the actual identifier (possibly wrapped in pointer_declarator)
        if let Some(declarator) = self.child_by_field(node, "declarator") {
            return self.extract_name_from_declarator(declarator, source);
        }

        // Fallback: search children
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "identifier" {
                return Some(self.node_text(child, source));
            }
            if child.kind() == "pointer_declarator" {
                let (name, _) = self.extract_pointer_declarator(child, source);
                if !name.is_empty() {
                    return Some(name);
                }
            }
        }

        None
    }

    /// Extract name from a declarator node (handles nested pointer_declarator).
    fn extract_name_from_declarator(&self, node: Node, source: &[u8]) -> Option<String> {
        match node.kind() {
            "identifier" => Some(self.node_text(node, source)),
            "pointer_declarator" => {
                let (name, _) = self.extract_pointer_declarator(node, source);
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

    /// Extract variable name from parent declaration for anonymous struct/union/enum.
    ///
    /// For code like `struct { int x; } my_var;`, extracts "my_var" from the declaration.
    /// Returns None if parent is not a declaration or no identifier found.
    fn extract_name_from_declaration_parent(&self, node: Node, source: &[u8]) -> Option<String> {
        let parent = node.parent()?;
        if parent.kind() != "declaration" {
            return None;
        }

        // In a declaration like `struct { ... } var;`, the declarator contains the variable name
        let mut cursor = parent.walk();
        for child in parent.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    return Some(self.node_text(child, source));
                }
                "init_declarator" => {
                    // Handle `struct { ... } var = {...};`
                    if let Some(decl) = self.child_by_field(child, "declarator") {
                        return self.extract_name_from_declarator(decl, source);
                    }
                }
                "pointer_declarator" => {
                    // Handle `struct { ... } *ptr;`
                    let (name, _) = self.extract_pointer_declarator(child, source);
                    if !name.is_empty() {
                        return Some(name);
                    }
                }
                "array_declarator" => {
                    // Handle `struct { ... } arr[10];`
                    let (name, _) = self.extract_array_declarator(child, source);
                    if !name.is_empty() {
                        return Some(name);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Build CFG for a C function.
    ///
    /// Supports goto/label control flow: creates proper CFG edges from goto
    /// statements to their target labels, handling both forward and backward jumps.
    fn build_c_cfg(&self, node: Node, source: &[u8], func_name: &str) -> CFGInfo {
        let mut blocks = FxHashMap::default();
        let mut edges = Vec::new();
        let mut block_id = 0;
        let mut exits = Vec::new();

        // Label tracking for goto support
        let mut label_blocks: FxHashMap<String, BlockId> = FxHashMap::default();
        let mut pending_gotos: Vec<(BlockId, String)> = Vec::new();

        // Entry block
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

        // Find body (compound_statement)
        let mut decision_points: usize = 0;
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
                &mut label_blocks,
                &mut pending_gotos,
                &mut decision_points,
            );
        }

        // Resolve pending goto edges (forward references to labels)
        for (from_block, target_label) in pending_gotos {
            if let Some(&target_block) = label_blocks.get(&target_label) {
                edges.push(CFGEdge::from_label(
                    from_block,
                    target_block,
                    Some(format!("goto {}", target_label)),
                ));
            }
        }

        // If no explicit exits, the entry block is also an exit
        if exits.is_empty() {
            exits.push(entry);
        }

        CFGInfo {
            function_name: func_name.to_string(),
            blocks: blocks.into_iter().collect(), // Convert FxHashMap to HashMap
            edges,
            entry,
            exits,
            decision_points,
            comprehension_decision_points: 0, // C doesn't have comprehensions
            nested_cfgs: FxHashMap::default(), // C doesn't have closures but may have nested functions via GCC extension
            is_async: false,             // C doesn't have async/await
            await_points: 0,             // C doesn't have await
            blocking_calls: Vec::new(),  // C doesn't have async context
            ..Default::default()
        }
    }

    /// Process a compound statement for CFG construction.
    ///
    /// Handles goto/label control flow by tracking label blocks and pending goto edges.
    /// Labels create new blocks that can be targeted by goto statements.
    /// Gotos create edges to their target labels (resolved immediately if label seen,
    /// or queued in pending_gotos for forward references).
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
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
        decision_points: &mut usize,
    ) -> BlockId {
        // Handle the case where a single statement is passed directly (not a block-like construct)
        // This happens when if/while/for consequences are single statements without braces
        let node_kind = node.kind();

        // These are block-like constructs that contain children we should iterate over
        let is_block_like = matches!(
            node_kind,
            "compound_statement" | "case_statement" | "translation_unit"
        );

        if !is_block_like {
            // Single statement - delegate to statement handler
            let mut unreachable = false;
            return self.process_cfg_statement(
                node,
                source,
                blocks,
                edges,
                block_id,
                current_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                &mut unreachable,
                decision_points,
            );
        }

        let mut last_block = current_block;
        let mut cursor = node.walk();
        // Track if we're in unreachable code after goto/return/break/continue (no fall-through)
        let mut unreachable = false;

        for child in node.children(&mut cursor) {
            match child.kind() {
                "return_statement" => {
                    if unreachable {
                        continue;
                    }
                    *block_id += 1;
                    let ret_block = BlockId(*block_id);
                    let stmt = self.node_text(child, source);

                    blocks.insert(
                        ret_block,
                        CFGBlock {
                            id: ret_block,
                            label: "return".to_string(),
                            block_type: BlockType::Body,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(last_block, ret_block, None));

                    exits.push(ret_block);
                    last_block = ret_block;
                    unreachable = true;
                }
                "labeled_statement" => {
                    // labeled_statement has structure: label: statement
                    // The label field contains the statement_identifier
                    let label_name = self
                        .child_by_field(child, "label")
                        .map(|n| self.node_text(n, source))
                        .unwrap_or_else(|| "unknown_label".to_string());

                    // Create a new block for this label
                    *block_id += 1;
                    let label_block = BlockId(*block_id);

                    blocks.insert(
                        label_block,
                        CFGBlock {
                            id: label_block,
                            label: format!("{}:", label_name),
                            block_type: BlockType::Body,
                            statements: Vec::new(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    // Register this label for goto resolution
                    label_blocks.insert(label_name.clone(), label_block);

                    // Add fall-through edge from previous block (if not unreachable)
                    if !unreachable {
                        edges.push(CFGEdge::from_label(last_block, label_block, None));
                    }

                    // A label makes subsequent code reachable again
                    unreachable = false;
                    last_block = label_block;

                    // Process the nested statement that follows the label
                    // The statement is typically the last child after 'label' and ':'
                    let mut stmt_cursor = child.walk();
                    for stmt_child in child.children(&mut stmt_cursor) {
                        // Skip the label identifier and the colon
                        if stmt_child.kind() != "statement_identifier" && stmt_child.kind() != ":" {
                            last_block = self.process_cfg_statement(
                                stmt_child,
                                source,
                                blocks,
                                edges,
                                block_id,
                                last_block,
                                exits,
                                loop_headers,
                                loop_exits,
                                label_blocks,
                                pending_gotos,
                                &mut unreachable,
                                decision_points,
                            );
                        }
                    }
                }
                "goto_statement" => {
                    if unreachable {
                        continue;
                    }
                    // goto_statement has structure: goto label;
                    // The label field contains the target identifier
                    let target_label = self
                        .child_by_field(child, "label")
                        .map(|n| self.node_text(n, source))
                        .unwrap_or_else(|| "unknown_label".to_string());

                    // Add the goto statement to current block
                    if let Some(block) = blocks.get_mut(&last_block) {
                        let stmt = self.node_text(child, source);
                        block.statements.push(stmt);
                        block.end_line = child.end_position().row + 1;
                    }

                    // Create edge to target label
                    if let Some(&target_block) = label_blocks.get(&target_label) {
                        // Label already seen (backward goto)
                        edges.push(CFGEdge::from_label(
                            last_block,
                            target_block,
                            Some(format!("goto {}", target_label)),
                        ));
                    } else {
                        // Label not yet seen (forward goto) - queue for later resolution
                        pending_gotos.push((last_block, target_label));
                    }

                    // After goto, there's no fall-through
                    unreachable = true;
                }
                "if_statement" => {
                    if unreachable {
                        continue;
                    }
                    last_block = self.process_if_cfg(
                        child,
                        source,
                        blocks,
                        edges,
                        block_id,
                        last_block,
                        exits,
                        loop_headers,
                        loop_exits,
                        label_blocks,
                        pending_gotos,
                        decision_points,
                    );
                }
                "while_statement" => {
                    if unreachable {
                        continue;
                    }
                    last_block = self.process_while_cfg(
                        child,
                        source,
                        blocks,
                        edges,
                        block_id,
                        last_block,
                        exits,
                        loop_headers,
                        loop_exits,
                        label_blocks,
                        pending_gotos,
                        decision_points,
                    );
                }
                "for_statement" => {
                    if unreachable {
                        continue;
                    }
                    last_block = self.process_for_cfg(
                        child,
                        source,
                        blocks,
                        edges,
                        block_id,
                        last_block,
                        exits,
                        loop_headers,
                        loop_exits,
                        label_blocks,
                        pending_gotos,
                        decision_points,
                    );
                }
                "do_statement" => {
                    if unreachable {
                        continue;
                    }
                    last_block = self.process_do_while_cfg(
                        child,
                        source,
                        blocks,
                        edges,
                        block_id,
                        last_block,
                        exits,
                        loop_headers,
                        loop_exits,
                        label_blocks,
                        pending_gotos,
                        decision_points,
                    );
                }
                "switch_statement" => {
                    if unreachable {
                        continue;
                    }
                    last_block = self.process_switch_cfg(
                        child,
                        source,
                        blocks,
                        edges,
                        block_id,
                        last_block,
                        exits,
                        loop_headers,
                        loop_exits,
                        label_blocks,
                        pending_gotos,
                        decision_points,
                    );
                }
                "break_statement" => {
                    if unreachable {
                        continue;
                    }
                    if let Some(&exit_block) = loop_exits.last() {
                        edges.push(CFGEdge::from_label(
                            last_block,
                            exit_block,
                            Some("break".to_string()),
                        ));
                    }
                    unreachable = true;
                }
                "continue_statement" => {
                    if unreachable {
                        continue;
                    }
                    if let Some(&header) = loop_headers.last() {
                        edges.push(CFGEdge::from_label(
                            last_block,
                            header,
                            Some("continue".to_string()),
                        ));
                    }
                    unreachable = true;
                }
                "compound_statement" => {
                    // Process compound statements even if unreachable (for labels inside)
                    last_block = self.process_cfg_block(
                        child,
                        source,
                        blocks,
                        edges,
                        block_id,
                        last_block,
                        exits,
                        loop_headers,
                        loop_exits,
                        label_blocks,
                        pending_gotos,
                        decision_points,
                    );
                }
                // Regular statements
                "declaration" | "expression_statement" => {
                    if unreachable {
                        continue;
                    }
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

    /// Process a single statement for CFG (used by labeled_statement).
    ///
    /// This handles the statement that follows a label, which could be any
    /// statement type including control flow statements.
    #[allow(clippy::too_many_arguments)]
    fn process_cfg_statement(
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
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
        unreachable: &mut bool,
        decision_points: &mut usize,
    ) -> BlockId {
        match node.kind() {
            "compound_statement" => self.process_cfg_block(
                node,
                source,
                blocks,
                edges,
                block_id,
                current_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            ),
            "if_statement" => self.process_if_cfg(
                node,
                source,
                blocks,
                edges,
                block_id,
                current_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            ),
            "while_statement" => self.process_while_cfg(
                node,
                source,
                blocks,
                edges,
                block_id,
                current_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            ),
            "for_statement" => self.process_for_cfg(
                node,
                source,
                blocks,
                edges,
                block_id,
                current_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            ),
            "do_statement" => self.process_do_while_cfg(
                node,
                source,
                blocks,
                edges,
                block_id,
                current_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            ),
            "switch_statement" => self.process_switch_cfg(
                node,
                source,
                blocks,
                edges,
                block_id,
                current_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            ),
            "goto_statement" => {
                let target_label = self
                    .child_by_field(node, "label")
                    .map(|n| self.node_text(n, source))
                    .unwrap_or_else(|| "unknown_label".to_string());

                if let Some(block) = blocks.get_mut(&current_block) {
                    let stmt = self.node_text(node, source);
                    block.statements.push(stmt);
                    block.end_line = node.end_position().row + 1;
                }

                if let Some(&target_block) = label_blocks.get(&target_label) {
                    edges.push(CFGEdge::from_label(
                        current_block,
                        target_block,
                        Some(format!("goto {}", target_label)),
                    ));
                } else {
                    pending_gotos.push((current_block, target_label));
                }

                *unreachable = true;
                current_block
            }
            "return_statement" => {
                *block_id += 1;
                let ret_block = BlockId(*block_id);
                let stmt = self.node_text(node, source);

                blocks.insert(
                    ret_block,
                    CFGBlock {
                        id: ret_block,
                        label: "return".to_string(),
                        block_type: BlockType::Body,
                        statements: vec![stmt],
                        func_calls: Vec::new(),
                        start_line: node.start_position().row + 1,
                        end_line: node.end_position().row + 1,
                    },
                );

                edges.push(CFGEdge::from_label(current_block, ret_block, None));

                exits.push(ret_block);
                *unreachable = true;
                ret_block
            }
            "break_statement" => {
                if let Some(&exit_block) = loop_exits.last() {
                    edges.push(CFGEdge::from_label(
                        current_block,
                        exit_block,
                        Some("break".to_string()),
                    ));
                }
                *unreachable = true;
                current_block
            }
            "continue_statement" => {
                if let Some(&header) = loop_headers.last() {
                    edges.push(CFGEdge::from_label(
                        current_block,
                        header,
                        Some("continue".to_string()),
                    ));
                }
                *unreachable = true;
                current_block
            }
            _ => {
                // Regular statement - add to current block
                if let Some(block) = blocks.get_mut(&current_block) {
                    let stmt = self.node_text(node, source);
                    block.statements.push(stmt);
                    block.end_line = node.end_position().row + 1;
                }
                current_block
            }
        }
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
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
        decision_points: &mut usize,
    ) -> BlockId {
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
                label: format!("if {}", condition),
                block_type: BlockType::Branch,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(current_block, cond_block, None));

        // Merge block after if
        *block_id += 1;
        let merge_block = BlockId(*block_id);
        blocks.insert(
            merge_block,
            CFGBlock {
                id: merge_block,
                label: "endif".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        // True branch (consequence)
        if let Some(consequence) = self.child_by_field(node, "consequence") {
            *block_id += 1;
            let true_block = BlockId(*block_id);
            blocks.insert(
                true_block,
                CFGBlock {
                    id: true_block,
                    label: "then".to_string(),
                    block_type: BlockType::Body,
                    statements: Vec::new(),
                    func_calls: Vec::new(),
                    start_line: consequence.start_position().row + 1,
                    end_line: consequence.end_position().row + 1,
                },
            );

            edges.push(CFGEdge::from_label(
                cond_block,
                true_block,
                Some("true".to_string()),
            ));

            let true_end = self.process_cfg_block(
                consequence,
                source,
                blocks,
                edges,
                block_id,
                true_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            );

            if !exits.contains(&true_end) {
                edges.push(CFGEdge::from_label(true_end, merge_block, None));
            }
        }

        // False branch (alternative)
        if let Some(alternative) = self.child_by_field(node, "alternative") {
            *block_id += 1;
            let false_block = BlockId(*block_id);
            blocks.insert(
                false_block,
                CFGBlock {
                    id: false_block,
                    label: "else".to_string(),
                    block_type: BlockType::Body,
                    statements: Vec::new(),
                    func_calls: Vec::new(),
                    start_line: alternative.start_position().row + 1,
                    end_line: alternative.end_position().row + 1,
                },
            );

            edges.push(CFGEdge::from_label(
                cond_block,
                false_block,
                Some("false".to_string()),
            ));

            let false_end = self.process_cfg_block(
                alternative,
                source,
                blocks,
                edges,
                block_id,
                false_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            );

            if !exits.contains(&false_end) {
                edges.push(CFGEdge::from_label(false_end, merge_block, None));
            }
        } else {
            // No else branch
            edges.push(CFGEdge::from_label(
                cond_block,
                merge_block,
                Some("false".to_string()),
            ));
        }

        merge_block
    }

    /// Process while statement for CFG.
    #[allow(clippy::too_many_arguments)]
    fn process_while_cfg(
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
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
        decision_points: &mut usize,
    ) -> BlockId {
        *block_id += 1;
        let header_block = BlockId(*block_id);
        let condition = self
            .child_by_field(node, "condition")
            .map(|n| self.node_text(n, source))
            .unwrap_or_else(|| "condition".to_string());

        blocks.insert(
            header_block,
            CFGBlock {
                id: header_block,
                label: format!("while {}", condition),
                block_type: BlockType::Body,
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
                label: "endwhile".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        loop_headers.push(header_block);
        loop_exits.push(exit_block);

        // Body
        if let Some(body) = self.child_by_field(node, "body") {
            *block_id += 1;
            let body_block = BlockId(*block_id);
            blocks.insert(
                body_block,
                CFGBlock {
                    id: body_block,
                    label: "loop_body".to_string(),
                    block_type: BlockType::Body,
                    statements: Vec::new(),
                    func_calls: Vec::new(),
                    start_line: body.start_position().row + 1,
                    end_line: body.end_position().row + 1,
                },
            );

            edges.push(CFGEdge::from_label(
                header_block,
                body_block,
                Some("true".to_string()),
            ));

            let body_end = self.process_cfg_block(
                body,
                source,
                blocks,
                edges,
                block_id,
                body_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            );

            if !exits.contains(&body_end) {
                edges.push(CFGEdge::from_label(
                    body_end,
                    header_block,
                    Some("back_edge".to_string()),
                ));
            }
        }

        edges.push(CFGEdge::from_label(
            header_block,
            exit_block,
            Some("false".to_string()),
        ));

        loop_headers.pop();
        loop_exits.pop();

        exit_block
    }

    /// Process for statement for CFG.
    #[allow(clippy::too_many_arguments)]
    fn process_for_cfg(
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
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
        decision_points: &mut usize,
    ) -> BlockId {
        // For loop: for (init; cond; update) body
        *block_id += 1;
        let header_block = BlockId(*block_id);
        let header_text = self
            .node_text(node, source)
            .lines()
            .next()
            .unwrap_or("for")
            .to_string();

        blocks.insert(
            header_block,
            CFGBlock {
                id: header_block,
                label: header_text,
                block_type: BlockType::Body,
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
                label: "endfor".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        loop_headers.push(header_block);
        loop_exits.push(exit_block);

        // Process body - handles both compound_statement (braces) and single statements
        if let Some(body) = self.child_by_field(node, "body") {
            *block_id += 1;
            let body_block = BlockId(*block_id);
            blocks.insert(
                body_block,
                CFGBlock {
                    id: body_block,
                    label: "loop_body".to_string(),
                    block_type: BlockType::Body,
                    statements: Vec::new(),
                    func_calls: Vec::new(),
                    start_line: body.start_position().row + 1,
                    end_line: body.end_position().row + 1,
                },
            );

            edges.push(CFGEdge::from_label(
                header_block,
                body_block,
                Some("iterate".to_string()),
            ));

            let body_end = self.process_cfg_block(
                body,
                source,
                blocks,
                edges,
                block_id,
                body_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            );

            if !exits.contains(&body_end) {
                edges.push(CFGEdge::from_label(
                    body_end,
                    header_block,
                    Some("back_edge".to_string()),
                ));
            }
        }

        edges.push(CFGEdge::from_label(
            header_block,
            exit_block,
            Some("done".to_string()),
        ));

        loop_headers.pop();
        loop_exits.pop();

        exit_block
    }

    /// Process do-while statement for CFG.
    #[allow(clippy::too_many_arguments)]
    fn process_do_while_cfg(
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
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
        decision_points: &mut usize,
    ) -> BlockId {
        // Body block (executes at least once)
        *block_id += 1;
        let body_block = BlockId(*block_id);
        blocks.insert(
            body_block,
            CFGBlock {
                id: body_block,
                label: "do".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(current_block, body_block, None));

        // Condition block (at the end)
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
                label: format!("while {}", condition),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row,
                end_line: node.end_position().row + 1,
            },
        );

        // Exit block
        *block_id += 1;
        let exit_block = BlockId(*block_id);
        blocks.insert(
            exit_block,
            CFGBlock {
                id: exit_block,
                label: "enddo".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        loop_headers.push(cond_block);
        loop_exits.push(exit_block);

        // Process body
        if let Some(body) = self.child_by_field(node, "body") {
            let body_end = self.process_cfg_block(
                body,
                source,
                blocks,
                edges,
                block_id,
                body_block,
                exits,
                loop_headers,
                loop_exits,
                label_blocks,
                pending_gotos,
                decision_points,
            );

            if !exits.contains(&body_end) {
                edges.push(CFGEdge::from_label(body_end, cond_block, None));
            }
        }

        // Condition edges
        edges.push(CFGEdge::from_label(
            cond_block,
            body_block,
            Some("true".to_string()),
        ));
        edges.push(CFGEdge::from_label(
            cond_block,
            exit_block,
            Some("false".to_string()),
        ));

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
        label_blocks: &mut FxHashMap<String, BlockId>,
        pending_gotos: &mut Vec<(BlockId, String)>,
        decision_points: &mut usize,
    ) -> BlockId {
        *block_id += 1;
        let switch_block = BlockId(*block_id);
        let expr = self
            .child_by_field(node, "condition")
            .map(|n| self.node_text(n, source))
            .unwrap_or_else(|| "expr".to_string());

        blocks.insert(
            switch_block,
            CFGBlock {
                id: switch_block,
                label: format!("switch {}", expr),
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
                label: "endswitch".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        // Push exit for break statements
        loop_exits.push(exit_block);

        // Find body and process cases
        if let Some(body) = self.child_by_field(node, "body") {
            let mut cursor = body.walk();
            for child in body.children(&mut cursor) {
                if child.kind() == "case_statement" {
                    *block_id += 1;
                    let case_block = BlockId(*block_id);
                    let case_label = self
                        .node_text(child, source)
                        .lines()
                        .next()
                        .unwrap_or("case")
                        .to_string();

                    blocks.insert(
                        case_block,
                        CFGBlock {
                            id: case_block,
                            label: case_label,
                            block_type: BlockType::Body,
                            statements: Vec::new(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(switch_block, case_block, None));

                    let case_end = self.process_cfg_block(
                        child,
                        source,
                        blocks,
                        edges,
                        block_id,
                        case_block,
                        exits,
                        loop_headers,
                        loop_exits,
                        label_blocks,
                        pending_gotos,
                        decision_points,
                    );

                    if !exits.contains(&case_end) {
                        edges.push(CFGEdge::from_label(case_end, exit_block, None));
                    }
                }
            }
        }

        loop_exits.pop();

        exit_block
    }

    // =========================================================================
    // DFG (Data Flow Graph) construction
    // =========================================================================

    /// Build DFG for a C function.
    fn build_c_dfg(&self, node: Node, source: &[u8], func_name: &str) -> DFGInfo {
        let mut edges = Vec::new();
        let mut definitions: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        let mut uses: FxHashMap<String, Vec<usize>> = FxHashMap::default();

        if let Some(declarator) = self.child_by_field(node, "declarator") {
            if let Some(params) = self.child_by_field(declarator, "parameters") {
                let mut cursor = params.walk();
                for child in params.children(&mut cursor) {
                    if child.kind() == "parameter_declaration" {
                        let line = child.start_position().row + 1;
                        self.dfg_extract_param(
                            child, source, line, &mut edges, &mut definitions,
                        );
                    }
                }
            }
        }

        if let Some(body) = self.child_by_field(node, "body") {
            self.dfg_process_block(body, source, &mut edges, &mut definitions, &mut uses);
        }

        DFGInfo::new(
            func_name.to_string(),
            edges,
            definitions.into_iter().collect(),
            uses.into_iter().collect(),
        )
    }

    fn dfg_extract_param(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
    ) {
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
                    let (name, _) = self.extract_pointer_declarator(child, source);
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
                "array_declarator" => {
                    let (name, _) = self.extract_array_declarator(child, source);
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
                _ => {}
            }
        }
    }

    /// Recursively process a block for DFG, including control flow conditions.
    fn dfg_process_block(
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
                    self.dfg_process_declaration(child, source, line, edges, definitions, uses);
                }
                "expression_statement" => {
                    self.dfg_process_expr_stmt(child, source, line, edges, definitions, uses);
                }
                "return_statement" => {
                    self.dfg_process_return(child, source, line, edges, definitions, uses);
                }
                "if_statement" => {
                    if let Some(cond) = self.child_by_field(child, "condition") {
                        self.dfg_collect_uses(cond, source, line, edges, definitions, uses);
                    }
                    if let Some(consequence) = self.child_by_field(child, "consequence") {
                        self.dfg_process_block(consequence, source, edges, definitions, uses);
                    }
                    if let Some(alternative) = self.child_by_field(child, "alternative") {
                        self.dfg_process_block(alternative, source, edges, definitions, uses);
                    }
                }
                "while_statement" | "do_statement" => {
                    if let Some(cond) = self.child_by_field(child, "condition") {
                        let cond_line = cond.start_position().row + 1;
                        self.dfg_collect_uses(cond, source, cond_line, edges, definitions, uses);
                    }
                    if let Some(body) = self.child_by_field(child, "body") {
                        self.dfg_process_block(body, source, edges, definitions, uses);
                    }
                }
                "for_statement" => {
                    if let Some(init) = self.child_by_field(child, "initializer") {
                        let il = init.start_position().row + 1;
                        if init.kind() == "declaration" {
                            self.dfg_process_declaration(init, source, il, edges, definitions, uses);
                        } else {
                            self.dfg_process_top_expr(init, source, il, edges, definitions, uses);
                        }
                    }
                    if let Some(cond) = self.child_by_field(child, "condition") {
                        let cl = cond.start_position().row + 1;
                        self.dfg_collect_uses(cond, source, cl, edges, definitions, uses);
                    }
                    if let Some(update) = self.child_by_field(child, "update") {
                        let ul = update.start_position().row + 1;
                        self.dfg_process_top_expr(update, source, ul, edges, definitions, uses);
                    }
                    if let Some(body) = self.child_by_field(child, "body") {
                        self.dfg_process_block(body, source, edges, definitions, uses);
                    }
                }
                "switch_statement" => {
                    if let Some(cond) = self.child_by_field(child, "condition") {
                        self.dfg_collect_uses(cond, source, line, edges, definitions, uses);
                    }
                    if let Some(body) = self.child_by_field(child, "body") {
                        self.dfg_process_block(body, source, edges, definitions, uses);
                    }
                }
                "compound_statement" | "case_statement" | "labeled_statement" => {
                    self.dfg_process_block(child, source, edges, definitions, uses);
                }
                _ => {}
            }
        }
    }

    fn dfg_process_declaration(
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
                    if let Some(declarator) = self.child_by_field(child, "declarator") {
                        if let Some(name) = self.dfg_lvalue_name(declarator, source) {
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
                        self.dfg_collect_uses(value, source, line, edges, definitions, uses);
                    }
                }
                "identifier" | "pointer_declarator" | "array_declarator" => {
                    if let Some(name) = self.dfg_lvalue_name(child, source) {
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

    fn dfg_process_expr_stmt(
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
                self.dfg_process_top_expr(child, source, line, edges, definitions, uses);
            }
        }
    }

    /// Process a top-level expression: assignments, compound assignments,
    /// updates, calls, and comma expressions.
    fn dfg_process_top_expr(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "assignment_expression" => {
                if let Some(right) = self.child_by_field(node, "right") {
                    self.dfg_collect_uses(right, source, line, edges, definitions, uses);
                }
                if let Some(left) = self.child_by_field(node, "left") {
                    self.dfg_process_lvalue_mutation(left, source, line, edges, definitions, uses);
                }
            }
            "compound_assignment_expr" => {
                // x += expr: x is both used and mutated
                if let Some(right) = self.child_by_field(node, "right") {
                    self.dfg_collect_uses(right, source, line, edges, definitions, uses);
                }
                if let Some(left) = self.child_by_field(node, "left") {
                    self.dfg_collect_uses(left, source, line, edges, definitions, uses);
                    self.dfg_process_lvalue_mutation(left, source, line, edges, definitions, uses);
                }
            }
            "update_expression" => {
                // x++ / ++x: use + mutation
                if let Some(arg) = self.child_by_field(node, "argument") {
                    self.dfg_collect_uses(arg, source, line, edges, definitions, uses);
                    self.dfg_process_lvalue_mutation(arg, source, line, edges, definitions, uses);
                }
            }
            "comma_expression" => {
                if let Some(left) = self.child_by_field(node, "left") {
                    self.dfg_process_top_expr(left, source, line, edges, definitions, uses);
                }
                if let Some(right) = self.child_by_field(node, "right") {
                    self.dfg_process_top_expr(right, source, line, edges, definitions, uses);
                }
            }
            _ => {
                self.dfg_collect_uses(node, source, line, edges, definitions, uses);
            }
        }
    }

    /// Process an lvalue mutation target.
    fn dfg_process_lvalue_mutation(
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
                // *p = x: p is used, (*p) is mutated
                if let Some(arg) = self.child_by_field(node, "argument") {
                    self.dfg_collect_uses(arg, source, line, edges, definitions, uses);
                    if let Some(base) = self.dfg_lvalue_name(arg, source) {
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
                if let Some(name) = self.dfg_field_expr_name(node, source) {
                    definitions.entry(name.clone()).or_default().push(line);
                    edges.push(DataflowEdge {
                        variable: name,
                        from_line: line,
                        to_line: line,
                        kind: DataflowKind::Mutation,
                    });
                }
                if let Some(arg) = self.child_by_field(node, "argument") {
                    if let Some(base) = self.dfg_lvalue_name(arg, source) {
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
                    if let Some(base) = self.dfg_lvalue_name(arg, source) {
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
                    self.dfg_collect_uses(idx, source, line, edges, definitions, uses);
                }
            }
            "parenthesized_expression" => {
                let mut inner_cursor = node.walk();
                for child in node.children(&mut inner_cursor) {
                    if child.is_named() {
                        self.dfg_process_lvalue_mutation(child, source, line, edges, definitions, uses);
                        return;
                    }
                }
            }
            _ => {
                if let Some(name) = self.dfg_lvalue_name(node, source) {
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

    /// Extract the name of an lvalue target for DFG tracking.
    fn dfg_lvalue_name(&self, node: Node, source: &[u8]) -> Option<String> {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node, source);
                if name.is_empty() { None } else { Some(name) }
            }
            "pointer_declarator" => {
                let (name, _) = self.extract_pointer_declarator(node, source);
                if name.is_empty() { None } else { Some(name) }
            }
            "array_declarator" => {
                let (name, _) = self.extract_array_declarator(node, source);
                if name.is_empty() { None } else { Some(name) }
            }
            "field_expression" => self.dfg_field_expr_name(node, source),
            "subscript_expression" => {
                self.child_by_field(node, "argument")
                    .and_then(|arg| self.dfg_lvalue_name(arg, source))
            }
            "pointer_expression" => {
                self.child_by_field(node, "argument")
                    .and_then(|arg| self.dfg_lvalue_name(arg, source))
            }
            "parenthesized_expression" => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.is_named() {
                        return self.dfg_lvalue_name(child, source);
                    }
                }
                None
            }
            _ => self.extract_name_from_declarator(node, source),
        }
    }

    /// Build a dotted name for a field expression: `s.field` or `p->field`.
    fn dfg_field_expr_name(&self, node: Node, source: &[u8]) -> Option<String> {
        let arg = self.child_by_field(node, "argument")?;
        let field = self.child_by_field(node, "field")?;
        let base = self.dfg_lvalue_name(arg, source)?;
        let field_name = self.node_text(field, source);
        let op = self.dfg_field_operator(node, source);
        Some(format!("{}{}{}", base, op, field_name))
    }

    fn dfg_field_operator(&self, node: Node, source: &[u8]) -> &'static str {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if !child.is_named() {
                let text = self.get_text(child, source);
                if text == "->" {
                    return "->";
                }
            }
        }
        "."
    }

    fn dfg_process_return(
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
                self.dfg_collect_return_uses(child, source, line, edges, definitions, uses);
            }
        }
    }

    fn dfg_collect_return_uses(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "identifier" => {
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
                if let Some(name) = self.dfg_field_expr_name(node, source) {
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
                    self.dfg_collect_return_uses(arg, source, line, edges, definitions, uses);
                }
            }
            _ => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.is_named() {
                        self.dfg_collect_return_uses(child, source, line, edges, definitions, uses);
                    }
                }
            }
        }
    }

    /// Recursively collect variable uses from an expression for DFG.
    fn dfg_collect_uses(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "identifier" => {
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
                if let Some(name) = self.dfg_field_expr_name(node, source) {
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
                    self.dfg_collect_uses(arg, source, line, edges, definitions, uses);
                }
            }
            "pointer_expression" => {
                if let Some(arg) = self.child_by_field(node, "argument") {
                    self.dfg_collect_uses(arg, source, line, edges, definitions, uses);
                    if let Some(base) = self.dfg_lvalue_name(arg, source) {
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
                    self.dfg_collect_uses(arg, source, line, edges, definitions, uses);
                }
                if let Some(idx) = self.child_by_field(node, "index") {
                    self.dfg_collect_uses(idx, source, line, edges, definitions, uses);
                }
            }
            "sizeof_expression" => {}
            "cast_expression" => {
                if let Some(value) = self.child_by_field(node, "value") {
                    self.dfg_collect_uses(value, source, line, edges, definitions, uses);
                }
            }
            _ => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.is_named() {
                        self.dfg_collect_uses(child, source, line, edges, definitions, uses);
                    }
                }
            }
        }
    }
}

impl Language for C {
    fn name(&self) -> &'static str {
        "c"
    }

    fn extensions(&self) -> &[&'static str] {
        &[".c", ".h"]
    }

    fn parser(&self) -> Result<Parser> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_c::LANGUAGE.into())
            .map_err(|e| BrrrError::TreeSitter(e.to_string()))?;
        Ok(parser)
    }

    fn extract_function(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        match node.kind() {
            "function_definition" => {
                // func_definition has type, declarator, body
                let declarator = self.child_by_field(node, "declarator")?;
                let name = self.extract_function_name(declarator, source)?;

                // Check for K&R style parameters
                let is_knr = self.is_knr_style(node);

                // Extract parameters - handle K&R style differently
                let params = if is_knr {
                    // K&R style: parameter names are in parameter_list,
                    // types are in separate declarations
                    let knr_types = self.extract_knr_params(node, source);

                    // Get parameter names from the parameter_list
                    let param_names: Vec<String> = self
                        .child_by_field(declarator, "parameters")
                        .map(|p| {
                            let mut names = Vec::new();
                            let mut cursor = p.walk();
                            for child in p.children(&mut cursor) {
                                if child.kind() == "identifier" {
                                    names.push(self.node_text(child, source));
                                }
                            }
                            names
                        })
                        .unwrap_or_default();

                    // Merge names with their types
                    param_names
                        .into_iter()
                        .map(|name| {
                            if let Some(ty) = knr_types.get(&name) {
                                format!("{} {}", ty, name)
                            } else {
                                name
                            }
                        })
                        .collect()
                } else {
                    // Modern style: types and names together in parameter_list
                    self.child_by_field(declarator, "parameters")
                        .map(|p| self.extract_params(p, source))
                        .unwrap_or_default()
                };

                // Extract return type
                let return_type = self.extract_return_type(node, source);

                // Extract doc comment
                let docstring = self.get_doc_comment(node, source);

                // Build decorators list
                let mut decorators = Vec::new();

                // Mark K&R style functions
                if is_knr {
                    decorators.push("knr_style".to_string());
                }

                // Storage class specifiers
                if self.has_storage_class(node, source, "static") {
                    decorators.push("static".to_string());
                }
                if self.has_storage_class(node, source, "inline") {
                    decorators.push("inline".to_string());
                }
                if self.has_storage_class(node, source, "extern") {
                    decorators.push("extern".to_string());
                }

                // Extract __attribute__ decorators
                decorators.extend(self.extract_attributes(node, source));

                // Check for inline assembly in function body
                if let Some(body) = self.child_by_field(node, "body") {
                    if self.contains_inline_assembly(body) {
                        decorators.push("inline_assembly".to_string());
                    }
                }

                Some(FunctionInfo {
                    name,
                    params,
                    return_type,
                    docstring,
                    is_method: false,
                    is_async: false,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "c".to_string(),
                })
            }
            "declaration" => {
                // Function declaration (prototype): int foo(int x);
                // Or function pointer variable: void (*callback)(void);
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "function_declarator" {
                        // Check if this is a function pointer (has parenthesized_declarator)
                        if let Some(decl) = self.child_by_field(child, "declarator") {
                            if decl.kind() == "parenthesized_declarator" {
                                // This is a function pointer variable
                                return self.extract_function_pointer(node, source);
                            }
                        }

                        // Regular function declaration
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

                        // Extract __attribute__ decorators
                        decorators.extend(self.extract_attributes(node, source));

                        return Some(FunctionInfo {
                            name,
                            params,
                            return_type,
                            docstring,
                            is_method: false,
                            is_async: false,
                            decorators,
                            line_number: node.start_position().row + 1,
                            end_line_number: Some(node.end_position().row + 1),
                            language: "c".to_string(),
                        });
                    }
                    // Also handle pointer return type: int* foo()
                    if child.kind() == "pointer_declarator" {
                        let mut current = child;
                        while current.kind() == "pointer_declarator" {
                            if let Some(decl) = self.child_by_field(current, "declarator") {
                                current = decl;
                            } else {
                                let mut c = current.walk();
                                let mut found = false;
                                for ch in current.children(&mut c) {
                                    if ch.kind() != "*" {
                                        current = ch;
                                        found = true;
                                        break;
                                    }
                                }
                                if !found {
                                    break;
                                }
                            }
                        }

                        if current.kind() == "function_declarator" {
                            let name = self.extract_function_name(current, source)?;
                            let params = self
                                .child_by_field(current, "parameters")
                                .map(|p| self.extract_params(p, source))
                                .unwrap_or_default();
                            let return_type = self.extract_return_type(node, source);
                            let docstring = self.get_doc_comment(node, source);

                            let mut decorators = vec!["declaration".to_string()];
                            if self.has_storage_class(node, source, "static") {
                                decorators.push("static".to_string());
                            }

                            // Extract __attribute__ decorators
                            decorators.extend(self.extract_attributes(node, source));

                            return Some(FunctionInfo {
                                name,
                                params,
                                return_type,
                                docstring,
                                is_method: false,
                                is_async: false,
                                decorators,
                                line_number: node.start_position().row + 1,
                                end_line_number: Some(node.end_position().row + 1),
                                language: "c".to_string(),
                            });
                        }
                    }
                }
                // If not a function declaration, check for thread-local variable
                self.extract_thread_local_variable(node, source)
            }
            // Macro definitions
            "preproc_def" => self.extract_object_macro(node, source),
            "preproc_function_def" => self.extract_function_macro(node, source),
            // Function pointer typedef: typedef int (*fn_ptr)(int, int);
            "type_definition" => self.extract_function_pointer(node, source),
            // Static assertions (C11): _Static_assert or static_assert
            "expression_statement" => self.extract_static_assert(node, source),
            _ => None,
        }
    }

    fn extract_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        match node.kind() {
            "struct_specifier" => {
                // Struct definition: struct Name { ... } or anonymous struct { ... } var;
                let explicit_name = self
                    .child_by_field(node, "name")
                    .map(|n| self.node_text(n, source));

                // Determine name and whether this is anonymous
                let (name, is_anonymous) = match explicit_name {
                    Some(n) => (n, false),
                    None => {
                        // Anonymous struct - try to get name from declaration context
                        // e.g., `struct { int x; } my_var;` -> use "my_var"
                        let context_name = self.extract_name_from_declaration_parent(node, source);
                        match context_name {
                            Some(n) => (n, true),
                            None => ("<anonymous>".to_string(), true),
                        }
                    }
                };

                let docstring = self.get_doc_comment(node, source);

                // Extract fields including bitfield information
                let fields = self.extract_struct_fields(node, source);

                // Extract anonymous struct/union members
                let inner_classes = self.extract_anonymous_members_from_body(node, source, &name);

                // Extract __attribute__ decorators
                // Attributes may be on parent declaration node
                let mut decorators = Vec::new();
                if is_anonymous {
                    decorators.push("anonymous_struct".to_string());
                }
                if let Some(parent) = node.parent() {
                    if parent.kind() == "declaration" || parent.kind() == "type_definition" {
                        decorators.extend(self.extract_attributes(parent, source));
                    }
                }

                Some(ClassInfo {
                    name,
                    bases: Vec::new(),
                    docstring,
                    methods: Vec::new(),
                    fields,
                    inner_classes,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "c".to_string(),
                })
            }
            "type_definition" => {
                // typedef struct X X; or typedef struct { ... } Name;
                let mut struct_name = None;
                let mut typedef_name = None;
                let mut struct_node: Option<Node> = None;
                let mut cursor = node.walk();

                for child in node.children(&mut cursor) {
                    if child.kind() == "struct_specifier" || child.kind() == "union_specifier" {
                        struct_name = self
                            .child_by_field(child, "name")
                            .map(|n| self.node_text(n, source));
                        struct_node = Some(child);
                    } else if child.kind() == "type_identifier" {
                        typedef_name = Some(self.node_text(child, source));
                    }
                }

                // Check for alias before consuming the values
                let mut decorators = vec!["typedef".to_string()];
                if struct_name.is_some() && typedef_name.is_some() && struct_name != typedef_name {
                    decorators.push(format!(
                        "alias:{}",
                        struct_name.as_ref().unwrap_or(&String::new())
                    ));
                }

                // Extract __attribute__ decorators
                decorators.extend(self.extract_attributes(node, source));

                let name = typedef_name.or(struct_name)?;
                let docstring = self.get_doc_comment(node, source);

                // Extract fields from the embedded struct/union if present
                let fields = struct_node
                    .map(|s| self.extract_struct_fields(s, source))
                    .unwrap_or_default();

                // Extract inner classes from embedded struct/union
                let inner_classes = struct_node
                    .map(|s| self.extract_anonymous_members_from_body(s, source, &name))
                    .unwrap_or_default();

                Some(ClassInfo {
                    name,
                    bases: Vec::new(),
                    docstring,
                    methods: Vec::new(),
                    fields,
                    inner_classes,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "c".to_string(),
                })
            }
            "enum_specifier" => {
                // enum Name { ... } or anonymous enum { ... } var;
                let explicit_name = self
                    .child_by_field(node, "name")
                    .map(|n| self.node_text(n, source));

                // Determine name and whether this is anonymous
                let (name, is_anonymous) = match explicit_name {
                    Some(n) => (n, false),
                    None => {
                        // Anonymous enum - try to get name from declaration context
                        let context_name = self.extract_name_from_declaration_parent(node, source);
                        match context_name {
                            Some(n) => (n, true),
                            None => ("<anonymous>".to_string(), true),
                        }
                    }
                };

                let docstring = self.get_doc_comment(node, source);

                let mut decorators = vec!["enum".to_string()];
                if is_anonymous {
                    decorators.push("anonymous_enum".to_string());
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
                    language: "c".to_string(),
                })
            }
            "union_specifier" => {
                // union Name { ... } or anonymous union { ... } var;
                let explicit_name = self
                    .child_by_field(node, "name")
                    .map(|n| self.node_text(n, source));

                // Determine name and whether this is anonymous
                let (name, is_anonymous) = match explicit_name {
                    Some(n) => (n, false),
                    None => {
                        // Anonymous union - try to get name from declaration context
                        let context_name = self.extract_name_from_declaration_parent(node, source);
                        match context_name {
                            Some(n) => (n, true),
                            None => ("<anonymous>".to_string(), true),
                        }
                    }
                };

                let docstring = self.get_doc_comment(node, source);

                // Extract fields including bitfield information
                let fields = self.extract_struct_fields(node, source);

                // Extract anonymous struct/union members
                let inner_classes = self.extract_anonymous_members_from_body(node, source, &name);

                // Extract __attribute__ decorators
                // Attributes may be on parent declaration node
                let mut decorators = vec!["union".to_string()];
                if is_anonymous {
                    decorators.push("anonymous_union".to_string());
                }
                if let Some(parent) = node.parent() {
                    if parent.kind() == "declaration" || parent.kind() == "type_definition" {
                        decorators.extend(self.extract_attributes(parent, source));
                    }
                }

                Some(ClassInfo {
                    name,
                    bases: Vec::new(),
                    docstring,
                    methods: Vec::new(),
                    fields,
                    inner_classes,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "c".to_string(),
                })
            }
            // Preprocessor conditionals
            "preproc_ifdef" | "preproc_if" => self.extract_preproc_conditional(node, source),
            _ => None,
        }
    }

    fn extract_imports(&self, tree: &Tree, source: &[u8]) -> Vec<ImportInfo> {
        let mut imports = Vec::new();
        let root = tree.root_node();
        self.collect_includes_recursive(root, source, &mut imports);
        imports
    }

    fn function_query(&self) -> &'static str {
        r#"[
            (function_definition
                declarator: (function_declarator
                    declarator: (identifier) @name)) @function
            (function_definition
                declarator: (pointer_declarator
                    declarator: (function_declarator
                        declarator: (identifier) @name))) @function
            (declaration
                declarator: (function_declarator
                    declarator: (identifier) @name)) @function
            (preproc_def
                name: (identifier) @name) @function
            (preproc_function_def
                name: (identifier) @name) @function
            (type_definition
                declarator: (function_declarator
                    declarator: (parenthesized_declarator
                        (pointer_declarator
                            declarator: (type_identifier) @name)))) @function
            (declaration
                declarator: (function_declarator
                    declarator: (parenthesized_declarator
                        (pointer_declarator
                            declarator: (identifier) @name)))) @function
            (expression_statement
                (call_expression
                    function: (identifier) @name)) @function
            (declaration
                (storage_class_specifier)
                declarator: (init_declarator
                    declarator: (identifier) @name)) @function
        ]"#
    }

    fn class_query(&self) -> &'static str {
        r#"[
            (struct_specifier name: (type_identifier) @name) @struct
            (struct_specifier body: (field_declaration_list) @name) @struct
            (enum_specifier name: (type_identifier) @name) @enum
            (enum_specifier body: (enumerator_list) @name) @enum
            (union_specifier name: (type_identifier) @name) @union
            (union_specifier body: (field_declaration_list) @name) @union
            (type_definition declarator: (type_identifier) @name) @typedef
            (preproc_ifdef name: (identifier) @name) @preproc_ifdef
            (preproc_if condition: (_) @name) @preproc_if
        ]"#
    }

    fn call_query(&self) -> &'static str {
        r#"[
            ; Direct function call: foo()
            (call_expression function: (identifier) @callee) @call

            ; Member access call: obj->method() or obj.method()
            (call_expression
                function: (field_expression
                    field: (field_identifier) @callee)) @call

            ; Pointer dereference call: (*ptr)()
            (call_expression
                function: (parenthesized_expression
                    (pointer_expression) @callee)) @call

            ; Subscript call: callbacks[i]()
            (call_expression
                function: (subscript_expression) @callee) @call
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

        Ok(self.build_c_cfg(node, source, &func_name))
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

        Ok(self.build_c_dfg(node, source, &func_name))
    }

    /// Skip `.h` header files that contain C++ code.
    ///
    /// Many projects have mixed C/C++ headers. When the user specifies `--lang c`,
    /// we should not attempt to parse C++ headers with the C parser, as this would
    /// result in parse errors or incorrect extraction.
    ///
    /// This method checks `.h` files for C++ indicators and returns `true` if
    /// the file should be skipped (parsed with C++ parser instead).
    fn should_skip_file(&self, path: &Path, content: &[u8]) -> bool {
        // Only check .h files - .c files are always C
        if let Some(ext) = path.extension() {
            if ext == "h" {
                return is_cpp_header(content);
            }
        }
        false
    }
}

impl C {
    /// Recursively traverse AST to find all preproc_include nodes.
    /// This handles includes nested inside preprocessor conditionals:
    /// #ifdef, #ifndef, #if, #else, #elif blocks.
    fn collect_includes_recursive(&self, node: Node, source: &[u8], imports: &mut Vec<ImportInfo>) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "preproc_include" => {
                    if let Some(import) = self.extract_include(child, source) {
                        imports.push(import);
                    }
                }
                // Recurse into preprocessor conditional blocks
                "preproc_ifdef" | "preproc_ifndef" | "preproc_if" | "preproc_else"
                | "preproc_elif" => {
                    self.collect_includes_recursive(child, source, imports);
                }
                _ => {
                    // Also check other container nodes that might have includes
                    if child.child_count() > 0 {
                        self.collect_includes_recursive(child, source, imports);
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
                    // #include <stdio.h>
                    path = self.node_text(child, source);
                    // Remove < and >
                    path = path
                        .trim_start_matches('<')
                        .trim_end_matches('>')
                        .to_string();
                    is_system = true;
                }
                "string_literal" => {
                    // #include "myheader.h"
                    path = self.node_text(child, source);
                    // Remove quotes
                    path = path.trim_matches('"').to_string();
                    is_system = false;
                }
                _ => {}
            }
        }

        if path.is_empty() {
            return None;
        }

        let mut aliases = FxHashMap::default();
        if is_system {
            aliases.insert(path.clone(), "system".to_string());
        } else {
            aliases.insert(path.clone(), "local".to_string());
        }

        Some(ImportInfo {
            module: path,
            names: Vec::new(),
            aliases,
            is_from: false, // C doesn't have "from X import Y"
            level: 0,       // C doesn't have relative imports
            line_number: node.start_position().row + 1,
            visibility: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_c(source: &str) -> (Tree, Vec<u8>) {
        let c = C;
        let mut parser = c.parser().unwrap();
        let source_bytes = source.as_bytes().to_vec();
        let tree = parser.parse(&source_bytes, None).unwrap();
        (tree, source_bytes)
    }

    #[test]
    fn test_extract_simple_function() {
        let source = r#"
/* Adds two integers */
int add(int a, int b) {
    return a + b;
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let func = c.extract_function(child, &source_bytes);
                assert!(func.is_some());
                let func = func.unwrap();
                assert_eq!(func.name, "add");
                assert_eq!(func.params.len(), 2);
                assert!(func.params[0].contains("int"));
                assert!(func.params[0].contains("a"));
                assert_eq!(func.return_type, Some("int".to_string()));
                assert!(func.docstring.is_some());
                assert!(func.docstring.unwrap().contains("Adds two integers"));
                assert_eq!(func.language, "c");
                found = true;
            }
        }
        assert!(found, "Function definition not found");
    }

    #[test]
    fn test_extract_static_function() {
        let source = r#"
static int helper(void) {
    return 42;
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let func = c.extract_function(child, &source_bytes).unwrap();
                assert_eq!(func.name, "helper");
                assert!(func.decorators.contains(&"static".to_string()));
            }
        }
    }

    #[test]
    fn test_extract_pointer_return() {
        let source = r#"
int* create_array(size_t len) {
    return malloc(len * sizeof(int));
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let func = c.extract_function(child, &source_bytes).unwrap();
                assert_eq!(func.name, "create_array");
                assert_eq!(func.return_type, Some("int*".to_string()));
            }
        }
    }

    #[test]
    fn test_extract_struct() {
        let source = r#"
/* Person structure */
struct Person {
    char* name;
    int age;
};
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "struct_specifier" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "Person");
                assert_eq!(cls.language, "c");
                assert!(cls.docstring.is_some());
            }
        }
    }

    #[test]
    fn test_extract_typedef() {
        let source = r#"
typedef struct Node {
    int value;
    struct Node* next;
} Node;
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "type_definition" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "Node");
                assert!(cls.decorators.contains(&"typedef".to_string()));
            }
        }
    }

    #[test]
    fn test_extract_includes() {
        let source = r#"
#include <stdio.h>
#include <stdlib.h>
#include "myheader.h"
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let imports = c.extract_imports(&tree, &source_bytes);

        assert_eq!(imports.len(), 3);

        // System includes
        let stdio = imports.iter().find(|i| i.module == "stdio.h").unwrap();
        assert_eq!(stdio.aliases.get("stdio.h"), Some(&"system".to_string()));

        let stdlib = imports.iter().find(|i| i.module == "stdlib.h").unwrap();
        assert_eq!(stdlib.aliases.get("stdlib.h"), Some(&"system".to_string()));

        // Local include
        let myheader = imports.iter().find(|i| i.module == "myheader.h").unwrap();
        assert_eq!(
            myheader.aliases.get("myheader.h"),
            Some(&"local".to_string())
        );
    }

    #[test]
    fn test_extract_includes_in_conditionals() {
        // Test that includes nested inside preprocessor conditionals are found
        let source = r#"
#include <stdio.h>

#ifdef USE_FEATURE
#include "feature.h"
#endif

#ifndef HAVE_STDLIB
#include <stdlib.h>
#endif

#if defined(LINUX)
#include <unistd.h>
#else
#include <windows.h>
#endif

#ifdef NESTED
    #ifdef DEEP
    #include "deep.h"
    #endif
#endif
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let imports = c.extract_imports(&tree, &source_bytes);

        // Should find all 6 includes: stdio.h, feature.h, stdlib.h, unistd.h, windows.h, deep.h
        assert_eq!(imports.len(), 6);

        // Top-level include
        assert!(imports.iter().any(|i| i.module == "stdio.h"));

        // Include inside #ifdef
        assert!(imports.iter().any(|i| i.module == "feature.h"));

        // Include inside #ifndef
        assert!(imports.iter().any(|i| i.module == "stdlib.h"));

        // Includes inside #if/#else
        assert!(imports.iter().any(|i| i.module == "unistd.h"));
        assert!(imports.iter().any(|i| i.module == "windows.h"));

        // Deeply nested include
        assert!(imports.iter().any(|i| i.module == "deep.h"));
    }

    #[test]
    fn test_extract_function_declaration() {
        let source = r#"
int process(const char* data, size_t len);
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "declaration" {
                let func = c.extract_function(child, &source_bytes);
                if let Some(func) = func {
                    assert_eq!(func.name, "process");
                    assert!(func.decorators.contains(&"declaration".to_string()));
                    assert_eq!(func.params.len(), 2);
                }
            }
        }
    }

    #[test]
    fn test_function_signature() {
        let func = FunctionInfo {
            name: "process".to_string(),
            params: vec!["const char* data".to_string(), "size_t len".to_string()],
            return_type: Some("int*".to_string()),
            docstring: None,
            is_method: false,
            is_async: false,
            decorators: Vec::new(),
            line_number: 1,
            end_line_number: Some(5),
            language: "c".to_string(),
        };

        assert_eq!(
            func.signature(),
            "int* process(const char* data, size_t len)"
        );
    }

    #[test]
    fn test_extract_enum() {
        let source = r#"
enum Color {
    RED,
    GREEN,
    BLUE
};
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "enum_specifier" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "Color");
                assert!(cls.decorators.contains(&"enum".to_string()));
            }
        }
    }

    #[test]
    fn test_build_cfg() {
        let source = r#"
int factorial(int n) {
    if (n <= 1) {
        return 1;
    }
    return n * factorial(n - 1);
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let cfg = c.build_cfg(child, &source_bytes);
                assert!(cfg.is_ok());
                let cfg = cfg.unwrap();
                assert_eq!(cfg.function_name, "factorial");
                assert!(!cfg.blocks.is_empty());
                assert!(!cfg.edges.is_empty());
            }
        }
    }

    #[test]
    fn test_build_dfg() {
        let source = r#"
int sum(int a, int b) {
    int result = a + b;
    return result;
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let dfg = c.build_dfg(child, &source_bytes);
                assert!(dfg.is_ok());
                let dfg = dfg.unwrap();
                assert_eq!(dfg.function_name, "sum");
                // Should have definitions for a, b, result
                assert!(dfg.definitions.contains_key("a"));
                assert!(dfg.definitions.contains_key("b"));
                assert!(dfg.definitions.contains_key("result"));
            }
        }
    }

    #[test]
    fn test_extract_object_macro() {
        let source = r#"
/* Buffer size constant */
#define BUFFER_SIZE 1024
#define NULL_PTR ((void*)0)
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut macros = Vec::new();
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "preproc_def" {
                if let Some(func) = c.extract_function(child, &source_bytes) {
                    macros.push(func);
                }
            }
        }

        assert_eq!(macros.len(), 2);

        let buffer_size = macros.iter().find(|m| m.name == "BUFFER_SIZE").unwrap();
        assert!(buffer_size.decorators.contains(&"macro".to_string()));
        assert_eq!(buffer_size.return_type, Some("1024".to_string()));
        assert!(buffer_size.params.is_empty());
        assert!(buffer_size.docstring.is_some());

        let null_ptr = macros.iter().find(|m| m.name == "NULL_PTR").unwrap();
        assert!(null_ptr.decorators.contains(&"macro".to_string()));
        assert_eq!(null_ptr.return_type, Some("((void*)0)".to_string()));
    }

    #[test]
    fn test_extract_function_macro() {
        let source = r#"
/* Returns the maximum of two values */
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define SWAP(x, y, T) do { T tmp = x; x = y; y = tmp; } while(0)
#define DEBUG_LOG(fmt, ...) printf(fmt, __VA_ARGS__)
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut macros = Vec::new();
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "preproc_function_def" {
                if let Some(func) = c.extract_function(child, &source_bytes) {
                    macros.push(func);
                }
            }
        }

        assert_eq!(macros.len(), 3);

        let max_macro = macros.iter().find(|m| m.name == "MAX").unwrap();
        assert!(max_macro.decorators.contains(&"macro".to_string()));
        assert_eq!(max_macro.params, vec!["a", "b"]);
        assert!(max_macro.return_type.is_some());
        assert!(max_macro.docstring.is_some());

        let swap_macro = macros.iter().find(|m| m.name == "SWAP").unwrap();
        assert_eq!(swap_macro.params, vec!["x", "y", "T"]);

        let debug_macro = macros.iter().find(|m| m.name == "DEBUG_LOG").unwrap();
        assert_eq!(debug_macro.params, vec!["fmt", "..."]);
    }

    #[test]
    fn test_extract_function_pointer_typedef() {
        let source = r#"
/* Comparator function type */
typedef int (*comparator_fn)(const void*, const void*);
typedef void (*callback_t)(int status, void* data);
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut fn_ptrs = Vec::new();
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "type_definition" {
                if let Some(func) = c.extract_function(child, &source_bytes) {
                    fn_ptrs.push(func);
                }
            }
        }

        assert_eq!(fn_ptrs.len(), 2);

        let comparator = fn_ptrs.iter().find(|f| f.name == "comparator_fn").unwrap();
        assert!(comparator
            .decorators
            .contains(&"function_pointer".to_string()));
        assert!(comparator.decorators.contains(&"typedef".to_string()));
        assert_eq!(comparator.return_type, Some("int".to_string()));
        assert_eq!(comparator.params.len(), 2);
        // Verify unnamed pointer parameters preserve the * (abstract_pointer_declarator fix)
        assert_eq!(comparator.params[0], "const void*");
        assert_eq!(comparator.params[1], "const void*");
        assert!(comparator.docstring.is_some());

        let callback = fn_ptrs.iter().find(|f| f.name == "callback_t").unwrap();
        assert!(callback
            .decorators
            .contains(&"function_pointer".to_string()));
        assert_eq!(callback.return_type, Some("void".to_string()));
        // Verify mixed named and pointer parameters
        assert_eq!(callback.params.len(), 2);
        assert_eq!(callback.params[0], "int status");
        assert_eq!(callback.params[1], "void* data");
    }

    #[test]
    fn test_extract_function_pointer_variable() {
        let source = r#"
void (*signal_handler)(int);
int (*operation)(int, int);
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut fn_ptrs = Vec::new();
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "declaration" {
                if let Some(func) = c.extract_function(child, &source_bytes) {
                    if func.decorators.contains(&"function_pointer".to_string()) {
                        fn_ptrs.push(func);
                    }
                }
            }
        }

        assert_eq!(fn_ptrs.len(), 2);

        let signal_h = fn_ptrs.iter().find(|f| f.name == "signal_handler").unwrap();
        assert!(signal_h
            .decorators
            .contains(&"function_pointer".to_string()));
        assert!(!signal_h.decorators.contains(&"typedef".to_string()));
        assert_eq!(signal_h.return_type, Some("void".to_string()));
        assert_eq!(signal_h.params.len(), 1);

        let operation = fn_ptrs.iter().find(|f| f.name == "operation").unwrap();
        assert_eq!(operation.return_type, Some("int".to_string()));
        assert_eq!(operation.params.len(), 2);
    }

    #[test]
    fn test_abstract_pointer_multi_level() {
        // Test multi-level unnamed pointers (void**, char***, etc.)
        let source = r#"
typedef void (*double_ptr_fn)(void**, int**);
typedef int (*triple_ptr_fn)(char***, void****);
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut fn_ptrs = Vec::new();
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "type_definition" {
                if let Some(func) = c.extract_function(child, &source_bytes) {
                    fn_ptrs.push(func);
                }
            }
        }

        assert_eq!(fn_ptrs.len(), 2);

        let double_fn = fn_ptrs.iter().find(|f| f.name == "double_ptr_fn").unwrap();
        assert_eq!(double_fn.params[0], "void**");
        assert_eq!(double_fn.params[1], "int**");

        let triple_fn = fn_ptrs.iter().find(|f| f.name == "triple_ptr_fn").unwrap();
        assert_eq!(triple_fn.params[0], "char***");
        assert_eq!(triple_fn.params[1], "void****");
    }

    #[test]
    fn test_macro_signature() {
        let func = FunctionInfo {
            name: "MAX".to_string(),
            params: vec!["a".to_string(), "b".to_string()],
            return_type: Some("((a)>(b)?(a):(b))".to_string()),
            docstring: None,
            is_method: false,
            is_async: false,
            decorators: vec!["macro".to_string()],
            line_number: 1,
            end_line_number: Some(1),
            language: "c".to_string(),
        };

        // Signature should show the macro with params
        assert_eq!(func.signature(), "((a)>(b)?(a):(b)) MAX(a, b)");
    }

    #[test]
    fn test_function_pointer_signature() {
        let func = FunctionInfo {
            name: "comparator_fn".to_string(),
            params: vec!["const void*".to_string(), "const void*".to_string()],
            return_type: Some("int".to_string()),
            docstring: None,
            is_method: false,
            is_async: false,
            decorators: vec!["function_pointer".to_string(), "typedef".to_string()],
            line_number: 1,
            end_line_number: Some(1),
            language: "c".to_string(),
        };

        assert_eq!(
            func.signature(),
            "int comparator_fn(const void*, const void*)"
        );
    }

    #[test]
    fn test_extract_preproc_ifdef() {
        let source = r#"
#ifdef DEBUG
int debug_mode = 1;
#endif
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "preproc_ifdef" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "DEBUG");
                assert!(cls.decorators.contains(&"preproc_ifdef".to_string()));
                assert_eq!(cls.language, "c");
                found = true;
            }
        }
        assert!(found, "preproc_ifdef not found");
    }

    #[test]
    fn test_extract_preproc_ifndef() {
        let source = r#"
#ifndef HEADER_H
#define HEADER_H
int value;
#endif
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "preproc_ifdef" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "HEADER_H");
                assert!(cls.decorators.contains(&"preproc_ifndef".to_string()));
                found = true;
            }
        }
        assert!(found, "preproc_ifndef not found");
    }

    #[test]
    fn test_extract_preproc_if_elif_else() {
        let source = r#"
#if defined(FEATURE_A)
int feature_a = 1;
#elif defined(FEATURE_B)
int feature_b = 1;
#else
int default_feature = 1;
#endif
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "preproc_if" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert!(cls.name.contains("FEATURE_A"));
                assert!(cls.decorators.contains(&"preproc_if".to_string()));

                // Should have inner_classes for elif and else branches
                assert!(!cls.inner_classes.is_empty());

                // Find elif
                let elif = cls
                    .inner_classes
                    .iter()
                    .find(|c| c.decorators.contains(&"preproc_elif".to_string()));
                assert!(elif.is_some());
                let elif = elif.unwrap();
                assert!(elif.name.contains("FEATURE_B"));

                // Find else (nested in elif's inner_classes)
                let else_branch = elif
                    .inner_classes
                    .iter()
                    .find(|c| c.decorators.contains(&"preproc_else".to_string()));
                assert!(else_branch.is_some());

                found = true;
            }
        }
        assert!(found, "preproc_if not found");
    }

    #[test]
    fn test_extract_nested_preproc() {
        let source = r#"
#ifdef OUTER
    #ifdef INNER
    int nested = 1;
    #endif
#endif
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "preproc_ifdef" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "OUTER");

                // Should have nested preproc
                assert!(!cls.inner_classes.is_empty());
                let inner = &cls.inner_classes[0];
                assert_eq!(inner.name, "INNER");
                assert!(inner.decorators.contains(&"preproc_ifdef".to_string()));
            }
        }
    }

    #[test]
    fn test_extract_anonymous_struct() {
        let source = r#"
struct outer {
    int x;
    struct {
        int a, b;
    };
};
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "struct_specifier" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "outer");

                // Should have anonymous struct as inner class
                assert_eq!(cls.inner_classes.len(), 1);
                let anon = &cls.inner_classes[0];
                assert!(anon.name.contains("outer_anon_struct"));
                assert!(anon.decorators.contains(&"anonymous_struct".to_string()));
            }
        }
    }

    #[test]
    fn test_extract_anonymous_union() {
        let source = r#"
struct container {
    int type;
    union {
        float f;
        int i;
        char c;
    };
};
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "struct_specifier" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "container");

                // Should have anonymous union as inner class
                assert_eq!(cls.inner_classes.len(), 1);
                let anon = &cls.inner_classes[0];
                assert!(anon.name.contains("container_anon_union"));
                assert!(anon.decorators.contains(&"anonymous_union".to_string()));
            }
        }
    }

    #[test]
    fn test_extract_multiple_anonymous_members() {
        let source = r#"
struct mixed {
    int x;
    struct {
        int a, b;
    };
    union {
        float f;
        int i;
    };
};
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "struct_specifier" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "mixed");

                // Should have both anonymous struct and union
                assert_eq!(cls.inner_classes.len(), 2);

                let has_anon_struct = cls
                    .inner_classes
                    .iter()
                    .any(|c| c.decorators.contains(&"anonymous_struct".to_string()));
                let has_anon_union = cls
                    .inner_classes
                    .iter()
                    .any(|c| c.decorators.contains(&"anonymous_union".to_string()));

                assert!(has_anon_struct, "Missing anonymous struct");
                assert!(has_anon_union, "Missing anonymous union");
            }
        }
    }

    #[test]
    fn test_extract_nested_anonymous() {
        let source = r#"
struct outer {
    struct {
        union {
            int x;
            float y;
        };
    };
};
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "struct_specifier" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "outer");

                // Should have anonymous struct
                assert_eq!(cls.inner_classes.len(), 1);
                let anon_struct = &cls.inner_classes[0];
                assert!(anon_struct
                    .decorators
                    .contains(&"anonymous_struct".to_string()));

                // Anonymous struct should have nested anonymous union
                assert_eq!(anon_struct.inner_classes.len(), 1);
                let nested_union = &anon_struct.inner_classes[0];
                assert!(nested_union
                    .decorators
                    .contains(&"anonymous_union".to_string()));
            }
        }
    }

    #[test]
    fn test_union_with_anonymous_struct() {
        let source = r#"
union data {
    int raw;
    struct {
        char low;
        char high;
    };
};
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "union_specifier" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "data");
                assert!(cls.decorators.contains(&"union".to_string()));

                // Should have anonymous struct as inner class
                assert_eq!(cls.inner_classes.len(), 1);
                let anon = &cls.inner_classes[0];
                assert!(anon.decorators.contains(&"anonymous_struct".to_string()));
            }
        }
    }

    #[test]
    fn test_inline_assembly_detection() {
        let source = r#"
void enable_interrupts(void) {
    __asm__ volatile ("sti" : : : "memory");
}

void nop_function(void) {
    asm("nop");
}

int normal_function(int x) {
    return x + 1;
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut functions = Vec::new();
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                if let Some(func) = c.extract_function(child, &source_bytes) {
                    functions.push(func);
                }
            }
        }

        assert_eq!(functions.len(), 3);

        // enable_interrupts should have inline_assembly decorator
        let enable_ints = functions
            .iter()
            .find(|f| f.name == "enable_interrupts")
            .unwrap();
        assert!(
            enable_ints
                .decorators
                .contains(&"inline_assembly".to_string()),
            "enable_interrupts should have inline_assembly decorator"
        );

        // nop_function should have inline_assembly decorator
        let nop_fn = functions.iter().find(|f| f.name == "nop_function").unwrap();
        assert!(
            nop_fn.decorators.contains(&"inline_assembly".to_string()),
            "nop_function should have inline_assembly decorator"
        );

        // normal_function should NOT have inline_assembly decorator
        let normal_fn = functions
            .iter()
            .find(|f| f.name == "normal_function")
            .unwrap();
        assert!(
            !normal_fn
                .decorators
                .contains(&"inline_assembly".to_string()),
            "normal_function should NOT have inline_assembly decorator"
        );
    }

    #[test]
    fn test_static_assert_extraction() {
        let source = r#"
_Static_assert(sizeof(void*) == 8, "64-bit only");
_Static_assert(sizeof(int) == 4, "int must be 4 bytes");
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut assertions = Vec::new();
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "expression_statement" {
                if let Some(func) = c.extract_function(child, &source_bytes) {
                    assertions.push(func);
                }
            }
        }

        assert_eq!(assertions.len(), 2);

        // Check first static_assert
        let first = &assertions[0];
        assert!(first.decorators.contains(&"static_assert".to_string()));
        assert!(first.name.contains("static_assert"));
        assert!(first.name.contains("sizeof"));
        assert_eq!(first.docstring, Some("64-bit only".to_string()));

        // Check second static_assert
        let second = &assertions[1];
        assert!(second.decorators.contains(&"static_assert".to_string()));
        assert_eq!(second.docstring, Some("int must be 4 bytes".to_string()));
    }

    #[test]
    fn test_thread_local_storage() {
        let source = r#"
/* Thread-local counter */
__thread int thread_counter = 0;
static __thread int static_thread_local = 42;
extern __thread void* thread_data;
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut variables = Vec::new();
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "declaration" {
                if let Some(func) = c.extract_function(child, &source_bytes) {
                    variables.push(func);
                }
            }
        }

        // Should find 3 thread-local variables
        assert_eq!(variables.len(), 3);

        // Check thread_counter
        let counter = variables
            .iter()
            .find(|v| v.name == "thread_counter")
            .unwrap();
        assert!(counter.decorators.contains(&"thread_local".to_string()));
        assert!(counter.decorators.contains(&"variable".to_string()));
        assert_eq!(counter.return_type, Some("int".to_string()));
        assert!(counter.docstring.is_some());
        assert!(counter
            .docstring
            .as_ref()
            .unwrap()
            .contains("Thread-local counter"));

        // Check static_thread_local
        let static_tl = variables
            .iter()
            .find(|v| v.name == "static_thread_local")
            .unwrap();
        assert!(static_tl.decorators.contains(&"thread_local".to_string()));
        assert!(static_tl.decorators.contains(&"static".to_string()));
        assert_eq!(static_tl.return_type, Some("int".to_string()));

        // Check extern thread_data
        let extern_tl = variables.iter().find(|v| v.name == "thread_data").unwrap();
        assert!(extern_tl.decorators.contains(&"thread_local".to_string()));
        assert!(extern_tl.decorators.contains(&"extern".to_string()));
    }

    // ============= GOTO/LABEL CFG TESTS =============

    #[test]
    fn test_cfg_forward_goto() {
        // Test forward goto: goto appears before label
        let source = r#"
void test_forward_goto() {
    int x = 0;
    goto end;
    x = 1;
end:
    return;
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let cfg = c.build_c_cfg(child, &source_bytes, "test_forward_goto");

                // Verify we have blocks for: entry, goto block, end label block
                assert!(cfg.blocks.len() >= 3, "Should have at least 3 blocks");

                // Find the edge labeled "goto end"
                let goto_edge = cfg.edges.iter().find(|e| e.label().contains("goto end"));
                assert!(goto_edge.is_some(), "Should have a goto end edge");

                // Verify the end label block exists
                let end_block = cfg.blocks.values().find(|b| b.label.contains("end:"));
                assert!(end_block.is_some(), "Should have an 'end:' label block");
            }
        }
    }

    #[test]
    fn test_cfg_backward_goto() {
        // Test backward goto: label appears before goto (loop pattern)
        let source = r#"
void test_backward_goto() {
    int x = 0;
start:
    x++;
    if (x < 10)
        goto start;
    return;
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let cfg = c.build_c_cfg(child, &source_bytes, "test_backward_goto");

                // Find the start label block
                let start_block = cfg.blocks.values().find(|b| b.label.contains("start:"));
                assert!(start_block.is_some(), "Should have a 'start:' label block");

                // Find the edge labeled "goto start"
                let goto_edge = cfg.edges.iter().find(|e| e.label().contains("goto start"));
                assert!(goto_edge.is_some(), "Should have a goto start edge");

                // Verify the goto edge points to the start block
                if let (Some(start), Some(edge)) = (start_block, goto_edge) {
                    assert_eq!(
                        edge.to, start.id,
                        "Goto edge should point to start label block"
                    );
                }
            }
        }
    }

    #[test]
    fn test_cfg_multiple_gotos_same_label() {
        // Test multiple gotos targeting the same label
        let source = r#"
void test_multiple_gotos() {
    int x = 0;
    if (x == 0)
        goto end;
    if (x == 1)
        goto end;
    x = 2;
end:
    return;
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let cfg = c.build_c_cfg(child, &source_bytes, "test_multiple_gotos");

                // Find the end label block
                let end_block = cfg.blocks.values().find(|b| b.label.contains("end:"));
                assert!(end_block.is_some(), "Should have an 'end:' label block");

                // Count edges targeting the end label
                if let Some(end) = end_block {
                    let goto_edges_to_end: Vec<_> = cfg
                        .edges
                        .iter()
                        .filter(|e| e.to == end.id && e.label().contains("goto"))
                        .collect();

                    // Should have at least 2 goto edges to end (from the two if branches)
                    assert!(
                        goto_edges_to_end.len() >= 2,
                        "Should have at least 2 goto edges to end label, found {}",
                        goto_edges_to_end.len()
                    );
                }
            }
        }
    }

    #[test]
    fn test_cfg_goto_in_loop() {
        // Test goto used to break out of nested structure
        let source = r#"
void test_goto_in_loop() {
    for (int i = 0; i < 10; i++) {
        if (i == 5)
            goto done;
    }
done:
    return;
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let cfg = c.build_c_cfg(child, &source_bytes, "test_goto_in_loop");

                // Verify we have the done label block
                let done_block = cfg.blocks.values().find(|b| b.label.contains("done:"));
                assert!(done_block.is_some(), "Should have a 'done:' label block");

                // Verify we have a goto done edge
                let goto_edge = cfg.edges.iter().find(|e| e.label().contains("goto done"));
                assert!(goto_edge.is_some(), "Should have a goto done edge");
            }
        }
    }

    #[test]
    fn test_cfg_label_makes_code_reachable() {
        // Test that labels make code reachable even after goto
        let source = r#"
void test_reachability() {
    goto skip;
    int unreachable = 1;  // This should be skipped
skip:
    int reachable = 2;    // This should be in the CFG
    return;
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let cfg = c.build_c_cfg(child, &source_bytes, "test_reachability");

                // Find the skip label block
                let skip_block = cfg.blocks.values().find(|b| b.label.contains("skip:"));
                assert!(skip_block.is_some(), "Should have a 'skip:' label block");

                // The skip block or its successors should contain "reachable = 2"
                // or have an edge leading to it
                if let Some(skip) = skip_block {
                    // Verify there's a goto edge to skip
                    let goto_to_skip = cfg.edges.iter().any(|e| e.to == skip.id);
                    assert!(goto_to_skip, "Should have edge to skip label");
                }
            }
        }
    }

    #[test]
    fn test_cfg_multiple_labels() {
        // Test function with multiple labels
        let source = r#"
int test_state_machine(int state) {
    switch (state) {
        case 0: goto state_a;
        case 1: goto state_b;
        default: goto state_c;
    }
state_a:
    return 1;
state_b:
    return 2;
state_c:
    return 3;
}
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_definition" {
                let cfg = c.build_c_cfg(child, &source_bytes, "test_state_machine");

                // Verify all three state labels exist
                let state_a = cfg.blocks.values().find(|b| b.label.contains("state_a:"));
                let state_b = cfg.blocks.values().find(|b| b.label.contains("state_b:"));
                let state_c = cfg.blocks.values().find(|b| b.label.contains("state_c:"));

                assert!(state_a.is_some(), "Should have 'state_a:' label");
                assert!(state_b.is_some(), "Should have 'state_b:' label");
                assert!(state_c.is_some(), "Should have 'state_c:' label");

                // Verify goto edges exist for each state
                let has_goto_a = cfg.edges.iter().any(|e| e.label().contains("goto state_a"));
                let has_goto_b = cfg.edges.iter().any(|e| e.label().contains("goto state_b"));
                let has_goto_c = cfg.edges.iter().any(|e| e.label().contains("goto state_c"));

                assert!(has_goto_a, "Should have goto state_a edge");
                assert!(has_goto_b, "Should have goto state_b edge");
                assert!(has_goto_c, "Should have goto state_c edge");
            }
        }
    }

    // ============= ANONYMOUS STRUCT/UNION/ENUM TESTS =============

    #[test]
    fn test_extract_toplevel_anonymous_struct() {
        // Test anonymous struct with variable name extracted from declaration
        let source = r#"
struct { int x; int y; } global_point;
struct { float real; float imag; } *complex_ptr;
struct { char name[32]; int age; } person_arr[10];
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut structs = Vec::new();
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "declaration" {
                // Look for struct_specifier inside declaration
                let mut inner_cursor = child.walk();
                for inner in child.children(&mut inner_cursor) {
                    if inner.kind() == "struct_specifier" {
                        if let Some(cls) = c.extract_class(inner, &source_bytes) {
                            structs.push(cls);
                        }
                    }
                }
            }
        }

        // Should extract all 3 anonymous structs
        assert_eq!(structs.len(), 3, "Should find 3 anonymous structs");

        // Check global_point
        let point = structs.iter().find(|s| s.name == "global_point");
        assert!(point.is_some(), "Should extract global_point");
        let point = point.unwrap();
        assert!(point.decorators.contains(&"anonymous_struct".to_string()));
        assert_eq!(point.fields.len(), 2);

        // Check complex_ptr
        let complex = structs.iter().find(|s| s.name == "complex_ptr");
        assert!(complex.is_some(), "Should extract complex_ptr");
        assert!(complex
            .unwrap()
            .decorators
            .contains(&"anonymous_struct".to_string()));

        // Check person_arr
        let person = structs.iter().find(|s| s.name == "person_arr");
        assert!(person.is_some(), "Should extract person_arr");
        assert!(person
            .unwrap()
            .decorators
            .contains(&"anonymous_struct".to_string()));
    }

    #[test]
    fn test_extract_toplevel_anonymous_union() {
        let source = r#"
union { int i; float f; } data_union;
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "declaration" {
                let mut inner_cursor = child.walk();
                for inner in child.children(&mut inner_cursor) {
                    if inner.kind() == "union_specifier" {
                        let cls = c.extract_class(inner, &source_bytes);
                        assert!(cls.is_some(), "Should extract anonymous union");
                        let cls = cls.unwrap();
                        assert_eq!(cls.name, "data_union");
                        assert!(cls.decorators.contains(&"union".to_string()));
                        assert!(cls.decorators.contains(&"anonymous_union".to_string()));
                        return;
                    }
                }
            }
        }
        panic!("Anonymous union not found");
    }

    #[test]
    fn test_extract_toplevel_anonymous_enum() {
        let source = r#"
enum { RED, GREEN, BLUE } color_var;
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "declaration" {
                let mut inner_cursor = child.walk();
                for inner in child.children(&mut inner_cursor) {
                    if inner.kind() == "enum_specifier" {
                        let cls = c.extract_class(inner, &source_bytes);
                        assert!(cls.is_some(), "Should extract anonymous enum");
                        let cls = cls.unwrap();
                        assert_eq!(cls.name, "color_var");
                        assert!(cls.decorators.contains(&"enum".to_string()));
                        assert!(cls.decorators.contains(&"anonymous_enum".to_string()));
                        return;
                    }
                }
            }
        }
        panic!("Anonymous enum not found");
    }

    // ==========================================================================
    // C++ HEADER DETECTION TESTS
    // ==========================================================================

    #[test]
    fn test_is_cpp_header_detects_templates() {
        let content = b"template<typename T>\nclass Container {};";
        assert!(is_cpp_header(content));

        let content = b"template <typename T>\nclass Container {};";
        assert!(is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_detects_namespace() {
        let content = b"namespace fast_float {\n  int x;\n}";
        assert!(is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_detects_class_definition() {
        let content = b"class Foo : public Bar {\n  int x;\n};";
        assert!(is_cpp_header(content));

        let content = b"class Foo {\npublic:\n  int x;\n};";
        assert!(is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_ignores_class_in_comment() {
        // This tests the fix for false positives from comment prose
        let content = b"/* Keyspace changes notification classes. Every class is associated */";
        assert!(!is_cpp_header(content));

        let content = b"/* Key metadata class configuration structure. */";
        assert!(!is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_detects_constexpr() {
        let content = b"constexpr int MAX_SIZE = 100;";
        assert!(is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_detects_nullptr() {
        let content = b"int* ptr = nullptr;";
        assert!(is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_detects_noexcept() {
        let content = b"void func() noexcept;";
        assert!(is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_detects_static_cast() {
        let content = b"auto x = static_cast<int>(y);";
        assert!(is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_detects_access_specifiers() {
        let content = b"public:\n  int x;";
        assert!(is_cpp_header(content));

        let content = b"private:\n  int _y;";
        assert!(is_cpp_header(content));

        let content = b"protected:\n  int z;";
        assert!(is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_pure_c_code() {
        // Pure C code should NOT trigger C++ detection
        let content = b"#include <stdio.h>\nvoid main() { printf(\"Hello\"); }";
        assert!(!is_cpp_header(content));

        let content = b"struct Point { int x; int y; };";
        assert!(!is_cpp_header(content));

        let content = b"typedef struct { int x; int y; } Point;";
        assert!(!is_cpp_header(content));

        let content = b"enum { RED, GREEN, BLUE };";
        assert!(!is_cpp_header(content));

        let content = b"#define MAX(a,b) ((a)>(b)?(a):(b))";
        assert!(!is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_detects_enum_class() {
        // 'enum class' is C++11 but our heuristic should not false positive on this
        // because we check for 'enum ' prefix before 'class '
        let content = b"enum class Color { Red, Green, Blue };";
        assert!(!is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_detects_using_namespace() {
        let content = b"using namespace std;";
        assert!(is_cpp_header(content));
    }

    #[test]
    fn test_is_cpp_header_detects_typename() {
        let content = b"typename T::value_type";
        assert!(is_cpp_header(content));
    }

    #[test]
    fn test_extract_anonymous_struct_no_context() {
        // Test anonymous struct without declaration context (pure specifier)
        // This would happen if we extract the struct_specifier directly
        let source = r#"
struct Named { int x; };
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "struct_specifier" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                // Named struct should NOT have anonymous decorator
                assert_eq!(cls.name, "Named");
                assert!(!cls.decorators.contains(&"anonymous_struct".to_string()));
            }
        }
    }

    #[test]
    fn test_extract_typedef_anonymous_struct() {
        // Typedef anonymous structs should still work via type_definition branch
        let source = r#"
typedef struct { float real; float imag; } Complex;
"#;

        let (tree, source_bytes) = parse_c(source);
        let c = C;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "type_definition" {
                let cls = c.extract_class(child, &source_bytes);
                assert!(cls.is_some(), "Should extract typedef anonymous struct");
                let cls = cls.unwrap();
                assert_eq!(cls.name, "Complex");
                assert!(cls.decorators.contains(&"typedef".to_string()));
                assert_eq!(cls.fields.len(), 2);
            }
        }
    }
}
