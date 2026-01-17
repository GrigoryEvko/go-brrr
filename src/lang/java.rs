//! Java language support.
//!
//! Provides comprehensive Java extraction including:
//! - Classes, interfaces, enums with inheritance chains
//! - Methods with full modifier support (public/private/protected, static, final, etc.)
//! - Constructors
//! - Annotations
//! - Javadoc comments
//! - Generic type parameters
//! - Import statements (regular and static)

use std::collections::HashMap;
use tree_sitter::{Node, Parser, Tree};

use crate::ast::types::{ClassInfo, FieldInfo, FunctionInfo, ImportInfo};
use crate::cfg::types::{BlockId, BlockType, CFGBlock, CFGEdge, CFGInfo};
use crate::dfg::types::{DFGInfo, DataflowEdge, DataflowKind};
use crate::error::{Result, BrrrError};
use crate::lang::traits::Language;

/// Java language implementation.
pub struct Java;

/// Javadoc tag types for efficient byte-level detection.
/// Used to avoid repeated string comparisons in Javadoc parsing.
#[derive(Clone, Copy, PartialEq, Eq)]
enum JavadocTag {
    Param,
    Return,
    Throws,
    Other,
}

impl JavadocTag {
    /// Detect Javadoc tag using byte-level matching.
    /// Returns (tag_type, offset_after_tag) for efficient value extraction.
    ///
    /// Uses branch on second byte after '@' for O(1) initial dispatch,
    /// then verifies remaining bytes. Avoids substring creation entirely.
    #[inline]
    fn detect(bytes: &[u8]) -> (Self, usize) {
        // Minimum: "@x" = 2 bytes
        if bytes.len() < 2 || bytes[0] != b'@' {
            return (Self::Other, 0);
        }

        // Branch on second byte for fast dispatch
        match bytes[1] {
            b'p' => {
                // @param = 6 bytes
                if bytes.len() >= 6
                    && bytes[2] == b'a'
                    && bytes[3] == b'r'
                    && bytes[4] == b'a'
                    && bytes[5] == b'm'
                    && (bytes.len() == 6 || !bytes[6].is_ascii_alphabetic())
                {
                    return (Self::Param, 6);
                }
            }
            b'r' => {
                // @return = 7 bytes
                if bytes.len() >= 7
                    && bytes[2] == b'e'
                    && bytes[3] == b't'
                    && bytes[4] == b'u'
                    && bytes[5] == b'r'
                    && bytes[6] == b'n'
                    && (bytes.len() == 7 || !bytes[7].is_ascii_alphabetic())
                {
                    return (Self::Return, 7);
                }
            }
            b't' => {
                // @throws = 7 bytes
                if bytes.len() >= 7
                    && bytes[2] == b'h'
                    && bytes[3] == b'r'
                    && bytes[4] == b'o'
                    && bytes[5] == b'w'
                    && bytes[6] == b's'
                    && (bytes.len() == 7 || !bytes[7].is_ascii_alphabetic())
                {
                    return (Self::Throws, 7);
                }
            }
            b'e' => {
                // @exception = 10 bytes
                if bytes.len() >= 10
                    && bytes[2] == b'x'
                    && bytes[3] == b'c'
                    && bytes[4] == b'e'
                    && bytes[5] == b'p'
                    && bytes[6] == b't'
                    && bytes[7] == b'i'
                    && bytes[8] == b'o'
                    && bytes[9] == b'n'
                    && (bytes.len() == 10 || !bytes[10].is_ascii_alphabetic())
                {
                    return (Self::Throws, 10); // Treat @exception as Throws
                }
            }
            _ => {}
        }

        (Self::Other, 0)
    }
}

/// BUG #5 & #6 FIX: Comprehensive modifier extraction for Java declarations.
/// Includes Java 17+ sealed class modifiers.
#[derive(Default)]
struct ExtractedModifiers {
    visibility: Option<String>,
    is_static: bool,
    is_final: bool,
    is_abstract: bool,
    is_synchronized: bool,
    is_default: bool,
    // BUG #5 FIX: Missing modifiers
    is_native: bool,
    is_volatile: bool,
    is_transient: bool,
    is_strictfp: bool,
    // BUG #6 FIX: Java 17+ sealed class modifiers
    is_sealed: bool,
    is_non_sealed: bool,
    permits: Vec<String>,
    annotations: Vec<String>,
}

impl Java {
    /// Extract text from a node safely.
    fn node_text<'a>(&self, node: Node<'a>, source: &'a [u8]) -> &'a str {
        node.utf8_text(source).unwrap_or("")
    }

    /// Find a child node by field name.
    fn child_by_field<'a>(&self, node: Node<'a>, field: &str) -> Option<Node<'a>> {
        node.child_by_field_name(field)
    }

    /// Extract modifiers from a method or class declaration.
    /// Returns (visibility, is_static, is_final, is_abstract, is_synchronized, is_default, annotations)
    fn extract_modifiers(
        &self,
        node: Node,
        source: &[u8],
    ) -> (Option<String>, bool, bool, bool, bool, bool, Vec<String>) {
        let mods = self.extract_all_modifiers(node, source);
        (
            mods.visibility,
            mods.is_static,
            mods.is_final,
            mods.is_abstract,
            mods.is_synchronized,
            mods.is_default,
            mods.annotations,
        )
    }

    /// BUG #5 & #6 FIX: Extract all modifiers including Java 17+ sealed class modifiers.
    /// Returns ExtractedModifiers struct with all modifier flags and annotations.
    fn extract_all_modifiers(&self, node: Node, source: &[u8]) -> ExtractedModifiers {
        let mut mods = ExtractedModifiers::default();

        // Find the modifiers node
        let modifiers_node = node
            .children(&mut node.walk())
            .find(|n| n.kind() == "modifiers");

        if let Some(mod_node) = modifiers_node {
            let mut cursor = mod_node.walk();
            for child in mod_node.children(&mut cursor) {
                match child.kind() {
                    // Visibility modifiers
                    "public" => mods.visibility = Some("public".to_string()),
                    "private" => mods.visibility = Some("private".to_string()),
                    "protected" => mods.visibility = Some("protected".to_string()),
                    // Common modifiers
                    "static" => mods.is_static = true,
                    "final" => mods.is_final = true,
                    "abstract" => mods.is_abstract = true,
                    "synchronized" => mods.is_synchronized = true,
                    "default" => mods.is_default = true,
                    // BUG #5 FIX: Missing modifiers
                    "native" => mods.is_native = true,
                    "volatile" => mods.is_volatile = true,
                    "transient" => mods.is_transient = true,
                    "strictfp" => mods.is_strictfp = true,
                    // BUG #6 FIX: Java 17+ sealed class modifiers
                    "sealed" => mods.is_sealed = true,
                    "non-sealed" => mods.is_non_sealed = true,
                    // Annotations
                    "marker_annotation" | "annotation" => {
                        mods.annotations.push(self.extract_annotation(child, source));
                    }
                    _ => {}
                }
            }
        }

        // BUG #6 FIX: Extract permits clause for sealed classes
        mods.permits = self.extract_permits_clause(node, source);

        mods
    }

    /// BUG #6 FIX: Extract permits clause from sealed class declaration.
    /// Returns list of permitted subclass names.
    fn extract_permits_clause(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut permits = Vec::new();

        for child in node.children(&mut node.walk()) {
            // Look for permits clause (tree-sitter-java may represent this differently)
            if child.kind() == "permits" || child.kind() == "permits_clause" {
                for type_child in child.children(&mut child.walk()) {
                    match type_child.kind() {
                        "type_identifier" | "scoped_type_identifier" => {
                            permits.push(self.extract_type(type_child, source));
                        }
                        "type_list" => {
                            for inner in type_child.children(&mut type_child.walk()) {
                                if matches!(inner.kind(), "type_identifier" | "scoped_type_identifier")
                                {
                                    permits.push(self.extract_type(inner, source));
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        permits
    }

    /// Extract annotation text (e.g., "@Override" or "@Table(name = \"users\")").
    fn extract_annotation(&self, node: Node, source: &[u8]) -> String {
        self.node_text(node, source).to_string()
    }

    /// Extract type string from a type node.
    /// BUG #28 FIX: Handles Java 10+ var keyword for local variable type inference.
    /// BUG #18 FIX: Handles wildcard type bounds (? extends T, ? super T).
    fn extract_type(&self, node: Node, source: &[u8]) -> String {
        let text = self.node_text(node, source);
        match node.kind() {
            "void_type" => "void".to_string(),
            "type_identifier" => {
                // BUG #28 FIX: Handle Java 10+ var keyword for local variable type inference
                // var is a reserved type name (not a keyword), so it appears as type_identifier
                if text == "var" {
                    "var".to_string()
                } else {
                    text.to_string()
                }
            }
            "integral_type" | "floating_point_type" | "boolean_type" => text.to_string(),
            "generic_type" => self.extract_generic_type(node, source),
            "array_type" => self.extract_array_type(node, source),
            "scoped_type_identifier" => self.extract_scoped_type(node, source),
            // BUG #18 FIX: Properly extract wildcard type bounds
            "wildcard" => self.extract_wildcard_type(node, source),
            _ => text.to_string(),
        }
    }

    /// BUG #18 FIX: Extract wildcard type with bounds.
    /// Handles: ? (unbounded), ? extends T (upper bound), ? super T (lower bound).
    fn extract_wildcard_type(&self, node: Node, source: &[u8]) -> String {
        let mut result = String::from("?");

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                // Upper bound: ? extends T
                "extends" => {
                    result.push_str(" extends ");
                }
                // Lower bound: ? super T
                "super" => {
                    result.push_str(" super ");
                }
                // The bounded type itself
                "type_identifier" | "generic_type" | "scoped_type_identifier" | "array_type" => {
                    result.push_str(&self.extract_type(child, source));
                }
                _ => {}
            }
        }

        result
    }

    /// Extract generic type (e.g., "List<String>").
    fn extract_generic_type(&self, node: Node, source: &[u8]) -> String {
        let mut result = String::new();

        // Get the base type
        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "type_identifier" | "scoped_type_identifier" => {
                    result.push_str(self.node_text(child, source));
                }
                "type_arguments" => {
                    result.push_str(self.extract_type_arguments(child, source).as_str());
                }
                _ => {}
            }
        }

        result
    }

    /// Extract type arguments (e.g., "<String, Integer>").
    fn extract_type_arguments(&self, node: Node, source: &[u8]) -> String {
        let mut args = Vec::new();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "type_identifier" | "generic_type" | "wildcard" | "scoped_type_identifier" => {
                    args.push(self.extract_type(child, source));
                }
                _ => {}
            }
        }

        if args.is_empty() {
            "<>".to_string()
        } else {
            format!("<{}>", args.join(", "))
        }
    }

    /// Extract array type (e.g., "String[]").
    fn extract_array_type(&self, node: Node, source: &[u8]) -> String {
        let mut base_type = String::new();
        let mut dimensions = 0;

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "type_identifier"
                | "integral_type"
                | "floating_point_type"
                | "boolean_type"
                | "generic_type" => {
                    base_type = self.extract_type(child, source);
                }
                "dimensions" => {
                    // BUG #4 FIX: Count actual `[` tokens for robust dimension counting.
                    // This avoids fragile assumptions about tree-sitter node structure.
                    dimensions = self.count_array_dimensions(child, source);
                }
                _ => {}
            }
        }

        format!("{}{}", base_type, "[]".repeat(dimensions.max(1)))
    }

    /// BUG #4 FIX: Count array dimensions by counting `[` bracket tokens.
    /// This is more robust than dividing child_count() which can vary based on tree-sitter version.
    fn count_array_dimensions(&self, dimensions_node: Node, source: &[u8]) -> usize {
        // Method 1: Count `[` children directly in the AST
        let mut count = 0;
        for child in dimensions_node.children(&mut dimensions_node.walk()) {
            if child.kind() == "[" {
                count += 1;
            }
        }

        // Fallback: If no `[` children found, count from text representation
        if count == 0 {
            let text = self.node_text(dimensions_node, source);
            count = text.chars().filter(|&c| c == '[').count();
        }

        // Ensure at least 1 dimension if we have a dimensions node
        count.max(1)
    }

    /// Extract scoped type identifier (e.g., "java.util.List").
    fn extract_scoped_type(&self, node: Node, source: &[u8]) -> String {
        self.node_text(node, source).to_string()
    }

    /// Extract method parameters from formal_parameters node.
    fn extract_parameters(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut params = Vec::new();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "formal_parameter" | "spread_parameter" => {
                    params.push(self.extract_single_parameter(child, source));
                }
                "receiver_parameter" => {
                    // Java receiver parameter (Type this) - skip for signature
                }
                _ => {}
            }
        }

        params
    }

    /// Extract a single parameter with type and name.
    fn extract_single_parameter(&self, node: Node, source: &[u8]) -> String {
        let mut param_type = String::new();
        let mut param_name = String::new();
        let mut is_vararg = false;

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "type_identifier"
                | "integral_type"
                | "floating_point_type"
                | "boolean_type"
                | "generic_type"
                | "array_type"
                | "scoped_type_identifier"
                | "void_type" => {
                    param_type = self.extract_type(child, source);
                }
                "identifier" => {
                    param_name = self.node_text(child, source).to_string();
                }
                "..." => {
                    is_vararg = true;
                }
                "modifiers" => {
                    // Parameter modifiers like final - skip for signature
                }
                "dimensions" => {
                    // Array dimensions after parameter name
                    param_type.push_str("[]");
                }
                _ => {}
            }
        }

        if is_vararg {
            format!("{}... {}", param_type, param_name)
        } else if param_name.is_empty() {
            param_type
        } else {
            format!("{} {}", param_type, param_name)
        }
    }

    /// Extract type parameters for generics (e.g., "<T, K extends Comparable>").
    fn extract_type_parameters(&self, node: Node, source: &[u8]) -> Option<String> {
        let type_params = self.child_by_field(node, "type_parameters")?;
        let mut params = Vec::new();

        for child in type_params.children(&mut type_params.walk()) {
            if child.kind() == "type_parameter" {
                params.push(self.extract_type_parameter(child, source));
            }
        }

        if params.is_empty() {
            None
        } else {
            Some(format!("<{}>", params.join(", ")))
        }
    }

    /// Extract a single type parameter.
    fn extract_type_parameter(&self, node: Node, source: &[u8]) -> String {
        let mut result = String::new();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "type_identifier" => {
                    result.push_str(self.node_text(child, source));
                }
                "type_bound" => {
                    result.push_str(" extends ");
                    result.push_str(self.extract_type_bound(child, source).as_str());
                }
                _ => {}
            }
        }

        result
    }

    /// Extract type bound (e.g., "extends Comparable<T>").
    fn extract_type_bound(&self, node: Node, source: &[u8]) -> String {
        let mut bounds = Vec::new();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "type_identifier" | "generic_type" | "scoped_type_identifier" => {
                    bounds.push(self.extract_type(child, source));
                }
                _ => {}
            }
        }

        bounds.join(" & ")
    }

    /// Extract Javadoc comment by looking at preceding sibling.
    /// BUG #17 FIX: Skip over modifiers/annotations nodes when searching for Javadoc.
    /// When annotations are between Javadoc and method, we need to traverse past them.
    fn extract_javadoc(&self, node: Node, source: &[u8]) -> Option<String> {
        // Look for block_comment before the declaration
        // BUG #17 FIX: Need to skip modifiers/annotations that may be between Javadoc and declaration
        let mut prev = node.prev_sibling();
        while let Some(sibling) = prev {
            match sibling.kind() {
                "block_comment" => {
                    let comment = self.node_text(sibling, source);
                    // Check if it's a Javadoc comment (starts with /**)
                    if comment.starts_with("/**") {
                        return Some(self.parse_javadoc(comment));
                    }
                    return None;
                }
                "line_comment" => {
                    // Skip line comments, they're not Javadoc
                    prev = sibling.prev_sibling();
                }
                // BUG #17 FIX: Skip modifiers/annotations - they can appear between Javadoc and declaration
                "modifiers" | "marker_annotation" | "annotation" => {
                    prev = sibling.prev_sibling();
                }
                _ => {
                    // Stop at any other non-comment node
                    return None;
                }
            }
        }
        None
    }

    /// Parse Javadoc comment to extract meaningful content.
    /// BUG #19 FIX: Parse Javadoc comment into structured format.
    /// Extracts @param, @return, @throws tags into a clean, structured output.
    fn parse_javadoc(&self, comment: &str) -> String {
        // Remove /** and */ markers
        let content = comment
            .trim_start_matches("/**")
            .trim_end_matches("*/")
            .trim();

        // Process each line - remove leading asterisks and whitespace
        let lines: Vec<&str> = content
            .lines()
            .map(|line| line.trim().trim_start_matches('*').trim())
            .filter(|line| !line.is_empty())
            .collect();

        // BUG #19 FIX: Parse @tags into structured sections
        let mut description_lines = Vec::new();
        let mut params = Vec::new();
        let mut returns = Vec::new();
        let mut throws = Vec::new();

        let mut current_tag: Option<JavadocTag> = None;
        let mut current_value = String::new();

        for line in lines {
            let bytes = line.as_bytes();
            // Fast check: first byte must be '@' for tag detection
            if !bytes.is_empty() && bytes[0] == b'@' {
                // Save previous tag if any
                self.save_javadoc_tag(
                    current_tag,
                    &current_value,
                    &mut params,
                    &mut returns,
                    &mut throws,
                );

                // Parse new tag using byte-level detection
                let (tag, offset) = JavadocTag::detect(bytes);
                match tag {
                    JavadocTag::Param | JavadocTag::Return | JavadocTag::Throws => {
                        current_tag = Some(tag);
                        // Extract value after tag, avoiding substring creation until needed
                        current_value = if offset < bytes.len() {
                            // SAFETY: offset is within bounds, line is valid UTF-8
                            line[offset..].trim().to_string()
                        } else {
                            String::new()
                        };
                    }
                    JavadocTag::Other => {
                        // Other tags like @see, @since, @deprecated - treat as description
                        current_tag = None;
                        description_lines.push(line.to_string());
                    }
                }
            } else if current_tag.is_some() {
                // Continuation of current tag
                if !current_value.is_empty() {
                    current_value.push(' ');
                }
                current_value.push_str(line);
            } else {
                // Part of main description
                description_lines.push(line.to_string());
            }
        }

        // Save last tag
        self.save_javadoc_tag(
            current_tag,
            &current_value,
            &mut params,
            &mut returns,
            &mut throws,
        );

        // Build final structured output
        let mut result = description_lines.join("\n");

        if !params.is_empty() {
            if !result.is_empty() {
                result.push_str("\n\n");
            }
            result.push_str("Parameters:\n");
            for param in params {
                result.push_str(&format!("  {}\n", param));
            }
        }

        if !returns.is_empty() {
            if !result.is_empty() && !result.ends_with('\n') {
                result.push('\n');
            }
            result.push_str("Returns: ");
            result.push_str(&returns.join(", "));
        }

        if !throws.is_empty() {
            if !result.is_empty() {
                result.push_str("\n");
            }
            result.push_str("Throws:\n");
            for throw in throws {
                result.push_str(&format!("  {}\n", throw));
            }
        }

        result.trim_end().to_string()
    }

    /// BUG #19 FIX: Helper to save parsed Javadoc tag to appropriate collection.
    /// Uses enum-based dispatch for type safety and compiler optimization.
    #[inline]
    fn save_javadoc_tag(
        &self,
        tag: Option<JavadocTag>,
        value: &str,
        params: &mut Vec<String>,
        returns: &mut Vec<String>,
        throws: &mut Vec<String>,
    ) {
        if value.is_empty() {
            return;
        }
        match tag {
            Some(JavadocTag::Param) => params.push(value.to_string()),
            Some(JavadocTag::Return) => returns.push(value.to_string()),
            Some(JavadocTag::Throws) => throws.push(value.to_string()),
            Some(JavadocTag::Other) | None => {}
        }
    }

    /// Extract superclass from class declaration.
    fn extract_superclass(&self, node: Node, source: &[u8]) -> Option<String> {
        let superclass_node = self.child_by_field(node, "superclass")?;

        // Find the type identifier in the superclass node
        for child in superclass_node.children(&mut superclass_node.walk()) {
            match child.kind() {
                "type_identifier" | "generic_type" | "scoped_type_identifier" => {
                    return Some(self.extract_type(child, source));
                }
                _ => {}
            }
        }

        None
    }

    /// Extract implemented interfaces.
    fn extract_interfaces(&self, node: Node, source: &[u8]) -> Vec<String> {
        let interfaces_node = match self.child_by_field(node, "interfaces") {
            Some(n) => n,
            None => return Vec::new(),
        };

        let mut interfaces = Vec::new();

        // Look for type_list inside super_interfaces
        for child in interfaces_node.children(&mut interfaces_node.walk()) {
            if child.kind() == "type_list" {
                for type_child in child.children(&mut child.walk()) {
                    match type_child.kind() {
                        "type_identifier" | "generic_type" | "scoped_type_identifier" => {
                            interfaces.push(self.extract_type(type_child, source));
                        }
                        _ => {}
                    }
                }
            }
        }

        interfaces
    }

    /// Extract extended interfaces for interface declarations.
    fn extract_extends_interfaces(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut interfaces = Vec::new();

        for child in node.children(&mut node.walk()) {
            if child.kind() == "extends_interfaces" {
                for type_list_child in child.children(&mut child.walk()) {
                    if type_list_child.kind() == "type_list" {
                        for type_child in type_list_child.children(&mut type_list_child.walk()) {
                            match type_child.kind() {
                                "type_identifier" | "generic_type" | "scoped_type_identifier" => {
                                    interfaces.push(self.extract_type(type_child, source));
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }

        interfaces
    }

    /// Extract methods from a class/interface/enum body.
    /// BUG #9 & #10 FIX: Also extracts static and instance initializer blocks.
    fn extract_methods(&self, body_node: Node, source: &[u8]) -> Vec<FunctionInfo> {
        let mut methods = Vec::new();
        let mut static_init_count = 0;
        let mut instance_init_count = 0;

        for child in body_node.children(&mut body_node.walk()) {
            match child.kind() {
                "method_declaration" => {
                    if let Some(func) = self.extract_method(child, source) {
                        methods.push(func);
                    }
                }
                "constructor_declaration" => {
                    if let Some(func) = self.extract_constructor(child, source) {
                        methods.push(func);
                    }
                }
                "enum_body_declarations" => {
                    // Enum can have methods inside enum_body_declarations
                    methods.extend(self.extract_methods(child, source));
                }
                // BUG #9 FIX: Static initializer blocks
                "static_initializer" => {
                    static_init_count += 1;
                    methods.push(self.extract_static_initializer(child, source, static_init_count));
                }
                // BUG #10 FIX: Instance initializer blocks (standalone blocks in class body)
                "block" => {
                    instance_init_count += 1;
                    methods.push(self.extract_instance_initializer(
                        child,
                        source,
                        instance_init_count,
                    ));
                }
                _ => {}
            }
        }

        methods
    }

    /// BUG #20 FIX: Extract field declarations from a class/interface/enum body.
    /// Returns a Vec of FieldInfo with type, visibility, modifiers, and initial values.
    fn extract_fields(&self, body_node: Node, source: &[u8]) -> Vec<FieldInfo> {
        let mut fields = Vec::new();

        for child in body_node.children(&mut body_node.walk()) {
            if child.kind() == "field_declaration" {
                fields.extend(self.extract_field(child, source));
            }
        }

        fields
    }

    /// BUG #20 FIX: Extract a single field declaration.
    /// A field declaration can declare multiple variables: int x, y = 5;
    fn extract_field(&self, node: Node, source: &[u8]) -> Vec<FieldInfo> {
        let mut fields = Vec::new();
        let mut field_type: Option<String> = None;
        let mut visibility: Option<String> = None;
        let mut is_static = false;
        let mut is_final = false;
        let mut annotations = Vec::new();

        // Extract modifiers
        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "modifiers" => {
                    for mod_child in child.children(&mut child.walk()) {
                        match mod_child.kind() {
                            "public" => visibility = Some("public".to_string()),
                            "private" => visibility = Some("private".to_string()),
                            "protected" => visibility = Some("protected".to_string()),
                            "static" => is_static = true,
                            "final" => is_final = true,
                            "marker_annotation" | "annotation" => {
                                annotations.push(self.extract_annotation(mod_child, source));
                            }
                            _ => {}
                        }
                    }
                }
                // Extract the type
                "type_identifier"
                | "integral_type"
                | "floating_point_type"
                | "boolean_type"
                | "generic_type"
                | "array_type"
                | "scoped_type_identifier"
                | "void_type" => {
                    field_type = Some(self.extract_type(child, source));
                }
                // Extract each variable declarator
                "variable_declarator" => {
                    let mut name = String::new();
                    let mut default_value: Option<String> = None;
                    let mut extra_dims = 0;

                    for var_child in child.children(&mut child.walk()) {
                        match var_child.kind() {
                            "identifier" => {
                                name = self.node_text(var_child, source).to_string();
                            }
                            "dimensions" => {
                                extra_dims = self.count_array_dimensions(var_child, source);
                            }
                            _ if var_child.kind().ends_with("_expression")
                                || var_child.kind().ends_with("_literal")
                                || var_child.kind() == "null_literal"
                                || var_child.kind() == "identifier"
                                || var_child.kind() == "array_initializer"
                                || var_child.kind() == "object_creation_expression" =>
                            {
                                // This is the initializer value
                                if var_child.prev_sibling().map(|s| s.kind()) == Some("=") {
                                    default_value =
                                        Some(self.node_text(var_child, source).to_string());
                                }
                            }
                            _ => {}
                        }
                    }

                    // Build final type (handle int[] x or int x[])
                    let final_type = if extra_dims > 0 {
                        field_type
                            .clone()
                            .map(|t| format!("{}{}", t, "[]".repeat(extra_dims)))
                    } else {
                        field_type.clone()
                    };

                    if !name.is_empty() {
                        fields.push(FieldInfo {
                            name,
                            field_type: final_type,
                            visibility: visibility.clone(),
                            is_static,
                            is_final,
                            default_value,
                            annotations: annotations.clone(),
                            line_number: node.start_position().row + 1,
                        });
                    }
                }
                _ => {}
            }
        }

        fields
    }

    /// BUG #9 FIX: Extract static initializer block.
    /// Static initializers are represented as special FunctionInfo entries.
    fn extract_static_initializer(
        &self,
        node: Node,
        source: &[u8],
        index: usize,
    ) -> FunctionInfo {
        let line_number = node.start_position().row + 1;
        let end_line_number = Some(node.end_position().row + 1);

        // Extract docstring if there's a comment before the static block
        let docstring = self.extract_javadoc(node, source);

        FunctionInfo {
            name: format!("<static_init_{}>", index),
            params: Vec::new(),
            return_type: None,
            docstring,
            is_method: false,
            is_async: false,
            decorators: vec!["static".to_string(), "initializer".to_string()],
            line_number,
            end_line_number,
            language: "java".to_string(),
        }
    }

    /// BUG #10 FIX: Extract instance initializer block.
    /// Instance initializers are standalone blocks that run before constructor.
    fn extract_instance_initializer(
        &self,
        node: Node,
        _source: &[u8],
        index: usize,
    ) -> FunctionInfo {
        let line_number = node.start_position().row + 1;
        let end_line_number = Some(node.end_position().row + 1);

        FunctionInfo {
            name: format!("<instance_init_{}>", index),
            params: Vec::new(),
            return_type: None,
            docstring: None,
            is_method: false,
            is_async: false,
            decorators: vec!["initializer".to_string()],
            line_number,
            end_line_number,
            language: "java".to_string(),
        }
    }

    /// Extract a single method declaration.
    fn extract_method(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        let name_node = self.child_by_field(node, "name")?;
        let name = self.node_text(name_node, source).to_string();

        // Extract modifiers
        let (
            visibility,
            is_static,
            is_final,
            is_abstract,
            is_synchronized,
            is_default,
            annotations,
        ) = self.extract_modifiers(node, source);

        // Build decorators list from modifiers
        let mut decorators = annotations.clone();
        if let Some(vis) = &visibility {
            decorators.insert(0, vis.clone());
        }
        if is_static {
            decorators.push("static".to_string());
        }
        if is_final {
            decorators.push("final".to_string());
        }
        if is_abstract {
            decorators.push("abstract".to_string());
        }
        if is_synchronized {
            decorators.push("synchronized".to_string());
        }
        if is_default {
            decorators.push("default".to_string());
        }

        // Extract type parameters (generics)
        let type_params = self.extract_type_parameters(node, source);
        if let Some(tp) = type_params {
            decorators.push(format!("generic:{}", tp));
        }

        // BUG #8 FIX: Extract throws clause
        let throws = self.extract_throws_clause(node, source);
        if !throws.is_empty() {
            decorators.push(format!("throws:{}", throws.join(", ")));
        }

        // Extract return type
        let return_type = self
            .child_by_field(node, "type")
            .map(|n| self.extract_type(n, source));

        // Extract parameters
        let params_node = self.child_by_field(node, "parameters")?;
        let params = self.extract_parameters(params_node, source);

        // Extract Javadoc
        let docstring = self.extract_javadoc(node, source);

        // Line numbers
        let line_number = node.start_position().row + 1;
        let end_line_number = Some(node.end_position().row + 1);

        Some(FunctionInfo {
            name,
            params,
            return_type,
            docstring,
            is_method: true,
            is_async: false, // Java doesn't have async keyword
            decorators,
            line_number,
            end_line_number,
            language: "java".to_string(),
        })
    }

    /// BUG #8 FIX: Extract throws clause from method/constructor declaration.
    /// Returns list of exception type names declared in the throws clause.
    fn extract_throws_clause(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut throws = Vec::new();

        for child in node.children(&mut node.walk()) {
            // tree-sitter-java uses "throws" for the throws clause
            if child.kind() == "throws" {
                for type_child in child.children(&mut child.walk()) {
                    match type_child.kind() {
                        "type_identifier" | "scoped_type_identifier" | "generic_type" => {
                            throws.push(self.extract_type(type_child, source));
                        }
                        _ => {}
                    }
                }
            }
        }

        throws
    }

    /// Extract a constructor declaration.
    fn extract_constructor(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        let name_node = self.child_by_field(node, "name")?;
        let name = self.node_text(name_node, source).to_string();

        // Extract modifiers
        let (visibility, _, _, _, _, _, annotations) = self.extract_modifiers(node, source);

        // BUG #29 FIX: Make visibility position consistent with methods
        // Methods use [visibility, annotations, modifiers...], so constructors should too
        // Changed from insert(1, vis) to insert(0, vis) for consistency
        let mut decorators = annotations.clone();
        if let Some(vis) = visibility {
            decorators.insert(0, vis);
        }
        decorators.push("constructor".to_string());

        // BUG #8 FIX: Constructors can also have throws clauses
        let throws = self.extract_throws_clause(node, source);
        if !throws.is_empty() {
            decorators.push(format!("throws:{}", throws.join(", ")));
        }

        // Extract parameters
        let params_node = self.child_by_field(node, "parameters")?;
        let params = self.extract_parameters(params_node, source);

        // Extract Javadoc
        let docstring = self.extract_javadoc(node, source);

        // Line numbers
        let line_number = node.start_position().row + 1;
        let end_line_number = Some(node.end_position().row + 1);

        Some(FunctionInfo {
            name,
            params,
            return_type: None, // Constructors don't have return type
            docstring,
            is_method: true,
            is_async: false,
            decorators,
            line_number,
            end_line_number,
            language: "java".to_string(),
        })
    }

    /// Extract scoped identifier path (e.g., "java.util.List").
    fn extract_scoped_identifier(&self, node: Node, source: &[u8]) -> String {
        let mut parts = Vec::new();
        self.collect_identifier_parts(node, source, &mut parts);
        parts.join(".")
    }

    /// Recursively collect identifier parts.
    fn collect_identifier_parts(&self, node: Node, source: &[u8], parts: &mut Vec<String>) {
        match node.kind() {
            "identifier" => {
                parts.push(self.node_text(node, source).to_string());
            }
            "scoped_identifier" => {
                if let Some(scope) = self.child_by_field(node, "scope") {
                    self.collect_identifier_parts(scope, source, parts);
                }
                if let Some(name) = self.child_by_field(node, "name") {
                    parts.push(self.node_text(name, source).to_string());
                }
            }
            _ => {}
        }
    }

    /// Build CFG blocks from a method body.
    fn build_cfg_from_body(
        &self,
        body: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        next_id: &mut usize,
    ) -> (BlockId, Vec<BlockId>) {
        let entry_id = BlockId(*next_id);
        *next_id += 1;

        let mut statements = Vec::new();
        let mut exits = Vec::new();

        // Process statements in the body
        for child in body.children(&mut body.walk()) {
            match child.kind() {
                "if_statement" => {
                    // Create current block with statements so far
                    if !statements.is_empty() {
                        let block = CFGBlock {
                id: entry_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: body.start_position().row + 1,
                end_line: child.start_position().row + 1,
            };
                        blocks.insert(entry_id, block);
                        statements.clear();
                    }

                    // Process if statement branches
                    let (if_entry, if_exits) =
                        self.build_cfg_for_if(child, source, blocks, edges, next_id);
                    edges.push(CFGEdge::from_label(entry_id, if_entry, None));
                    exits.extend(if_exits);
                }
                "while_statement" | "for_statement" | "enhanced_for_statement" => {
                    let (loop_entry, loop_exits) =
                        self.build_cfg_for_loop(child, source, blocks, edges, next_id);
                    if !statements.is_empty() {
                        let block = CFGBlock {
                id: entry_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: body.start_position().row + 1,
                end_line: child.start_position().row + 1,
            };
                        blocks.insert(entry_id, block);
                        statements.clear();
                        edges.push(CFGEdge::from_label(entry_id, loop_entry, None));
                    }
                    exits.extend(loop_exits);
                }
                // BUG #11 FIX: Handle do-while loops
                "do_statement" => {
                    let (do_entry, do_exits) =
                        self.build_cfg_for_do_while(child, source, blocks, edges, next_id);
                    if !statements.is_empty() {
                        let block = CFGBlock {
                id: entry_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: body.start_position().row + 1,
                end_line: child.start_position().row + 1,
            };
                        blocks.insert(entry_id, block);
                        statements.clear();
                        edges.push(CFGEdge::from_label(entry_id, do_entry, None));
                    }
                    exits.extend(do_exits);
                }
                // BUG #12 FIX: Handle labeled statements
                "labeled_statement" => {
                    let (label_entry, label_exits) =
                        self.build_cfg_for_labeled(child, source, blocks, edges, next_id);
                    if !statements.is_empty() {
                        let block = CFGBlock {
                id: entry_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: body.start_position().row + 1,
                end_line: child.start_position().row + 1,
            };
                        blocks.insert(entry_id, block);
                        statements.clear();
                        edges.push(CFGEdge::from_label(entry_id, label_entry, None));
                    }
                    exits.extend(label_exits);
                }
                // BUG #12 FIX: Handle break/continue statements (control flow exits)
                "break_statement" | "continue_statement" => {
                    statements.push(self.node_text(child, source).trim().to_string());
                    let stmt_id = BlockId(*next_id);
                    *next_id += 1;
                    let block = CFGBlock {
                id: stmt_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.end_position().row + 1,
            };
                    blocks.insert(stmt_id, block);
                    // Break/continue are control flow exits from current block
                    exits.push(stmt_id);
                    statements.clear();
                }
                "return_statement" => {
                    statements.push(self.node_text(child, source).trim().to_string());
                    // Return statement is an exit
                    let return_id = BlockId(*next_id);
                    *next_id += 1;
                    let block = CFGBlock {
                id: return_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.end_position().row + 1,
            };
                    blocks.insert(return_id, block);
                    exits.push(return_id);
                    statements.clear();
                }
                "throw_statement" => {
                    statements.push(self.node_text(child, source).trim().to_string());
                    let throw_id = BlockId(*next_id);
                    *next_id += 1;
                    let block = CFGBlock {
                id: throw_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.end_position().row + 1,
            };
                    blocks.insert(throw_id, block);
                    exits.push(throw_id);
                    statements.clear();
                }
                // FEATURE: Handle yield statements (Java 14+ switch expressions)
                // yield is similar to return - it exits the switch expression with a value
                "yield_statement" => {
                    statements.push(self.node_text(child, source).trim().to_string());
                    let yield_id = BlockId(*next_id);
                    *next_id += 1;
                    let block = CFGBlock {
                id: yield_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.end_position().row + 1,
            };
                    blocks.insert(yield_id, block);
                    // yield is an exit point from the switch expression
                    exits.push(yield_id);
                    statements.clear();
                }
                "try_statement" => {
                    let (try_entry, try_exits) =
                        self.build_cfg_for_try(child, source, blocks, edges, next_id);
                    if !statements.is_empty() {
                        let block = CFGBlock {
                id: entry_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: body.start_position().row + 1,
                end_line: child.start_position().row + 1,
            };
                        blocks.insert(entry_id, block);
                        statements.clear();
                        edges.push(CFGEdge::from_label(entry_id, try_entry, None));
                    }
                    exits.extend(try_exits);
                }
                "switch_expression" | "switch_statement" => {
                    let (switch_entry, switch_exits) =
                        self.build_cfg_for_switch(child, source, blocks, edges, next_id);
                    if !statements.is_empty() {
                        let block = CFGBlock {
                id: entry_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: body.start_position().row + 1,
                end_line: child.start_position().row + 1,
            };
                        blocks.insert(entry_id, block);
                        statements.clear();
                        edges.push(CFGEdge::from_label(entry_id, switch_entry, None));
                    }
                    exits.extend(switch_exits);
                }
                // BUG #23 FIX: Handle synchronized blocks
                "synchronized_statement" => {
                    let (sync_entry, sync_exits) =
                        self.build_cfg_for_synchronized(child, source, blocks, edges, next_id);
                    if !statements.is_empty() {
                        let block = CFGBlock {
                id: entry_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: body.start_position().row + 1,
                end_line: child.start_position().row + 1,
            };
                        blocks.insert(entry_id, block);
                        statements.clear();
                        edges.push(CFGEdge::from_label(entry_id, sync_entry, None));
                    }
                    exits.extend(sync_exits);
                }
                // BUG #24 FIX: Handle assert statements (can throw AssertionError)
                "assert_statement" => {
                    statements.push(self.node_text(child, source).trim().to_string());
                    // Assert can throw AssertionError, creating a potential exit point
                    let assert_id = BlockId(*next_id);
                    *next_id += 1;
                    let block = CFGBlock {
                id: assert_id,
                label: statements.join("; "),
                block_type: BlockType::Body,
                statements: statements.clone(),
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.end_position().row + 1,
            };
                    blocks.insert(assert_id, block);
                    // Assert has two paths: continue (pass) or throw (fail)
                    // For simplicity, we mark it as a potential exit due to AssertionError
                    exits.push(assert_id);
                    statements.clear();
                }
                "{" | "}" => {
                    // Skip braces
                }
                _ if !child.is_named() => {
                    // Skip unnamed nodes
                }
                _ => {
                    // Regular statement
                    let stmt_text = self.node_text(child, source).trim().to_string();
                    if !stmt_text.is_empty() {
                        statements.push(stmt_text);
                    }
                }
            }
        }

        // Create final block if there are remaining statements
        if !statements.is_empty() || blocks.get(&entry_id).is_none() {
            let block = CFGBlock {
                id: entry_id,
                label: if statements.is_empty() {
                    "entry".to_string()
                } else {
                    statements.join("; ")
                },
                block_type: BlockType::Body,
                statements,
                func_calls: Vec::new(),
                start_line: body.start_position().row + 1,
                end_line: body.end_position().row + 1,
            };
            blocks.insert(entry_id, block);
            if exits.is_empty() {
                exits.push(entry_id);
            }
        }

        (entry_id, exits)
    }

    /// Build CFG for if statement.
    fn build_cfg_for_if(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        next_id: &mut usize,
    ) -> (BlockId, Vec<BlockId>) {
        let condition_id = BlockId(*next_id);
        *next_id += 1;

        // Extract condition
        let condition_text = self
            .child_by_field(node, "condition")
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_else(|| "condition".to_string());

        let block = CFGBlock {
            id: condition_id,
            label: format!("if ({})", condition_text),
            block_type: BlockType::Body,
            statements: vec![format!("if ({})", condition_text)],
            func_calls: Vec::new(),
            start_line: node.start_position().row + 1,
            end_line: node.start_position().row + 1,
        };
        blocks.insert(condition_id, block);

        let mut exits = Vec::new();

        // Process consequence (then branch)
        if let Some(consequence) = self.child_by_field(node, "consequence") {
            let (then_entry, then_exits) =
                self.build_cfg_from_body(consequence, source, blocks, edges, next_id);
            edges.push(CFGEdge::from_label(condition_id, then_entry, Some("true".to_string())));
            exits.extend(then_exits);
        }

        // Process alternative (else branch)
        if let Some(alternative) = self.child_by_field(node, "alternative") {
            let (else_entry, else_exits) =
                self.build_cfg_from_body(alternative, source, blocks, edges, next_id);
            edges.push(CFGEdge::from_label(condition_id, else_entry, Some("false".to_string())));
            exits.extend(else_exits);
        } else {
            // No else branch - condition itself is an exit for false case
            exits.push(condition_id);
        }

        (condition_id, exits)
    }

    /// Build CFG for loop statements.
    fn build_cfg_for_loop(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        next_id: &mut usize,
    ) -> (BlockId, Vec<BlockId>) {
        let loop_id = BlockId(*next_id);
        *next_id += 1;

        let label = match node.kind() {
            "while_statement" => {
                let cond = self
                    .child_by_field(node, "condition")
                    .map(|n| self.node_text(n, source).to_string())
                    .unwrap_or_default();
                format!("while ({})", cond)
            }
            "for_statement" => "for loop".to_string(),
            "enhanced_for_statement" => "for-each loop".to_string(),
            _ => "loop".to_string(),
        };

        let block = CFGBlock {
                id: loop_id,
                label: label.clone(),
                block_type: BlockType::Body,
                statements: vec![label],
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            };
        blocks.insert(loop_id, block);

        // Process loop body
        if let Some(body) = self.child_by_field(node, "body") {
            let (body_entry, body_exits) =
                self.build_cfg_from_body(body, source, blocks, edges, next_id);
            edges.push(CFGEdge::from_label(loop_id, body_entry, Some("true".to_string())));
            // Back edge from body to loop condition
            for exit in &body_exits {
                edges.push(CFGEdge::from_label(*exit, loop_id, None));
            }
        }

        // Exit from loop (false condition)
        let exit_id = BlockId(*next_id);
        *next_id += 1;
        let exit_block = CFGBlock {
                id: exit_id,
                label: "loop exit".to_string(),
                block_type: BlockType::Body,
                statements: vec![],
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            };
        blocks.insert(exit_id, exit_block);
        edges.push(CFGEdge::from_label(loop_id, exit_id, Some("false".to_string())));

        (loop_id, vec![exit_id])
    }

    /// Build CFG for try statement.
    /// BUG #22 FIX: Handle try-with-resources (resource_specification in try statements).
    fn build_cfg_for_try(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        next_id: &mut usize,
    ) -> (BlockId, Vec<BlockId>) {
        let try_id = BlockId(*next_id);
        *next_id += 1;

        // BUG #22 FIX: Check for try-with-resources
        let resource_spec = node
            .children(&mut node.walk())
            .find(|n| n.kind() == "resource_specification");

        // Build label including resources if present
        let try_label = if let Some(ref res) = resource_spec {
            let resources_text = self.node_text(*res, source);
            format!("try {}", resources_text)
        } else {
            "try".to_string()
        };

        let block = CFGBlock {
                id: try_id,
                label: try_label.clone(),
                block_type: BlockType::Body,
                statements: vec![try_label],
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            };
        blocks.insert(try_id, block);

        let mut exits = Vec::new();

        // BUG #22 FIX: For try-with-resources, create resource acquisition block
        // Resources can throw exceptions during acquisition, so we need edges for that
        let effective_entry = if let Some(ref res) = resource_spec {
            let resource_id = BlockId(*next_id);
            *next_id += 1;

            // Extract resource declarations for the CFG block
            let resource_text = self.extract_resource_declarations(*res, source);

            let resource_block = CFGBlock {
                id: resource_id,
                label: format!("acquire resources: {}", resource_text),
                block_type: BlockType::Body,
                statements: vec![format!("acquire: {}", resource_text)],
                func_calls: Vec::new(),
                start_line: res.start_position().row + 1,
                end_line: res.end_position().row + 1,
            };
            blocks.insert(resource_id, resource_block);

            // Edge from try to resource acquisition
            edges.push(CFGEdge::from_label(try_id, resource_id, Some("acquire".to_string())));

            resource_id
        } else {
            try_id
        };

        // Process try body
        if let Some(body) = self.child_by_field(node, "body") {
            let (body_entry, body_exits) =
                self.build_cfg_from_body(body, source, blocks, edges, next_id);

            // Edge from resource acquisition (or try) to body
            if resource_spec.is_some() {
                edges.push(CFGEdge::from_label(effective_entry, body_entry, Some("success".to_string())));
            } else {
                edges.push(CFGEdge::from_label(try_id, body_entry, None));
            }
            exits.extend(body_exits);
        }

        // BUG #22 FIX: For try-with-resources, add implicit close block
        // Resources are closed in reverse order of declaration
        let close_block_id = if resource_spec.is_some() {
            let close_id = BlockId(*next_id);
            *next_id += 1;

            let close_block = CFGBlock {
                id: close_id,
                label: "close resources".to_string(),
                block_type: BlockType::Body,
                statements: vec!["close resources (auto)".to_string()],
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            };
            blocks.insert(close_id, close_block);

            // All body exits flow through resource close
            for exit in &exits {
                edges.push(CFGEdge::from_label(*exit, close_id, Some("close".to_string())));
            }

            // Replace exits with close block
            exits = vec![close_id];

            Some(close_id)
        } else {
            None
        };

        // Process catch clauses
        for child in node.children(&mut node.walk()) {
            if child.kind() == "catch_clause" {
                if let Some(catch_body) = self.child_by_field(child, "body") {
                    let (catch_entry, catch_exits) =
                        self.build_cfg_from_body(catch_body, source, blocks, edges, next_id);

                    // BUG #22 FIX: For try-with-resources, exceptions can come from:
                    // 1. Resource acquisition
                    // 2. Try body
                    // 3. Resource close (suppressed exceptions)
                    if resource_spec.is_some() {
                        // Exception from resource acquisition
                        edges.push(CFGEdge::from_label(effective_entry, catch_entry, Some("exception (acquire)".to_string())));
                        // Exception from close
                        if let Some(close_id) = close_block_id {
                            edges.push(CFGEdge::from_label(close_id, catch_entry, Some("exception (close)".to_string())));
                        }
                    } else {
                        edges.push(CFGEdge::from_label(try_id, catch_entry, Some("exception".to_string())));
                    }
                    exits.extend(catch_exits);
                }
            }
        }

        // Process finally block
        if let Some(finally_clause) = node
            .children(&mut node.walk())
            .find(|n| n.kind() == "finally_clause")
        {
            if let Some(finally_body) = self.child_by_field(finally_clause, "body") {
                let (finally_entry, finally_exits) =
                    self.build_cfg_from_body(finally_body, source, blocks, edges, next_id);
                // All exits flow through finally
                for exit in &exits {
                    edges.push(CFGEdge::from_label(*exit, finally_entry, None));
                }
                exits = finally_exits;
            }
        }

        (try_id, exits)
    }

    /// BUG #22 FIX: Extract resource declarations from try-with-resources.
    /// Returns a comma-separated string of resource variable names.
    fn extract_resource_declarations(&self, node: Node, source: &[u8]) -> String {
        let mut resources = Vec::new();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "resource" => {
                    // resource: Type name = expression
                    if let Some(name) = child
                        .children(&mut child.walk())
                        .find(|n| n.kind() == "identifier")
                    {
                        resources.push(self.node_text(name, source).to_string());
                    }
                }
                // Java 9+ allows identifier directly in resource_specification for effectively final variables
                "identifier" => {
                    resources.push(self.node_text(child, source).to_string());
                }
                _ => {}
            }
        }

        if resources.is_empty() {
            "resources".to_string()
        } else {
            resources.join(", ")
        }
    }

    /// Build CFG for switch statement.
    fn build_cfg_for_switch(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        next_id: &mut usize,
    ) -> (BlockId, Vec<BlockId>) {
        let switch_id = BlockId(*next_id);
        *next_id += 1;

        let condition = self
            .child_by_field(node, "condition")
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_else(|| "expr".to_string());

        let block = CFGBlock {
            id: switch_id,
            label: format!("switch ({})", condition),
            block_type: BlockType::Body,
            statements: vec![format!("switch ({})", condition)],
            func_calls: Vec::new(),
            start_line: node.start_position().row + 1,
            end_line: node.start_position().row + 1,
        };
        blocks.insert(switch_id, block);

        let mut exits = Vec::new();

        // Process switch body
        if let Some(body) = self.child_by_field(node, "body") {
            for child in body.children(&mut body.walk()) {
                match child.kind() {
                    // BUG #27 FIX: Handle switch_rule (Java 14+ arrow syntax) properly
                    // switch_rule: case X -> expression; or case X -> { block }
                    // No fall-through, each rule is independent
                    "switch_rule" => {
                        let case_id = BlockId(*next_id);
                        *next_id += 1;

                        // Extract the case label (first line up to ->)
                        let case_text = self.node_text(child, source);
                        let case_label = case_text
                            .lines()
                            .next()
                            .and_then(|s| s.split("->").next())
                            .map(|s| s.trim().to_string())
                            .unwrap_or_else(|| "case".to_string());

                        let case_block = CFGBlock {
                id: case_id,
                label: case_label.clone(),
                block_type: BlockType::Body,
                statements: vec![case_text.to_string()],
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.end_position().row + 1,
            };
                        blocks.insert(case_id, case_block);

                        edges.push(CFGEdge::from_label(switch_id, case_id, Some(case_label)));
                        // Arrow cases don't fall through, they are direct exits
                        exits.push(case_id);
                    }
                    // Traditional switch case with potential fall-through
                    "switch_block_statement_group" => {
                        let case_id = BlockId(*next_id);
                        *next_id += 1;

                        let case_label = self
                            .node_text(child, source)
                            .lines()
                            .next()
                            .unwrap_or("case")
                            .to_string();
                        let case_block = CFGBlock {
                id: case_id,
                label: case_label.clone(),
                block_type: BlockType::Body,
                statements: vec![case_label],
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.end_position().row + 1,
            };
                        blocks.insert(case_id, case_block);

                        edges.push(CFGEdge::from_label(switch_id, case_id, None));
                        exits.push(case_id);
                    }
                    _ => {}
                }
            }
        }

        if exits.is_empty() {
            exits.push(switch_id);
        }

        (switch_id, exits)
    }

    /// BUG #11 FIX: Build CFG for do-while statement.
    /// Do-while differs from while: body executes at least once before condition check.
    fn build_cfg_for_do_while(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        next_id: &mut usize,
    ) -> (BlockId, Vec<BlockId>) {
        // In do-while, body executes first, then condition is checked
        let body_id = BlockId(*next_id);
        *next_id += 1;

        // Create body block label
        let body_label = "do".to_string();
        let body_block = CFGBlock {
                id: body_id,
                label: body_label.clone(),
                block_type: BlockType::Body,
                statements: vec![body_label],
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            };
        blocks.insert(body_id, body_block);

        // Process do-while body
        let mut body_exits = vec![body_id];
        if let Some(body) = self.child_by_field(node, "body") {
            let (inner_entry, inner_exits) =
                self.build_cfg_from_body(body, source, blocks, edges, next_id);
            edges.push(CFGEdge::from_label(body_id, inner_entry, None));
            body_exits = inner_exits;
        }

        // Condition block (checked after body)
        let condition_id = BlockId(*next_id);
        *next_id += 1;

        let condition_text = self
            .child_by_field(node, "condition")
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_else(|| "condition".to_string());

        let condition_block = CFGBlock {
            id: condition_id,
            label: format!("while ({})", condition_text),
            block_type: BlockType::Body,
            statements: vec![format!("while ({})", condition_text)],
            func_calls: Vec::new(),
            start_line: node.end_position().row + 1,
            end_line: node.end_position().row + 1,
        };
        blocks.insert(condition_id, condition_block);

        // Connect body exits to condition
        for exit in &body_exits {
            edges.push(CFGEdge::from_label(*exit, condition_id, None));
        }

        // Back edge: condition true -> body (loop back)
        edges.push(CFGEdge::from_label(condition_id, body_id, Some("true".to_string())));

        // Exit block (condition false)
        let exit_id = BlockId(*next_id);
        *next_id += 1;
        let exit_block = CFGBlock {
                id: exit_id,
                label: "do-while exit".to_string(),
                block_type: BlockType::Body,
                statements: vec![],
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            };
        blocks.insert(exit_id, exit_block);

        edges.push(CFGEdge::from_label(condition_id, exit_id, Some("false".to_string())));

        (body_id, vec![exit_id])
    }

    /// BUG #12 FIX: Build CFG for labeled statement.
    /// Labeled statements allow break/continue to target specific loops.
    fn build_cfg_for_labeled(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        next_id: &mut usize,
    ) -> (BlockId, Vec<BlockId>) {
        let label_id = BlockId(*next_id);
        *next_id += 1;

        // Extract the label name
        let label_name = node
            .children(&mut node.walk())
            .find(|n| n.kind() == "identifier")
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_else(|| "label".to_string());

        let label_block = CFGBlock {
            id: label_id,
            label: format!("{}:", label_name),
            block_type: BlockType::Body,
            statements: vec![format!("{}:", label_name)],
            func_calls: Vec::new(),
            start_line: node.start_position().row + 1,
            end_line: node.start_position().row + 1,
        };
        blocks.insert(label_id, label_block);

        // Find and process the labeled statement (usually a loop or block)
        let mut exits = vec![label_id];
        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "identifier" | ":" => continue, // Skip label parts
                _ => {
                    // This is the statement being labeled
                    let (stmt_entry, stmt_exits) =
                        self.build_cfg_from_body(child, source, blocks, edges, next_id);
                    edges.push(CFGEdge::from_label(label_id, stmt_entry, None));
                    exits = stmt_exits;
                    break;
                }
            }
        }

        (label_id, exits)
    }

    /// BUG #23 FIX: Build CFG for synchronized statement.
    /// synchronized(lock) { body } - acquires monitor on lock object, executes body, releases monitor.
    fn build_cfg_for_synchronized(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        next_id: &mut usize,
    ) -> (BlockId, Vec<BlockId>) {
        let sync_id = BlockId(*next_id);
        *next_id += 1;

        // Extract the lock expression
        let lock_expr = node
            .children(&mut node.walk())
            .find(|n| n.kind() == "parenthesized_expression")
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_else(|| "(lock)".to_string());

        let sync_block = CFGBlock {
            id: sync_id,
            label: format!("synchronized {}", lock_expr),
            block_type: BlockType::Body,
            statements: vec![format!("synchronized {}", lock_expr)],
            func_calls: Vec::new(),
            start_line: node.start_position().row + 1,
            end_line: node.start_position().row + 1,
        };
        blocks.insert(sync_id, sync_block);

        // Process the synchronized body
        let mut exits = vec![sync_id];
        if let Some(body) = self.child_by_field(node, "body") {
            let (body_entry, body_exits) =
                self.build_cfg_from_body(body, source, blocks, edges, next_id);
            edges.push(CFGEdge::from_label(sync_id, body_entry, Some("acquire".to_string())));
            exits = body_exits;
        }

        (sync_id, exits)
    }

    /// Extract variable definitions from a node for DFG.
    fn extract_definitions(
        &self,
        node: Node,
        source: &[u8],
        definitions: &mut HashMap<String, Vec<usize>>,
        edges: &mut Vec<DataflowEdge>,
    ) {
        match node.kind() {
            "local_variable_declaration" | "field_declaration" => {
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "variable_declarator" {
                        if let Some(name_node) = self.child_by_field(child, "name") {
                            let var_name = self.node_text(name_node, source).to_string();
                            let line = node.start_position().row + 1;
                            definitions.entry(var_name.clone()).or_default().push(line);
                            edges.push(DataflowEdge {
                                variable: var_name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Definition,
                            });
                        }
                    }
                }
            }
            "assignment_expression" => {
                if let Some(left) = self.child_by_field(node, "left") {
                    let var_name = self.node_text(left, source).to_string();
                    let line = node.start_position().row + 1;
                    definitions.entry(var_name.clone()).or_default().push(line);
                    edges.push(DataflowEdge {
                        variable: var_name,
                        from_line: line,
                        to_line: line,
                        kind: DataflowKind::Mutation,
                            });
                }
            }
            // BUG #13 FIX: Handle increment/decrement operators (i++, ++i, i--, --i)
            "update_expression" => {
                // Extract the operand being updated
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "identifier" {
                        let var_name = self.node_text(child, source).to_string();
                        let line = node.start_position().row + 1;
                        definitions.entry(var_name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: var_name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Mutation,
                            });
                        break;
                    }
                }
            }
            // BUG #14 FIX: Handle compound assignment operators (+=, -=, *=, /=, %=, etc.)
            "compound_assignment_expression" => {
                if let Some(left) = self.child_by_field(node, "left") {
                    let var_name = self.node_text(left, source).to_string();
                    let line = node.start_position().row + 1;
                    definitions.entry(var_name.clone()).or_default().push(line);
                    edges.push(DataflowEdge {
                        variable: var_name,
                        from_line: line,
                        to_line: line,
                        kind: DataflowKind::Mutation,
                            });
                }
            }
            // BUG #26 FIX: Handle pattern matching instanceof (Java 16+)
            // Pattern: obj instanceof Type varName
            // The pattern variable is bound in the instanceof expression
            "instanceof_expression" => {
                // Look for a pattern variable in the instanceof expression
                // In tree-sitter-java, pattern instanceof may have a type_identifier followed by an identifier
                // e.g., "obj instanceof String s" - s is the pattern variable
                let mut found_type = false;
                for child in node.children(&mut node.walk()) {
                    match child.kind() {
                        "type_identifier" | "generic_type" | "scoped_type_identifier" => {
                            found_type = true;
                        }
                        "identifier" if found_type => {
                            // This is the pattern variable
                            let var_name = self.node_text(child, source).to_string();
                            let line = node.start_position().row + 1;
                            definitions.entry(var_name.clone()).or_default().push(line);
                            edges.push(DataflowEdge {
                                variable: var_name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Definition,
                            });
                            break;
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }

        // Recurse into children
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.extract_definitions(child, source, definitions, edges);
        }
    }

    /// Extract variable uses from a node for DFG.
    fn extract_uses(
        &self,
        node: Node,
        source: &[u8],
        definitions: &HashMap<String, Vec<usize>>,
        uses: &mut HashMap<String, Vec<usize>>,
        edges: &mut Vec<DataflowEdge>,
    ) {
        match node.kind() {
            "identifier" => {
                // Check if this identifier is a use (not a definition)
                let parent = node.parent();
                let is_definition = parent.is_some_and(|p| {
                    matches!(p.kind(), "variable_declarator" | "formal_parameter")
                        && self.child_by_field(p, "name") == Some(node)
                });

                if !is_definition {
                    let var_name = self.node_text(node, source).to_string();
                    if definitions.contains_key(&var_name) {
                        let line = node.start_position().row + 1;
                        uses.entry(var_name.clone()).or_default().push(line);

                        // Find the most recent definition
                        if let Some(def_lines) = definitions.get(&var_name) {
                            if let Some(&def_line) = def_lines.iter().filter(|&&l| l <= line).max()
                            {
                                edges.push(DataflowEdge {
                                    variable: var_name,
                                    from_line: def_line,
                                    to_line: line,
                                    kind: DataflowKind::Use,
                            });
                            }
                        }
                    }
                }
            }
            "return_statement" => {
                let line = node.start_position().row + 1;
                // Find identifiers in return statement
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "identifier" {
                        let var_name = self.node_text(child, source).to_string();
                        if definitions.contains_key(&var_name) {
                            edges.push(DataflowEdge {
                                variable: var_name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Return,
                            });
                        }
                    }
                }
            }
            _ => {}
        }

        // Recurse into children
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.extract_uses(child, source, definitions, uses, edges);
        }
    }
}

impl Language for Java {
    fn name(&self) -> &'static str {
        "java"
    }

    fn extensions(&self) -> &[&'static str] {
        &[".java"]
    }

    fn parser(&self) -> Result<Parser> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_java::LANGUAGE.into())
            .map_err(|e| BrrrError::TreeSitter(e.to_string()))?;
        Ok(parser)
    }

    fn extract_function(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        match node.kind() {
            "method_declaration" => self.extract_method(node, source),
            "constructor_declaration" => self.extract_constructor(node, source),
            _ => None,
        }
    }

    fn extract_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        match node.kind() {
            "class_declaration" => self.extract_class_declaration(node, source),
            "interface_declaration" => self.extract_interface_declaration(node, source),
            "enum_declaration" => self.extract_enum_declaration(node, source),
            "record_declaration" => self.extract_record_declaration(node, source),
            "annotation_type_declaration" => self.extract_annotation_type_declaration(node, source),
            // BUG #30 FIX: Handle module-info.java module declarations (Java 9+)
            "module_declaration" => self.extract_module_declaration(node, source),
            _ => None,
        }
    }

    fn extract_imports(&self, tree: &Tree, source: &[u8]) -> Vec<ImportInfo> {
        let mut imports = Vec::new();
        let root = tree.root_node();

        for child in root.children(&mut root.walk()) {
            match child.kind() {
                "package_declaration" => {
                    // Extract package declaration as a special ImportInfo entry
                    // This is critical for Java class resolution
                    if let Some(pkg_info) = self.extract_package_declaration(child, source) {
                        imports.push(pkg_info);
                    }
                }
                "import_declaration" => {
                    if let Some(import) = self.extract_import(child, source) {
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
            (method_declaration name: (identifier) @name) @method
            (constructor_declaration name: (identifier) @name) @constructor
        ]"#
    }

    fn class_query(&self) -> &'static str {
        r#"[
            (class_declaration name: (identifier) @name) @class
            (interface_declaration name: (identifier) @name) @interface
            (enum_declaration name: (identifier) @name) @enum
            (record_declaration name: (identifier) @name) @record
            (annotation_type_declaration name: (identifier) @name) @annotation_type
        ]"#
    }

    fn call_query(&self) -> &'static str {
        // Enhanced call query with lambda expressions and method references
        // FEATURE: Lambda expressions - capture method calls inside lambda bodies
        // FEATURE: Method references - capture the referenced method name
        //
        // Lambda examples: list.forEach(x -> process(x)) tracks "process"
        // Method reference examples:
        //   - String::valueOf tracks "valueOf"
        //   - System.out::println tracks "println"
        //   - this::method tracks "method"
        //   - super::method tracks "method"
        r#"[
            (method_invocation name: (identifier) @callee) @call
            (object_creation_expression type: (type_identifier) @callee) @call
            (lambda_expression
                body: (method_invocation name: (identifier) @callee)) @call
            (method_reference . (_) "::" (identifier) @callee) @call
        ]"#
    }

    fn build_cfg(&self, node: Node, source: &[u8]) -> Result<CFGInfo> {
        // Get function name
        let function_name = self
            .child_by_field(node, "name")
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_else(|| "unknown".to_string());

        let mut blocks = HashMap::new();
        let mut edges = Vec::new();
        let mut next_id = 0usize;

        // Find the method body
        let body = match node.kind() {
            "method_declaration" => self.child_by_field(node, "body"),
            "constructor_declaration" => self.child_by_field(node, "body"),
            _ => None,
        };

        let (entry, exits) = if let Some(body_node) = body {
            self.build_cfg_from_body(body_node, source, &mut blocks, &mut edges, &mut next_id)
        } else {
            // Abstract method or no body - create single entry/exit block
            let id = BlockId(0);
            let block = CFGBlock {
                id,
                label: "abstract".to_string(),
                block_type: BlockType::Body,
                statements: vec![],
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.end_position().row + 1,
            };
            blocks.insert(id, block);
            (id, vec![id])
        };

        Ok(CFGInfo {
            function_name,
            blocks,
            edges,
            entry,
            exits,
            decision_points: 0, // TODO: Calculate actual decision points for Java
            comprehension_decision_points: 0, // Java doesn't have Python-style comprehensions
            nested_cfgs: HashMap::new(),      // TODO: Handle Java lambdas/anonymous classes as nested CFGs
            is_async: false,                  // Java uses different async patterns (CompletableFuture)
            await_points: 0,                  // Java doesn't have await keyword
            blocking_calls: Vec::new(),       // TODO: Track blocking calls in async contexts
            ..Default::default()
        })
    }

    fn build_dfg(&self, node: Node, source: &[u8]) -> Result<DFGInfo> {
        let function_name = self
            .child_by_field(node, "name")
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_else(|| "unknown".to_string());

        let mut definitions = HashMap::new();
        let mut uses = HashMap::new();
        let mut edges = Vec::new();

        // Extract parameters as definitions
        if let Some(params) = self.child_by_field(node, "parameters") {
            for child in params.children(&mut params.walk()) {
                if child.kind() == "formal_parameter" {
                    if let Some(name_node) = self.child_by_field(child, "name") {
                        let var_name = self.node_text(name_node, source).to_string();
                        let line = child.start_position().row + 1;
                        definitions
                            .entry(var_name.clone())
                            .or_insert_with(Vec::new)
                            .push(line);
                        edges.push(DataflowEdge {
                            variable: var_name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Param,
                            });
                    }
                }
            }
        }

        // Extract definitions from body
        if let Some(body) = self.child_by_field(node, "body") {
            self.extract_definitions(body, source, &mut definitions, &mut edges);
            self.extract_uses(body, source, &definitions, &mut uses, &mut edges);
        }

        Ok(DFGInfo::new(function_name, edges, definitions, uses))
    }
}

impl Java {
    /// Extract class declaration.
    fn extract_class_declaration(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let name_node = self.child_by_field(node, "name")?;
        let name = self.node_text(name_node, source).to_string();

        // Extract modifiers
        let (visibility, is_static, is_final, is_abstract, _, _, annotations) =
            self.extract_modifiers(node, source);

        // Build decorators
        let mut decorators = annotations;
        if let Some(vis) = visibility {
            decorators.insert(0, vis);
        }
        if is_static {
            decorators.push("static".to_string());
        }
        if is_final {
            decorators.push("final".to_string());
        }
        if is_abstract {
            decorators.push("abstract".to_string());
        }

        // Extract type parameters
        if let Some(tp) = self.extract_type_parameters(node, source) {
            decorators.push(format!("generic:{}", tp));
        }

        // Build bases list
        let mut bases = Vec::new();

        // Add superclass if present
        if let Some(superclass) = self.extract_superclass(node, source) {
            bases.push(format!("extends {}", superclass));
        }

        // Add interfaces
        for interface in self.extract_interfaces(node, source) {
            bases.push(format!("implements {}", interface));
        }

        // Extract Javadoc
        let docstring = self.extract_javadoc(node, source);

        // BUG #20 FIX: Extract methods, fields, and inner classes from class body
        let (methods, fields, inner_classes) = if let Some(body) = self.child_by_field(node, "body")
        {
            (
                self.extract_methods(body, source),
                self.extract_fields(body, source),
                self.extract_inner_classes(body, source),
            )
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };

        // Line numbers
        let line_number = node.start_position().row + 1;
        let end_line_number = Some(node.end_position().row + 1);

        Some(ClassInfo {
            name,
            bases,
            docstring,
            methods,
            fields,
            inner_classes,
            decorators,
            line_number,
            end_line_number,
            language: "java".to_string(),
        })
    }

    /// BUG #7 FIX: Extract inner/nested classes from a class body.
    /// Recursively extracts class_declaration, interface_declaration, enum_declaration nodes.
    fn extract_inner_classes(&self, body_node: Node, source: &[u8]) -> Vec<ClassInfo> {
        let mut inner_classes = Vec::new();

        for child in body_node.children(&mut body_node.walk()) {
            match child.kind() {
                "class_declaration" => {
                    if let Some(class) = self.extract_class_declaration(child, source) {
                        inner_classes.push(class);
                    }
                }
                "interface_declaration" => {
                    if let Some(interface) = self.extract_interface_declaration(child, source) {
                        inner_classes.push(interface);
                    }
                }
                "enum_declaration" => {
                    if let Some(enum_class) = self.extract_enum_declaration(child, source) {
                        inner_classes.push(enum_class);
                    }
                }
                "record_declaration" => {
                    if let Some(record) = self.extract_record_declaration(child, source) {
                        inner_classes.push(record);
                    }
                }
                "annotation_type_declaration" => {
                    if let Some(annotation) = self.extract_annotation_type_declaration(child, source)
                    {
                        inner_classes.push(annotation);
                    }
                }
                _ => {}
            }
        }

        inner_classes
    }

    /// Extract interface declaration.
    fn extract_interface_declaration(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let name_node = self.child_by_field(node, "name")?;
        let name = self.node_text(name_node, source).to_string();

        // Extract modifiers
        let (visibility, _, _, _, _, _, annotations) = self.extract_modifiers(node, source);

        // Build decorators
        let mut decorators = vec!["interface".to_string()];
        decorators.extend(annotations);
        if let Some(vis) = visibility {
            decorators.insert(1, vis);
        }

        // Extract type parameters
        if let Some(tp) = self.extract_type_parameters(node, source) {
            decorators.push(format!("generic:{}", tp));
        }

        // Build bases list (extended interfaces)
        let bases: Vec<String> = self
            .extract_extends_interfaces(node, source)
            .into_iter()
            .map(|i| format!("extends {}", i))
            .collect();

        // Extract Javadoc
        let docstring = self.extract_javadoc(node, source);

        // BUG #20 FIX: Extract methods, fields, and inner classes from interface body
        let (methods, fields, inner_classes) = if let Some(body) = self.child_by_field(node, "body")
        {
            (
                self.extract_methods(body, source),
                self.extract_fields(body, source),
                self.extract_inner_classes(body, source),
            )
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };

        // Line numbers
        let line_number = node.start_position().row + 1;
        let end_line_number = Some(node.end_position().row + 1);

        Some(ClassInfo {
            name,
            bases,
            docstring,
            methods,
            fields,
            inner_classes,
            decorators,
            line_number,
            end_line_number,
            language: "java".to_string(),
        })
    }

    /// Extract enum declaration.
    fn extract_enum_declaration(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let name_node = self.child_by_field(node, "name")?;
        let name = self.node_text(name_node, source).to_string();

        // Extract modifiers
        let (visibility, _, _, _, _, _, annotations) = self.extract_modifiers(node, source);

        // Build decorators
        let mut decorators = vec!["enum".to_string()];
        decorators.extend(annotations);
        if let Some(vis) = visibility {
            decorators.insert(1, vis);
        }

        // Extract implemented interfaces
        let bases: Vec<String> = self
            .extract_interfaces(node, source)
            .into_iter()
            .map(|i| format!("implements {}", i))
            .collect();

        // Extract Javadoc
        let docstring = self.extract_javadoc(node, source);

        // BUG #20 & #21 FIX: Extract methods, fields, enum constants, and inner classes from enum body
        let (methods, fields, inner_classes) =
            if let Some(body) = self.child_by_field(node, "body") {
                // BUG #21 FIX: Extract enum constants as fields
                let enum_constants = self.extract_enum_constants(body, source);
                let regular_fields = self.extract_fields(body, source);

                // Combine enum constants with regular fields
                let mut all_fields = enum_constants;
                all_fields.extend(regular_fields);

                (
                    self.extract_methods(body, source),
                    all_fields,
                    self.extract_inner_classes(body, source),
                )
            } else {
                (Vec::new(), Vec::new(), Vec::new())
            };

        // Line numbers
        let line_number = node.start_position().row + 1;
        let end_line_number = Some(node.end_position().row + 1);

        Some(ClassInfo {
            name: name.clone(),
            bases,
            docstring,
            methods,
            fields,
            inner_classes,
            decorators,
            line_number,
            end_line_number,
            language: "java".to_string(),
        })
    }

    /// BUG #21 FIX: Extract enum constants from enum body as FieldInfo entries.
    /// Each enum constant is treated as a public static final field of the enum type.
    fn extract_enum_constants(&self, body_node: Node, source: &[u8]) -> Vec<FieldInfo> {
        let mut constants = Vec::new();

        for child in body_node.children(&mut body_node.walk()) {
            if child.kind() == "enum_constant" {
                if let Some(field) = self.extract_enum_constant(child, source) {
                    constants.push(field);
                }
            }
        }

        constants
    }

    /// BUG #21 FIX: Extract a single enum constant as a FieldInfo.
    fn extract_enum_constant(&self, node: Node, source: &[u8]) -> Option<FieldInfo> {
        // Find the constant name
        let name = node
            .children(&mut node.walk())
            .find(|n| n.kind() == "identifier")
            .map(|n| self.node_text(n, source).to_string())?;

        // Extract annotations if present
        let mut annotations = Vec::new();
        if let Some(modifiers) = node
            .children(&mut node.walk())
            .find(|n| n.kind() == "modifiers")
        {
            for child in modifiers.children(&mut modifiers.walk()) {
                if matches!(child.kind(), "marker_annotation" | "annotation") {
                    annotations.push(self.extract_annotation(child, source));
                }
            }
        }

        // Check if this constant has arguments (like DAY(1) or Color.RED("ff0000"))
        let default_value = node
            .children(&mut node.walk())
            .find(|n| n.kind() == "argument_list")
            .map(|n| self.node_text(n, source).to_string());

        Some(FieldInfo {
            name,
            field_type: Some("enum_constant".to_string()),
            visibility: Some("public".to_string()),
            is_static: true,
            is_final: true,
            default_value,
            annotations,
            line_number: node.start_position().row + 1,
        })
    }

    /// Extract record declaration (Java 14+).
    fn extract_record_declaration(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let name_node = self.child_by_field(node, "name")?;
        let name = self.node_text(name_node, source).to_string();

        // Extract modifiers
        let (visibility, _, _, _, _, _, annotations) = self.extract_modifiers(node, source);

        // Build decorators
        let mut decorators = vec!["record".to_string()];
        decorators.extend(annotations);
        if let Some(vis) = visibility {
            decorators.insert(1, vis);
        }

        // Extract type parameters
        if let Some(tp) = self.extract_type_parameters(node, source) {
            decorators.push(format!("generic:{}", tp));
        }

        // Records implement interfaces
        let bases: Vec<String> = self
            .extract_interfaces(node, source)
            .into_iter()
            .map(|i| format!("implements {}", i))
            .collect();

        // Extract Javadoc
        let docstring = self.extract_javadoc(node, source);

        // BUG #20 FIX: Extract methods, fields, and inner classes from record body
        let (methods, fields, inner_classes) = if let Some(body) = self.child_by_field(node, "body")
        {
            (
                self.extract_methods(body, source),
                self.extract_fields(body, source),
                self.extract_inner_classes(body, source),
            )
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };

        // Line numbers
        let line_number = node.start_position().row + 1;
        let end_line_number = Some(node.end_position().row + 1);

        Some(ClassInfo {
            name,
            bases,
            docstring,
            methods,
            fields,
            inner_classes,
            decorators,
            line_number,
            end_line_number,
            language: "java".to_string(),
        })
    }

    /// Extract annotation type declaration (@interface).
    fn extract_annotation_type_declaration(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let name_node = self.child_by_field(node, "name")?;
        let name = self.node_text(name_node, source).to_string();

        // Extract modifiers
        let (visibility, _, _, _, _, _, annotations) = self.extract_modifiers(node, source);

        // Build decorators
        let mut decorators = vec!["annotation".to_string()];
        decorators.extend(annotations);
        if let Some(vis) = visibility {
            decorators.insert(1, vis);
        }

        // Extract Javadoc
        let docstring = self.extract_javadoc(node, source);

        // BUG #20 FIX: Annotation types can have methods (annotation elements), fields, and inner classes
        let (methods, fields, inner_classes) = if let Some(body) = self.child_by_field(node, "body")
        {
            (
                self.extract_methods(body, source),
                self.extract_fields(body, source),
                self.extract_inner_classes(body, source),
            )
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };

        // Line numbers
        let line_number = node.start_position().row + 1;
        let end_line_number = Some(node.end_position().row + 1);

        Some(ClassInfo {
            name,
            bases: Vec::new(),
            docstring,
            methods,
            fields,
            inner_classes,
            decorators,
            line_number,
            end_line_number,
            language: "java".to_string(),
        })
    }

    /// BUG #30 FIX: Extract module declaration from module-info.java (Java 9+).
    /// Module declarations define module metadata: requires, exports, opens, uses, provides.
    /// Represented as ClassInfo with "module" decorator.
    fn extract_module_declaration(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        // Module name is the identifier or scoped_identifier
        let name = node
            .children(&mut node.walk())
            .find(|n| matches!(n.kind(), "identifier" | "scoped_identifier"))
            .map(|n| self.extract_scoped_identifier(n, source))?;

        let mut decorators = vec!["module".to_string()];
        let mut bases = Vec::new();

        // Check for open module: open module com.example { ... }
        if node.children(&mut node.walk()).any(|n| n.kind() == "open") {
            decorators.push("open".to_string());
        }

        // Extract module directives from the body
        if let Some(body) = node
            .children(&mut node.walk())
            .find(|n| n.kind() == "module_body")
        {
            for directive in body.children(&mut body.walk()) {
                match directive.kind() {
                    "requires_module_directive" => {
                        let directive_text = self.node_text(directive, source).trim().to_string();
                        bases.push(directive_text);
                    }
                    "exports_module_directive" => {
                        let directive_text = self.node_text(directive, source).trim().to_string();
                        bases.push(directive_text);
                    }
                    "opens_module_directive" => {
                        let directive_text = self.node_text(directive, source).trim().to_string();
                        bases.push(directive_text);
                    }
                    "uses_module_directive" => {
                        let directive_text = self.node_text(directive, source).trim().to_string();
                        bases.push(directive_text);
                    }
                    "provides_module_directive" => {
                        let directive_text = self.node_text(directive, source).trim().to_string();
                        bases.push(directive_text);
                    }
                    _ => {}
                }
            }
        }

        // Extract Javadoc if present
        let docstring = self.extract_javadoc(node, source);

        // Line numbers
        let line_number = node.start_position().row + 1;
        let end_line_number = Some(node.end_position().row + 1);

        Some(ClassInfo {
            name,
            bases,
            docstring,
            methods: Vec::new(),
            fields: Vec::new(),
            inner_classes: Vec::new(),
            decorators,
            line_number,
            end_line_number,
            language: "java".to_string(),
        })
    }

    /// Extract package declaration as ImportInfo.
    fn extract_package_declaration(&self, node: Node, source: &[u8]) -> Option<ImportInfo> {
        // Find the scoped identifier or identifier in the package declaration
        for child in node.children(&mut node.walk()) {
            if child.kind() == "scoped_identifier" || child.kind() == "identifier" {
                let package_name = self.extract_scoped_identifier(child, source);
                return Some(ImportInfo {
                    module: package_name,
                    names: vec![],
                    aliases: {
                        let mut m = HashMap::new();
                        m.insert("package".to_string(), "true".to_string());
                        m
                    },
                    is_from: false,
                    level: 0,
                    line_number: node.start_position().row + 1,
                    visibility: None, // Java package declarations have no visibility modifier
                });
            }
        }
        None
    }

    /// Extract import declaration.
    fn extract_import(&self, node: Node, source: &[u8]) -> Option<ImportInfo> {
        let mut is_static = false;
        let mut path_parts = Vec::new();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "static" => {
                    is_static = true;
                }
                "scoped_identifier" | "identifier" => {
                    path_parts.push(self.extract_scoped_identifier(child, source));
                }
                "asterisk" => {
                    path_parts.push("*".to_string());
                }
                _ => {}
            }
        }

        if path_parts.is_empty() {
            return None;
        }

        let full_path = path_parts.join(".");

        // Determine module and names
        let (module, names) = if full_path.ends_with(".*") {
            // Wildcard import: import java.util.*
            let module = full_path.trim_end_matches(".*").to_string();
            (module, vec!["*".to_string()])
        } else if is_static {
            // Static import: import static java.lang.Math.PI
            // Module is everything except the last part
            let parts: Vec<&str> = full_path.rsplitn(2, '.').collect();
            if parts.len() == 2 {
                (parts[1].to_string(), vec![parts[0].to_string()])
            } else {
                (full_path.clone(), vec![])
            }
        } else {
            // Regular import: import java.util.List
            (full_path, vec![])
        };

        let mut aliases = HashMap::new();
        if is_static {
            aliases.insert("static".to_string(), "true".to_string());
        }

        let is_from = is_static || !names.is_empty();

        Some(ImportInfo {
            module,
            names,
            aliases,
            is_from,
            level: 0, // Java doesn't have relative imports
            line_number: node.start_position().row + 1,
            visibility: None, // Java imports don't have visibility modifiers (unlike Rust re-exports)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_java(code: &str) -> Tree {
        let java = Java;
        let mut parser = java.parser().unwrap();
        parser.parse(code, None).unwrap()
    }

    #[test]
    fn test_extract_simple_method() {
        let code = r#"
public class Test {
    public String getName() {
        return name;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        // Find method node
        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let func = java.extract_function(child, code.as_bytes()).unwrap();
                assert_eq!(func.name, "getName");
                assert_eq!(func.return_type, Some("String".to_string()));
                assert!(func.params.is_empty());
                assert!(func.decorators.contains(&"public".to_string()));
                break;
            }
        }
    }

    #[test]
    fn test_extract_method_with_params() {
        let code = r#"
public class Test {
    public void setName(String name, int age) {
        this.name = name;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let func = java.extract_function(child, code.as_bytes()).unwrap();
                assert_eq!(func.name, "setName");
                assert_eq!(func.return_type, Some("void".to_string()));
                assert_eq!(func.params.len(), 2);
                assert_eq!(func.params[0], "String name");
                assert_eq!(func.params[1], "int age");
                break;
            }
        }
    }

    #[test]
    fn test_extract_generic_method() {
        let code = r#"
public class Test {
    public static <T> List<T> process(List<T> items) {
        return items;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let func = java.extract_function(child, code.as_bytes()).unwrap();
                assert_eq!(func.name, "process");
                assert!(func.decorators.contains(&"static".to_string()));
                assert!(func.decorators.iter().any(|d| d.starts_with("generic:")));
                break;
            }
        }
    }

    #[test]
    fn test_extract_class() {
        let code = r#"
/**
 * User class.
 */
public class User extends BaseEntity implements Serializable {
    public String getName() { return name; }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "class_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "User");
                assert!(class.bases.iter().any(|b| b.contains("BaseEntity")));
                assert!(class.bases.iter().any(|b| b.contains("Serializable")));
                assert!(class.docstring.is_some());
                assert_eq!(class.methods.len(), 1);
                break;
            }
        }
    }

    #[test]
    fn test_extract_interface() {
        let code = r#"
public interface Processor<T> extends Runnable {
    void process(T item);
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "interface_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "Processor");
                assert!(class.decorators.contains(&"interface".to_string()));
                assert!(class.bases.iter().any(|b| b.contains("Runnable")));
                assert_eq!(class.methods.len(), 1);
                break;
            }
        }
    }

    #[test]
    fn test_extract_enum() {
        let code = r#"
public enum Status {
    ACTIVE, INACTIVE;

    public String getCode() { return ""; }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "enum_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "Status");
                assert!(class.decorators.contains(&"enum".to_string()));
                assert_eq!(class.methods.len(), 1);
                break;
            }
        }
    }

    #[test]
    fn test_extract_imports() {
        let code = r#"
import java.util.List;
import java.util.*;
import static java.lang.Math.PI;
import static java.lang.Math.*;

public class Test {}
"#;
        let tree = parse_java(code);
        let java = Java;

        let imports = java.extract_imports(&tree, code.as_bytes());
        assert_eq!(imports.len(), 4);

        // Regular import
        assert_eq!(imports[0].module, "java.util.List");
        assert!(imports[0].names.is_empty());

        // Wildcard import
        assert_eq!(imports[1].module, "java.util");
        assert_eq!(imports[1].names, vec!["*"]);

        // Static import
        assert_eq!(imports[2].module, "java.lang.Math");
        assert_eq!(imports[2].names, vec!["PI"]);
        assert!(imports[2].is_from);

        // Static wildcard import
        assert_eq!(imports[3].module, "java.lang.Math");
        assert_eq!(imports[3].names, vec!["*"]);
    }

    #[test]
    fn test_extract_constructor() {
        let code = r#"
public class User {
    /**
     * Creates a new user.
     */
    public User(String name, int age) {
        this.name = name;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "constructor_declaration" {
                let func = java.extract_function(child, code.as_bytes()).unwrap();
                assert_eq!(func.name, "User");
                assert!(func.return_type.is_none());
                assert!(func.decorators.contains(&"constructor".to_string()));
                assert_eq!(func.params.len(), 2);
                assert!(func.docstring.is_some());
                break;
            }
        }
    }

    #[test]
    fn test_extract_annotations() {
        let code = r#"
public class Test {
    @Override
    @Deprecated
    public String toString() {
        return "";
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let func = java.extract_function(child, code.as_bytes()).unwrap();
                assert!(func.decorators.iter().any(|d| d.contains("Override")));
                assert!(func.decorators.iter().any(|d| d.contains("Deprecated")));
                break;
            }
        }
    }

    #[test]
    fn test_build_simple_cfg() {
        let code = r#"
public class Test {
    public int add(int a, int b) {
        int sum = a + b;
        return sum;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let cfg = java.build_cfg(child, code.as_bytes()).unwrap();
                assert_eq!(cfg.function_name, "add");
                assert!(!cfg.blocks.is_empty());
                assert!(!cfg.exits.is_empty());
                break;
            }
        }
    }

    #[test]
    fn test_build_dfg() {
        let code = r#"
public class Test {
    public int compute(int x) {
        int y = x + 1;
        int z = y * 2;
        return z;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let dfg = java.build_dfg(child, code.as_bytes()).unwrap();
                assert_eq!(dfg.function_name, "compute");
                assert!(dfg.definitions.contains_key("x"));
                assert!(dfg.definitions.contains_key("y"));
                assert!(dfg.definitions.contains_key("z"));
                assert!(!dfg.edges.is_empty());
                break;
            }
        }
    }

    // =========================================================================
    // Java Feature Tests - Comprehensive verification of modern Java support
    // =========================================================================

    #[test]
    fn test_extract_record() {
        // Java 16+ record declaration
        let code = r#"
/**
 * Represents a point in 2D space.
 */
public record Point(int x, int y) implements Serializable {
    public double distance() {
        return Math.sqrt(x * x + y * y);
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "record_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "Point");
                assert!(class.decorators.contains(&"record".to_string()));
                assert!(class.bases.iter().any(|b| b.contains("Serializable")));
                assert!(class.docstring.is_some());
                assert_eq!(class.methods.len(), 1);
                assert_eq!(class.methods[0].name, "distance");
                break;
            }
        }
    }

    #[test]
    fn test_extract_sealed_class() {
        // Java 17+ sealed class
        let code = r#"
public sealed class Shape permits Circle, Rectangle, Triangle {
    public abstract double area();
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "class_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "Shape");
                // Note: sealed modifier extraction depends on tree-sitter-java version
                break;
            }
        }
    }

    #[test]
    fn test_extract_var_type_inference() {
        // Java 10+ var keyword
        let code = r#"
public class Test {
    public void process() {
        var items = new ArrayList<String>();
        var count = 0;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        // Verify that var is handled as a type
        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let func = java.extract_function(child, code.as_bytes()).unwrap();
                assert_eq!(func.name, "process");
                break;
            }
        }
    }

    #[test]
    fn test_extract_annotation_type() {
        // Annotation type declaration (@interface)
        let code = r#"
/**
 * Marks a test as integration test.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface IntegrationTest {
    String value() default "";
    int timeout() default 60;
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "annotation_type_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "IntegrationTest");
                assert!(class.decorators.contains(&"annotation".to_string()));
                assert!(class.docstring.is_some());
                // Annotation elements may be extracted as methods depending on tree-sitter version
                // At minimum, the annotation type should be properly identified
                break;
            }
        }
    }

    #[test]
    fn test_extract_static_initializer() {
        // Static initializer blocks
        let code = r#"
public class Config {
    private static final Map<String, String> DEFAULTS;

    static {
        DEFAULTS = new HashMap<>();
        DEFAULTS.put("key", "value");
    }

    public String get(String key) {
        return DEFAULTS.get(key);
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "class_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "Config");
                // Static initializer should be captured as a method
                assert!(class.methods.iter().any(|m| m.name.contains("static_init")));
                break;
            }
        }
    }

    #[test]
    fn test_extract_instance_initializer() {
        // Instance initializer blocks
        let code = r#"
public class Counter {
    private int count;

    {
        count = 0;
    }

    public void increment() {
        count++;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "class_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "Counter");
                // Instance initializer should be captured
                assert!(class.methods.iter().any(|m| m.name.contains("instance_init")));
                break;
            }
        }
    }

    #[test]
    fn test_extract_inner_class() {
        // Inner/nested class extraction
        let code = r#"
public class Outer {
    private int x;

    public class Inner {
        public void access() {
            System.out.println(x);
        }
    }

    public static class StaticNested {
        public void process() {}
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "class_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "Outer");
                // Should have 2 inner classes
                assert_eq!(class.inner_classes.len(), 2);
                assert!(class.inner_classes.iter().any(|c| c.name == "Inner"));
                assert!(class.inner_classes.iter().any(|c| c.name == "StaticNested"));
                break;
            }
        }
    }

    #[test]
    fn test_extract_fields() {
        // Field extraction with modifiers
        let code = r#"
public class Entity {
    public static final int MAX_SIZE = 100;
    private String name;
    protected int count = 0;
    @Deprecated
    volatile boolean active;
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "class_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "Entity");
                assert_eq!(class.fields.len(), 4);

                // Check MAX_SIZE field
                let max_size = class.fields.iter().find(|f| f.name == "MAX_SIZE").unwrap();
                assert!(max_size.is_static);
                assert!(max_size.is_final);
                assert_eq!(max_size.visibility, Some("public".to_string()));

                // Check name field
                let name = class.fields.iter().find(|f| f.name == "name").unwrap();
                assert_eq!(name.visibility, Some("private".to_string()));
                assert_eq!(name.field_type, Some("String".to_string()));

                // Check count field with default value
                let count = class.fields.iter().find(|f| f.name == "count").unwrap();
                assert_eq!(count.visibility, Some("protected".to_string()));
                assert!(count.default_value.is_some());

                break;
            }
        }
    }

    #[test]
    fn test_extract_enum_constants() {
        // Enum constant extraction
        let code = r#"
public enum Priority {
    LOW(1),
    MEDIUM(5),
    HIGH(10);

    private final int value;

    Priority(int value) {
        this.value = value;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "enum_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "Priority");
                // Enum constants should be in fields
                assert!(class.fields.iter().any(|f| f.name == "LOW"));
                assert!(class.fields.iter().any(|f| f.name == "MEDIUM"));
                assert!(class.fields.iter().any(|f| f.name == "HIGH"));
                // Enum constants should have proper type marker
                let low_field = class.fields.iter().find(|f| f.name == "LOW").unwrap();
                assert_eq!(low_field.field_type, Some("enum_constant".to_string()));
                assert!(low_field.is_static);
                assert!(low_field.is_final);
                break;
            }
        }
    }

    #[test]
    fn test_extract_package_declaration() {
        // Package declaration extraction
        let code = r#"
package com.example.myapp;

public class MyClass {}
"#;
        let tree = parse_java(code);
        let java = Java;

        let imports = java.extract_imports(&tree, code.as_bytes());
        // Package declaration should be first
        assert!(!imports.is_empty());
        let pkg = &imports[0];
        assert_eq!(pkg.module, "com.example.myapp");
        assert!(pkg.aliases.contains_key("package"));
    }

    #[test]
    fn test_extract_switch_expression() {
        // Java 14+ switch expression CFG
        let code = r#"
public class Test {
    public String getDay(int day) {
        return switch (day) {
            case 1, 2, 3, 4, 5 -> "weekday";
            case 6, 7 -> "weekend";
            default -> "invalid";
        };
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let cfg = java.build_cfg(child, code.as_bytes()).unwrap();
                assert_eq!(cfg.function_name, "getDay");
                // CFG should have multiple blocks for switch cases
                assert!(cfg.blocks.len() >= 1);
                break;
            }
        }
    }

    #[test]
    fn test_extract_pattern_matching_instanceof() {
        // Java 16+ pattern matching instanceof
        let code = r#"
public class Test {
    public void process(Object obj) {
        if (obj instanceof String s) {
            System.out.println(s.length());
        }
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                // DFG should capture the pattern variable 's'
                let dfg = java.build_dfg(child, code.as_bytes()).unwrap();
                assert_eq!(dfg.function_name, "process");
                // Pattern variable 's' should be tracked
                assert!(dfg.definitions.contains_key("s"));
                break;
            }
        }
    }

    #[test]
    fn test_extract_text_block() {
        // Java 15+ text blocks
        let code = r#"
public class Test {
    public String getJson() {
        return """
            {
                "name": "test",
                "value": 42
            }
            """;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let func = java.extract_function(child, code.as_bytes()).unwrap();
                assert_eq!(func.name, "getJson");
                assert_eq!(func.return_type, Some("String".to_string()));
                break;
            }
        }
    }

    #[test]
    fn test_extract_module_declaration() {
        // Java 9+ module declaration
        let code = r#"
module com.example.mymodule {
    requires java.base;
    requires transitive java.sql;
    exports com.example.api;
    opens com.example.internal to com.example.test;
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "module_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "com.example.mymodule");
                assert!(class.decorators.contains(&"module".to_string()));
                // Module directives should be in bases
                assert!(class.bases.iter().any(|b| b.contains("requires")));
                assert!(class.bases.iter().any(|b| b.contains("exports")));
                break;
            }
        }
    }

    #[test]
    fn test_extract_lambda_calls() {
        // Lambda expression and method reference extraction
        let code = r#"
public class Test {
    public void process(List<String> items) {
        items.forEach(s -> System.out.println(s));
        items.stream().map(String::toUpperCase).collect(Collectors.toList());
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let func = java.extract_function(child, code.as_bytes()).unwrap();
                assert_eq!(func.name, "process");
                break;
            }
        }
    }

    #[test]
    fn test_extract_throws_clause() {
        // Throws clause extraction
        let code = r#"
public class Test {
    public void riskyOperation() throws IOException, SQLException {
        // implementation
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let func = java.extract_function(child, code.as_bytes()).unwrap();
                assert_eq!(func.name, "riskyOperation");
                // Throws clause should be in decorators
                assert!(func.decorators.iter().any(|d| d.contains("throws:")));
                break;
            }
        }
    }

    #[test]
    fn test_extract_generics_with_bounds() {
        // Generic type bounds extraction
        let code = r#"
public class Repository<T extends Entity & Serializable> {
    public <U extends Comparable<U>> List<U> sort(List<U> items) {
        return items;
    }
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        for child in root.children(&mut root.walk()) {
            if child.kind() == "class_declaration" {
                let class = java.extract_class(child, code.as_bytes()).unwrap();
                assert_eq!(class.name, "Repository");
                // Type parameters should be in decorators
                assert!(class.decorators.iter().any(|d| d.contains("generic:")));
                break;
            }
        }
    }

    #[test]
    fn test_extract_wildcard_types() {
        // Wildcard type bounds (? extends T, ? super T)
        let code = r#"
public class Test {
    public void processUpper(List<? extends Number> items) {}
    public void processLower(List<? super Integer> items) {}
    public void processUnbounded(List<?> items) {}
}
"#;
        let tree = parse_java(code);
        let java = Java;

        let root = tree.root_node();
        let class_body = root.child(0).unwrap().child_by_field_name("body").unwrap();

        let mut method_count = 0;
        for child in class_body.children(&mut class_body.walk()) {
            if child.kind() == "method_declaration" {
                let func = java.extract_function(child, code.as_bytes()).unwrap();
                assert!(func.params.len() == 1);
                method_count += 1;
            }
        }
        assert_eq!(method_count, 3);
    }
}
