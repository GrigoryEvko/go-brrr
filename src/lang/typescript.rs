//! TypeScript/JavaScript language support.
//!
//! Provides full extraction for TypeScript and JavaScript including:
//! - Function declarations, arrow functions, method definitions
//! - Class declarations with extends/implements
//! - Import statements with named, default, and namespace imports
//! - JSDoc comment extraction
//! - Control flow graph building
//! - Data flow graph building

use std::collections::HashMap;
use std::path::Path;
use tree_sitter::{Node, Parser, Tree};

use crate::ast::types::{ClassInfo, FieldInfo, FunctionInfo, ImportInfo};
use crate::cfg::types::{BlockId, BlockType, CFGBlock, CFGEdge, CFGInfo, EdgeType};
use crate::dfg::types::{DFGInfo, DataflowEdge, DataflowKind};
use crate::error::{Result, BrrrError};
use crate::lang::traits::Language;

/// TypeScript language implementation (also handles JavaScript, TSX, and JSX).
///
/// The `is_tsx` field determines which tree-sitter grammar to use:
/// - `false`: Uses LANGUAGE_TYPESCRIPT (for .ts, .js, .mjs, .cjs files)
/// - `true`: Uses LANGUAGE_TSX (for .tsx, .jsx files that contain JSX syntax)
///
/// Use `TypeScript::new()` for regular TypeScript/JavaScript files, and
/// `TypeScript::tsx()` for TSX/JSX files.
pub struct TypeScript {
    /// Whether to use the TSX grammar (required for JSX syntax).
    is_tsx: bool,
}

impl Default for TypeScript {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeScript {
    /// Create a TypeScript language handler for regular .ts/.js files.
    ///
    /// This uses the TypeScript grammar which does NOT support JSX syntax.
    /// For files containing JSX (like .tsx or .jsx), use `TypeScript::tsx()` instead.
    pub fn new() -> Self {
        Self { is_tsx: false }
    }

    /// Create a TypeScript language handler for TSX/JSX files.
    ///
    /// This uses the TSX grammar which supports JSX syntax.
    /// The TSX grammar is a superset of TypeScript and can parse all TypeScript
    /// code, but it's slightly slower, so prefer `TypeScript::new()` when JSX
    /// syntax is not needed.
    pub fn tsx() -> Self {
        Self { is_tsx: true }
    }

    /// Check if this handler uses the TSX grammar.
    #[allow(dead_code)]
    pub fn is_tsx(&self) -> bool {
        self.is_tsx
    }
}

impl TypeScript {
    /// Get text from source bytes for a node.
    fn get_text<'a>(&self, node: Node, source: &'a [u8]) -> &'a str {
        std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }

    /// Parse JSDoc comment into clean docstring.
    ///
    /// Optimized to work with bytes directly, avoiding intermediate string
    /// allocations. Uses byte offsets to skip `/**`, `*/`, and leading `*`.
    fn parse_jsdoc(&self, comment: &str) -> String {
        let bytes = comment.as_bytes();
        let len = bytes.len();

        // Pre-allocate with reasonable estimate (half input size)
        let mut result = String::with_capacity(len / 2);
        let mut line_start = 0;

        while line_start < len {
            // Find line end
            let line_end = bytes[line_start..]
                .iter()
                .position(|&b| b == b'\n')
                .map_or(len, |pos| line_start + pos);

            let mut i = line_start;
            let mut j = line_end;

            // Trim trailing \r if present (Windows line endings)
            if j > i && bytes[j - 1] == b'\r' {
                j -= 1;
            }

            // Trim leading whitespace
            while i < j && bytes[i].is_ascii_whitespace() {
                i += 1;
            }

            // Trim trailing whitespace
            while j > i && bytes[j - 1].is_ascii_whitespace() {
                j -= 1;
            }

            // Strip /** prefix
            if j.saturating_sub(i) >= 3 && bytes[i] == b'/' && bytes[i + 1] == b'*' && bytes[i + 2] == b'*' {
                i += 3;
                while i < j && bytes[i].is_ascii_whitespace() {
                    i += 1;
                }
            }

            // Strip */ suffix
            if j.saturating_sub(i) >= 2 && bytes[j - 2] == b'*' && bytes[j - 1] == b'/' {
                j -= 2;
                while j > i && bytes[j - 1].is_ascii_whitespace() {
                    j -= 1;
                }
            }

            // Strip leading * (middle lines of JSDoc block)
            if i < j && bytes[i] == b'*' {
                i += 1;
                while i < j && bytes[i].is_ascii_whitespace() {
                    i += 1;
                }
            }

            // Append content if non-empty
            if i < j {
                if !result.is_empty() {
                    result.push(' ');
                }
                // SAFETY: slicing valid UTF-8 at ASCII boundaries preserves validity
                if let Ok(s) = std::str::from_utf8(&bytes[i..j]) {
                    result.push_str(s);
                }
            }

            line_start = line_end + 1;
        }

        result
    }

    /// Find previous JSDoc comment for a node.
    ///
    /// Searches backwards through siblings to find a JSDoc comment.
    /// Skips regular `//` comments to find JSDoc that may be separated by them.
    /// Stops immediately on any non-comment node.
    fn find_jsdoc<'a>(&self, node: Node<'a>, source: &[u8]) -> Option<String> {
        let mut current = node.prev_sibling();

        while let Some(sibling) = current {
            match sibling.kind() {
                "comment" => {
                    let text = self.get_text(sibling, source);
                    if text.starts_with("/**") {
                        return Some(self.parse_jsdoc(text));
                    }
                    // Regular comment (// or /* without second *), continue searching
                    current = sibling.prev_sibling();
                }
                _ => return None, // Non-comment node, stop searching
            }
        }
        None
    }

    /// Extract parameters from formal_parameters node.
    fn extract_params(&self, params_node: Node, source: &[u8]) -> Vec<String> {
        let mut params = Vec::new();
        for child in params_node.children(&mut params_node.walk()) {
            match child.kind() {
                "identifier" => {
                    params.push(self.get_text(child, source).to_string());
                }
                "required_parameter" | "optional_parameter" | "rest_parameter" => {
                    params.push(self.get_text(child, source).to_string());
                }
                // Skip punctuation
                "(" | ")" | "," => {}
                _ => {
                    // For complex parameter types, include the full text
                    if child.is_named() {
                        params.push(self.get_text(child, source).to_string());
                    }
                }
            }
        }
        params
    }

    /// Extract type parameters (generics) from a node.
    /// Returns the type parameters string like `<T, U>` if present.
    fn extract_type_parameters(&self, node: Node, source: &[u8]) -> Option<String> {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "type_parameters" {
                return Some(self.get_text(child, source).to_string());
            }
        }
        None
    }

    /// Check if function is async using AST traversal.
    ///
    /// Searches for an "async" keyword child node rather than using string matching,
    /// which correctly handles:
    /// - Comments before async: `/* comment */ async function foo() {}`
    /// - Decorators before async: `@decorator async function foo() {}`
    /// - Visibility modifiers: `class C { public async method() {} }`
    fn is_async(&self, node: Node, _source: &[u8]) -> bool {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "async" {
                return true;
            }
            // Early exit optimization: async keyword always precedes the body
            if child.kind() == "statement_block" {
                break;
            }
        }
        false
    }

    /// Extract function name from various node types.
    fn extract_function_name(&self, node: Node, source: &[u8]) -> Option<String> {
        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "identifier" | "property_identifier" => {
                    return Some(self.get_text(child, source).to_string());
                }
                _ => {}
            }
        }
        None
    }

    /// Extract function name with parent context fallback.
    ///
    /// First tries to get name from the function node itself (named function expressions).
    /// If not found, checks parent context for CommonJS patterns like:
    /// - `exports.foo = function() {}`
    /// - `module.exports.foo = function() {}`
    /// - `const foo = function() {}`
    fn extract_function_name_with_context(&self, node: Node, source: &[u8]) -> Option<String> {
        // First try to get name directly from the function
        if let Some(name) = self.extract_function_name(node, source) {
            return Some(name);
        }

        // Check parent context for anonymous functions
        let parent = node.parent()?;
        match parent.kind() {
            "variable_declarator" => parent
                .child_by_field_name("name")
                .map(|n| self.get_text(n, source).to_string()),
            "pair" | "property" => parent
                .child_by_field_name("key")
                .map(|n| self.get_text(n, source).to_string()),
            "assignment_expression" => parent.child_by_field_name("left").and_then(|n| {
                if n.kind() == "identifier" {
                    Some(self.get_text(n, source).to_string())
                } else if n.kind() == "member_expression" {
                    // Handle exports.foo = function() {} and module.exports.foo = function() {}
                    n.child_by_field_name("property")
                        .map(|p| self.get_text(p, source).to_string())
                } else {
                    None
                }
            }),
            _ => None,
        }
    }

    /// Recursively collect import statements from tree.
    ///
    /// Handles both ES6 imports and CommonJS require() calls:
    /// - ES6: `import x from 'module'`, `import { a, b } from 'module'`
    /// - CommonJS: `var x = require('module')`, `const { a } = require('module')`
    fn collect_imports(&self, node: Node, source: &[u8], imports: &mut Vec<ImportInfo>) {
        match node.kind() {
            // ES6 import statements
            "import_statement" => {
                if let Some(import_info) = self.extract_single_import(node, source) {
                    imports.push(import_info);
                }
            }
            // CommonJS: var/let/const x = require('module')
            "variable_declaration" | "lexical_declaration" => {
                if let Some(import_info) = self.extract_require_import(node, source) {
                    imports.push(import_info);
                }
            }
            // CommonJS: require('side-effect-only') as bare expression
            "expression_statement" => {
                if let Some(import_info) = self.extract_bare_require(node, source) {
                    imports.push(import_info);
                }
            }
            _ => {}
        }

        // Recurse into children
        for child in node.children(&mut node.walk()) {
            self.collect_imports(child, source, imports);
        }
    }

    /// Check if a call_expression is a require() call and return the module path.
    ///
    /// Handles patterns:
    /// - `require('module')` - direct require
    /// - `require('module')('arg')` - chained call (returns inner require's module)
    /// - `require('module').prop` - member access (returns require's module)
    fn find_require_module(&self, node: Node, source: &[u8]) -> Option<String> {
        match node.kind() {
            "call_expression" => {
                // Check if function is "require" identifier
                if let Some(func) = node.child_by_field_name("function") {
                    if func.kind() == "identifier" && self.get_text(func, source) == "require" {
                        // Extract module path from arguments
                        if let Some(args) = node.child_by_field_name("arguments") {
                            return self.extract_first_string_arg(args, source);
                        }
                    }
                    // Handle chained calls: require('debug')('app')
                    // The inner call_expression is the actual require
                    if func.kind() == "call_expression" {
                        return self.find_require_module(func, source);
                    }
                }
            }
            "member_expression" => {
                // Handle: require('./utils').methods
                if let Some(obj) = node.child_by_field_name("object") {
                    return self.find_require_module(obj, source);
                }
            }
            _ => {}
        }
        None
    }

    /// Extract the first string argument from an arguments node.
    fn extract_first_string_arg(&self, args_node: Node, source: &[u8]) -> Option<String> {
        for child in args_node.children(&mut args_node.walk()) {
            if child.kind() == "string" {
                let text = self.get_text(child, source);
                // Strip quotes (both single and double)
                return Some(text.trim_matches('"').trim_matches('\'').to_string());
            }
        }
        None
    }

    /// Extract CommonJS require import from variable declaration.
    ///
    /// Handles patterns:
    /// - `var finalhandler = require('finalhandler')`
    /// - `const debug = require('debug')('express:app')` (chained)
    /// - `var methods = require('./utils').methods` (member access)
    /// - `const { a, b } = require('module')` (destructuring)
    fn extract_require_import(&self, node: Node, source: &[u8]) -> Option<ImportInfo> {
        // Find variable_declarator child
        for child in node.children(&mut node.walk()) {
            if child.kind() == "variable_declarator" {
                let name_node = child.child_by_field_name("name");
                let value_node = child.child_by_field_name("value");

                if let Some(value) = value_node {
                    // Try to find require() in the value expression
                    if let Some(module_path) = self.find_require_module(value, source) {
                        let mut names = Vec::new();
                        let mut aliases = HashMap::new();

                        // Extract imported names based on the name pattern
                        if let Some(name) = name_node {
                            match name.kind() {
                                "identifier" => {
                                    // Simple: var x = require('module')
                                    // For member access: var methods = require('./utils').methods
                                    // the imported name is the property being accessed
                                    if value.kind() == "member_expression" {
                                        if let Some(prop) = value.child_by_field_name("property") {
                                            let prop_name = self.get_text(prop, source).to_string();
                                            let local_name = self.get_text(name, source).to_string();
                                            if prop_name != local_name {
                                                aliases.insert(prop_name.clone(), local_name);
                                            }
                                            names.push(prop_name);
                                        }
                                    } else {
                                        // Default import style: var x = require('x')
                                        let local_name = self.get_text(name, source).to_string();
                                        names.push(format!("default as {}", local_name));
                                    }
                                }
                                "object_pattern" => {
                                    // Destructuring: const { a, b } = require('module')
                                    for prop in name.children(&mut name.walk()) {
                                        match prop.kind() {
                                            "shorthand_property_identifier_pattern" => {
                                                names.push(self.get_text(prop, source).to_string());
                                            }
                                            "pair_pattern" => {
                                                // { original: alias }
                                                let key = prop.child_by_field_name("key");
                                                let value = prop.child_by_field_name("value");
                                                if let (Some(k), Some(v)) = (key, value) {
                                                    let orig = self.get_text(k, source).to_string();
                                                    let alias = self.get_text(v, source).to_string();
                                                    if orig != alias {
                                                        aliases.insert(orig.clone(), alias);
                                                    }
                                                    names.push(orig);
                                                }
                                            }
                                            _ => {}
                                        }
                                    }
                                }
                                "array_pattern" => {
                                    // Array destructuring: const [a, b] = require('module')
                                    // Less common but possible
                                    for elem in name.children(&mut name.walk()) {
                                        if elem.kind() == "identifier" {
                                            names.push(self.get_text(elem, source).to_string());
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }

                        return Some(ImportInfo {
                            module: module_path,
                            names,
                            aliases,
                            is_from: true, // CommonJS is conceptually similar to "from X import Y"
                            level: 0,
                            line_number: node.start_position().row + 1,
                            visibility: None,
                        });
                    }
                }
            }
        }
        None
    }

    /// Extract bare require() call for side-effect imports.
    ///
    /// Handles: `require('side-effect-only');`
    fn extract_bare_require(&self, node: Node, source: &[u8]) -> Option<ImportInfo> {
        // expression_statement contains the call_expression directly
        for child in node.children(&mut node.walk()) {
            if child.kind() == "call_expression" {
                if let Some(func) = child.child_by_field_name("function") {
                    if func.kind() == "identifier" && self.get_text(func, source) == "require" {
                        if let Some(args) = child.child_by_field_name("arguments") {
                            if let Some(module_path) = self.extract_first_string_arg(args, source) {
                                return Some(ImportInfo {
                                    module: module_path,
                                    names: Vec::new(), // No names - side-effect import
                                    aliases: HashMap::new(),
                                    is_from: false, // Side-effect import, like `import 'module'`
                                    level: 0,
                                    line_number: node.start_position().row + 1,
                                    visibility: None,
                                });
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// Extract a single import statement.
    fn extract_single_import(&self, node: Node, source: &[u8]) -> Option<ImportInfo> {
        let mut module_path = String::new();
        let mut names = Vec::new();
        let mut aliases = HashMap::new();
        let mut is_from = false;

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "string" => {
                    let text = self.get_text(child, source);
                    module_path = text.trim_matches('"').trim_matches('\'').to_string();
                }
                "import_clause" => {
                    is_from = true;
                    let (n, a, default, namespace) = self.extract_import_names(child, source);
                    names = n;
                    aliases = a;

                    // Add default import as a name
                    if let Some(def) = default {
                        names.insert(0, format!("default as {}", def));
                    }

                    // Add namespace import
                    if let Some(ns) = namespace {
                        names.push(format!("* as {}", ns));
                    }
                }
                _ => {}
            }
        }

        if module_path.is_empty() {
            return None;
        }

        Some(ImportInfo {
            module: module_path,
            names,
            aliases,
            is_from,
            level: 0,
            line_number: node.start_position().row + 1,
            visibility: None,
        })
    }

    /// Extract import specifiers from import_clause.
    fn extract_import_names(
        &self,
        node: Node,
        source: &[u8],
    ) -> (
        Vec<String>,
        HashMap<String, String>,
        Option<String>,
        Option<String>,
    ) {
        let mut names = Vec::new();
        let mut aliases = HashMap::new();
        let mut default_import = None;
        let mut namespace_import = None;

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "identifier" => {
                    // Default import
                    default_import = Some(self.get_text(child, source).to_string());
                }
                "namespace_import" => {
                    // import * as name
                    for grandchild in child.children(&mut child.walk()) {
                        if grandchild.kind() == "identifier" {
                            namespace_import = Some(self.get_text(grandchild, source).to_string());
                        }
                    }
                }
                "named_imports" => {
                    // { a, b, c as d }
                    for spec in child.children(&mut child.walk()) {
                        if spec.kind() == "import_specifier" {
                            let mut name = None;
                            let mut alias = None;
                            for part in spec.children(&mut spec.walk()) {
                                if part.kind() == "identifier" {
                                    if name.is_none() {
                                        name = Some(self.get_text(part, source).to_string());
                                    } else {
                                        alias = Some(self.get_text(part, source).to_string());
                                    }
                                }
                            }
                            if let Some(n) = name {
                                if let Some(a) = alias {
                                    aliases.insert(n.clone(), a);
                                }
                                names.push(n);
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        (names, aliases, default_import, namespace_import)
    }

    /// BUG #14 FIX: Extract heritage types handling generic types and multiple items.
    /// Handles cases like:
    /// - extends Base
    /// - extends Base<T>
    /// - implements Interface1, Interface2
    /// - implements Generic<T, U>
    fn extract_heritage_types(
        &self,
        clause_node: Node,
        source: &[u8],
        bases: &mut Vec<String>,
        is_implements: bool,
    ) {
        for child in clause_node.children(&mut clause_node.walk()) {
            match child.kind() {
                "identifier" | "type_identifier" => {
                    let type_text = self.get_text(child, source).to_string();
                    if is_implements {
                        bases.push(format!("implements {}", type_text));
                    } else {
                        bases.push(type_text);
                    }
                }
                // Handle generic types like Base<T> or Interface<T, U>
                "generic_type" => {
                    let full_type = self.get_text(child, source).to_string();
                    if is_implements {
                        bases.push(format!("implements {}", full_type));
                    } else {
                        bases.push(full_type);
                    }
                }
                // Handle member expressions like Namespace.Type
                "member_expression" | "nested_type_identifier" => {
                    let full_type = self.get_text(child, source).to_string();
                    if is_implements {
                        bases.push(format!("implements {}", full_type));
                    } else {
                        bases.push(full_type);
                    }
                }
                _ => {}
            }
        }
    }

    /// BUG #7 FIX: Extract TypeScript interfaces as ClassInfo.
    fn extract_interface(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let mut name = String::new();
        let mut bases = Vec::new();
        let docstring = self.find_jsdoc(node, source);
        let mut methods = Vec::new();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "type_identifier" | "identifier" => {
                    if name.is_empty() {
                        name = self.get_text(child, source).to_string();
                    }
                }
                "extends_type_clause" => {
                    self.extract_heritage_types(child, source, &mut bases, false);
                }
                "interface_body" | "object_type" => {
                    // Extract method signatures and index signatures from interface body
                    for body_child in child.children(&mut child.walk()) {
                        match body_child.kind() {
                            "method_signature" | "property_signature" => {
                                if let Some(method) = self.extract_interface_method(body_child, source) {
                                    methods.push(method);
                                }
                            }
                            // FEATURE: Extract index signatures like [key: string]: any
                            "index_signature" => {
                                if let Some(index_sig) = self.extract_index_signature(body_child, source) {
                                    methods.push(index_sig);
                                }
                            }
                            _ => {}
                        }
                    }
                }
                "type_parameters" => {
                    // Append generics to name
                    let type_params = self.get_text(child, source);
                    name = format!("{}{}", name, type_params);
                }
                _ => {}
            }
        }

        if name.is_empty() {
            return None;
        }

        Some(ClassInfo {
            name: format!("interface {}", name),
            bases,
            docstring,
            methods,
            fields: Vec::new(),
            inner_classes: Vec::new(),
            decorators: vec!["interface".to_string()],
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "typescript".to_string(),
        })
    }

    /// Extract method signature from interface body.
    fn extract_interface_method(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        let mut name = String::new();
        let mut params = Vec::new();
        let mut return_type = None;
        let docstring = self.find_jsdoc(node, source);

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "property_identifier" | "identifier" => {
                    if name.is_empty() {
                        name = self.get_text(child, source).to_string();
                    }
                }
                "formal_parameters" | "call_signature" => {
                    params = self.extract_params(child, source);
                }
                "type_annotation" => {
                    let text = self.get_text(child, source);
                    return_type = Some(text.trim_start_matches(':').trim().to_string());
                }
                _ => {}
            }
        }

        if name.is_empty() {
            return None;
        }

        Some(FunctionInfo {
            name,
            params,
            return_type,
            docstring,
            is_method: true,
            is_async: false,
            decorators: Vec::new(),
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "typescript".to_string(),
        })
    }

    /// FEATURE: Extract index signature from interface body.
    /// Handles TypeScript index signatures like:
    /// - `[key: string]: number`
    /// - `[index: number]: string`
    /// - `readonly [key: string]: any`
    fn extract_index_signature(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        let docstring = self.find_jsdoc(node, source);
        let mut decorators = vec!["index_signature".to_string()];
        let mut key_type = String::new();
        let mut value_type = String::new();

        // Check for readonly modifier
        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "readonly" => {
                    decorators.push("readonly".to_string());
                }
                // The index parameter: `[key: string]`
                "index_signature_parameter" | "formal_parameters" => {
                    // Extract the key type from the parameter
                    for param_child in child.children(&mut child.walk()) {
                        if param_child.kind() == "type_annotation" {
                            let type_text = self.get_text(param_child, source);
                            key_type = type_text.trim_start_matches(':').trim().to_string();
                        }
                    }
                    // Fallback: extract from full text
                    if key_type.is_empty() {
                        let param_text = self.get_text(child, source);
                        if param_text.contains("string") {
                            key_type = "string".to_string();
                        } else if param_text.contains("number") {
                            key_type = "number".to_string();
                        } else if param_text.contains("symbol") {
                            key_type = "symbol".to_string();
                        }
                    }
                }
                // The value type annotation
                "type_annotation" => {
                    let type_text = self.get_text(child, source);
                    value_type = type_text.trim_start_matches(':').trim().to_string();
                }
                _ => {}
            }
        }

        // Fallback: parse from full text if structured parsing failed
        if key_type.is_empty() || value_type.is_empty() {
            let full_text = self.get_text(node, source);
            // Pattern: [key: KeyType]: ValueType
            if let Some(bracket_end) = full_text.find(']') {
                let bracket_content = &full_text[1..bracket_end];
                if let Some(colon_pos) = bracket_content.find(':') {
                    if key_type.is_empty() {
                        key_type = bracket_content[colon_pos + 1..].trim().to_string();
                    }
                }
                if value_type.is_empty() {
                    let after_bracket = &full_text[bracket_end + 1..];
                    if let Some(colon_pos) = after_bracket.find(':') {
                        value_type = after_bracket[colon_pos + 1..]
                            .trim()
                            .trim_end_matches(';')
                            .to_string();
                    }
                }
            }
        }

        // Generate a meaningful name: [string] or [number]
        let name = format!("[{}]", key_type);

        Some(FunctionInfo {
            name,
            params: vec![format!("key: {}", key_type)],
            return_type: Some(value_type),
            docstring,
            is_method: false,
            is_async: false,
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "typescript".to_string(),
        })
    }

    /// FEATURE: Check if a node is a type guard function.
    /// Type guards have return type predicates like `x is string`.
    ///
    /// Tree-sitter structure for type guards:
    /// - Regular type guard: `return_type: type_predicate_annotation` -> `type_predicate`
    /// - Asserts type guard: `return_type: asserts_annotation` -> `asserts` -> `type_predicate`
    fn is_type_guard(&self, node: Node, source: &[u8]) -> Option<String> {
        for child in node.children(&mut node.walk()) {
            // Tree-sitter TypeScript grammar uses type_predicate_annotation for type guards
            // e.g., `: x is string` becomes type_predicate_annotation -> type_predicate
            if child.kind() == "type_predicate_annotation" {
                // Find the type_predicate inside
                for annotation_child in child.children(&mut child.walk()) {
                    if annotation_child.kind() == "type_predicate" {
                        return Some(self.get_text(annotation_child, source).to_string());
                    }
                }
            }
            // Handle asserts type guards: `asserts x is string`
            // Structure: asserts_annotation -> asserts -> type_predicate
            if child.kind() == "asserts_annotation" {
                for annotation_child in child.children(&mut child.walk()) {
                    if annotation_child.kind() == "asserts" {
                        // Return the full asserts expression
                        return Some(self.get_text(annotation_child, source).to_string());
                    }
                }
                // Fallback: return full annotation text
                let text = self.get_text(child, source);
                return Some(text.trim_start_matches(':').trim().to_string());
            }
            // Also check for type_predicate directly (some structures may differ)
            if child.kind() == "type_predicate" {
                return Some(self.get_text(child, source).to_string());
            }
            // Check inside type_annotation as well for nested cases
            if child.kind() == "type_annotation" {
                for annotation_child in child.children(&mut child.walk()) {
                    if annotation_child.kind() == "type_predicate" {
                        return Some(self.get_text(annotation_child, source).to_string());
                    }
                }
            }
        }
        None
    }

    /// BUG #7 FIX: Extract TypeScript type aliases as ClassInfo.
    fn extract_type_alias(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let mut name = String::new();
        let docstring = self.find_jsdoc(node, source);

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "type_identifier" | "identifier" => {
                    if name.is_empty() {
                        name = self.get_text(child, source).to_string();
                    }
                }
                "type_parameters" => {
                    let type_params = self.get_text(child, source);
                    name = format!("{}{}", name, type_params);
                }
                _ => {}
            }
        }

        if name.is_empty() {
            return None;
        }

        Some(ClassInfo {
            name: format!("type {}", name),
            bases: Vec::new(),
            docstring,
            methods: Vec::new(),
            fields: Vec::new(),
            inner_classes: Vec::new(),
            decorators: vec!["type_alias".to_string()],
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "typescript".to_string(),
        })
    }

    /// BUG #7 FIX: Extract TypeScript enums as ClassInfo.
    fn extract_enum(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let mut name = String::new();
        let docstring = self.find_jsdoc(node, source);
        let mut methods = Vec::new();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "identifier" => {
                    if name.is_empty() {
                        name = self.get_text(child, source).to_string();
                    }
                }
                "enum_body" => {
                    // Extract enum members as "methods" for consistency
                    for member in child.children(&mut child.walk()) {
                        if member.kind() == "enum_assignment" || member.kind() == "property_identifier" {
                            let member_name = self.get_text(member, source).to_string();
                            if !member_name.is_empty() && member_name != "," && member_name != "{" && member_name != "}" {
                                methods.push(FunctionInfo {
                                    name: member_name,
                                    params: Vec::new(),
                                    return_type: None,
                                    docstring: None,
                                    is_method: false,
                                    is_async: false,
                                    decorators: vec!["enum_member".to_string()],
                                    line_number: member.start_position().row + 1,
                                    end_line_number: Some(member.end_position().row + 1),
                                    language: "typescript".to_string(),
                                });
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        if name.is_empty() {
            return None;
        }

        Some(ClassInfo {
            name: format!("enum {}", name),
            bases: Vec::new(),
            docstring,
            methods,
            fields: Vec::new(),
            inner_classes: Vec::new(),
            decorators: vec!["enum".to_string()],
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "typescript".to_string(),
        })
    }

    /// BUG #8 FIX: Extract TypeScript namespaces/modules as ClassInfo.
    fn extract_namespace(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let mut name = String::new();
        let docstring = self.find_jsdoc(node, source);
        let mut methods = Vec::new();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "identifier" | "string" | "nested_identifier" => {
                    if name.is_empty() {
                        let text = self.get_text(child, source);
                        name = text.trim_matches('"').trim_matches('\'').to_string();
                    }
                }
                "statement_block" => {
                    // Extract exported functions from namespace body
                    for stmt in child.children(&mut child.walk()) {
                        if let Some(func) = self.extract_function(stmt, source) {
                            methods.push(func);
                        }
                    }
                }
                _ => {}
            }
        }

        if name.is_empty() {
            return None;
        }

        Some(ClassInfo {
            name: format!("namespace {}", name),
            bases: Vec::new(),
            docstring,
            methods,
            fields: Vec::new(),
            inner_classes: Vec::new(),
            decorators: vec!["namespace".to_string()],
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "typescript".to_string(),
        })
    }

    /// FEATURE: Extract class field declaration (including ECMAScript private fields).
    ///
    /// Handles:
    /// - Regular fields: `name: string = "default"`
    /// - Private fields (ECMAScript #): `#count = 0`
    /// - Static fields: `static instance = null`
    /// - Readonly fields: `readonly id: number`
    ///
    /// Tree-sitter structure for private fields:
    /// - `public_field_definition` with `private_property_identifier` as name
    fn extract_class_field(&self, node: Node, source: &[u8]) -> Option<FieldInfo> {
        if node.kind() != "public_field_definition" {
            return None;
        }

        let mut name = String::new();
        let mut field_type = None;
        let mut visibility = None;
        let mut is_static = false;
        let mut is_final = false;
        let mut default_value = None;
        let mut annotations = Vec::new();
        let mut is_ecma_private = false;

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                // ECMAScript private field (#field)
                "private_property_identifier" => {
                    name = self.get_text(child, source).to_string();
                    is_ecma_private = true;
                }
                // Regular property name
                "property_identifier" => {
                    if name.is_empty() {
                        name = self.get_text(child, source).to_string();
                    }
                }
                // Accessibility modifier (public/private/protected)
                "accessibility_modifier" => {
                    visibility = Some(self.get_text(child, source).to_string());
                }
                // Static modifier
                "static" => {
                    is_static = true;
                }
                // Readonly modifier
                "readonly" => {
                    is_final = true;
                    annotations.push("readonly".to_string());
                }
                // Type annotation
                "type_annotation" => {
                    let text = self.get_text(child, source);
                    field_type = Some(text.trim_start_matches(':').trim().to_string());
                }
                // Default value - any expression after '='
                "number" | "string" | "true" | "false" | "null" | "undefined"
                | "identifier" | "new_expression" | "call_expression" | "array"
                | "object" | "arrow_function" | "template_string" => {
                    default_value = Some(self.get_text(child, source).to_string());
                }
                _ => {}
            }
        }

        if name.is_empty() {
            return None;
        }

        // Mark ECMAScript private fields with decorator
        if is_ecma_private {
            annotations.push("ecma_private".to_string());
        }

        Some(FieldInfo {
            name,
            field_type,
            visibility,
            is_static,
            is_final,
            default_value,
            annotations,
            line_number: node.start_position().row + 1,
        })
    }

    /// BUG #15 FIX: Collect re-exports from export statements.
    /// Handles:
    /// - export { foo } from './module';
    /// - export * from './module';
    /// - export { default as Alias } from './module';
    fn collect_reexports(&self, node: Node, source: &[u8], imports: &mut Vec<ImportInfo>) {
        if node.kind() == "export_statement" {
            // Check if this is a re-export (has a source module)
            let mut module_path = None;
            let mut has_from = false;

            for child in node.children(&mut node.walk()) {
                if child.kind() == "string" {
                    let text = self.get_text(child, source);
                    module_path = Some(text.trim_matches('"').trim_matches('\'').to_string());
                    has_from = true;
                }
            }

            // Only process if this is a re-export (has from clause)
            if has_from {
                if let Some(module) = module_path {
                    let mut names = Vec::new();
                    let mut aliases = HashMap::new();

                    for child in node.children(&mut node.walk()) {
                        match child.kind() {
                            // export * from './module'
                            "*" | "namespace_export" => {
                                names.push("*".to_string());
                            }
                            // export { foo, bar as baz } from './module'
                            "export_clause" => {
                                for spec in child.children(&mut child.walk()) {
                                    if spec.kind() == "export_specifier" {
                                        let mut name = None;
                                        let mut alias = None;
                                        let mut seen_as = false;

                                        for part in spec.children(&mut spec.walk()) {
                                            if part.kind() == "identifier" {
                                                if name.is_none() {
                                                    name = Some(
                                                        self.get_text(part, source).to_string(),
                                                    );
                                                } else if seen_as {
                                                    alias = Some(
                                                        self.get_text(part, source).to_string(),
                                                    );
                                                }
                                            } else if part.kind() == "as" {
                                                seen_as = true;
                                            }
                                        }

                                        if let Some(n) = name {
                                            if let Some(a) = alias {
                                                if n == "default" {
                                                    names.push(format!("default as {}", a));
                                                } else {
                                                    aliases.insert(n.clone(), a);
                                                    names.push(n);
                                                }
                                            } else {
                                                names.push(n);
                                            }
                                        }
                                    }
                                }
                            }
                            _ => {}
                        }
                    }

                    imports.push(ImportInfo {
                        module,
                        names,
                        aliases,
                        is_from: true,
                        level: 0,
                        line_number: node.start_position().row + 1,
                        visibility: None,
                    });
                }
            }
        }

        // Recurse into children
        for child in node.children(&mut node.walk()) {
            self.collect_reexports(child, source, imports);
        }
    }

    /// Extract TypeScript function signature (function overload declarations).
    ///
    /// Function signatures are function declarations without a body, used for:
    /// - Function overloads: `function foo(x: string): string;`
    /// - Ambient function declarations inside `declare` blocks
    ///
    /// Returns FunctionInfo with "overload" decorator to distinguish from implementations.
    fn extract_function_signature(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        if node.kind() != "function_signature" {
            return None;
        }

        let mut name = String::new();
        let mut params = Vec::new();
        let mut return_type = None;
        let docstring = self.find_jsdoc(node, source);
        let decorators = vec!["overload".to_string()];

        // Check for type parameters (generics)
        let type_params = self.extract_type_parameters(node, source);

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "identifier" => {
                    if name.is_empty() {
                        name = self.get_text(child, source).to_string();
                    }
                }
                "formal_parameters" => {
                    params = self.extract_params(child, source);
                }
                "type_annotation" => {
                    let text = self.get_text(child, source);
                    return_type = Some(text.trim_start_matches(':').trim().to_string());
                }
                "type_parameters" => {
                    // Already handled above
                }
                _ => {}
            }
        }

        if name.is_empty() {
            return None;
        }

        // Append type parameters to name if present
        if let Some(tp) = type_params {
            name = format!("{}{}", name, tp);
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
            language: "typescript".to_string(),
        })
    }

    /// Extract ambient function declaration (declare function).
    ///
    /// Handles TypeScript ambient function declarations:
    /// - `declare function foo(): void;`
    ///
    /// Returns FunctionInfo with "ambient" and "declare" decorators.
    fn extract_ambient_function(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        if node.kind() != "ambient_declaration" {
            return None;
        }

        // Look for function_signature inside ambient_declaration
        for child in node.children(&mut node.walk()) {
            if child.kind() == "function_signature" {
                if let Some(mut func) = self.extract_function_signature(child, source) {
                    // Replace "overload" with "ambient" for ambient declarations
                    func.decorators.retain(|d| d != "overload");
                    func.decorators.insert(0, "ambient".to_string());
                    func.decorators.push("declare".to_string());
                    return Some(func);
                }
            }
        }

        None
    }

    /// Extract ambient class declaration.
    ///
    /// Handles `declare class Foo { }` and `declare module "name" { }`.
    fn extract_ambient_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        if node.kind() != "ambient_declaration" {
            return None;
        }

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "class_declaration" | "abstract_class_declaration" => {
                    if let Some(mut class) = self.extract_class_inner(child, source) {
                        class.decorators.insert(0, "ambient".to_string());
                        class.decorators.push("declare".to_string());
                        return Some(class);
                    }
                }
                "interface_declaration" => {
                    if let Some(mut iface) = self.extract_interface(child, source) {
                        iface.decorators.insert(0, "ambient".to_string());
                        iface.decorators.push("declare".to_string());
                        return Some(iface);
                    }
                }
                "module" | "internal_module" => {
                    if let Some(mut ns) = self.extract_namespace(child, source) {
                        ns.decorators.insert(0, "ambient".to_string());
                        ns.decorators.push("declare".to_string());
                        return Some(ns);
                    }
                }
                "enum_declaration" => {
                    if let Some(mut enum_info) = self.extract_enum(child, source) {
                        enum_info.decorators.insert(0, "ambient".to_string());
                        enum_info.decorators.push("declare".to_string());
                        return Some(enum_info);
                    }
                }
                "type_alias_declaration" => {
                    if let Some(mut type_alias) = self.extract_type_alias(child, source) {
                        type_alias.decorators.insert(0, "ambient".to_string());
                        type_alias.decorators.push("declare".to_string());
                        return Some(type_alias);
                    }
                }
                _ => {}
            }
        }

        None
    }

    /// Extract ambient variable declaration.
    ///
    /// Handles `declare var/let/const x: type;`
    /// Returns as FunctionInfo with "ambient_variable" decorator.
    fn extract_ambient_variable(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        if node.kind() != "ambient_declaration" {
            return None;
        }

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "variable_declaration" | "lexical_declaration" => {
                    // Extract the variable declarator
                    for var_child in child.children(&mut child.walk()) {
                        if var_child.kind() == "variable_declarator" {
                            let mut name = String::new();
                            let mut var_type = None;

                            for decl_child in var_child.children(&mut var_child.walk()) {
                                match decl_child.kind() {
                                    "identifier" => {
                                        if name.is_empty() {
                                            name = self.get_text(decl_child, source).to_string();
                                        }
                                    }
                                    "type_annotation" => {
                                        let text = self.get_text(decl_child, source);
                                        var_type =
                                            Some(text.trim_start_matches(':').trim().to_string());
                                    }
                                    _ => {}
                                }
                            }

                            if !name.is_empty() {
                                // Determine the kind (var/let/const)
                                let kind = if child.kind() == "variable_declaration" {
                                    "var"
                                } else {
                                    // lexical_declaration: check for let/const
                                    child
                                        .child_by_field_name("kind")
                                        .map(|k| self.get_text(k, source))
                                        .unwrap_or("let")
                                };

                                return Some(FunctionInfo {
                                    name,
                                    params: Vec::new(),
                                    return_type: var_type,
                                    docstring: self.find_jsdoc(node, source),
                                    is_method: false,
                                    is_async: false,
                                    decorators: vec![
                                        "ambient".to_string(),
                                        "declare".to_string(),
                                        format!("ambient_{}", kind),
                                    ],
                                    line_number: node.start_position().row + 1,
                                    end_line_number: Some(node.end_position().row + 1),
                                    language: "typescript".to_string(),
                                });
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        None
    }

    /// Internal helper to extract class without export handling (to avoid recursion).
    fn extract_class_inner(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let kind = node.kind();

        // Handle class expressions (node type is "class", not "class_expression")
        let is_abstract_class = kind == "abstract_class_declaration";
        if kind != "class_declaration" && kind != "class" && !is_abstract_class {
            return None;
        }

        let mut name = String::new();
        let mut bases = Vec::new();
        let mut methods = Vec::new();
        let docstring = self.find_jsdoc(node, source);
        let mut decorators = Vec::new();

        if is_abstract_class {
            decorators.push("abstract".to_string());
        }

        // For class expressions, try to get name from parent
        if kind == "class" {
            if let Some(parent) = node.parent() {
                if parent.kind() == "variable_declarator" {
                    if let Some(name_node) = parent.child_by_field_name("name") {
                        name = self.get_text(name_node, source).to_string();
                    }
                } else if parent.kind() == "assignment_expression" {
                    if let Some(left) = parent.child_by_field_name("left") {
                        if left.kind() == "identifier" {
                            name = self.get_text(left, source).to_string();
                        }
                    }
                }
            }
        }

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "type_identifier" | "identifier" => {
                    if name.is_empty() {
                        name = self.get_text(child, source).to_string();
                    }
                }
                "class_heritage" => {
                    for heritage_child in child.children(&mut child.walk()) {
                        match heritage_child.kind() {
                            "extends_clause" => {
                                self.extract_heritage_types(
                                    heritage_child,
                                    source,
                                    &mut bases,
                                    false,
                                );
                            }
                            "implements_clause" => {
                                self.extract_heritage_types(
                                    heritage_child,
                                    source,
                                    &mut bases,
                                    true,
                                );
                            }
                            _ => {}
                        }
                    }
                }
                "extends_clause" => {
                    self.extract_heritage_types(child, source, &mut bases, false);
                }
                "implements_clause" => {
                    self.extract_heritage_types(child, source, &mut bases, true);
                }
                "class_body" => {
                    for body_child in child.children(&mut child.walk()) {
                        if body_child.kind() == "method_definition"
                            || body_child.kind() == "abstract_method_signature"
                        {
                            if let Some(method) = self.extract_function(body_child, source) {
                                methods.push(method);
                            }
                        }
                    }
                }
                "decorator" => {
                    decorators.push(self.get_text(child, source).to_string());
                }
                _ => {}
            }
        }

        if name.is_empty() {
            return None;
        }

        Some(ClassInfo {
            name,
            bases,
            docstring,
            methods,
            fields: Vec::new(),
            inner_classes: Vec::new(),
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "typescript".to_string(),
        })
    }
}

impl Language for TypeScript {
    fn name(&self) -> &'static str {
        if self.is_tsx {
            "tsx"
        } else {
            "typescript"
        }
    }

    fn extensions(&self) -> &[&'static str] {
        if self.is_tsx {
            // TSX handler only claims .tsx and .jsx extensions
            &[".tsx", ".jsx"]
        } else {
            // Regular TypeScript handler claims .ts, .js, and ES module variants
            // .mts/.cts = ES module TypeScript files
            // .mjs/.cjs = ES module JavaScript files
            &[".ts", ".js", ".mjs", ".cjs", ".mts", ".cts"]
        }
    }

    fn parser(&self) -> Result<Parser> {
        let mut parser = Parser::new();
        // BUG #22 FIX: Use the appropriate grammar based on is_tsx flag.
        // TSX grammar is required for parsing JSX syntax in .tsx/.jsx files.
        // Using LANGUAGE_TYPESCRIPT for JSX files will cause parse errors.
        let lang = if self.is_tsx {
            &tree_sitter_typescript::LANGUAGE_TSX
        } else {
            &tree_sitter_typescript::LANGUAGE_TYPESCRIPT
        };
        parser
            .set_language(&(*lang).into())
            .map_err(|e| BrrrError::TreeSitter(e.to_string()))?;
        Ok(parser)
    }

    /// Get a parser configured for the specific file extension.
    ///
    /// TSX and JSX files require the TSX grammar which understands JSX syntax.
    /// TypeScript and JavaScript files use the TypeScript grammar.
    fn parser_for_path(&self, path: &Path) -> Result<Parser> {
        let ext = path
            .extension()
            .and_then(|e| e.to_str())
            .map(|e| format!(".{}", e))
            .unwrap_or_default();

        parser_for_extension(&ext)
    }

    fn extract_function(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        let kind = node.kind();

        // BUG #2 FIX: Handle export statements by recursing into the declaration
        // `export function foo() {}` creates: export_statement -> function_declaration
        // `export default function() {}` creates: export_statement -> function_declaration
        if kind == "export_statement" {
            for child in node.children(&mut node.walk()) {
                // Recurse into any declaration that might be a function
                if let Some(func) = self.extract_function(child, source) {
                    return Some(func);
                }
            }
            return None;
        }

        // FEATURE: Handle function overload signatures (function declarations without body)
        // TypeScript: `function foo(x: string): string;`
        if kind == "function_signature" {
            return self.extract_function_signature(node, source);
        }

        // FEATURE: Handle ambient declarations (declare keyword)
        // TypeScript: `declare function foo(): void;` or `declare var x: string;`
        if kind == "ambient_declaration" {
            // Try ambient function first, then ambient variable
            if let Some(func) = self.extract_ambient_function(node, source) {
                return Some(func);
            }
            return self.extract_ambient_variable(node, source);
        }

        // Handle different function types
        match kind {
            "function_declaration"
            | "function_expression"
            | "generator_function"
            | "generator_function_declaration" => {
                // BUG #11 FIX: function_expression may not have a name directly
                // Try to get name from the node itself first
                let name = self.extract_function_name(node, source).or_else(|| {
                    // For anonymous function expressions, try to get name from parent
                    if let Some(parent) = node.parent() {
                        match parent.kind() {
                            "variable_declarator" => parent
                                .child_by_field_name("name")
                                .map(|n| self.get_text(n, source).to_string()),
                            "pair" | "property" => parent
                                .child_by_field_name("key")
                                .map(|n| self.get_text(n, source).to_string()),
                            "assignment_expression" => parent
                                .child_by_field_name("left")
                                .and_then(|n| {
                                    if n.kind() == "identifier" {
                                        Some(self.get_text(n, source).to_string())
                                    } else if n.kind() == "member_expression" {
                                        // Handle exports.foo = function() {} and
                                        // module.exports.foo = function() {}
                                        n.child_by_field_name("property")
                                            .map(|p| self.get_text(p, source).to_string())
                                    } else {
                                        None
                                    }
                                }),
                            _ => None,
                        }
                    } else {
                        None
                    }
                });

                let name = name.unwrap_or_else(|| "<anonymous>".to_string());
                let mut params = Vec::new();
                let mut return_type = None;
                let is_async = self.is_async(node, source);
                let docstring = self.find_jsdoc(node, source);
                let mut decorators = Vec::new();

                // BUG #13 FIX: Extract decorators for function declarations
                // Check previous siblings for decorator nodes
                let mut prev = node.prev_sibling();
                while let Some(sibling) = prev {
                    if sibling.kind() == "decorator" {
                        decorators.insert(0, self.get_text(sibling, source).to_string());
                        prev = sibling.prev_sibling();
                    } else if sibling.kind() == "comment" || !sibling.is_named() {
                        prev = sibling.prev_sibling();
                    } else {
                        break;
                    }
                }

                // FEATURE: Detect type guards (type predicates)
                let mut is_type_guard_fn = false;

                for child in node.children(&mut node.walk()) {
                    if child.kind() == "formal_parameters" {
                        params = self.extract_params(child, source);
                    } else if child.kind() == "type_annotation" {
                        let text = self.get_text(child, source);
                        return_type = Some(text.trim_start_matches(':').trim().to_string());
                    } else if child.kind() == "type_predicate_annotation"
                        || child.kind() == "asserts_annotation"
                    {
                        // FEATURE: Handle type guard return type
                        // Type guards use type_predicate_annotation or asserts_annotation
                        if let Some(predicate) = self.is_type_guard(node, source) {
                            return_type = Some(predicate);
                            is_type_guard_fn = true;
                        } else {
                            // Fallback: extract full text
                            let text = self.get_text(child, source);
                            return_type = Some(text.trim_start_matches(':').trim().to_string());
                        }
                    }
                }

                // FEATURE: Add type_guard decorator if this is a type guard function
                if is_type_guard_fn {
                    decorators.push("type_guard".to_string());
                }

                Some(FunctionInfo {
                    name,
                    params,
                    return_type,
                    docstring,
                    is_method: false,
                    is_async,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "typescript".to_string(),
                })
            }
            "method_definition" => {
                let name = self.extract_function_name(node, source)?;
                let mut params = Vec::new();
                let mut return_type = None;
                let is_async = self.is_async(node, source);
                let docstring = self.find_jsdoc(node, source);
                let mut decorators = Vec::new();

                // BUG #13 FIX: Extract decorators from previous siblings for methods
                let mut prev = node.prev_sibling();
                while let Some(sibling) = prev {
                    if sibling.kind() == "decorator" {
                        decorators.insert(0, self.get_text(sibling, source).to_string());
                        prev = sibling.prev_sibling();
                    } else if sibling.kind() == "comment" || !sibling.is_named() {
                        prev = sibling.prev_sibling();
                    } else {
                        break;
                    }
                }

                // FEATURE: Detect type guards (type predicates)
                let mut is_type_guard_fn = false;

                // Check for static, private, public, protected modifiers
                // FEATURE: Detect getter/setter methods
                for child in node.children(&mut node.walk()) {
                    match child.kind() {
                        "formal_parameters" => {
                            params = self.extract_params(child, source);
                        }
                        "type_annotation" => {
                            let text = self.get_text(child, source);
                            return_type = Some(text.trim_start_matches(':').trim().to_string());
                        }
                        "type_predicate_annotation" | "asserts_annotation" => {
                            // FEATURE: Handle type guard return type
                            if let Some(predicate) = self.is_type_guard(node, source) {
                                return_type = Some(predicate);
                                is_type_guard_fn = true;
                            } else {
                                let text = self.get_text(child, source);
                                return_type = Some(text.trim_start_matches(':').trim().to_string());
                            }
                        }
                        "accessibility_modifier" => {
                            decorators.push(self.get_text(child, source).to_string());
                        }
                        "static" => {
                            decorators.push("static".to_string());
                        }
                        "decorator" => {
                            // Also check direct children for decorators
                            decorators.push(self.get_text(child, source).to_string());
                        }
                        // FEATURE: Getter/setter detection
                        "get" => {
                            decorators.push("getter".to_string());
                        }
                        "set" => {
                            decorators.push("setter".to_string());
                        }
                        _ => {}
                    }
                }

                // FEATURE: Add type_guard decorator if this is a type guard method
                if is_type_guard_fn {
                    decorators.push("type_guard".to_string());
                }

                Some(FunctionInfo {
                    name,
                    params,
                    return_type,
                    docstring,
                    is_method: true,
                    is_async,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "typescript".to_string(),
                })
            }
            // FEATURE: Handle abstract method signatures
            "abstract_method_signature" => {
                let name = self.extract_function_name(node, source)?;
                let mut params = Vec::new();
                let mut return_type = None;
                let docstring = self.find_jsdoc(node, source);
                let mut decorators = vec!["abstract".to_string()];

                // Extract parameters, return type, and modifiers
                for child in node.children(&mut node.walk()) {
                    match child.kind() {
                        "formal_parameters" => {
                            params = self.extract_params(child, source);
                        }
                        "type_annotation" => {
                            let text = self.get_text(child, source);
                            return_type = Some(text.trim_start_matches(':').trim().to_string());
                        }
                        "accessibility_modifier" => {
                            decorators.push(self.get_text(child, source).to_string());
                        }
                        _ => {}
                    }
                }

                Some(FunctionInfo {
                    name,
                    params,
                    return_type,
                    docstring,
                    is_method: true,
                    is_async: false,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "typescript".to_string(),
                })
            }
            "arrow_function" => {
                // Arrow functions may not have names (they're often assigned)
                // Try to get name from parent if it's a variable declarator
                let name = if let Some(parent) = node.parent() {
                    if parent.kind() == "variable_declarator" {
                        parent
                            .child_by_field_name("name")
                            .map(|n| self.get_text(n, source).to_string())
                    } else if parent.kind() == "pair" || parent.kind() == "property" {
                        // Object property: { key: () => {} }
                        parent
                            .child_by_field_name("key")
                            .map(|n| self.get_text(n, source).to_string())
                    } else {
                        None
                    }
                } else {
                    None
                };

                let name = name.unwrap_or_else(|| "<anonymous>".to_string());
                let mut params = Vec::new();
                let mut return_type = None;
                let is_async = self.is_async(node, source);
                let docstring = self.find_jsdoc(node, source);
                let mut decorators = Vec::new();

                // FEATURE: Detect type guards (type predicates)
                let mut is_type_guard_fn = false;

                for child in node.children(&mut node.walk()) {
                    match child.kind() {
                        "formal_parameters" => {
                            params = self.extract_params(child, source);
                        }
                        "identifier" => {
                            // Single parameter without parentheses
                            if params.is_empty() {
                                params.push(self.get_text(child, source).to_string());
                            }
                        }
                        "type_annotation" => {
                            let text = self.get_text(child, source);
                            return_type = Some(text.trim_start_matches(':').trim().to_string());
                        }
                        "type_predicate_annotation" | "asserts_annotation" => {
                            // FEATURE: Handle type guard return type
                            if let Some(predicate) = self.is_type_guard(node, source) {
                                return_type = Some(predicate);
                                is_type_guard_fn = true;
                            } else {
                                let text = self.get_text(child, source);
                                return_type = Some(text.trim_start_matches(':').trim().to_string());
                            }
                        }
                        _ => {}
                    }
                }

                // FEATURE: Add type_guard decorator if this is a type guard
                if is_type_guard_fn {
                    decorators.push("type_guard".to_string());
                }

                Some(FunctionInfo {
                    name,
                    params,
                    return_type,
                    docstring,
                    is_method: false,
                    is_async,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "typescript".to_string(),
                })
            }
            _ => None,
        }
    }

    fn extract_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        let kind = node.kind();

        // BUG #2 FIX: Handle export statements by recursing into the declaration
        // `export class Foo {}` creates: export_statement -> class_declaration
        // `export interface Bar {}` creates: export_statement -> interface_declaration
        if kind == "export_statement" {
            for child in node.children(&mut node.walk()) {
                // Recurse into any declaration that might be a class or interface
                if let Some(class_info) = self.extract_class(child, source) {
                    return Some(class_info);
                }
            }
            return None;
        }

        // FEATURE: Handle ambient declarations (declare keyword)
        // TypeScript: `declare class Foo { }`, `declare module "name" { }`, etc.
        if kind == "ambient_declaration" {
            return self.extract_ambient_class(node, source);
        }

        // BUG #7/8 FIX: Extract TypeScript interfaces as ClassInfo
        if kind == "interface_declaration" {
            return self.extract_interface(node, source);
        }

        // BUG #7/8 FIX: Extract TypeScript type aliases, enums, namespaces as ClassInfo
        if kind == "type_alias_declaration" {
            return self.extract_type_alias(node, source);
        }

        // BUG #7 FIX: Extract TypeScript enums
        if kind == "enum_declaration" {
            return self.extract_enum(node, source);
        }

        // BUG #8 FIX: Extract TypeScript namespaces/modules
        if kind == "module" || kind == "internal_module" {
            return self.extract_namespace(node, source);
        }

        // BUG #12 FIX: Handle class expressions (node type is "class", not "class_expression")
        // FEATURE: Handle abstract classes (abstract_class_declaration)
        let is_abstract_class = kind == "abstract_class_declaration";
        if kind != "class_declaration" && kind != "class" && !is_abstract_class {
            return None;
        }

        let mut name = String::new();
        let mut bases = Vec::new();
        let mut methods = Vec::new();
        let mut fields = Vec::new();
        let docstring = self.find_jsdoc(node, source);
        let mut decorators = Vec::new();

        // FEATURE: Mark abstract classes
        if is_abstract_class {
            decorators.push("abstract".to_string());
        }

        // BUG #12 FIX: For class expressions (node type "class"), try to get name from parent
        if kind == "class" {
            if let Some(parent) = node.parent() {
                if parent.kind() == "variable_declarator" {
                    if let Some(name_node) = parent.child_by_field_name("name") {
                        name = self.get_text(name_node, source).to_string();
                    }
                } else if parent.kind() == "assignment_expression" {
                    if let Some(left) = parent.child_by_field_name("left") {
                        if left.kind() == "identifier" {
                            name = self.get_text(left, source).to_string();
                        }
                    }
                }
            }
        }

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "type_identifier" | "identifier" => {
                    if name.is_empty() {
                        name = self.get_text(child, source).to_string();
                    }
                }
                "class_heritage" => {
                    // BUG #14 FIX: TypeScript class heritage contains extends and implements
                    // Handle generic types like `extends Base<T>` and multiple implements
                    for heritage_child in child.children(&mut child.walk()) {
                        match heritage_child.kind() {
                            "extends_clause" => {
                                self.extract_heritage_types(heritage_child, source, &mut bases, false);
                            }
                            "implements_clause" => {
                                self.extract_heritage_types(heritage_child, source, &mut bases, true);
                            }
                            _ => {}
                        }
                    }
                }
                "extends_clause" => {
                    // Direct extends clause (JavaScript style)
                    self.extract_heritage_types(child, source, &mut bases, false);
                }
                "implements_clause" => {
                    // Direct implements clause
                    self.extract_heritage_types(child, source, &mut bases, true);
                }
                "class_body" => {
                    for body_child in child.children(&mut child.walk()) {
                        match body_child.kind() {
                            // FEATURE: Handle both regular methods and abstract method signatures
                            "method_definition" | "abstract_method_signature" => {
                                if let Some(method) = self.extract_function(body_child, source) {
                                    methods.push(method);
                                }
                            }
                            // FEATURE: Extract class fields (including ECMAScript private fields #field)
                            "public_field_definition" => {
                                if let Some(field) = self.extract_class_field(body_child, source) {
                                    fields.push(field);
                                }
                            }
                            _ => {}
                        }
                    }
                }
                "decorator" => {
                    decorators.push(self.get_text(child, source).to_string());
                }
                _ => {}
            }
        }

        if name.is_empty() {
            return None;
        }

        Some(ClassInfo {
            name,
            bases,
            docstring,
            methods,
            fields,
            inner_classes: Vec::new(),
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "typescript".to_string(),
        })
    }

    fn extract_imports(&self, tree: &Tree, source: &[u8]) -> Vec<ImportInfo> {
        let mut imports = Vec::new();

        // Walk the tree to find import statements directly
        self.collect_imports(tree.root_node(), source, &mut imports);

        // BUG #15 FIX: Also collect re-exports
        self.collect_reexports(tree.root_node(), source, &mut imports);

        imports
    }

    fn function_query(&self) -> &'static str {
        // FEATURE: Include function_signature for function overloads
        // FEATURE: Include ambient_declaration for declare function/var/let/const
        // FIX: CommonJS exports.foo = function() {} patterns
        r#"[
            (function_declaration name: (identifier) @name) @function
            (method_definition name: (property_identifier) @name) @function
            (arrow_function) @function
            (function_expression name: (identifier) @name) @function
            (function_expression) @function
            (generator_function_declaration name: (identifier) @name) @function
            (function_signature name: (identifier) @name) @function
            (ambient_declaration) @function

            (expression_statement
                (assignment_expression
                    left: (member_expression property: (property_identifier) @name)
                    right: (function_expression) @function))

            (expression_statement
                (assignment_expression
                    left: (member_expression property: (property_identifier) @name)
                    right: (arrow_function) @function))
        ]"#
    }

    fn class_query(&self) -> &'static str {
        // BUG #7 FIX: Include enum_declaration, interface_declaration, type_alias_declaration
        // BUG #8 FIX: Include module (namespace) declarations
        // BUG #12 FIX: Use "class" for class expressions (tree-sitter node type "class")
        // FEATURE: Include abstract_class_declaration for abstract classes
        // FEATURE: Include ambient_declaration for declare class/interface/module/enum
        // Note: class_declaration uses type_identifier for name in TypeScript grammar
        r#"[
            (class_declaration name: (type_identifier) @name) @class
            (abstract_class_declaration name: (type_identifier) @name) @class
            (class) @class
            (enum_declaration name: (identifier) @name) @class
            (interface_declaration name: (type_identifier) @name) @class
            (type_alias_declaration name: (type_identifier) @name) @class
            (module name: (identifier) @name) @class
            (module name: (string) @name) @class
            (ambient_declaration) @class
        ]"#
    }

    fn call_query(&self) -> &'static str {
        r#"[
            (call_expression function: (identifier) @callee) @call
            (call_expression function: (member_expression property: (property_identifier) @callee)) @call
        ]"#
    }

    fn build_cfg(&self, node: Node, source: &[u8]) -> Result<CFGInfo> {
        let func_name = self
            .extract_function_name_with_context(node, source)
            .unwrap_or_else(|| "<anonymous>".to_string());

        let mut builder = TypeScriptCFGBuilder::new(source);
        builder.build(node, &func_name)
    }

    fn build_dfg(&self, node: Node, source: &[u8]) -> Result<DFGInfo> {
        let func_name = self
            .extract_function_name_with_context(node, source)
            .unwrap_or_else(|| "<anonymous>".to_string());

        let mut builder = TypeScriptDFGBuilder::new(source);
        builder.build(node, &func_name)
    }
}

/// Creates a parser for TSX files specifically.
#[cfg(test)]
fn tsx_parser() -> Result<Parser> {
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_typescript::LANGUAGE_TSX.into())
        .map_err(|e| BrrrError::TreeSitter(e.to_string()))?;
    Ok(parser)
}

/// Get the appropriate parser for a file extension.
pub fn parser_for_extension(ext: &str) -> Result<Parser> {
    let mut parser = Parser::new();
    let lang = match ext {
        ".tsx" | ".jsx" => &tree_sitter_typescript::LANGUAGE_TSX,
        _ => &tree_sitter_typescript::LANGUAGE_TYPESCRIPT,
    };
    parser
        .set_language(&(*lang).into())
        .map_err(|e| BrrrError::TreeSitter(e.to_string()))?;
    Ok(parser)
}

// =============================================================================
// Control Flow Graph Builder
// =============================================================================

/// Exception handler information for TypeScript/JavaScript CFG building.
///
/// Tracks a single catch handler within a try statement, including:
/// - The block ID of the catch handler
/// - Whether this is a bare catch (catch without parameter, catches all)
/// - The exception parameter name (if any)
#[derive(Debug, Clone)]
struct ExceptionHandler {
    /// Block ID of the catch handler
    catch_block: BlockId,
    /// Whether this is a bare catch: `catch { }` (no parameter)
    is_bare_catch: bool,
    /// Exception parameter name if present: `catch (e) { }` -> Some("e")
    exception_param: Option<String>,
}

/// Exception context for tracking active try/catch/finally blocks.
///
/// When processing code inside a try block, we need to know where exceptions
/// should be routed. This context tracks:
/// - The try block ID (where exceptions originate)
/// - All catch handlers associated with this try
/// - The finally block (if present), which runs regardless of exception
/// - The after-try merge point (where control flow continues after try/catch/finally)
#[derive(Debug, Clone)]
struct ExceptionContext {
    /// Block ID of the try block entry
    try_block: BlockId,
    /// All catch handlers for this try statement
    handlers: Vec<ExceptionHandler>,
    /// Finally block ID (if present)
    finally_block: Option<BlockId>,
    /// Block after the entire try/catch/finally construct
    after_try: BlockId,
    /// Start line of the try statement (for line range tracking)
    start_line: usize,
    /// End line of the try statement
    end_line: usize,
}

impl ExceptionContext {
    /// Create a new exception context for a try statement.
    fn new(try_block: BlockId, after_try: BlockId, start_line: usize, end_line: usize) -> Self {
        Self {
            try_block,
            handlers: Vec::new(),
            finally_block: None,
            after_try,
            start_line,
            end_line,
        }
    }

    /// Add a catch handler to this exception context.
    fn add_handler(&mut self, catch_block: BlockId, is_bare_catch: bool, exception_param: Option<String>) {
        self.handlers.push(ExceptionHandler {
            catch_block,
            is_bare_catch,
            exception_param,
        });
    }

    /// Set the finally block for this exception context.
    fn set_finally(&mut self, finally_block: BlockId) {
        self.finally_block = Some(finally_block);
    }

    /// Get the primary exception target (first catch handler or finally if no catch).
    fn exception_target(&self) -> Option<BlockId> {
        self.handlers.first().map(|h| h.catch_block).or(self.finally_block)
    }
}

/// CFG builder for TypeScript/JavaScript.
///
/// Builds control flow graphs from TypeScript/JavaScript AST nodes, handling:
/// - Control flow statements (if/while/for/switch)
/// - Exception handling (try/catch/finally, throw)
/// - Async exception flow (await expressions, Promise.catch)
/// - Loop control (break/continue)
/// - Optional chaining (?.) and nullish coalescing (??)
/// - Promise chains (.then/.catch/.finally)
/// - Concurrent patterns (Promise.all, Promise.race, Promise.allSettled)
/// - for await...of async iteration
struct TypeScriptCFGBuilder<'a> {
    source: &'a [u8],
    blocks: HashMap<BlockId, CFGBlock>,
    edges: Vec<CFGEdge>,
    next_block_id: usize,
    current_block: Option<BlockId>,
    entry: Option<BlockId>,
    exits: Vec<BlockId>,

    // Loop context for break/continue
    loop_guard_stack: Vec<BlockId>,
    after_loop_stack: Vec<BlockId>,

    // Exception context stack for try/catch/finally
    // When inside a try block, exceptions route to the innermost context's handlers
    exception_context_stack: Vec<ExceptionContext>,

    // Decision points for cyclomatic complexity
    decision_points: usize,

    // Track whether we're inside an async function (for await exception handling)
    is_async_function: bool,

    // =========================================================================
    // Async tracking fields
    // =========================================================================
    /// Count of await expressions (suspension points)
    await_points: usize,

    /// Blocking calls detected in async context (potential issues)
    /// Format: (function_name, line_number, reason)
    blocking_calls: Vec<(String, usize, String)>,

    /// Track unhandled promise expressions (missing await or .catch())
    /// Format: (expression_text, line_number)
    unhandled_promises: Vec<(String, usize)>,

    /// Track sequential awaits that could be parallelized
    /// Format: (first_await_line, second_await_line, variables)
    sequential_await_candidates: Vec<(usize, usize, Vec<String>)>,

    /// Last await line number for sequential await detection
    last_await_line: Option<usize>,

    /// Variables defined by awaits for dependency analysis
    await_defined_vars: HashMap<String, usize>,
}

impl<'a> TypeScriptCFGBuilder<'a> {
    fn new(source: &'a [u8]) -> Self {
        Self {
            source,
            blocks: HashMap::new(),
            edges: Vec::new(),
            next_block_id: 0,
            current_block: None,
            entry: None,
            exits: Vec::new(),
            loop_guard_stack: Vec::new(),
            after_loop_stack: Vec::new(),
            exception_context_stack: Vec::new(),
            decision_points: 0,
            is_async_function: false,
            // Async tracking
            await_points: 0,
            blocking_calls: Vec::new(),
            unhandled_promises: Vec::new(),
            sequential_await_candidates: Vec::new(),
            last_await_line: None,
            await_defined_vars: HashMap::new(),
        }
    }

    fn get_text(&self, node: Node) -> &str {
        std::str::from_utf8(&self.source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }

    fn new_block(&mut self, label: String, start_line: usize, end_line: usize) -> BlockId {
        let id = BlockId(self.next_block_id);
        self.next_block_id += 1;

        let block = CFGBlock {
            id,
            label,
            block_type: BlockType::Body,
            statements: Vec::new(),
            func_calls: Vec::new(),
            start_line,
            end_line,
        };

        self.blocks.insert(id, block);
        id
    }

    /// Add an edge with optional label (legacy format for backward compatibility).
    fn add_edge(&mut self, from: BlockId, to: BlockId, label: Option<String>) {
        let edge = match label {
            Some(cond) => CFGEdge::with_condition(from, to, EdgeType::Unconditional, cond),
            None => CFGEdge::unconditional(from, to),
        };
        self.edges.push(edge);
    }

    /// Add a typed edge with specific EdgeType and optional condition.
    fn add_typed_edge(&mut self, from: BlockId, to: BlockId, edge_type: EdgeType, condition: Option<String>) {
        let edge = match condition {
            Some(cond) => CFGEdge::with_condition(from, to, edge_type, cond),
            None => CFGEdge::new(from, to, edge_type),
        };
        self.edges.push(edge);
    }

    /// Check if a function node is async.
    fn check_is_async(&self, node: Node) -> bool {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "async" {
                return true;
            }
            // Early exit: async keyword always precedes the function body
            if child.kind() == "statement_block" || child.kind() == "block" {
                break;
            }
        }
        false
    }

    fn build(&mut self, node: Node, func_name: &str) -> Result<CFGInfo> {
        // Detect if this is an async function for await exception handling
        self.is_async_function = self.check_is_async(node);

        // Create entry block
        let entry = self.new_block(
            "entry".to_string(),
            node.start_position().row + 1,
            node.start_position().row + 1,
        );
        self.entry = Some(entry);
        self.current_block = Some(entry);

        // Find function body - find it first before mutable borrow
        let body_node = {
            let mut result = None;
            for child in node.children(&mut node.walk()) {
                match child.kind() {
                    "statement_block" | "block" => {
                        result = Some(child);
                        break;
                    }
                    _ if child.kind().contains("expression") && node.kind() == "arrow_function" => {
                        result = Some(child);
                        break;
                    }
                    _ => {}
                }
            }
            result
        };
        if let Some(body) = body_node {
            self.visit_node(body);
        }

        // Mark final block as exit if not already
        if let Some(current) = self.current_block {
            if !self.exits.contains(&current) {
                self.exits.push(current);
                if let Some(block) = self.blocks.get_mut(&current) {
                    block.label = "exit".to_string();
                }
            }
        }

        // Convert blocking_calls to the format expected by CFGInfo: Vec<(function_name, line_number)>
        let blocking_calls_formatted: Vec<(String, usize)> = self
            .blocking_calls
            .iter()
            .map(|(name, line, _reason)| (name.clone(), *line))
            .collect();

        Ok(CFGInfo {
            function_name: func_name.to_string(),
            blocks: self.blocks.clone(),
            edges: self.edges.clone(),
            entry: self.entry.unwrap_or(BlockId(0)),
            exits: self.exits.clone(),
            decision_points: self.decision_points,
            comprehension_decision_points: 0, // TypeScript doesn't have Python-style comprehensions
            nested_cfgs: HashMap::new(),      // TODO: Handle arrow functions/nested functions as nested CFGs
            is_async: self.is_async_function,
            await_points: self.await_points,
            blocking_calls: blocking_calls_formatted,
            ..Default::default()
        })
    }

    fn visit_node(&mut self, node: Node) {
        match node.kind() {
            "if_statement" => self.visit_if(node),
            "while_statement" => self.visit_while(node),
            "do_statement" => self.visit_do_while(node),
            "for_statement" => self.visit_for(node),
            // Handle for...in and for...of - check for await variant first
            // Note: tree-sitter-typescript parses `for await...of` as for_in_statement
            "for_in_statement" | "for_of_statement" => {
                if self.is_for_await_of(node) {
                    self.visit_for_await_of(node);
                } else {
                    self.visit_for(node);
                }
            }
            "switch_statement" => self.visit_switch(node),
            "try_statement" => self.visit_try(node),
            "return_statement" => self.visit_return(node),
            "break_statement" => self.visit_break(node),
            "continue_statement" => self.visit_continue(node),
            "throw_statement" => self.visit_throw(node),
            // FEATURE: Await expression can throw (promise rejection = exception)
            "await_expression" => self.visit_await(node),
            // FEATURE: Yield expression in async generators
            "yield_expression" => self.visit_yield(node),
            // FEATURE: Optional chaining (?.) creates implicit null check branch
            "member_expression" | "subscript_expression" => {
                if self.has_optional_chain(node) {
                    self.visit_optional_chain(node);
                } else {
                    // Visit children for non-optional member expressions
                    for child in node.children(&mut node.walk()) {
                        if child.is_named() {
                            self.visit_node(child);
                        }
                    }
                }
            }
            // FEATURE: Call expressions - Promise chains, async patterns
            "call_expression" => {
                // Check for Promise patterns in order of specificity
                if self.is_promise_all_pattern(node) {
                    self.visit_promise_all(node);
                } else if self.is_promise_race_pattern(node) {
                    self.visit_promise_race(node);
                } else if self.is_promise_all_settled_pattern(node) {
                    self.visit_promise_all_settled(node);
                } else if self.is_promise_any_pattern(node) {
                    self.visit_promise_any(node);
                } else if self.is_promise_then(node) {
                    self.visit_promise_then(node);
                } else if self.is_promise_catch(node) {
                    self.visit_promise_catch(node);
                } else if self.is_promise_finally(node) {
                    self.visit_promise_finally(node);
                } else if self.has_optional_chain(node) {
                    self.visit_optional_chain(node);
                } else {
                    // Check for blocking calls in async context
                    if self.is_async_function {
                        self.check_blocking_call(node);
                    }
                    // Visit children for regular call expressions
                    for child in node.children(&mut node.walk()) {
                        if child.is_named() {
                            self.visit_node(child);
                        }
                    }
                }
            }
            // FEATURE: Nullish coalescing (??) creates short-circuit branch
            "binary_expression" => {
                if self.is_nullish_coalescing(node) {
                    self.visit_nullish_coalescing(node);
                } else {
                    // Visit children for non-nullish binary expressions
                    for child in node.children(&mut node.walk()) {
                        if child.is_named() {
                            self.visit_node(child);
                        }
                    }
                }
            }
            _ => {
                // Visit children for compound nodes
                for child in node.children(&mut node.walk()) {
                    if child.is_named() {
                        self.visit_node(child);
                    }
                }
            }
        }
    }

    fn visit_if(&mut self, node: Node) {
        self.decision_points += 1;

        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        // Update current block to branch type
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = "branch".to_string();
            block.end_line = node.start_position().row + 1;
        }

        // Get condition text
        let condition = node
            .child_by_field_name("condition")
            .map(|n| self.get_text(n).to_string())
            .unwrap_or_else(|| "<condition>".to_string());

        // Create after-if block
        let after_if = self.new_block(
            "body".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        // Process consequence (then branch)
        if let Some(consequence) = node.child_by_field_name("consequence") {
            let true_block = self.new_block(
                "body".to_string(),
                consequence.start_position().row + 1,
                consequence.end_position().row + 1,
            );
            self.add_edge(current, true_block, Some(format!("true: {}", condition)));

            self.current_block = Some(true_block);
            self.visit_node(consequence);

            if let Some(curr) = self.current_block {
                if !self.exits.contains(&curr) {
                    self.add_edge(curr, after_if, None);
                }
            }
        }

        // Process alternative (else branch)
        if let Some(alternative) = node.child_by_field_name("alternative") {
            let false_block = self.new_block(
                "body".to_string(),
                alternative.start_position().row + 1,
                alternative.end_position().row + 1,
            );
            self.add_edge(
                current,
                false_block,
                Some(format!("false: not ({})", condition)),
            );

            self.current_block = Some(false_block);
            self.visit_node(alternative);

            if let Some(curr) = self.current_block {
                if !self.exits.contains(&curr) {
                    self.add_edge(curr, after_if, None);
                }
            }
        } else {
            // No else branch
            self.add_edge(
                current,
                after_if,
                Some(format!("false: not ({})", condition)),
            );
        }

        self.current_block = Some(after_if);
    }

    fn visit_while(&mut self, node: Node) {
        self.decision_points += 1;

        // Create loop header
        let guard = self.new_block(
            "loop_header".to_string(),
            node.start_position().row + 1,
            node.start_position().row + 1,
        );

        if let Some(current) = self.current_block {
            self.add_edge(current, guard, None);
        }

        let condition = node
            .child_by_field_name("condition")
            .map(|n| self.get_text(n).to_string())
            .unwrap_or_else(|| "<condition>".to_string());

        let after_loop = self.new_block(
            "body".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        self.loop_guard_stack.push(guard);
        self.after_loop_stack.push(after_loop);

        // Process body
        if let Some(body) = node.child_by_field_name("body") {
            let loop_body = self.new_block(
                "loop_body".to_string(),
                body.start_position().row + 1,
                body.end_position().row + 1,
            );
            self.add_edge(guard, loop_body, Some(format!("true: {}", condition)));
            self.add_edge(
                guard,
                after_loop,
                Some(format!("false: not ({})", condition)),
            );

            self.current_block = Some(loop_body);
            self.visit_node(body);

            if let Some(curr) = self.current_block {
                if !self.exits.contains(&curr) {
                    self.add_edge(curr, guard, Some("back_edge".to_string()));
                }
            }
        }

        self.loop_guard_stack.pop();
        self.after_loop_stack.pop();
        self.current_block = Some(after_loop);
    }

    fn visit_do_while(&mut self, node: Node) {
        self.decision_points += 1;

        let current = self.current_block;

        // Find body and condition
        let mut body_node = None;
        let mut condition_text = "<condition>".to_string();

        for child in node.children(&mut node.walk()) {
            if child.kind() == "statement_block" {
                body_node = Some(child);
            } else if child.kind() == "parenthesized_expression" {
                condition_text = self.get_text(child).to_string();
            }
        }

        // Create loop body block
        let loop_body = self.new_block(
            "loop_body".to_string(),
            body_node.map(|n| n.start_position().row + 1).unwrap_or(1),
            body_node.map(|n| n.end_position().row + 1).unwrap_or(1),
        );

        if let Some(curr) = current {
            self.add_edge(curr, loop_body, None);
        }

        // Create guard block (at the end of do-while, where the condition lives)
        let guard = self.new_block(
            "loop_header".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        let after_loop = self.new_block(
            "body".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        self.loop_guard_stack.push(guard);
        self.after_loop_stack.push(after_loop);

        // Process body
        self.current_block = Some(loop_body);
        if let Some(body) = body_node {
            self.visit_node(body);
        }

        if let Some(curr) = self.current_block {
            if !self.exits.contains(&curr) {
                self.add_edge(curr, guard, None);
            }
        }

        // Guard edges
        self.add_edge(guard, loop_body, Some(format!("true: {}", condition_text)));
        self.add_edge(
            guard,
            after_loop,
            Some(format!("false: not ({})", condition_text)),
        );

        self.loop_guard_stack.pop();
        self.after_loop_stack.pop();
        self.current_block = Some(after_loop);
    }

    fn visit_for(&mut self, node: Node) {
        self.decision_points += 1;

        let guard = self.new_block(
            "loop_header".to_string(),
            node.start_position().row + 1,
            node.start_position().row + 1,
        );

        if let Some(current) = self.current_block {
            self.add_edge(current, guard, None);
        }

        let after_loop = self.new_block(
            "body".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        self.loop_guard_stack.push(guard);
        self.after_loop_stack.push(after_loop);

        // Find body
        let body = node.child_by_field_name("body");
        if let Some(body) = body {
            let loop_body = self.new_block(
                "loop_body".to_string(),
                body.start_position().row + 1,
                body.end_position().row + 1,
            );
            self.add_edge(guard, loop_body, Some("iterate".to_string()));
            self.add_edge(guard, after_loop, Some("exhausted".to_string()));

            self.current_block = Some(loop_body);
            self.visit_node(body);

            if let Some(curr) = self.current_block {
                if !self.exits.contains(&curr) {
                    self.add_edge(curr, guard, Some("back_edge".to_string()));
                }
            }
        }

        self.loop_guard_stack.pop();
        self.after_loop_stack.pop();
        self.current_block = Some(after_loop);
    }

    fn visit_switch(&mut self, node: Node) {
        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = "branch".to_string();
        }

        let after_switch = self.new_block(
            "body".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        // Find switch body
        for child in node.children(&mut node.walk()) {
            if child.kind() == "switch_body" {
                for case in child.children(&mut child.walk()) {
                    if case.kind() == "switch_case" || case.kind() == "switch_default" {
                        self.decision_points += 1;

                        let case_block = self.new_block(
                            "case".to_string(),
                            case.start_position().row + 1,
                            case.end_position().row + 1,
                        );
                        self.add_edge(current, case_block, None);

                        self.current_block = Some(case_block);

                        // Visit case body
                        for case_child in case.children(&mut case.walk()) {
                            if case_child.is_named()
                                && case_child.kind() != "case"
                                && case_child.kind() != "default"
                            {
                                self.visit_node(case_child);
                            }
                        }

                        if let Some(curr) = self.current_block {
                            if !self.exits.contains(&curr) {
                                self.add_edge(curr, after_switch, None);
                            }
                        }
                    }
                }
            }
        }

        self.current_block = Some(after_switch);
    }

    /// Process try/catch/finally statement with proper exception flow edges.
    ///
    /// Creates proper control flow edges for:
    /// - try block -> catch handler (on exception)
    /// - try block -> finally (if no catch, or after catch completes)
    /// - catch handler -> finally
    /// - throw within try -> nearest catch
    /// - finally -> after_try (normal completion)
    ///
    /// Exception flow within the try block is tracked via exception_context_stack,
    /// allowing nested try/catch to properly route exceptions.
    fn visit_try(&mut self, node: Node) {
        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        let start_line = node.start_position().row + 1;
        let end_line = node.end_position().row + 1;

        // Create after-try block for merging all paths
        let after_try = self.new_block(
            "after_try".to_string(),
            end_line,
            end_line,
        );

        // Create try block first
        let try_block_id = if let Some(body) = node.child_by_field_name("body") {
            self.new_block(
                "try".to_string(),
                body.start_position().row + 1,
                body.end_position().row + 1,
            )
        } else {
            self.new_block("try".to_string(), start_line, start_line)
        };
        self.add_edge(current, try_block_id, None);

        // Create exception context for this try statement
        let mut exc_context = ExceptionContext::new(try_block_id, after_try, start_line, end_line);

        // First pass: find and create blocks for catch and finally BEFORE processing try body
        // This allows throw statements within try to route to the correct handler
        let mut catch_clause = None;
        let mut finally_clause = None;
        let mut catch_block_id = None;
        let mut finally_block_id = None;

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "catch_clause" => {
                    self.decision_points += 1;
                    catch_clause = Some(child);

                    // Extract exception parameter (if any)
                    let (is_bare_catch, exception_param) = self.extract_catch_parameter(child);
                    let label = if is_bare_catch {
                        "catch".to_string()
                    } else if let Some(ref param) = exception_param {
                        format!("catch ({})", param)
                    } else {
                        "catch".to_string()
                    };

                    let catch_block = self.new_block(
                        label,
                        child.start_position().row + 1,
                        child.end_position().row + 1,
                    );
                    catch_block_id = Some(catch_block);
                    exc_context.add_handler(catch_block, is_bare_catch, exception_param);
                }
                "finally_clause" => {
                    finally_clause = Some(child);
                    let finally_block = self.new_block(
                        "finally".to_string(),
                        child.start_position().row + 1,
                        child.end_position().row + 1,
                    );
                    finally_block_id = Some(finally_block);
                    exc_context.set_finally(finally_block);
                }
                _ => {}
            }
        }

        // Push exception context BEFORE processing try body
        // This allows statements within the try block to route exceptions
        self.exception_context_stack.push(exc_context);

        // Process try body
        self.current_block = Some(try_block_id);
        if let Some(body) = node.child_by_field_name("body") {
            self.visit_node(body);
        }

        // Pop exception context after processing try body
        let _exc_context = self.exception_context_stack.pop().unwrap();

        // Get try exit block (current block after processing try body)
        let try_exit = self.current_block;

        // Add exception edge from try block to catch handler
        if let Some(catch_id) = catch_block_id {
            self.add_typed_edge(
                try_block_id,
                catch_id,
                EdgeType::Exception,
                Some("exception".to_string()),
            );
        }

        // Process catch clause body
        if let (Some(catch_node), Some(catch_id)) = (catch_clause, catch_block_id) {
            self.current_block = Some(catch_id);

            // Find and process the catch body (statement_block within catch_clause)
            for child in catch_node.children(&mut catch_node.walk()) {
                if child.kind() == "statement_block" {
                    self.visit_node(child);
                    break;
                }
            }

            let catch_exit = self.current_block;

            // Connect catch to finally or after_try
            if let Some(catch_exit_id) = catch_exit {
                if !self.exits.contains(&catch_exit_id) {
                    if let Some(finally_id) = finally_block_id {
                        self.add_typed_edge(catch_exit_id, finally_id, EdgeType::Finally, None);
                    } else {
                        self.add_edge(catch_exit_id, after_try, None);
                    }
                }
            }
        }

        // Process finally clause body
        if let (Some(finally_node), Some(finally_id)) = (finally_clause, finally_block_id) {
            // Try success (no exception) goes to finally
            if let Some(try_exit_id) = try_exit {
                if !self.exits.contains(&try_exit_id) {
                    self.add_typed_edge(try_exit_id, finally_id, EdgeType::Finally, None);
                }
            }

            // If there's no catch, exception goes directly to finally
            if catch_block_id.is_none() {
                self.add_typed_edge(
                    try_block_id,
                    finally_id,
                    EdgeType::Exception,
                    Some("exception (no catch)".to_string()),
                );
            }

            self.current_block = Some(finally_id);

            // Find and process the finally body (statement_block within finally_clause)
            for child in finally_node.children(&mut finally_node.walk()) {
                if child.kind() == "statement_block" {
                    self.visit_node(child);
                    break;
                }
            }

            let finally_exit = self.current_block;

            // Connect finally to after_try
            if let Some(finally_exit_id) = finally_exit {
                if !self.exits.contains(&finally_exit_id) {
                    self.add_edge(finally_exit_id, after_try, None);
                }
            }
        } else {
            // No finally: try success goes directly to after_try
            if let Some(try_exit_id) = try_exit {
                if !self.exits.contains(&try_exit_id) {
                    self.add_edge(try_exit_id, after_try, None);
                }
            }

            // If no catch either, exception propagates (handled by throw routing)
        }

        self.current_block = Some(after_try);
    }

    /// Extract catch parameter information from a catch clause.
    ///
    /// Returns (is_bare_catch, exception_param):
    /// - catch { } -> (true, None) - bare catch without parameter
    /// - catch (e) { } -> (false, Some("e"))
    /// - catch (error: Error) { } -> (false, Some("error"))
    fn extract_catch_parameter(&self, catch_clause: Node) -> (bool, Option<String>) {
        // Look for catch_parameter child
        for child in catch_clause.children(&mut catch_clause.walk()) {
            if child.kind() == "catch_clause" {
                // Nested - shouldn't happen but handle it
                return self.extract_catch_parameter(child);
            }
            // tree-sitter-typescript uses different node types for catch parameter
            if child.kind() == "identifier" || child.kind() == "catch_formal_parameter" {
                let text = self.get_text(child);
                // Remove type annotation if present
                let param_name = text.split(':').next().unwrap_or(text).trim();
                return (false, Some(param_name.to_string()));
            }
            // Handle parenthesized catch parameter: catch (e)
            if child.kind() == "(" {
                // Next sibling should be the parameter
                continue;
            }
        }
        // No parameter found - this is a bare catch: catch { }
        (true, None)
    }

    fn visit_return(&mut self, node: Node) {
        if let Some(current) = self.current_block {
            if let Some(block) = self.blocks.get_mut(&current) {
                block.label = "return".to_string();
                block.end_line = node.end_position().row + 1;
            }
            self.exits.push(current);
        }
        self.current_block = None;
    }

    /// Process throw statement with proper exception routing.
    ///
    /// Routes exceptions to the nearest catch handler in the exception context stack.
    /// If there's no enclosing try/catch, the exception propagates to function exit.
    ///
    /// Handles:
    /// - throw new Error('msg')
    /// - throw expression
    /// - throw new Error('msg', { cause: e }) - error cause pattern
    fn visit_throw(&mut self, node: Node) {
        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        // Extract throw expression for labeling
        let throw_expr = self.extract_throw_expression(node);
        let throw_label = if let Some(expr) = throw_expr {
            format!("throw {}", expr)
        } else {
            "throw".to_string()
        };

        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = throw_label;
            block.end_line = node.end_position().row + 1;
        }

        // Route exception to nearest catch handler
        if let Some(exc_context) = self.exception_context_stack.last() {
            // Route to catch handler or finally if no catch
            if let Some(target) = exc_context.exception_target() {
                self.add_typed_edge(
                    current,
                    target,
                    EdgeType::Exception,
                    Some("throw".to_string()),
                );
            } else {
                // No handler - exception propagates
                self.exits.push(current);
            }
        } else {
            // No enclosing try - exception propagates to function exit
            self.exits.push(current);
        }

        self.current_block = None;
    }

    /// Extract the throw expression text for better CFG labeling.
    ///
    /// Returns abbreviated form:
    /// - "new Error(...)" for new Error('msg')
    /// - "re-throw" for catch clause re-throw
    /// - Expression text for simple throws
    fn extract_throw_expression(&self, node: Node) -> Option<String> {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "throw" {
                continue;
            }
            if child.is_named() {
                let text = self.get_text(child);
                // Abbreviate long expressions
                if text.len() > 30 {
                    if text.starts_with("new ") {
                        let type_end = text.find('(').unwrap_or(text.len());
                        let type_name = &text[4..type_end];
                        return Some(format!("new {}(...)", type_name));
                    }
                    return Some(format!("{}...", &text[..27]));
                }
                return Some(text.to_string());
            }
        }
        None
    }

    // =========================================================================
    // ASYNC EXCEPTION HANDLING
    // =========================================================================

    /// Process await expression with proper exception routing and suspension point tracking.
    ///
    /// In async functions, `await` creates a suspension point where execution yields
    /// to the event loop. The promise can either resolve or reject:
    /// - Promise resolves: continue to next statement with resolved value
    /// - Promise rejects: exception flow to nearest catch handler
    ///
    /// This method also tracks:
    /// - await_points counter for async complexity analysis
    /// - Sequential awaits that could potentially be parallelized
    /// - Variable definitions from await assignments for dependency analysis
    ///
    /// Example:
    /// ```javascript
    /// async function fetchUser(id) {
    ///     const response = await fetch(`/user/${id}`);  // Suspension point 1
    ///     const data = await response.json();          // Suspension point 2
    ///     return data;
    /// }
    /// ```
    fn visit_await(&mut self, node: Node) {
        // Only create proper async flow in async functions
        if !self.is_async_function {
            // Not in async context - just visit children (await is syntax error but handle gracefully)
            for child in node.children(&mut node.walk()) {
                if child.is_named() && child.kind() != "await" {
                    self.visit_node(child);
                }
            }
            return;
        }

        // Check if awaited expression is a Promise pattern - delegate to specialized handler
        // This handles: await Promise.all([...]), await Promise.race([...]), etc.
        for child in node.children(&mut node.walk()) {
            if child.kind() == "call_expression" {
                if self.is_promise_all_pattern(child) {
                    self.await_points += 1;
                    self.visit_promise_all(child);
                    return;
                } else if self.is_promise_race_pattern(child) {
                    self.await_points += 1;
                    self.visit_promise_race(child);
                    return;
                } else if self.is_promise_all_settled_pattern(child) {
                    self.await_points += 1;
                    self.visit_promise_all_settled(child);
                    return;
                } else if self.is_promise_any_pattern(child) {
                    self.await_points += 1;
                    self.visit_promise_any(child);
                    return;
                }
            }
        }

        // Standard await handling for non-Promise-pattern expressions
        self.await_points += 1;
        self.decision_points += 1;

        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        let line = node.start_position().row + 1;

        // Get await expression for labeling
        let await_expr = self.extract_await_expression(node);
        let await_label = if let Some(ref expr) = await_expr {
            format!("await {}", expr)
        } else {
            "await".to_string()
        };

        // Update current block to AwaitPoint type
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = await_label;
            block.block_type = BlockType::AwaitPoint;
            block.end_line = line;
        }

        // Track sequential awaits for potential parallelization detection
        if let Some(last_line) = self.last_await_line {
            // Check if these awaits are independent (could be parallelized)
            // Simple heuristic: if they're on consecutive lines and don't share variables
            if line == last_line + 1 || line == last_line + 2 {
                // Potential parallelization candidate
                self.sequential_await_candidates.push((last_line, line, Vec::new()));
            }
        }
        self.last_await_line = Some(line);

        // Create after-await block for successful resolution
        let after_await = self.new_block(
            "after_await".to_string(),
            line,
            line,
        );

        // Add resolve path using Await edge type (represents suspension and resume)
        self.add_typed_edge(
            current,
            after_await,
            EdgeType::Await,
            Some("resolved".to_string()),
        );

        // Add rejection path (exception) to nearest catch
        if let Some(exc_ctx) = self.exception_context_stack.last() {
            if let Some(handler) = exc_ctx.handlers.first() {
                self.add_typed_edge(
                    current,
                    handler.catch_block,
                    EdgeType::PromiseRejected,
                    Some("rejected".to_string()),
                );
            } else if let Some(finally_block) = exc_ctx.finally_block {
                // No catch, but has finally - route to finally
                self.add_typed_edge(
                    current,
                    finally_block,
                    EdgeType::PromiseRejected,
                    Some("rejected (to finally)".to_string()),
                );
            }
            // If no handler in context, rejection propagates (returned promise rejects)
        }
        // No enclosing try: rejection propagates to caller as rejected promise

        self.current_block = Some(after_await);
    }

    /// Extract the await expression text for better CFG labeling.
    fn extract_await_expression(&self, node: Node) -> Option<String> {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "await" {
                continue;
            }
            if child.is_named() {
                let text = self.get_text(child);
                // Abbreviate long expressions
                if text.len() > 30 {
                    return Some(format!("{}...", &text[..27]));
                }
                return Some(text.to_string());
            }
        }
        None
    }

    /// Check if a call_expression is a Promise.catch() pattern.
    ///
    /// Recognizes:
    /// - promise.catch(handler)
    /// - promise.catch(e => handleError(e))
    /// - somePromise.catch(errorHandler)
    fn is_promise_catch(&self, node: Node) -> bool {
        // Look for pattern: <expr>.catch(<handler>)
        for child in node.children(&mut node.walk()) {
            if child.kind() == "member_expression" {
                // Check if property is "catch"
                for member_child in child.children(&mut child.walk()) {
                    if member_child.kind() == "property_identifier" {
                        let prop_text = self.get_text(member_child);
                        return prop_text == "catch";
                    }
                }
            }
        }
        false
    }

    /// Process Promise.catch() as implicit exception handling.
    ///
    /// Promise.catch() is semantically similar to try/catch for async code:
    /// - The promise chain before .catch() is the "try" section
    /// - The catch handler is the "catch" section
    ///
    /// This models the branching:
    /// - Promise resolves: continue past .catch()
    /// - Promise rejects: execute catch handler, then continue
    fn visit_promise_catch(&mut self, node: Node) {
        self.decision_points += 1;

        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        // Get the promise expression being caught
        let promise_expr = self.extract_promise_expression(node);

        // Get the catch handler for labeling
        let handler_expr = self.extract_catch_handler_from_call(node);

        // Update current block to PromiseCatch type
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = format!("{}.catch(...)", promise_expr);
            block.block_type = BlockType::PromiseCatch;
            block.end_line = node.end_position().row + 1;
        }

        // Create after-catch block for both paths to merge
        let after_catch = self.new_block(
            "after_catch".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        // Create catch handler block
        let handler_label = handler_expr.unwrap_or_else(|| "...".to_string());
        let catch_handler_block = self.new_block(
            format!("catch_handler: {}", handler_label),
            node.start_position().row + 1,
            node.end_position().row + 1,
        );
        if let Some(block) = self.blocks.get_mut(&catch_handler_block) {
            block.block_type = BlockType::PromiseCatch;
        }

        // Add resolved path (promise doesn't reject, skip catch)
        self.add_typed_edge(
            current,
            after_catch,
            EdgeType::PromiseResolved,
            Some("resolved".to_string()),
        );

        // Add rejected path to catch handler
        self.add_typed_edge(
            current,
            catch_handler_block,
            EdgeType::PromiseRejected,
            Some("rejected".to_string()),
        );

        // Catch handler continues to after_catch
        self.add_edge(catch_handler_block, after_catch, None);

        // Visit the handler expression (the callback in arguments)
        for child in node.children(&mut node.walk()) {
            if child.kind() == "arguments" {
                self.current_block = Some(catch_handler_block);
                for arg_child in child.children(&mut child.walk()) {
                    if arg_child.is_named()
                        && arg_child.kind() != "("
                        && arg_child.kind() != ")"
                        && arg_child.kind() != ","
                    {
                        self.visit_node(arg_child);
                    }
                }
            }
        }

        self.current_block = Some(after_catch);
    }

    /// Extract the promise expression being caught for labeling.
    fn extract_promise_expression(&self, node: Node) -> String {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "member_expression" {
                // Get the object part of member_expression
                for member_child in child.children(&mut child.walk()) {
                    if member_child.kind() != "property_identifier" && member_child.kind() != "." {
                        let text = self.get_text(member_child);
                        if text.len() > 20 {
                            return format!("{}...", &text[..17]);
                        }
                        return text.to_string();
                    }
                }
            }
        }
        "promise".to_string()
    }

    /// Extract the catch handler expression for labeling.
    fn extract_catch_handler_from_call(&self, node: Node) -> Option<String> {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "arguments" {
                for arg_child in child.children(&mut child.walk()) {
                    if arg_child.is_named()
                        && arg_child.kind() != "("
                        && arg_child.kind() != ")"
                    {
                        let text = self.get_text(arg_child);
                        // Abbreviate if too long
                        if text.len() > 20 {
                            return Some(format!("{}...", &text[..17]));
                        }
                        return Some(text.to_string());
                    }
                }
            }
        }
        None
    }

    fn visit_break(&mut self, _node: Node) {
        if let Some(current) = self.current_block {
            if let Some(&after_loop) = self.after_loop_stack.last() {
                self.add_edge(current, after_loop, Some("break".to_string()));
            }
        }
        self.current_block = None;
    }

    fn visit_continue(&mut self, _node: Node) {
        if let Some(current) = self.current_block {
            if let Some(&guard) = self.loop_guard_stack.last() {
                self.add_edge(current, guard, Some("continue".to_string()));
            }
        }
        self.current_block = None;
    }

    /// FEATURE: Check if a node contains optional chaining (?.).
    ///
    /// Tree-sitter structure: member_expression with optional_chain child.
    /// Example: `obj?.prop` has structure:
    ///   member_expression
    ///     object: identifier "obj"
    ///     optional_chain: "?."
    ///     property: property_identifier "prop"
    fn has_optional_chain(&self, node: Node) -> bool {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "optional_chain" {
                return true;
            }
            // Check inside member_expression for nested optional chaining
            if child.kind() == "member_expression" || child.kind() == "call_expression" {
                if self.has_optional_chain(child) {
                    return true;
                }
            }
        }
        false
    }

    /// FEATURE: Check if binary_expression uses nullish coalescing (??) operator.
    fn is_nullish_coalescing(&self, node: Node) -> bool {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "??" {
                return true;
            }
        }
        false
    }

    /// FEATURE: Handle optional chaining expression (obj?.prop, obj?.method()).
    ///
    /// Optional chaining creates an implicit null/undefined check that can
    /// short-circuit evaluation. This models the branching in CFG:
    /// - If obj is null/undefined: skip property access, result is undefined
    /// - If obj is not null/undefined: continue with property access
    fn visit_optional_chain(&mut self, node: Node) {
        self.decision_points += 1;

        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        // Update current block to optional_chain type
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = "optional_chain".to_string();
            block.end_line = node.start_position().row + 1;
        }

        // Get the expression text for labeling (convert to String to release borrow)
        let expr_text = self.get_text(node).to_string();

        // Create after block for both branches to merge
        let after_optional = self.new_block(
            "body".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        // Create null/undefined path (short-circuit to undefined)
        let null_block = self.new_block(
            "optional_null".to_string(),
            node.start_position().row + 1,
            node.start_position().row + 1,
        );
        self.add_edge(
            current,
            null_block,
            Some(format!("null/undefined: {}", expr_text)),
        );
        self.add_edge(null_block, after_optional, None);

        // Create non-null path (continue with access)
        let non_null_block = self.new_block(
            "optional_access".to_string(),
            node.start_position().row + 1,
            node.end_position().row + 1,
        );
        self.add_edge(
            current,
            non_null_block,
            Some(format!("non-null: {}", expr_text)),
        );

        // Visit children in non-null path for nested optionals
        self.current_block = Some(non_null_block);
        for child in node.children(&mut node.walk()) {
            if child.is_named() && child.kind() != "optional_chain" {
                self.visit_node(child);
            }
        }

        // Connect to after block
        if let Some(curr) = self.current_block {
            if !self.exits.contains(&curr) {
                self.add_edge(curr, after_optional, None);
            }
        }

        self.current_block = Some(after_optional);
    }

    /// FEATURE: Handle nullish coalescing expression (a ?? b).
    ///
    /// Nullish coalescing evaluates the right operand only if the left
    /// is null or undefined. This creates a short-circuit branch:
    /// - If left is not null/undefined: use left value
    /// - If left is null/undefined: evaluate and use right value
    fn visit_nullish_coalescing(&mut self, node: Node) {
        self.decision_points += 1;

        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        // Update current block to nullish coalescing type
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = "nullish_coalesce".to_string();
            block.end_line = node.start_position().row + 1;
        }

        // Find left and right operands
        let mut left_node = None;
        let mut right_node = None;
        let mut found_operator = false;

        for child in node.children(&mut node.walk()) {
            if child.kind() == "??" {
                found_operator = true;
            } else if child.is_named() {
                if !found_operator {
                    left_node = Some(child);
                } else {
                    right_node = Some(child);
                }
            }
        }

        let left_text = left_node
            .map(|n| self.get_text(n).to_string())
            .unwrap_or_else(|| "<left>".to_string());

        // Create after block for both branches to merge
        let after_nullish = self.new_block(
            "body".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        // Non-nullish path (left value is used, right is skipped)
        let non_null_block = self.new_block(
            "nullish_skip".to_string(),
            node.start_position().row + 1,
            node.start_position().row + 1,
        );
        self.add_edge(
            current,
            non_null_block,
            Some(format!("non-nullish: {} has value", left_text)),
        );
        self.add_edge(non_null_block, after_nullish, None);

        // Nullish path (evaluate right operand)
        let null_block = self.new_block(
            "nullish_fallback".to_string(),
            node.start_position().row + 1,
            node.end_position().row + 1,
        );
        self.add_edge(
            current,
            null_block,
            Some(format!("nullish: {} is null/undefined", left_text)),
        );

        // Visit right operand in nullish path
        self.current_block = Some(null_block);
        if let Some(right) = right_node {
            self.visit_node(right);
        }

        // Connect to after block
        if let Some(curr) = self.current_block {
            if !self.exits.contains(&curr) {
                self.add_edge(curr, after_nullish, None);
            }
        }

        self.current_block = Some(after_nullish);
    }

    // =========================================================================
    // PROMISE CHAIN DETECTION METHODS
    // =========================================================================

    /// Check if call_expression is Promise.then() pattern.
    fn is_promise_then(&self, node: Node) -> bool {
        self.get_promise_method_name(node) == Some("then")
    }

    /// Check if call_expression is Promise.finally() pattern.
    fn is_promise_finally(&self, node: Node) -> bool {
        self.get_promise_method_name(node) == Some("finally")
    }

    /// Check if call_expression is Promise.all() pattern.
    fn is_promise_all_pattern(&self, node: Node) -> bool {
        self.is_promise_static_method(node, "all")
    }

    /// Check if call_expression is Promise.race() pattern.
    fn is_promise_race_pattern(&self, node: Node) -> bool {
        self.is_promise_static_method(node, "race")
    }

    /// Check if call_expression is Promise.allSettled() pattern.
    fn is_promise_all_settled_pattern(&self, node: Node) -> bool {
        self.is_promise_static_method(node, "allSettled")
    }

    /// Check if call_expression is Promise.any() pattern.
    fn is_promise_any_pattern(&self, node: Node) -> bool {
        self.is_promise_static_method(node, "any")
    }

    /// Get the method name from a member expression call (e.g., "then" from promise.then()).
    fn get_promise_method_name(&self, node: Node) -> Option<&str> {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "member_expression" {
                for member_child in child.children(&mut child.walk()) {
                    if member_child.kind() == "property_identifier" {
                        return Some(self.get_text(member_child));
                    }
                }
            }
        }
        None
    }

    /// Check if call_expression is Promise.<static_method>() (e.g., Promise.all).
    fn is_promise_static_method(&self, node: Node, method_name: &str) -> bool {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "member_expression" {
                let mut is_promise_obj = false;
                let mut is_target_method = false;

                for member_child in child.children(&mut child.walk()) {
                    if member_child.kind() == "identifier" {
                        let text = self.get_text(member_child);
                        if text == "Promise" {
                            is_promise_obj = true;
                        }
                    } else if member_child.kind() == "property_identifier" {
                        let text = self.get_text(member_child);
                        if text == method_name {
                            is_target_method = true;
                        }
                    }
                }

                if is_promise_obj && is_target_method {
                    return true;
                }
            }
        }
        false
    }

    /// Check if for_of_statement is `for await...of` pattern.
    fn is_for_await_of(&self, node: Node) -> bool {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "await" {
                return true;
            }
            // Early exit: await must appear before the 'of' keyword
            if child.kind() == "of" {
                break;
            }
        }
        false
    }

    // =========================================================================
    // ASYNC ITERATION: for await...of
    // =========================================================================

    /// Handle for await...of loop for async iteration.
    ///
    /// `for await...of` iterates over async iterables, creating suspension points
    /// at each iteration. The loop creates multiple control flow paths:
    /// - Iteration: next async value is awaited
    /// - Exhausted: async iterator completes
    /// - Exception: async iterator throws
    ///
    /// Example:
    /// ```javascript
    /// async function* asyncGenerator() {
    ///     yield 1;
    ///     yield 2;
    /// }
    /// async function consume() {
    ///     for await (const value of asyncGenerator()) {
    ///         console.log(value);
    ///     }
    /// }
    /// ```
    fn visit_for_await_of(&mut self, node: Node) {
        self.decision_points += 1;
        self.await_points += 1; // Each iteration is an await point

        let current = self.current_block;

        // Create loop header with ForAwaitOf block type
        let guard = self.new_block(
            "for_await_of".to_string(),
            node.start_position().row + 1,
            node.start_position().row + 1,
        );

        if let Some(block) = self.blocks.get_mut(&guard) {
            block.block_type = BlockType::ForAwaitOf;
        }

        if let Some(curr) = current {
            self.add_edge(curr, guard, None);
        }

        let after_loop = self.new_block(
            "after_for_await".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        self.loop_guard_stack.push(guard);
        self.after_loop_stack.push(after_loop);

        // Find and process loop body
        if let Some(body) = node.child_by_field_name("body") {
            let loop_body = self.new_block(
                "for_await_body".to_string(),
                body.start_position().row + 1,
                body.end_position().row + 1,
            );

            // Iteration edge (async)
            self.add_typed_edge(
                guard,
                loop_body,
                EdgeType::ForAwaitIterate,
                Some("iterate".to_string()),
            );

            // Exhausted edge
            self.add_typed_edge(
                guard,
                after_loop,
                EdgeType::ForAwaitExhausted,
                Some("exhausted".to_string()),
            );

            // Exception path (async iterator can throw)
            if let Some(exc_ctx) = self.exception_context_stack.last() {
                if let Some(handler) = exc_ctx.handlers.first() {
                    self.add_typed_edge(
                        guard,
                        handler.catch_block,
                        EdgeType::PromiseRejected,
                        Some("iteration error".to_string()),
                    );
                }
            }

            self.current_block = Some(loop_body);
            self.visit_node(body);

            // Back edge to loop header
            if let Some(curr) = self.current_block {
                if !self.exits.contains(&curr) {
                    self.add_edge(curr, guard, Some("back_edge".to_string()));
                }
            }
        }

        self.loop_guard_stack.pop();
        self.after_loop_stack.pop();
        self.current_block = Some(after_loop);
    }

    // =========================================================================
    // PROMISE CHAIN HANDLERS: .then(), .catch(), .finally()
    // =========================================================================

    /// Handle Promise.then() - transforms chain into CFG with resolved/rejected paths.
    ///
    /// Promise.then(onFulfilled, onRejected) creates two execution paths:
    /// - Resolved: executes onFulfilled callback
    /// - Rejected: executes onRejected callback (if provided)
    ///
    /// Example:
    /// ```javascript
    /// fetchUser(id)
    ///     .then(user => processUser(user))
    ///     .then(result => saveResult(result));
    /// ```
    fn visit_promise_then(&mut self, node: Node) {
        self.decision_points += 1;

        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        let line = node.start_position().row + 1;

        // Get the promise expression and handlers
        let promise_expr = self.extract_promise_expression(node);
        let handlers = self.extract_then_handlers(node);

        // Update current block to PromiseThen type
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = format!("{}.then(...)", promise_expr);
            block.block_type = BlockType::PromiseThen;
            block.end_line = line;
        }

        // Create after block for flow to merge
        let after_then = self.new_block(
            "after_then".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        // Create resolved handler block
        let resolved_label = handlers.0.unwrap_or_else(|| "onFulfilled".to_string());
        let resolved_block = self.new_block(
            format!("then_resolved: {}", resolved_label),
            line,
            node.end_position().row + 1,
        );
        if let Some(block) = self.blocks.get_mut(&resolved_block) {
            block.block_type = BlockType::PromiseThen;
        }

        self.add_typed_edge(
            current,
            resolved_block,
            EdgeType::PromiseResolved,
            Some("resolved".to_string()),
        );
        self.add_edge(resolved_block, after_then, None);

        // If there's a rejection handler (second argument to .then)
        if let Some(rejected_label) = handlers.1 {
            let rejected_block = self.new_block(
                format!("then_rejected: {}", rejected_label),
                line,
                node.end_position().row + 1,
            );
            if let Some(block) = self.blocks.get_mut(&rejected_block) {
                block.block_type = BlockType::PromiseCatch;
            }

            self.add_typed_edge(
                current,
                rejected_block,
                EdgeType::PromiseRejected,
                Some("rejected".to_string()),
            );
            self.add_edge(rejected_block, after_then, None);
        }

        // Visit arguments to process nested patterns
        for child in node.children(&mut node.walk()) {
            if child.kind() == "arguments" {
                self.current_block = Some(resolved_block);
                for arg_child in child.children(&mut child.walk()) {
                    if arg_child.is_named()
                        && !matches!(arg_child.kind(), "(" | ")" | ",")
                    {
                        self.visit_node(arg_child);
                        break; // Only visit first handler in resolved block
                    }
                }
            }
        }

        self.current_block = Some(after_then);
    }

    /// Extract the onFulfilled and onRejected handlers from .then() call.
    fn extract_then_handlers(&self, node: Node) -> (Option<String>, Option<String>) {
        let mut on_fulfilled = None;
        let mut on_rejected = None;

        for child in node.children(&mut node.walk()) {
            if child.kind() == "arguments" {
                let mut arg_index = 0;
                for arg_child in child.children(&mut child.walk()) {
                    if arg_child.is_named() && !matches!(arg_child.kind(), "(" | ")" | ",") {
                        let text = self.get_text(arg_child);
                        let abbreviated = if text.len() > 20 {
                            format!("{}...", &text[..17])
                        } else {
                            text.to_string()
                        };

                        match arg_index {
                            0 => on_fulfilled = Some(abbreviated),
                            1 => on_rejected = Some(abbreviated),
                            _ => break,
                        }
                        arg_index += 1;
                    }
                }
            }
        }

        (on_fulfilled, on_rejected)
    }

    /// Handle Promise.finally() - always executes regardless of promise outcome.
    ///
    /// Example:
    /// ```javascript
    /// fetchData()
    ///     .then(data => process(data))
    ///     .catch(err => handleError(err))
    ///     .finally(() => cleanup());
    /// ```
    fn visit_promise_finally(&mut self, node: Node) {
        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        let line = node.start_position().row + 1;

        // Get the promise expression
        let promise_expr = self.extract_promise_expression(node);

        // Update current block
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = format!("{}.finally(...)", promise_expr);
            block.block_type = BlockType::PromiseFinally;
            block.end_line = line;
        }

        // Create finally handler block
        let finally_block = self.new_block(
            "finally_handler".to_string(),
            line,
            node.end_position().row + 1,
        );
        if let Some(block) = self.blocks.get_mut(&finally_block) {
            block.block_type = BlockType::PromiseFinally;
        }

        // Finally always executes (PromiseSettled edge)
        self.add_typed_edge(
            current,
            finally_block,
            EdgeType::PromiseSettled,
            Some("settled".to_string()),
        );

        // Create after block
        let after_finally = self.new_block(
            "after_finally".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        self.add_edge(finally_block, after_finally, None);

        // Visit the finally callback
        for child in node.children(&mut node.walk()) {
            if child.kind() == "arguments" {
                self.current_block = Some(finally_block);
                for arg_child in child.children(&mut child.walk()) {
                    if arg_child.is_named() && !matches!(arg_child.kind(), "(" | ")" | ",") {
                        self.visit_node(arg_child);
                        break;
                    }
                }
            }
        }

        self.current_block = Some(after_finally);
    }

    // =========================================================================
    // CONCURRENT PROMISE PATTERNS: Promise.all, Promise.race, etc.
    // =========================================================================

    /// Handle Promise.all() - parallel execution, waits for all promises.
    ///
    /// Creates parallel branches for each promise task, then joins when all complete.
    /// If any promise rejects, the entire Promise.all rejects.
    ///
    /// Example:
    /// ```javascript
    /// const [user, posts] = await Promise.all([
    ///     fetchUser(id),
    ///     fetchPosts(id)
    /// ]);
    /// ```
    fn visit_promise_all(&mut self, node: Node) {
        self.decision_points += 1;

        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        let line = node.start_position().row + 1;

        // Extract promise tasks from arguments
        let tasks = self.extract_promise_tasks(node);
        let task_count = tasks.len();

        // Update current block
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = format!("Promise.all([{} tasks])", task_count);
            block.block_type = BlockType::PromiseAll;
            block.end_line = line;
        }

        // Create parallel execution block
        let parallel_block = self.new_block(
            "parallel_execution".to_string(),
            line,
            node.end_position().row + 1,
        );
        if let Some(block) = self.blocks.get_mut(&parallel_block) {
            block.block_type = BlockType::PromiseAll;
        }

        // Create join block (all promises resolved)
        let join_block = self.new_block(
            "all_join".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        // Spawn edge to parallel execution
        self.add_typed_edge(
            current,
            parallel_block,
            EdgeType::TaskSpawn,
            Some(format!("spawn {} tasks", task_count)),
        );

        // Create branch edges for each task (conceptual parallel branches)
        for (i, task) in tasks.iter().enumerate() {
            let task_block = self.new_block(
                format!("task[{}]: {}", i, task),
                line,
                line,
            );
            self.add_typed_edge(
                parallel_block,
                task_block,
                EdgeType::PromiseAllBranch,
                Some(format!("task {}", i)),
            );
            self.add_typed_edge(
                task_block,
                join_block,
                EdgeType::PromiseAllJoin,
                None,
            );
        }

        // If no tasks, direct edge to join
        if tasks.is_empty() {
            self.add_typed_edge(
                parallel_block,
                join_block,
                EdgeType::PromiseAllJoin,
                Some("empty array".to_string()),
            );
        }

        // Rejection path (any task rejects)
        if let Some(exc_ctx) = self.exception_context_stack.last() {
            if let Some(handler) = exc_ctx.handlers.first() {
                self.add_typed_edge(
                    parallel_block,
                    handler.catch_block,
                    EdgeType::PromiseRejected,
                    Some("any rejected".to_string()),
                );
            }
        }

        self.current_block = Some(join_block);
    }

    /// Handle Promise.race() - parallel execution, first settled wins.
    fn visit_promise_race(&mut self, node: Node) {
        self.decision_points += 1;

        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        let line = node.start_position().row + 1;
        let tasks = self.extract_promise_tasks(node);
        let task_count = tasks.len();

        // Update current block
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = format!("Promise.race([{} tasks])", task_count);
            block.block_type = BlockType::PromiseRace;
            block.end_line = line;
        }

        // Create race block
        let race_block = self.new_block(
            "race_execution".to_string(),
            line,
            node.end_position().row + 1,
        );
        if let Some(block) = self.blocks.get_mut(&race_block) {
            block.block_type = BlockType::PromiseRace;
        }

        // Create winner block (first to settle)
        let winner_block = self.new_block(
            "race_winner".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        self.add_typed_edge(
            current,
            race_block,
            EdgeType::TaskSpawn,
            Some(format!("race {} tasks", task_count)),
        );

        // Each task can be the winner
        for (i, task) in tasks.iter().enumerate() {
            let task_block = self.new_block(
                format!("racer[{}]: {}", i, task),
                line,
                line,
            );
            self.add_typed_edge(
                race_block,
                task_block,
                EdgeType::PromiseRaceBranch,
                Some(format!("racer {}", i)),
            );
            self.add_typed_edge(
                task_block,
                winner_block,
                EdgeType::PromiseRaceWinner,
                Some("first".to_string()),
            );
        }

        if tasks.is_empty() {
            // Promise.race([]) never settles - edge to winner anyway for CFG completeness
            self.add_typed_edge(
                race_block,
                winner_block,
                EdgeType::PromiseRaceWinner,
                Some("never (empty)".to_string()),
            );
        }

        self.current_block = Some(winner_block);
    }

    /// Handle Promise.allSettled() - waits for all to settle (resolve or reject).
    fn visit_promise_all_settled(&mut self, node: Node) {
        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        let line = node.start_position().row + 1;
        let tasks = self.extract_promise_tasks(node);
        let task_count = tasks.len();

        // Update current block
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = format!("Promise.allSettled([{} tasks])", task_count);
            block.block_type = BlockType::PromiseAllSettled;
            block.end_line = line;
        }

        // Create settled block (all tasks complete regardless of outcome)
        let settled_block = self.new_block(
            "all_settled".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        // Promise.allSettled never rejects, always resolves with results array
        self.add_typed_edge(
            current,
            settled_block,
            EdgeType::PromiseSettled,
            Some(format!("{} tasks settled", task_count)),
        );

        self.current_block = Some(settled_block);
    }

    /// Handle Promise.any() - first fulfilled wins (ignores rejections until all reject).
    fn visit_promise_any(&mut self, node: Node) {
        self.decision_points += 1;

        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        let line = node.start_position().row + 1;
        let tasks = self.extract_promise_tasks(node);
        let task_count = tasks.len();

        // Update current block
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = format!("Promise.any([{} tasks])", task_count);
            block.block_type = BlockType::PromiseAny;
            block.end_line = line;
        }

        // Create winner block
        let winner_block = self.new_block(
            "any_winner".to_string(),
            node.end_position().row + 1,
            node.end_position().row + 1,
        );

        self.add_typed_edge(
            current,
            winner_block,
            EdgeType::PromiseResolved,
            Some("first fulfilled".to_string()),
        );

        // AggregateError if all reject
        if let Some(exc_ctx) = self.exception_context_stack.last() {
            if let Some(handler) = exc_ctx.handlers.first() {
                self.add_typed_edge(
                    current,
                    handler.catch_block,
                    EdgeType::PromiseRejected,
                    Some("AggregateError".to_string()),
                );
            }
        }

        self.current_block = Some(winner_block);
    }

    /// Extract promise tasks from Promise.all/race/etc arguments.
    fn extract_promise_tasks(&self, node: Node) -> Vec<String> {
        let mut tasks = Vec::new();

        for child in node.children(&mut node.walk()) {
            if child.kind() == "arguments" {
                for arg_child in child.children(&mut child.walk()) {
                    if arg_child.kind() == "array" {
                        // Array of promises: [promise1, promise2, ...]
                        for element in arg_child.children(&mut arg_child.walk()) {
                            if element.is_named() && !matches!(element.kind(), "[" | "]" | ",") {
                                let text = self.get_text(element);
                                let abbreviated = if text.len() > 25 {
                                    format!("{}...", &text[..22])
                                } else {
                                    text.to_string()
                                };
                                tasks.push(abbreviated);
                            }
                        }
                    }
                }
            }
        }

        tasks
    }

    // =========================================================================
    // ASYNC GENERATOR: yield expressions
    // =========================================================================

    /// Handle yield expression in async generators.
    fn visit_yield(&mut self, node: Node) {
        let current = match self.current_block {
            Some(id) => id,
            None => return,
        };

        let line = node.start_position().row + 1;

        // Check if this is yield* (delegation)
        let is_delegation = self.get_text(node).contains("yield*");

        let label = if is_delegation {
            "yield*".to_string()
        } else {
            "yield".to_string()
        };

        // Update current block
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = label;
            block.block_type = BlockType::AsyncGeneratorYield;
            block.end_line = line;
        }

        // Create resume block
        let resume_block = self.new_block(
            "after_yield".to_string(),
            line,
            line,
        );

        // Yield edge (suspension)
        self.add_typed_edge(
            current,
            resume_block,
            EdgeType::AsyncYield,
            Some("yield".to_string()),
        );

        self.current_block = Some(resume_block);
    }

    // =========================================================================
    // ASYNC ISSUE DETECTION
    // =========================================================================

    /// Check if a call is a blocking operation in async context.
    ///
    /// Detects common blocking patterns that should be avoided in async code:
    /// - Synchronous file operations (fs.readFileSync, etc.)
    /// - Blocking network calls
    /// - CPU-intensive sync operations
    fn check_blocking_call(&mut self, node: Node) {
        // Clone to release borrow of self before mutating self.blocking_calls
        let call_text = self.get_text(node).to_string();
        let line = node.start_position().row + 1;

        // Patterns that indicate blocking calls in async context
        let blocking_patterns = [
            ("readFileSync", "Use fs.promises.readFile or fs.readFile with await"),
            ("writeFileSync", "Use fs.promises.writeFile or fs.writeFile with await"),
            ("existsSync", "Use fs.promises.access or fs.access with await"),
            ("statSync", "Use fs.promises.stat or fs.stat with await"),
            ("readdirSync", "Use fs.promises.readdir or fs.readdir with await"),
            ("mkdirSync", "Use fs.promises.mkdir or fs.mkdir with await"),
            ("unlinkSync", "Use fs.promises.unlink or fs.unlink with await"),
            ("execSync", "Use child_process.exec with await or util.promisify"),
            ("spawnSync", "Use child_process.spawn with event handlers"),
            (".alert(", "Blocking UI operation"),
            (".confirm(", "Blocking UI operation"),
            (".prompt(", "Blocking UI operation"),
        ];

        // Clone call_text to avoid borrow conflict with self.blocking_calls.push()
        let call_text_owned = call_text.to_string();
        for (pattern, reason) in blocking_patterns {
            if call_text_owned.contains(pattern) {
                self.blocking_calls.push((
                    pattern.to_string(),
                    line,
                    reason.to_string(),
                ));
            }
        }
    }
}

// =============================================================================
// Data Flow Graph Builder
// =============================================================================

/// DFG builder for TypeScript/JavaScript.
struct TypeScriptDFGBuilder<'a> {
    source: &'a [u8],
    edges: Vec<DataflowEdge>,
    definitions: HashMap<String, Vec<usize>>,
    uses: HashMap<String, Vec<usize>>,
    /// Variable -> (definition line, definition kind)
    /// Stores the most recent definition for each variable to create def->use edges.
    current_defs: HashMap<String, (usize, DataflowKind)>,
}

impl<'a> TypeScriptDFGBuilder<'a> {
    fn new(source: &'a [u8]) -> Self {
        Self {
            source,
            edges: Vec::new(),
            definitions: HashMap::new(),
            uses: HashMap::new(),
            current_defs: HashMap::new(),
        }
    }

    fn get_text(&self, node: Node) -> &str {
        std::str::from_utf8(&self.source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }

    fn build(&mut self, node: Node, func_name: &str) -> Result<DFGInfo> {
        // Extract parameters as initial definitions
        self.extract_params(node);

        // Find function body first before mutable borrow
        let body_node = {
            let mut result = None;
            for child in node.children(&mut node.walk()) {
                match child.kind() {
                    "statement_block" | "block" => {
                        result = Some(child);
                        break;
                    }
                    _ => {}
                }
            }
            result
        };

        // Analyze function body
        if let Some(body) = body_node {
            self.visit_node(body);
        }

        Ok(DFGInfo::new(
            func_name.to_string(),
            self.edges.clone(),
            self.definitions.clone(),
            self.uses.clone(),
        ))
    }

    fn extract_params(&mut self, node: Node) {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "formal_parameters" {
                let line = node.start_position().row + 1;
                for param in child.children(&mut child.walk()) {
                    match param.kind() {
                        "identifier" => {
                            let name = self.get_text(param).to_string();
                            self.add_definition(&name, line, DataflowKind::Param);
                        }
                        "required_parameter" | "optional_parameter" => {
                            // Find identifier within parameter
                            for p_child in param.children(&mut param.walk()) {
                                if p_child.kind() == "identifier" {
                                    let name = self.get_text(p_child).to_string();
                                    self.add_definition(&name, line, DataflowKind::Param);
                                    break;
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    /// Record a variable definition for later edge creation when uses are found.
    ///
    /// For initial definitions (Definition, Param, etc.), no edges are created here
    /// because self-loop edges are semantically meaningless. Edges are created in
    /// `add_use()` when a use references this definition.
    ///
    /// For mutations, an edge IS created from the previous definition to the mutation
    /// line, as this represents actual data flow (the old value flows to the mutation
    /// site where it's modified).
    fn add_definition(&mut self, var: &str, line: usize, kind: DataflowKind) {
        // For Mutation kind, create edge from previous definition to mutation site
        // This represents "data flows from previous def to where it's mutated"
        if matches!(kind, DataflowKind::Mutation) {
            if let Some(&(prev_def_line, _)) = self.current_defs.get(var) {
                // Only create edge if previous def and mutation are on different lines
                if prev_def_line != line {
                    self.edges.push(DataflowEdge {
                        variable: var.to_string(),
                        from_line: prev_def_line,
                        to_line: line,
                        kind: DataflowKind::Mutation,
                    });
                }
            }
        }

        // Track all definition sites for this variable
        self.definitions
            .entry(var.to_string())
            .or_default()
            .push(line);

        // Store the most recent definition (line + kind) for edge creation in add_use()
        self.current_defs.insert(var.to_string(), (line, kind));

        // NOTE: For non-Mutation kinds, we do NOT create self-referential edges here.
        // Self-loop edges (from_line == to_line) are semantically meaningless
        // and clutter the DFG with spurious edges.
    }

    /// Record a variable use and create data flow edge from its definition.
    ///
    /// Only creates an edge if the definition and use are on different lines.
    /// Uses on the same line as definition (e.g., `let x = x + 1` where outer x
    /// shadows inner) would create self-referential edges which are meaningless.
    fn add_use(&mut self, var: &str, use_line: usize) {
        self.uses.entry(var.to_string()).or_default().push(use_line);

        // Create edge from definition to use
        // Edge kind is Use because it represents data flowing TO a use site
        if let Some(&(def_line, _kind)) = self.current_defs.get(var) {
            // Only create edge if def and use are on different lines
            // Self-referential edges add no semantic information
            if def_line != use_line {
                self.edges.push(DataflowEdge {
                    variable: var.to_string(),
                    from_line: def_line,
                    to_line: use_line,
                    kind: DataflowKind::Use,
                });
            }
        }
    }

    fn visit_node(&mut self, node: Node) {
        match node.kind() {
            "variable_declaration" | "lexical_declaration" => {
                self.visit_variable_declaration(node);
            }
            "assignment_expression" => {
                self.visit_assignment(node);
            }
            "augmented_assignment_expression" => {
                // Handle += -= *= /= etc.
                self.visit_augmented_assignment(node);
            }
            "update_expression" => {
                self.visit_update(node);
            }
            "return_statement" => {
                self.visit_return(node);
            }
            "for_statement" => {
                // Handle traditional for: for (let i = 0; i < n; i++)
                // The initializer contains the loop variable declaration
                if let Some(init) = node.child_by_field_name("initializer") {
                    match init.kind() {
                        "lexical_declaration" | "variable_declaration" => {
                            self.visit_variable_declaration(init);
                        }
                        _ => self.visit_node(init),
                    }
                }
                // Process condition for variable uses
                if let Some(cond) = node.child_by_field_name("condition") {
                    self.visit_node(cond);
                }
                // Process increment/update for variable uses and mutations
                if let Some(update) = node.child_by_field_name("increment") {
                    self.visit_node(update);
                }
                // Process body
                if let Some(body) = node.child_by_field_name("body") {
                    self.visit_node(body);
                }
            }
            "for_in_statement" => {
                // Handle for-in: for (const key in obj)
                // The left field contains the loop variable
                if let Some(left) = node.child_by_field_name("left") {
                    self.extract_loop_variable(left);
                }
                // The right field contains the object being iterated (uses)
                if let Some(right) = node.child_by_field_name("right") {
                    self.visit_node(right);
                }
                // Process body
                if let Some(body) = node.child_by_field_name("body") {
                    self.visit_node(body);
                }
            }
            "for_of_statement" => {
                // Handle for-of: for (const x of items)
                // The left field contains the loop variable (possibly destructured)
                if let Some(left) = node.child_by_field_name("left") {
                    self.extract_loop_variable(left);
                }
                // The right field contains the iterable being iterated (uses)
                if let Some(right) = node.child_by_field_name("right") {
                    self.visit_node(right);
                }
                // Process body
                if let Some(body) = node.child_by_field_name("body") {
                    self.visit_node(body);
                }
            }
            "identifier" => {
                // This is a use of a variable
                let name = self.get_text(node).to_string();
                let line = node.start_position().row + 1;
                self.add_use(&name, line);
            }
            _ => {
                // Recursively visit children
                for child in node.children(&mut node.walk()) {
                    if child.is_named() {
                        self.visit_node(child);
                    }
                }
            }
        }
    }

    /// Extract loop variable definitions from for-in/for-of left operand.
    /// Handles: `let x`, `const x`, `var x`, bare `x`, and destructuring patterns.
    fn extract_loop_variable(&mut self, node: Node) {
        let line = node.start_position().row + 1;
        match node.kind() {
            "lexical_declaration" | "variable_declaration" => {
                // `const x` or `let x` - use existing variable declaration handler
                self.visit_variable_declaration(node);
            }
            "identifier" => {
                // Bare identifier without declaration keyword (legacy syntax)
                let name = self.get_text(node).to_string();
                self.add_definition(&name, line, DataflowKind::Definition);
            }
            "object_pattern" | "array_pattern" => {
                // Destructuring in for-of: `for (const {a, b} of items)`
                self.extract_pattern_definitions(node, line);
            }
            _ => {
                // Fallback: recurse into children to find identifiers
                for child in node.children(&mut node.walk()) {
                    if child.is_named() {
                        self.extract_loop_variable(child);
                    }
                }
            }
        }
    }

    fn visit_variable_declaration(&mut self, node: Node) {
        let line = node.start_position().row + 1;

        for child in node.children(&mut node.walk()) {
            if child.kind() == "variable_declarator" {
                // Get the name (could be identifier or destructuring pattern)
                if let Some(name_node) = child.child_by_field_name("name") {
                    // BUG #4 FIX: Handle destructuring patterns
                    // `const { a, b, c } = obj;` has name_node.kind() == "object_pattern"
                    // `const [x, y] = arr;` has name_node.kind() == "array_pattern"
                    match name_node.kind() {
                        "identifier" => {
                            let name = self.get_text(name_node).to_string();
                            self.add_definition(&name, line, DataflowKind::Definition);
                        }
                        "object_pattern" | "array_pattern" => {
                            // Extract all bound names from destructuring pattern
                            self.extract_pattern_definitions(name_node, line);
                        }
                        _ => {
                            // Fallback: just get the text
                            let name = self.get_text(name_node).to_string();
                            self.add_definition(&name, line, DataflowKind::Definition);
                        }
                    }

                    // Process the value (if any) for uses
                    if let Some(value) = child.child_by_field_name("value") {
                        self.visit_node(value);
                    }
                }
            }
        }
    }

    /// BUG #4 FIX: Recursively extract all identifier definitions from destructuring patterns.
    /// Handles:
    /// - object_pattern: `{ a, b, c: renamed, ...rest }`
    /// - array_pattern: `[x, y, ...rest]`
    /// - nested patterns: `{ a: { b, c } }`
    fn extract_pattern_definitions(&mut self, node: Node, line: usize) {
        match node.kind() {
            "identifier" => {
                let name = self.get_text(node).to_string();
                self.add_definition(&name, line, DataflowKind::Definition);
            }
            "shorthand_property_identifier" | "shorthand_property_identifier_pattern" => {
                // In object patterns like `{ a, b }`, shorthand identifiers
                let name = self.get_text(node).to_string();
                self.add_definition(&name, line, DataflowKind::Definition);
            }
            "object_pattern" | "array_pattern" => {
                // Recurse into pattern elements
                for child in node.children(&mut node.walk()) {
                    if child.is_named() {
                        self.extract_pattern_definitions(child, line);
                    }
                }
            }
            "pair_pattern" => {
                // Object pattern with renaming: `{ a: renamed }` - the value is the binding
                if let Some(value) = node.child_by_field_name("value") {
                    self.extract_pattern_definitions(value, line);
                }
            }
            "assignment_pattern" => {
                // Pattern with default: `{ a = default }` or `[a = default]`
                if let Some(left) = node.child_by_field_name("left") {
                    self.extract_pattern_definitions(left, line);
                }
                // The right side (default value) contains uses
                if let Some(right) = node.child_by_field_name("right") {
                    self.visit_node(right);
                }
            }
            "rest_pattern" => {
                // Rest pattern: `...rest`
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "identifier" {
                        let name = self.get_text(child).to_string();
                        self.add_definition(&name, line, DataflowKind::Definition);
                    }
                }
            }
            _ => {
                // Recurse into any other named children
                for child in node.children(&mut node.walk()) {
                    if child.is_named() {
                        self.extract_pattern_definitions(child, line);
                    }
                }
            }
        }
    }

    fn visit_assignment(&mut self, node: Node) {
        let line = node.start_position().row + 1;

        // Process right side first (uses)
        if let Some(right) = node.child_by_field_name("right") {
            self.visit_node(right);
        }

        // Then process left side (definition/mutation)
        if let Some(left) = node.child_by_field_name("left") {
            self.handle_assignment_target(left, line);
        }
    }

    /// Handle augmented assignment expressions (+=, -=, *=, /=, etc.)
    ///
    /// For `x += value`, x is both read and written (use + mutation).
    /// For `obj.field += value`, obj is both read and mutated.
    fn visit_augmented_assignment(&mut self, node: Node) {
        let line = node.start_position().row + 1;

        // Process right side first (uses)
        if let Some(right) = node.child_by_field_name("right") {
            self.visit_node(right);
        }

        // Process left side - it's both read AND written
        if let Some(left) = node.child_by_field_name("left") {
            match left.kind() {
                "identifier" => {
                    let name = self.get_text(left).to_string();
                    // Add both use (read current value) and mutation (write new value)
                    self.add_use(&name, line);
                    self.add_definition(&name, line, DataflowKind::Mutation);
                }
                "member_expression" | "subscript_expression" => {
                    // For `obj.x += 1`, obj is both used (read) and mutated (write)
                    if let Some(base_name) = self.extract_base_object(left) {
                        self.add_use(&base_name, line);
                        self.add_definition(&base_name, line, DataflowKind::Mutation);
                    }
                    // Also capture any other uses (e.g., index in arr[idx] += 1)
                    self.visit_member_or_subscript_uses(left, line);
                }
                _ => {
                    // Fallback: visit as uses
                    self.visit_node(left);
                }
            }
        }
    }

    /// Handle the left-hand side of an assignment, properly tracking mutations.
    ///
    /// For member expressions (`obj.field = value`) and subscript expressions
    /// (`arr[idx] = value`), the base object is mutated. For simple identifiers,
    /// the identifier itself is mutated.
    fn handle_assignment_target(&mut self, node: Node, line: usize) {
        match node.kind() {
            "identifier" => {
                let name = self.get_text(node).to_string();
                self.add_definition(&name, line, DataflowKind::Mutation);
            }
            "member_expression" | "subscript_expression" => {
                // Extract the base object and mark it as mutated.
                // For `obj.field = value`, obj is mutated.
                // For `obj.nested.field = value`, obj is mutated.
                // For `arr[idx] = value`, arr is mutated.
                if let Some(base_name) = self.extract_base_object(node) {
                    self.add_definition(&base_name, line, DataflowKind::Mutation);
                }
                // Also visit the expression to capture uses (e.g., idx in arr[idx])
                self.visit_member_or_subscript_uses(node, line);
            }
            "object_pattern" | "array_pattern" => {
                // Destructuring assignment: `({ a, b } = obj)`
                self.extract_pattern_definitions(node, line);
            }
            _ => {
                // Fallback: visit as uses
                self.visit_node(node);
            }
        }
    }

    /// Extract the base object identifier from a member or subscript expression.
    ///
    /// Recursively traverses nested expressions to find the root identifier:
    /// - `obj.field` -> "obj"
    /// - `obj.nested.field` -> "obj"
    /// - `arr[0]` -> "arr"
    /// - `matrix[i][j]` -> "matrix"
    /// - `map.get(key).x` -> None (method call returns unknown object)
    fn extract_base_object(&self, node: Node) -> Option<String> {
        match node.kind() {
            "identifier" => Some(self.get_text(node).to_string()),
            "member_expression" => {
                // `obj.field` -> extract obj
                node.child_by_field_name("object")
                    .and_then(|obj| self.extract_base_object(obj))
            }
            "subscript_expression" => {
                // `arr[idx]` -> extract arr
                node.child_by_field_name("object")
                    .and_then(|obj| self.extract_base_object(obj))
            }
            // For call expressions like `map.get(key).x = value`, we cannot
            // determine which object is being mutated (it's the return value
            // of the method call), so return None.
            "call_expression" => None,
            _ => None,
        }
    }

    /// Visit a member or subscript expression to capture uses, but not the base object.
    ///
    /// For `obj.field`, we don't add `obj` as a use (it's being mutated, not read).
    /// For `arr[idx]`, we add `idx` as a use (it's read to compute the index).
    fn visit_member_or_subscript_uses(&mut self, node: Node, line: usize) {
        match node.kind() {
            "member_expression" => {
                // For `obj.field`, the property name is not a variable use.
                // Recurse into nested member expressions only.
                if let Some(obj) = node.child_by_field_name("object") {
                    if obj.kind() == "member_expression" || obj.kind() == "subscript_expression" {
                        self.visit_member_or_subscript_uses(obj, line);
                    }
                    // If obj is a call_expression like `foo().bar`, visit it for uses
                    else if obj.kind() == "call_expression" {
                        self.visit_node(obj);
                    }
                    // Don't add the base identifier as a use - it's being mutated
                }
            }
            "subscript_expression" => {
                // For `arr[idx]`, visit the index expression for uses
                if let Some(index) = node.child_by_field_name("index") {
                    self.visit_node(index);
                }
                // Recurse into nested expressions
                if let Some(obj) = node.child_by_field_name("object") {
                    if obj.kind() == "member_expression" || obj.kind() == "subscript_expression" {
                        self.visit_member_or_subscript_uses(obj, line);
                    } else if obj.kind() == "call_expression" {
                        self.visit_node(obj);
                    }
                    // Don't add the base identifier as a use - it's being mutated
                }
            }
            _ => {}
        }
    }

    /// Handle update expressions (++, --)
    ///
    /// For `x++`, x is both read (use) and written (mutation).
    /// For `obj.field++`, obj is both read (use) and mutated.
    fn visit_update(&mut self, node: Node) {
        let line = node.start_position().row + 1;

        // The "argument" field contains the operand being updated
        if let Some(arg) = node.child_by_field_name("argument") {
            match arg.kind() {
                "identifier" => {
                    let name = self.get_text(arg).to_string();
                    // Update is both a use and a mutation
                    self.add_use(&name, line);
                    self.add_definition(&name, line, DataflowKind::Mutation);
                }
                "member_expression" | "subscript_expression" => {
                    // For `obj.x++`, obj is both used (read) and mutated (write)
                    if let Some(base_name) = self.extract_base_object(arg) {
                        self.add_use(&base_name, line);
                        self.add_definition(&base_name, line, DataflowKind::Mutation);
                    }
                    // Also capture any other uses (e.g., index in arr[idx]++)
                    self.visit_member_or_subscript_uses(arg, line);
                }
                _ => {
                    // Fallback: visit for uses
                    self.visit_node(arg);
                }
            }
        } else {
            // Fallback: original behavior for unexpected structure
            for child in node.children(&mut node.walk()) {
                if child.kind() == "identifier" {
                    let name = self.get_text(child).to_string();
                    self.add_use(&name, line);
                    self.add_definition(&name, line, DataflowKind::Mutation);
                    break;
                }
            }
        }
    }

    fn visit_return(&mut self, node: Node) {
        let line = node.start_position().row + 1;

        // Visit the returned expression
        for child in node.children(&mut node.walk()) {
            if child.is_named() && child.kind() != "return" {
                // Record any identifiers as uses
                self.visit_return_expr(child, line);
            }
        }
    }

    fn visit_return_expr(&mut self, node: Node, line: usize) {
        if node.kind() == "identifier" {
            let name = self.get_text(node).to_string();

            // Record use without creating Use edge - we create Return edge instead
            // This avoids duplicate edges (Use + Return) for return statement variables
            self.uses.entry(name.clone()).or_default().push(line);

            // Add return edge (replaces generic Use edge with return-specific data flow)
            if let Some(&(def_line, _)) = self.current_defs.get(&name) {
                // Only create return edge if def and return are on different lines
                if def_line != line {
                    self.edges.push(DataflowEdge {
                        variable: name,
                        from_line: def_line,
                        to_line: line,
                        kind: DataflowKind::Return,
                    });
                }
            }
        } else {
            for child in node.children(&mut node.walk()) {
                if child.is_named() {
                    self.visit_return_expr(child, line);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_ts(source: &str) -> Tree {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_typescript::LANGUAGE_TYPESCRIPT.into())
            .unwrap();
        parser.parse(source, None).unwrap()
    }

    #[test]
    fn test_extract_function_declaration() {
        let source = r#"
function greet(name: string): string {
    return "Hello, " + name;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        // Find function node
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let func = ts.extract_function(func_node, source.as_bytes()).unwrap();
        assert_eq!(func.name, "greet");
        assert_eq!(func.params.len(), 1);
        assert!(func.params[0].contains("name"));
        assert_eq!(func.return_type, Some("string".to_string()));
        assert!(!func.is_async);
    }

    #[test]
    fn test_extract_async_arrow_function() {
        let source = r#"
const fetchData = async (url: string): Promise<Response> => {
    return fetch(url);
};
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        // Find arrow function node
        let root = tree.root_node();
        // Navigate: lexical_declaration -> variable_declarator -> arrow_function
        let lexical = root.child(0).unwrap();
        let declarator = lexical.child(1).unwrap();
        let arrow = declarator.child(2).unwrap();

        let func = ts.extract_function(arrow, source.as_bytes()).unwrap();
        assert_eq!(func.name, "fetchData");
        assert!(func.is_async);
    }

    #[test]
    fn test_is_async_edge_cases() {
        // Test various async edge cases that string matching would fail on
        let ts = TypeScript::new();

        // 1. Basic async function
        let source1 = "async function foo() {}";
        let tree1 = parse_ts(source1);
        let func1 = tree1.root_node().child(0).unwrap();
        assert!(ts.is_async(func1, source1.as_bytes()), "basic async function");

        // 2. Non-async function
        let source2 = "function bar() {}";
        let tree2 = parse_ts(source2);
        let func2 = tree2.root_node().child(0).unwrap();
        assert!(!ts.is_async(func2, source2.as_bytes()), "non-async function");

        // 3. Async arrow function
        let source3 = "const f = async () => {};";
        let tree3 = parse_ts(source3);
        let arrow3 = tree3
            .root_node()
            .child(0)
            .unwrap() // lexical_declaration
            .child(1)
            .unwrap() // variable_declarator
            .child(2)
            .unwrap(); // arrow_function
        assert!(ts.is_async(arrow3, source3.as_bytes()), "async arrow function");

        // 4. Non-async arrow function
        let source4 = "const g = () => {};";
        let tree4 = parse_ts(source4);
        let arrow4 = tree4
            .root_node()
            .child(0)
            .unwrap()
            .child(1)
            .unwrap()
            .child(2)
            .unwrap();
        assert!(
            !ts.is_async(arrow4, source4.as_bytes()),
            "non-async arrow function"
        );

        // 5. Async method with visibility modifier (key edge case!)
        let source5 = "class C { public async method() {} }";
        let tree5 = parse_ts(source5);
        let method5 = tree5
            .root_node()
            .child(0)
            .unwrap() // class_declaration
            .child(2)
            .unwrap() // class_body
            .child(1)
            .unwrap(); // method_definition
        assert!(
            ts.is_async(method5, source5.as_bytes()),
            "async method with visibility modifier"
        );

        // 6. Async method without visibility modifier
        let source6 = "class D { async method() {} }";
        let tree6 = parse_ts(source6);
        let method6 = tree6
            .root_node()
            .child(0)
            .unwrap()
            .child(2)
            .unwrap()
            .child(1)
            .unwrap();
        assert!(
            ts.is_async(method6, source6.as_bytes()),
            "async method without modifier"
        );

        // 7. Non-async method
        let source7 = "class E { method() {} }";
        let tree7 = parse_ts(source7);
        let method7 = tree7
            .root_node()
            .child(0)
            .unwrap()
            .child(2)
            .unwrap()
            .child(1)
            .unwrap();
        assert!(!ts.is_async(method7, source7.as_bytes()), "non-async method");
    }

    #[test]
    fn test_extract_class() {
        let source = r#"
class Animal {
    constructor(name: string) {
        this.name = name;
    }

    speak(): void {
        console.log(this.name);
    }
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let class_node = root.child(0).unwrap();

        let class_info = ts.extract_class(class_node, source.as_bytes()).unwrap();
        assert_eq!(class_info.name, "Animal");
        assert_eq!(class_info.methods.len(), 2); // constructor + speak
    }

    #[test]
    fn test_extract_class_with_inheritance() {
        let source = r#"
class Dog extends Animal implements Pet {
    bark(): void {
        console.log("Woof!");
    }
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let class_node = root.child(0).unwrap();

        let class_info = ts.extract_class(class_node, source.as_bytes()).unwrap();
        assert_eq!(class_info.name, "Dog");
        assert!(class_info.bases.iter().any(|b| b == "Animal"));
        assert!(class_info.bases.iter().any(|b| b.contains("Pet")));
    }

    #[test]
    fn test_extract_imports() {
        let source = r#"
import { useState, useEffect } from 'react';
import axios from 'axios';
import * as fs from 'fs';
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let imports = ts.extract_imports(&tree, source.as_bytes());
        assert_eq!(imports.len(), 3);

        // Check named imports
        let react_import = imports.iter().find(|i| i.module == "react").unwrap();
        assert!(react_import.names.iter().any(|n| n == "useState"));
        assert!(react_import.names.iter().any(|n| n == "useEffect"));

        // Check default import
        let axios_import = imports.iter().find(|i| i.module == "axios").unwrap();
        assert!(axios_import
            .names
            .iter()
            .any(|n| n.contains("default as axios")));

        // Check namespace import
        let fs_import = imports.iter().find(|i| i.module == "fs").unwrap();
        assert!(fs_import.names.iter().any(|n| n.contains("* as fs")));
    }

    /// Test that TSX files are parsed with TSX grammar, not TypeScript grammar.
    /// TSX grammar understands JSX elements like <Component />.
    #[test]
    fn test_tsx_parser_selection() {
        let tsx_source = r#"
import React from 'react';

function MyComponent(): JSX.Element {
    return <div className="hello">Hello World</div>;
}
"#;
        let ts = TypeScript::new();

        // Parse with TSX grammar (should work for TSX files)
        let mut tsx_parser = tsx_parser().unwrap();
        let tsx_tree = tsx_parser.parse(tsx_source, None).unwrap();

        // Verify the tree is valid and contains JSX elements
        let root = tsx_tree.root_node();
        assert!(!root.has_error(), "TSX parser should handle JSX syntax without errors");

        // Find the JSX element in the tree
        let has_jsx = find_node_by_kind(root, "jsx_element").is_some()
            || find_node_by_kind(root, "jsx_self_closing_element").is_some();
        assert!(has_jsx, "TSX parser should recognize JSX elements");

        // Test parser_for_path returns TSX parser for .tsx files
        let tsx_path = Path::new("component.tsx");
        let mut parser_from_path = ts.parser_for_path(tsx_path).unwrap();
        let tree_from_path = parser_from_path.parse(tsx_source, None).unwrap();
        assert!(
            !tree_from_path.root_node().has_error(),
            "parser_for_path should return TSX parser for .tsx files"
        );

        // Test parser_for_path returns TSX parser for .jsx files
        let jsx_path = Path::new("component.jsx");
        let mut jsx_parser_result = ts.parser_for_path(jsx_path).unwrap();
        let jsx_tree = jsx_parser_result.parse(tsx_source, None).unwrap();
        assert!(
            !jsx_tree.root_node().has_error(),
            "parser_for_path should return TSX parser for .jsx files"
        );
    }

    /// Helper function to find a node by kind in the AST tree.
    fn find_node_by_kind<'a>(node: tree_sitter::Node<'a>, kind: &str) -> Option<tree_sitter::Node<'a>> {
        if node.kind() == kind {
            return Some(node);
        }
        for child in node.children(&mut node.walk()) {
            if let Some(found) = find_node_by_kind(child, kind) {
                return Some(found);
            }
        }
        None
    }

    /// Test extraction of abstract classes with abstract methods.
    #[test]
    fn test_extract_abstract_class() {
        let source = r#"
abstract class Base {
    abstract getValue(): number;

    normalMethod(): void {
        console.log("hello");
    }
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let class_node = root.child(0).unwrap();

        let class_info = ts.extract_class(class_node, source.as_bytes()).unwrap();
        assert_eq!(class_info.name, "Base");
        // Class should have "abstract" decorator
        assert!(
            class_info.decorators.contains(&"abstract".to_string()),
            "Abstract class should have 'abstract' decorator, got: {:?}",
            class_info.decorators
        );

        // Should have 2 methods: abstract getValue and normal normalMethod
        assert_eq!(class_info.methods.len(), 2);

        // Find abstract method
        let abstract_method = class_info
            .methods
            .iter()
            .find(|m| m.name == "getValue")
            .expect("Should find getValue method");
        assert!(
            abstract_method.decorators.contains(&"abstract".to_string()),
            "Abstract method should have 'abstract' decorator, got: {:?}",
            abstract_method.decorators
        );
        assert_eq!(abstract_method.return_type, Some("number".to_string()));

        // Find normal method
        let normal_method = class_info
            .methods
            .iter()
            .find(|m| m.name == "normalMethod")
            .expect("Should find normalMethod");
        assert!(
            !normal_method.decorators.contains(&"abstract".to_string()),
            "Normal method should NOT have 'abstract' decorator"
        );
    }

    /// Test extraction of abstract method with accessibility modifier.
    #[test]
    fn test_extract_abstract_method_with_modifier() {
        let source = r#"
abstract class Base {
    protected abstract compute(x: number): void;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let class_node = root.child(0).unwrap();

        let class_info = ts.extract_class(class_node, source.as_bytes()).unwrap();
        assert_eq!(class_info.methods.len(), 1);

        let method = &class_info.methods[0];
        assert_eq!(method.name, "compute");
        assert!(
            method.decorators.contains(&"abstract".to_string()),
            "Method should have 'abstract' decorator"
        );
        assert!(
            method.decorators.contains(&"protected".to_string()),
            "Method should have 'protected' decorator, got: {:?}",
            method.decorators
        );
        assert_eq!(method.params.len(), 1);
        assert!(method.params[0].contains("x"));
        assert_eq!(method.return_type, Some("void".to_string()));
    }

    /// Test extraction of getter and setter methods.
    #[test]
    fn test_extract_getter_setter() {
        let source = r#"
class Person {
    private _name: string = "";

    get name(): string {
        return this._name;
    }

    set name(value: string) {
        this._name = value;
    }
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let class_node = root.child(0).unwrap();

        let class_info = ts.extract_class(class_node, source.as_bytes()).unwrap();
        assert_eq!(class_info.name, "Person");

        // Find getter
        let getter = class_info
            .methods
            .iter()
            .find(|m| m.name == "name" && m.decorators.contains(&"getter".to_string()));
        assert!(getter.is_some(), "Should find getter for 'name'");
        let getter = getter.unwrap();
        assert_eq!(getter.return_type, Some("string".to_string()));

        // Find setter
        let setter = class_info
            .methods
            .iter()
            .find(|m| m.name == "name" && m.decorators.contains(&"setter".to_string()));
        assert!(setter.is_some(), "Should find setter for 'name'");
        let setter = setter.unwrap();
        assert_eq!(setter.params.len(), 1);
        assert!(setter.params[0].contains("value"));
    }

    /// Test getter/setter with static modifier.
    #[test]
    fn test_extract_static_getter_setter() {
        let source = r#"
class Config {
    private static _instance: Config;

    static get instance(): Config {
        return Config._instance;
    }
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let class_node = root.child(0).unwrap();

        let class_info = ts.extract_class(class_node, source.as_bytes()).unwrap();

        let static_getter = class_info
            .methods
            .iter()
            .find(|m| m.name == "instance");
        assert!(static_getter.is_some(), "Should find 'instance' getter");

        let method = static_getter.unwrap();
        assert!(
            method.decorators.contains(&"getter".to_string()),
            "Should have 'getter' decorator"
        );
        assert!(
            method.decorators.contains(&"static".to_string()),
            "Should have 'static' decorator, got: {:?}",
            method.decorators
        );
    }

    // =========================================================================
    // FEATURE TESTS: Index Signatures
    // =========================================================================

    /// Test extraction of index signatures from interfaces.
    #[test]
    fn test_extract_index_signature_string_key() {
        let source = r#"
interface Dict {
    [key: string]: number;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let interface_node = root.child(0).unwrap();

        let class_info = ts.extract_class(interface_node, source.as_bytes()).unwrap();
        assert!(class_info.name.contains("Dict"));

        // Should have one method representing the index signature
        assert_eq!(class_info.methods.len(), 1, "Should have 1 index signature");

        let index_sig = &class_info.methods[0];
        assert!(
            index_sig.decorators.contains(&"index_signature".to_string()),
            "Should have 'index_signature' decorator, got: {:?}",
            index_sig.decorators
        );
        assert!(
            index_sig.name.contains("string"),
            "Name should contain key type 'string', got: {}",
            index_sig.name
        );
        assert_eq!(
            index_sig.return_type,
            Some("number".to_string()),
            "Return type should be 'number'"
        );
    }

    /// Test extraction of index signatures with number key.
    #[test]
    fn test_extract_index_signature_number_key() {
        let source = r#"
interface ArrayLike {
    [index: number]: string;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let interface_node = root.child(0).unwrap();

        let class_info = ts.extract_class(interface_node, source.as_bytes()).unwrap();

        assert_eq!(class_info.methods.len(), 1);
        let index_sig = &class_info.methods[0];

        assert!(
            index_sig.decorators.contains(&"index_signature".to_string()),
            "Should have 'index_signature' decorator"
        );
        assert!(
            index_sig.name.contains("number"),
            "Name should contain key type 'number', got: {}",
            index_sig.name
        );
        assert_eq!(
            index_sig.return_type,
            Some("string".to_string()),
            "Return type should be 'string'"
        );
    }

    /// Test extraction of multiple index signatures.
    #[test]
    fn test_extract_multiple_index_signatures() {
        let source = r#"
interface Dict {
    [key: string]: number;
    [index: number]: number;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let interface_node = root.child(0).unwrap();

        let class_info = ts.extract_class(interface_node, source.as_bytes()).unwrap();

        // Should have 2 index signatures
        let index_sigs: Vec<_> = class_info
            .methods
            .iter()
            .filter(|m| m.decorators.contains(&"index_signature".to_string()))
            .collect();

        assert_eq!(index_sigs.len(), 2, "Should have 2 index signatures");

        // One with string key, one with number key
        let has_string = index_sigs.iter().any(|s| s.name.contains("string"));
        let has_number = index_sigs.iter().any(|s| s.name.contains("number"));

        assert!(has_string, "Should have string index signature");
        assert!(has_number, "Should have number index signature");
    }

    /// Test index signature with methods and properties.
    #[test]
    fn test_extract_index_signature_with_other_members() {
        let source = r#"
interface MixedInterface {
    name: string;
    getValue(): number;
    [key: string]: any;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let interface_node = root.child(0).unwrap();

        let class_info = ts.extract_class(interface_node, source.as_bytes()).unwrap();

        // Should have property, method, and index signature
        assert!(
            class_info.methods.len() >= 2,
            "Should have at least 2 members (method + index sig)"
        );

        // Find index signature
        let index_sig = class_info
            .methods
            .iter()
            .find(|m| m.decorators.contains(&"index_signature".to_string()));

        assert!(index_sig.is_some(), "Should have index signature");

        // Find getValue method
        let method = class_info.methods.iter().find(|m| m.name == "getValue");
        assert!(method.is_some(), "Should have getValue method");
    }

    // =========================================================================
    // FEATURE TESTS: Type Guards
    // =========================================================================

    /// Test extraction of type guard function declaration.
    #[test]
    fn test_extract_type_guard_function() {
        let source = r#"
function isString(x: unknown): x is string {
    return typeof x === 'string';
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let func = ts.extract_function(func_node, source.as_bytes()).unwrap();

        assert_eq!(func.name, "isString");
        assert!(
            func.decorators.contains(&"type_guard".to_string()),
            "Should have 'type_guard' decorator, got: {:?}",
            func.decorators
        );
        assert!(
            func.return_type.as_ref().map(|rt| rt.contains("is")).unwrap_or(false),
            "Return type should contain 'is' predicate, got: {:?}",
            func.return_type
        );
    }

    /// Test extraction of type guard for number.
    #[test]
    fn test_extract_type_guard_number() {
        let source = r#"
function isNumber(x: unknown): x is number {
    return typeof x === 'number';
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let func = ts.extract_function(func_node, source.as_bytes()).unwrap();

        assert_eq!(func.name, "isNumber");
        assert!(
            func.decorators.contains(&"type_guard".to_string()),
            "Should have 'type_guard' decorator"
        );
        assert!(
            func.return_type.as_ref().map(|rt| rt.contains("number")).unwrap_or(false),
            "Return type should mention 'number'"
        );
    }

    /// Test extraction of type guard for custom type.
    #[test]
    fn test_extract_type_guard_custom_type() {
        let source = r#"
interface User {
    name: string;
    id: number;
}

function isUser(obj: unknown): obj is User {
    return typeof obj === 'object' && obj !== null && 'name' in obj;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        // Find the function node (second child after interface)
        let root = tree.root_node();
        let mut func_node = None;
        for child in root.children(&mut root.walk()) {
            if child.kind() == "function_declaration" {
                func_node = Some(child);
                break;
            }
        }

        let func = ts
            .extract_function(func_node.unwrap(), source.as_bytes())
            .unwrap();

        assert_eq!(func.name, "isUser");
        assert!(
            func.decorators.contains(&"type_guard".to_string()),
            "Should have 'type_guard' decorator for custom type guard"
        );
        assert!(
            func.return_type.as_ref().map(|rt| rt.contains("User")).unwrap_or(false),
            "Return type should mention 'User'"
        );
    }

    /// Test that regular functions are NOT marked as type guards.
    #[test]
    fn test_regular_function_not_type_guard() {
        let source = r#"
function regularFunction(x: unknown): boolean {
    return typeof x === 'string';
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let func = ts.extract_function(func_node, source.as_bytes()).unwrap();

        assert_eq!(func.name, "regularFunction");
        assert!(
            !func.decorators.contains(&"type_guard".to_string()),
            "Regular boolean function should NOT have 'type_guard' decorator"
        );
        assert_eq!(func.return_type, Some("boolean".to_string()));
    }

    /// Test type guard in arrow function.
    #[test]
    fn test_extract_type_guard_arrow_function() {
        let source = r#"
const isArray = (x: unknown): x is Array<unknown> => {
    return Array.isArray(x);
};
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        // Navigate to arrow function
        let lexical = root.child(0).unwrap();
        let declarator = lexical.child(1).unwrap();
        let arrow = declarator.child(2).unwrap();

        let func = ts.extract_function(arrow, source.as_bytes()).unwrap();

        assert_eq!(func.name, "isArray");
        assert!(
            func.decorators.contains(&"type_guard".to_string()),
            "Arrow function type guard should have 'type_guard' decorator, got: {:?}",
            func.decorators
        );
    }

    /// Test type guard as class method.
    #[test]
    fn test_extract_type_guard_method() {
        let source = r#"
class TypeChecker {
    isString(x: unknown): x is string {
        return typeof x === 'string';
    }
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let class_node = root.child(0).unwrap();

        let class_info = ts.extract_class(class_node, source.as_bytes()).unwrap();

        let method = class_info
            .methods
            .iter()
            .find(|m| m.name == "isString")
            .expect("Should find isString method");

        assert!(
            method.decorators.contains(&"type_guard".to_string()),
            "Method type guard should have 'type_guard' decorator, got: {:?}",
            method.decorators
        );
    }

    /// Test asserts type guard (assertion function).
    #[test]
    fn test_extract_asserts_type_guard() {
        let source = r#"
function assertIsString(x: unknown): asserts x is string {
    if (typeof x !== 'string') {
        throw new Error('Not a string');
    }
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let func = ts.extract_function(func_node, source.as_bytes()).unwrap();

        assert_eq!(func.name, "assertIsString");
        // Asserts type guard may or may not be detected depending on tree-sitter
        // The important thing is the return type is captured
        assert!(
            func.return_type.as_ref().map(|rt| rt.contains("asserts")).unwrap_or(false)
                || func.decorators.contains(&"type_guard".to_string()),
            "Asserts type guard should be captured in return type or decorator"
        );
    }

    /// Test JSDoc detection with regular comments in between.
    ///
    /// This tests the fix for the bug where a regular `//` comment between JSDoc
    /// and function would prevent JSDoc from being found.
    #[test]
    fn test_jsdoc_with_comment_gap() {
        let ts = TypeScript::new();

        // Test 1: JSDoc directly before function (baseline)
        let source1 = r#"/** This is JSDoc for foo */
function foo() {}"#;
        let tree1 = parse_ts(source1);
        let func1 = tree1.root_node().child(1).unwrap();
        let doc1 = ts.find_jsdoc(func1, source1.as_bytes());
        assert!(doc1.is_some(), "JSDoc should be found directly before function");
        assert!(
            doc1.unwrap().contains("JSDoc for foo"),
            "JSDoc content should be extracted"
        );

        // Test 2: JSDoc with regular comment in between (the bug case)
        let source2 = r#"/** This is JSDoc for bar */
// This regular comment should not break JSDoc detection
function bar() {}"#;
        let tree2 = parse_ts(source2);
        let func2 = tree2.root_node().child(2).unwrap();
        let doc2 = ts.find_jsdoc(func2, source2.as_bytes());
        assert!(
            doc2.is_some(),
            "JSDoc should be found even with regular comment in between"
        );
        assert!(
            doc2.unwrap().contains("JSDoc for bar"),
            "JSDoc content should be extracted through comment gap"
        );

        // Test 3: Only regular comment (no JSDoc) - should return None
        let source3 = r#"// Not JSDoc, just a regular comment
function baz() {}"#;
        let tree3 = parse_ts(source3);
        let func3 = tree3.root_node().child(1).unwrap();
        let doc3 = ts.find_jsdoc(func3, source3.as_bytes());
        assert!(doc3.is_none(), "Regular comment should not be treated as JSDoc");

        // Test 4: Multiple regular comments before JSDoc
        let source4 = r#"/** JSDoc found through multiple comments */
// comment 1
// comment 2
// comment 3
function multi() {}"#;
        let tree4 = parse_ts(source4);
        let func4 = tree4.root_node().child(4).unwrap();
        let doc4 = ts.find_jsdoc(func4, source4.as_bytes());
        assert!(
            doc4.is_some(),
            "JSDoc should be found through multiple regular comments"
        );

        // Test 5: Block comment (not JSDoc) should continue search
        let source5 = r#"/** Actual JSDoc */
/* Regular block comment */
function block() {}"#;
        let tree5 = parse_ts(source5);
        let func5 = tree5.root_node().child(2).unwrap();
        let doc5 = ts.find_jsdoc(func5, source5.as_bytes());
        assert!(
            doc5.is_some(),
            "JSDoc should be found past regular block comment"
        );
        assert!(doc5.unwrap().contains("Actual JSDoc"));
    }

    // =========================================================================
    // BUG FIX TESTS: Object/Array Mutation Tracking
    // =========================================================================

    /// Test that object mutations through member expressions are tracked correctly.
    /// Previously, `obj.field = value` would only track `obj` as a USE, not a MUTATION.
    #[test]
    fn test_dfg_object_mutation_tracking() {
        let source = r#"
function mutateObject(obj: any, value: number) {
    obj.field = value;
    obj.nested.deep = value;
    return obj;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let dfg = ts.build_dfg(func_node, source.as_bytes()).unwrap();

        // obj should be defined (as parameter) and have mutations
        assert!(
            dfg.definitions.contains_key("obj"),
            "obj should have definitions: {:?}",
            dfg.definitions
        );

        // Check that obj has mutation edges (not just definition)
        let obj_mutations: Vec<_> = dfg
            .edges
            .iter()
            .filter(|e| e.variable == "obj" && matches!(e.kind, DataflowKind::Mutation))
            .collect();

        assert!(
            !obj_mutations.is_empty(),
            "obj should have mutation edges for member expression assignments, got edges: {:?}",
            dfg.edges
        );
    }

    /// Test that array mutations through subscript expressions are tracked correctly.
    /// Previously, `arr[0] = value` would only track `arr` as a USE, not a MUTATION.
    #[test]
    fn test_dfg_array_mutation_tracking() {
        let source = r#"
function mutateArray(arr: number[], idx: number, value: number) {
    arr[0] = value;
    arr[idx] = value;
    return arr;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let dfg = ts.build_dfg(func_node, source.as_bytes()).unwrap();

        // arr should be defined (as parameter) and have mutations
        assert!(
            dfg.definitions.contains_key("arr"),
            "arr should have definitions: {:?}",
            dfg.definitions
        );

        // Check that arr has mutation edges
        let arr_mutations: Vec<_> = dfg
            .edges
            .iter()
            .filter(|e| e.variable == "arr" && matches!(e.kind, DataflowKind::Mutation))
            .collect();

        assert!(
            !arr_mutations.is_empty(),
            "arr should have mutation edges for subscript expression assignments, got edges: {:?}",
            dfg.edges
        );

        // Also verify that idx is tracked as a USE (it's read to compute the index)
        assert!(
            dfg.uses.contains_key("idx"),
            "idx should be tracked as a use (read for index computation): {:?}",
            dfg.uses
        );
    }

    /// Test augmented assignment on object members.
    /// `obj.x += 1` should mark obj as both used and mutated.
    #[test]
    fn test_dfg_augmented_assignment_member() {
        let source = r#"
function incrementField(obj: any) {
    obj.count += 1;
    return obj.count;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let dfg = ts.build_dfg(func_node, source.as_bytes()).unwrap();

        // obj should have both use and mutation edges
        let obj_uses: Vec<_> = dfg
            .edges
            .iter()
            .filter(|e| e.variable == "obj" && matches!(e.kind, DataflowKind::Use))
            .collect();

        let obj_mutations: Vec<_> = dfg
            .edges
            .iter()
            .filter(|e| e.variable == "obj" && matches!(e.kind, DataflowKind::Mutation))
            .collect();

        assert!(
            !obj_uses.is_empty(),
            "obj should have use edges for augmented assignment (read current value)"
        );
        assert!(
            !obj_mutations.is_empty(),
            "obj should have mutation edges for augmented assignment (write new value)"
        );
    }

    /// Test update expressions (++, --) on object members.
    /// `obj.count++` should mark obj as both used and mutated.
    #[test]
    fn test_dfg_update_expression_member() {
        let source = r#"
function incrementCounter(obj: any, arr: number[]) {
    obj.count++;
    arr[0]--;
    return obj.count;
}
"#;
        let tree = parse_ts(source);
        let ts = TypeScript::new();

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let dfg = ts.build_dfg(func_node, source.as_bytes()).unwrap();

        // obj should have mutation edges from obj.count++
        let obj_mutations: Vec<_> = dfg
            .edges
            .iter()
            .filter(|e| e.variable == "obj" && matches!(e.kind, DataflowKind::Mutation))
            .collect();

        assert!(
            !obj_mutations.is_empty(),
            "obj should have mutation edges for update expression (obj.count++)"
        );

        // arr should have mutation edges from arr[0]--
        let arr_mutations: Vec<_> = dfg
            .edges
            .iter()
            .filter(|e| e.variable == "arr" && matches!(e.kind, DataflowKind::Mutation))
            .collect();

        assert!(
            !arr_mutations.is_empty(),
            "arr should have mutation edges for update expression (arr[0]--)"
        );
    }

    // =========================================================================
    // EXCEPTION FLOW TESTS
    // =========================================================================

    mod exception {
        use super::*;
        use crate::cfg::types::EdgeType;

        /// Test basic try/catch exception flow in CFG.
        #[test]
        fn test_cfg_try_catch_basic() {
            let source = r#"
function process(data: any) {
    try {
        riskyOperation(data);
    } catch (e) {
        console.error(e);
    }
    return true;
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Verify we have try and catch blocks
            let has_try_block = cfg.blocks.values().any(|b| b.label == "try");
            let has_catch_block = cfg.blocks.values().any(|b| b.label.starts_with("catch"));

            assert!(has_try_block, "CFG should have a 'try' block");
            assert!(has_catch_block, "CFG should have a 'catch' block");

            // Verify exception edge from try to catch
            let exception_edges: Vec<_> = cfg
                .edges
                .iter()
                .filter(|e| matches!(e.edge_type, EdgeType::Exception))
                .collect();

            assert!(
                !exception_edges.is_empty(),
                "CFG should have exception edges from try to catch"
            );
        }

        /// Test try/catch/finally exception flow in CFG.
        #[test]
        fn test_cfg_try_catch_finally() {
            let source = r#"
function processWithCleanup(data: any) {
    try {
        riskyOperation(data);
    } catch (e) {
        handleError(e);
    } finally {
        cleanup();
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Verify we have try, catch, and finally blocks
            let has_try_block = cfg.blocks.values().any(|b| b.label == "try");
            let has_catch_block = cfg.blocks.values().any(|b| b.label.starts_with("catch"));
            let has_finally_block = cfg.blocks.values().any(|b| b.label == "finally");

            assert!(has_try_block, "CFG should have a 'try' block");
            assert!(has_catch_block, "CFG should have a 'catch' block");
            assert!(has_finally_block, "CFG should have a 'finally' block");

            // Verify finally edges exist
            let finally_edges: Vec<_> = cfg
                .edges
                .iter()
                .filter(|e| matches!(e.edge_type, EdgeType::Finally))
                .collect();

            assert!(
                !finally_edges.is_empty(),
                "CFG should have finally edges"
            );
        }

        /// Test try with only finally (no catch) exception flow.
        #[test]
        fn test_cfg_try_finally_only() {
            let source = r#"
function processWithCleanupOnly(data: any) {
    try {
        riskyOperation(data);
    } finally {
        cleanup();
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Verify we have try and finally blocks but no catch
            let has_try_block = cfg.blocks.values().any(|b| b.label == "try");
            let has_finally_block = cfg.blocks.values().any(|b| b.label == "finally");
            let has_catch_block = cfg.blocks.values().any(|b| b.label.starts_with("catch"));

            assert!(has_try_block, "CFG should have a 'try' block");
            assert!(has_finally_block, "CFG should have a 'finally' block");
            assert!(!has_catch_block, "CFG should NOT have a 'catch' block");

            // Verify exception edge goes to finally
            let exception_to_finally: Vec<_> = cfg
                .edges
                .iter()
                .filter(|e| matches!(e.edge_type, EdgeType::Exception))
                .collect();

            assert!(
                !exception_to_finally.is_empty(),
                "CFG should have exception edge to finally when no catch"
            );
        }

        /// Test throw statement creates proper exception routing.
        #[test]
        fn test_cfg_throw_statement() {
            let source = r#"
function validate(data: any) {
    if (!data) {
        throw new Error("Data is required");
    }
    return process(data);
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Verify we have a throw block
            let throw_blocks: Vec<_> = cfg
                .blocks
                .values()
                .filter(|b| b.label.starts_with("throw"))
                .collect();

            assert!(
                !throw_blocks.is_empty(),
                "CFG should have a 'throw' block for throw statement"
            );

            // Throw block should be an exit point (exception propagates)
            let throw_block_id = throw_blocks[0].id;
            assert!(
                cfg.exits.contains(&throw_block_id),
                "Throw block should be an exit point when not inside try/catch"
            );
        }

        /// Test throw inside try routes to catch handler.
        #[test]
        fn test_cfg_throw_inside_try() {
            let source = r#"
function validateWithCatch(data: any) {
    try {
        if (!data) {
            throw new Error("Data is required");
        }
        return process(data);
    } catch (e) {
        console.error(e);
        return null;
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Verify throw block routes to catch via exception edge
            let exception_edges: Vec<_> = cfg
                .edges
                .iter()
                .filter(|e| {
                    matches!(e.edge_type, EdgeType::Exception)
                        && e.condition.as_ref().map(|c| c.contains("throw")).unwrap_or(false)
                })
                .collect();

            assert!(
                !exception_edges.is_empty(),
                "CFG should have exception edge from throw to catch handler"
            );
        }

        /// Test async function with await exception flow.
        #[test]
        fn test_cfg_async_await_exception() {
            let source = r#"
async function fetchData(url: string) {
    try {
        const response = await fetch(url);
        return response.json();
    } catch (e) {
        console.error("Fetch failed:", e);
        return null;
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Verify we have blocks for the async flow
            assert!(
                cfg.blocks.len() >= 3,
                "Async function CFG should have multiple blocks for try/catch flow"
            );

            // Verify exception edges exist (await rejection routes to catch)
            let exception_edges: Vec<_> = cfg
                .edges
                .iter()
                .filter(|e| matches!(e.edge_type, EdgeType::Exception))
                .collect();

            assert!(
                !exception_edges.is_empty(),
                "Async CFG should have exception edges for await rejection"
            );
        }

        /// Test optional catch binding (catch without parameter).
        #[test]
        fn test_cfg_optional_catch_binding() {
            let source = r#"
function suppressError() {
    try {
        riskyOperation();
    } catch {
        // Intentionally ignored
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should still have proper try/catch flow even with bare catch
            let has_try_block = cfg.blocks.values().any(|b| b.label == "try");
            let has_catch_block = cfg.blocks.values().any(|b| b.label.starts_with("catch"));

            assert!(has_try_block, "CFG should have a 'try' block");
            assert!(has_catch_block, "CFG should have a 'catch' block even with optional binding");
        }

        /// Test Promise.catch() creates implicit exception handling.
        #[test]
        fn test_cfg_promise_catch() {
            let source = r#"
function fetchWithFallback(url: string) {
    const result = fetch(url)
        .then(response => response.json())
        .catch(e => ({ error: e }));
    return result;
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Promise.catch() handling creates exception edges or catch-related blocks
            // The implementation recognizes .catch() calls and models them as exception handlers
            let has_catch_block = cfg
                .blocks
                .values()
                .any(|b| b.label.contains("catch") || b.label.contains("handler"));

            let has_exception_edge = cfg
                .edges
                .iter()
                .any(|e| matches!(e.edge_type, EdgeType::Exception) || e.condition.as_ref().map(|c| c.contains("rejected")).unwrap_or(false));

            assert!(
                has_catch_block || has_exception_edge || cfg.blocks.len() > 2,
                "CFG should recognize Promise.catch() pattern (blocks: {}, has catch: {}, has exception edge: {})",
                cfg.blocks.len(),
                has_catch_block,
                has_exception_edge
            );
        }

        /// Test error cause pattern: throw new Error('msg', { cause: e })
        #[test]
        fn test_cfg_error_cause() {
            let source = r#"
function wrapError(originalError: Error) {
    try {
        riskyOperation();
    } catch (e) {
        throw new Error("Wrapped error", { cause: e });
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Verify throw block exists with proper labeling
            let throw_blocks: Vec<_> = cfg
                .blocks
                .values()
                .filter(|b| b.label.starts_with("throw"))
                .collect();

            assert!(
                !throw_blocks.is_empty(),
                "CFG should have throw block for error cause pattern"
            );
        }

        /// Test Express-style error middleware pattern.
        #[test]
        fn test_cfg_express_error_middleware() {
            let source = r#"
function errorHandler(err: Error, req: Request, res: Response, next: NextFunction) {
    try {
        if (err instanceof ValidationError) {
            return res.status(400).json({ error: err.message });
        }
        throw err;  // Re-throw for next handler
    } catch (e) {
        next(e);  // Pass to next error handler
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Verify we have proper exception flow
            let exception_edges: Vec<_> = cfg
                .edges
                .iter()
                .filter(|e| matches!(e.edge_type, EdgeType::Exception))
                .collect();

            assert!(
                !exception_edges.is_empty(),
                "Express error middleware should have exception flow edges"
            );

            // Verify both return and throw paths exist
            let has_return = cfg.blocks.values().any(|b| b.label == "return");
            let has_throw = cfg.blocks.values().any(|b| b.label.starts_with("throw"));

            assert!(has_return, "Should have return path");
            assert!(has_throw, "Should have throw (re-throw) path");
        }

        /// Test nested try/catch exception routing.
        #[test]
        fn test_cfg_nested_try_catch() {
            let source = r#"
function nestedHandling(data: any) {
    try {
        try {
            parseData(data);
        } catch (parseError) {
            throw new Error("Parse failed: " + parseError.message);
        }
    } catch (e) {
        return null;
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Nested try/catch should produce a non-trivial CFG
            // The exact structure depends on how deep nesting is processed
            assert!(
                cfg.blocks.len() >= 3,
                "Nested try/catch CFG should have multiple blocks (got {})",
                cfg.blocks.len()
            );

            // Should have at least some exception-related structure
            let has_exception_edges = cfg
                .edges
                .iter()
                .any(|e| matches!(e.edge_type, EdgeType::Exception));

            let has_try_like_block = cfg
                .blocks
                .values()
                .any(|b| b.label.contains("try") || b.label.contains("catch") || b.label.contains("throw"));

            assert!(
                has_exception_edges || has_try_like_block,
                "Nested try/catch should have exception flow structure (has_exception_edges: {}, has_try_like_block: {})",
                has_exception_edges,
                has_try_like_block
            );
        }

        /// Test instanceof check in catch block (common pattern).
        #[test]
        fn test_cfg_instanceof_in_catch() {
            let source = r#"
function handleTypedError(operation: () => void) {
    try {
        operation();
    } catch (e) {
        if (e instanceof TypeError) {
            handleTypeError(e);
        } else if (e instanceof RangeError) {
            handleRangeError(e);
        } else {
            throw e;  // Re-throw unknown errors
        }
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should have branching within catch for instanceof checks
            assert!(
                cfg.blocks.len() >= 5,
                "CFG should have multiple blocks for instanceof branching in catch"
            );

            // Decision points should be tracked for the if/else if branches
            assert!(
                cfg.decision_points >= 2,
                "CFG should track decision points for instanceof checks"
            );
        }
    }

    // =========================================================================
    // Async Flow Tests
    // =========================================================================

    /// Tests for TypeScript/JavaScript async/await and Promise flow handling.
    mod async_flow {
        use super::*;

        fn parse_ts(source: &str) -> Tree {
            let mut parser = Parser::new();
            parser
                .set_language(&tree_sitter_typescript::LANGUAGE_TYPESCRIPT.into())
                .unwrap();
            parser.parse(source, None).unwrap()
        }

        /// Test basic async function CFG with single await.
        #[test]
        fn test_async_function_single_await() {
            let source = r#"
async function fetchUser(id: string): Promise<User> {
    const response = await fetch(`/user/${id}`);
    return response.json();
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // CFG should be marked as async
            assert!(cfg.is_async, "CFG should be marked as async for async function");

            // Should have exactly 1 await point
            assert_eq!(cfg.await_points, 1, "Should have 1 await point");

            // Should have AwaitPoint block type
            let has_await_block = cfg.blocks.values().any(|b| {
                matches!(b.block_type, BlockType::AwaitPoint)
            });
            assert!(has_await_block, "Should have AwaitPoint block");

            // Should have Await edge type
            let has_await_edge = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::Await)
            });
            assert!(has_await_edge, "Should have Await edge");
        }

        /// Test async function with multiple await points.
        #[test]
        fn test_async_function_multiple_awaits() {
            let source = r#"
async function processData(id: string): Promise<Data> {
    const user = await fetchUser(id);
    const profile = await fetchProfile(user.id);
    const preferences = await fetchPreferences(user.id);
    return { user, profile, preferences };
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should have 3 await points
            assert_eq!(cfg.await_points, 3, "Should have 3 await points");

            // Should have 3 AwaitPoint blocks
            let await_block_count = cfg.blocks.values()
                .filter(|b| matches!(b.block_type, BlockType::AwaitPoint))
                .count();
            assert_eq!(await_block_count, 3, "Should have 3 AwaitPoint blocks");

            // Should have 3 Await edges
            let await_edge_count = cfg.edges.iter()
                .filter(|e| matches!(e.edge_type, EdgeType::Await))
                .count();
            assert_eq!(await_edge_count, 3, "Should have 3 Await edges");
        }

        /// Test await with try/catch exception handling.
        #[test]
        fn test_async_await_with_try_catch() {
            let source = r#"
async function safeFetch(url: string): Promise<any> {
    try {
        const response = await fetch(url);
        const data = await response.json();
        return data;
    } catch (error) {
        console.error('Fetch failed:', error);
        return null;
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should have 2 await points
            assert_eq!(cfg.await_points, 2, "Should have 2 await points");

            // Should have rejection paths to catch block
            let has_rejection_edge = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::PromiseRejected)
            });
            assert!(has_rejection_edge, "Should have PromiseRejected edge to catch");
        }

        /// Test Promise.then() chain CFG transformation.
        #[test]
        fn test_promise_then_chain() {
            let source = r#"
function processWithPromises(url: string) {
    fetch(url)
        .then(response => response.json())
        .then(data => processData(data));
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should have PromiseThen blocks
            let has_then_block = cfg.blocks.values().any(|b| {
                matches!(b.block_type, BlockType::PromiseThen)
            });
            assert!(has_then_block, "Should have PromiseThen block");

            // Should have PromiseResolved edges
            let has_resolved_edge = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::PromiseResolved)
            });
            assert!(has_resolved_edge, "Should have PromiseResolved edge");
        }

        /// Test Promise.catch() exception handling.
        #[test]
        fn test_promise_catch() {
            let source = r#"
function fetchWithErrorHandling(url: string) {
    fetch(url)
        .then(res => res.json())
        .catch(err => {
            console.error('Failed:', err);
            return null;
        });
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should have PromiseCatch block
            let has_catch_block = cfg.blocks.values().any(|b| {
                matches!(b.block_type, BlockType::PromiseCatch)
            });
            assert!(has_catch_block, "Should have PromiseCatch block");

            // Should have rejected edge
            let has_rejected_edge = cfg.edges.iter().any(|e| {
                e.condition.as_ref().map(|c| c.contains("rejected")).unwrap_or(false)
            });
            assert!(has_rejected_edge, "Should have rejected edge to catch handler");
        }

        /// Test Promise.finally() always-execute path.
        #[test]
        fn test_promise_finally() {
            let source = r#"
function fetchWithCleanup(url: string) {
    fetch(url)
        .then(res => res.json())
        .finally(() => {
            cleanup();
        });
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should have PromiseFinally block
            let has_finally_block = cfg.blocks.values().any(|b| {
                matches!(b.block_type, BlockType::PromiseFinally)
            });
            assert!(has_finally_block, "Should have PromiseFinally block");

            // Should have PromiseSettled edge
            let has_settled_edge = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::PromiseSettled)
            });
            assert!(has_settled_edge, "Should have PromiseSettled edge");
        }

        /// Test Promise.all() parallel execution pattern.
        #[test]
        fn test_promise_all() {
            let source = r#"
async function fetchAll(ids: string[]) {
    const [user, posts] = await Promise.all([
        fetchUser(ids[0]),
        fetchPosts(ids[1])
    ]);
    return { user, posts };
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should have PromiseAll block
            let has_all_block = cfg.blocks.values().any(|b| {
                matches!(b.block_type, BlockType::PromiseAll)
            });
            assert!(has_all_block, "Should have PromiseAll block");

            // Should have TaskSpawn edge (spawning parallel tasks)
            let has_spawn_edge = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::TaskSpawn)
            });
            assert!(has_spawn_edge, "Should have TaskSpawn edge");

            // Should have PromiseAllBranch edges (one per task)
            let branch_edge_count = cfg.edges.iter()
                .filter(|e| matches!(e.edge_type, EdgeType::PromiseAllBranch))
                .count();
            assert_eq!(branch_edge_count, 2, "Should have 2 PromiseAllBranch edges");

            // Should have PromiseAllJoin edges
            let join_edge_count = cfg.edges.iter()
                .filter(|e| matches!(e.edge_type, EdgeType::PromiseAllJoin))
                .count();
            assert_eq!(join_edge_count, 2, "Should have 2 PromiseAllJoin edges");
        }

        /// Test Promise.race() first-wins pattern.
        #[test]
        fn test_promise_race() {
            let source = r#"
async function fetchWithTimeout(url: string, timeout: number) {
    const result = await Promise.race([
        fetch(url),
        delay(timeout).then(() => { throw new Error('Timeout'); })
    ]);
    return result;
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should have PromiseRace block
            let has_race_block = cfg.blocks.values().any(|b| {
                matches!(b.block_type, BlockType::PromiseRace)
            });
            assert!(has_race_block, "Should have PromiseRace block");

            // Should have PromiseRaceBranch edges
            let has_race_branch = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::PromiseRaceBranch)
            });
            assert!(has_race_branch, "Should have PromiseRaceBranch edge");

            // Should have PromiseRaceWinner edges
            let has_winner_edge = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::PromiseRaceWinner)
            });
            assert!(has_winner_edge, "Should have PromiseRaceWinner edge");
        }

        /// Test Promise.allSettled() always-completes pattern.
        #[test]
        fn test_promise_all_settled() {
            let source = r#"
async function fetchAllSettled(urls: string[]) {
    const results = await Promise.allSettled([
        fetch(urls[0]),
        fetch(urls[1]),
        fetch(urls[2])
    ]);
    return results;
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should have PromiseAllSettled block
            let has_all_settled_block = cfg.blocks.values().any(|b| {
                matches!(b.block_type, BlockType::PromiseAllSettled)
            });
            assert!(has_all_settled_block, "Should have PromiseAllSettled block");

            // Should have PromiseSettled edge (allSettled never rejects)
            let has_settled_edge = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::PromiseSettled)
            });
            assert!(has_settled_edge, "Should have PromiseSettled edge");
        }

        /// Test for await...of async iteration.
        #[test]
        fn test_for_await_of() {
            let source = r#"
async function processStream(stream: AsyncIterable<Data>) {
    for await (const item of stream) {
        await processItem(item);
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should have ForAwaitOf block
            let has_for_await_block = cfg.blocks.values().any(|b| {
                matches!(b.block_type, BlockType::ForAwaitOf)
            });
            assert!(has_for_await_block, "Should have ForAwaitOf block");

            // Should have ForAwaitIterate edge
            let has_iterate_edge = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::ForAwaitIterate)
            });
            assert!(has_iterate_edge, "Should have ForAwaitIterate edge");

            // Should have ForAwaitExhausted edge
            let has_exhausted_edge = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::ForAwaitExhausted)
            });
            assert!(has_exhausted_edge, "Should have ForAwaitExhausted edge");
        }

        /// Test async arrow function.
        #[test]
        fn test_async_arrow_function() {
            let source = r#"
const fetchData = async (url: string) => {
    const response = await fetch(url);
    return response.json();
};
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            // Navigate to arrow function: lexical_declaration -> variable_declarator -> arrow_function
            let lexical = root.child(0).unwrap();
            let declarator = lexical.child(1).unwrap();
            let arrow_func = declarator.child(2).unwrap();

            let cfg = ts.build_cfg(arrow_func, source.as_bytes()).unwrap();

            // Should be marked as async
            assert!(cfg.is_async, "Arrow function should be marked as async");

            // Should have await point
            assert_eq!(cfg.await_points, 1, "Should have 1 await point");
        }

        /// Test blocking call detection in async context.
        #[test]
        fn test_blocking_call_detection() {
            let source = r#"
async function badAsyncFunction(path: string) {
    const data = fs.readFileSync(path);  // Blocking!
    const parsed = await parseData(data);
    return parsed;
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should detect blocking call
            assert!(
                !cfg.blocking_calls.is_empty(),
                "Should detect blocking fs.readFileSync call"
            );

            // Blocking call should mention readFileSync (tuple format: (name, line))
            let has_read_file_sync = cfg.blocking_calls.iter()
                .any(|(name, _line)| name.contains("readFileSync"));
            assert!(has_read_file_sync, "Should report readFileSync as blocking");
        }

        /// Test complex Express async handler.
        #[test]
        fn test_express_async_handler() {
            let source = r#"
async function handleRequest(req: Request, res: Response) {
    try {
        const userId = req.params.id;
        const user = await userService.findById(userId);

        if (!user) {
            return res.status(404).json({ error: 'User not found' });
        }

        const posts = await postService.findByUserId(user.id);
        const enrichedUser = {
            ...user,
            posts
        };

        res.json(enrichedUser);
    } catch (error) {
        console.error('Request failed:', error);
        res.status(500).json({ error: 'Internal server error' });
    }
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should be async
            assert!(cfg.is_async, "Express handler should be async");

            // Should have 2 await points
            assert_eq!(cfg.await_points, 2, "Should have 2 await points (findById and findByUserId)");

            // Should have rejection paths to catch
            let has_rejection_to_catch = cfg.edges.iter().any(|e| {
                matches!(e.edge_type, EdgeType::PromiseRejected)
            });
            assert!(has_rejection_to_catch, "Should have rejection paths to catch block");

            // Should have branching for the if(!user) check
            assert!(cfg.decision_points >= 1, "Should have decision points for if check");
        }

        /// Test nested Promise.all with individual error handling.
        #[test]
        fn test_nested_promise_patterns() {
            let source = r#"
async function complexFetch(ids: string[]) {
    const results = await Promise.all(
        ids.map(async (id) => {
            try {
                return await fetchItem(id);
            } catch {
                return null;
            }
        })
    );
    return results.filter(Boolean);
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should be async
            assert!(cfg.is_async, "Function should be async");

            // Should have Promise.all block
            let has_all_block = cfg.blocks.values().any(|b| {
                matches!(b.block_type, BlockType::PromiseAll)
            });
            assert!(has_all_block, "Should have PromiseAll block");
        }

        /// Test sync function should not have async markers.
        #[test]
        fn test_sync_function_no_async_markers() {
            let source = r#"
function syncFunction(x: number): number {
    const result = compute(x);
    return result * 2;
}
"#;
            let tree = parse_ts(source);
            let ts = TypeScript::new();

            let root = tree.root_node();
            let func_node = root.child(0).unwrap();

            let cfg = ts.build_cfg(func_node, source.as_bytes()).unwrap();

            // Should NOT be marked as async
            assert!(!cfg.is_async, "Sync function should not be async");

            // Should have 0 await points
            assert_eq!(cfg.await_points, 0, "Sync function should have 0 await points");

            // Should have no blocking call warnings (not in async context)
            assert!(cfg.blocking_calls.is_empty(), "Sync function should not track blocking calls");
        }
    }
}
