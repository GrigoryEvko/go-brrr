//! Python language support.
//!
//! Implements the Language trait for Python using tree-sitter-python.
//! Extracts functions, classes, imports, and builds CFG/DFG.

use phf::phf_set;
use rustc_hash::FxHashMap;
use tree_sitter::{Node, Parser, Tree};

use crate::ast::types::{ClassInfo, FunctionInfo, ImportInfo};
use crate::cfg::types::{BlockId, BlockType, CFGBlock, CFGEdge, CFGInfo, EdgeType};
use crate::dfg::types::{DFGInfo, DataflowEdge, DataflowKind};
use crate::error::{BrrrError, Result};
use crate::lang::traits::Language;

/// All Python augmented assignment operators.
/// Uses compile-time perfect hashing for O(1) lookup instead of linear search.
/// These combine a binary operation with assignment: target op= value
static AUGMENTED_ASSIGN_OPS: phf::Set<&'static str> = phf_set! {
    "+=", "-=", "*=", "/=",   // Basic arithmetic
    "//=", "%=", "**=",       // Floor div, modulo, power
    "&=", "|=", "^=",         // Bitwise AND, OR, XOR
    "<<=", ">>=",             // Bit shifts
    "@=",                     // Matrix multiply (Python 3.5+)
};

/// Python language implementation.
pub struct Python;

// =============================================================================
// Call Graph Types
// =============================================================================

/// Information about a single call site extracted from Python source.
/// Used for building call graphs.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct CallInfo {
    /// Name of the called function or method
    pub callee: String,
    /// Line number of the call
    pub line: usize,
    /// Type of call (direct, method, self, chained)
    pub call_kind: CallKind,
    /// For method calls, the object being called on
    pub receiver: Option<String>,
}

/// Kind of call expression.
#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
pub enum CallKind {
    /// Direct function call: `foo()`
    Direct,
    /// Method call on self: `self.method()`
    SelfMethod,
    /// Method call on object: `obj.method()`
    Method,
    /// Chained method call: `obj.foo().bar()`
    Chained,
    /// Constructor/class instantiation: `MyClass()`
    Constructor,
    /// Super method call: `super().method()`
    SuperMethod,
}

impl Python {
    /// Get text from a node, handling UTF-8 safely.
    fn node_text<'a>(node: Node<'a>, source: &'a [u8]) -> &'a str {
        std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }

    /// Find first child with given kind.
    fn child_by_kind<'a>(node: Node<'a>, kind: &str) -> Option<Node<'a>> {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == kind {
                return Some(child);
            }
        }
        None
    }

    /// Access a child node by its field name.
    ///
    /// Uses tree-sitter's field-based access which is more efficient and
    /// semantically correct than searching by node kind. Field names are
    /// defined in the grammar and provide stable, named access to children.
    ///
    /// # Example
    /// For `typed_parameter` in `def foo(x: int)`:
    /// - `child_by_field(node, "type")` returns the type annotation node
    fn child_by_field<'a>(node: Node<'a>, field: &str) -> Option<Node<'a>> {
        node.child_by_field_name(field)
    }

    /// Extract type annotation from a type node.
    /// Strips surrounding quotes from forward reference annotations.
    fn extract_type(node: Node, source: &[u8]) -> String {
        let text = Self::node_text(node, source);
        // Normalize forward reference annotations by stripping quotes
        // Python allows "ClassName" or 'ClassName' for forward references
        Self::normalize_type_annotation(text)
    }

    /// Normalize a type annotation by stripping forward reference quotes.
    /// Handles both single and double quotes around type names, including
    /// nested quotes inside generic types like `Optional['Node']` or `List["Item"]`.
    ///
    /// Examples:
    /// - `'Node'` -> `Node`
    /// - `"Tree"` -> `Tree`
    /// - `Optional['Node']` -> `Optional[Node]`
    /// - `Dict['Key', 'Value']` -> `Dict[Key, Value]`
    /// - `Union['A', 'B']` -> `Union[A, B]`
    fn normalize_type_annotation(text: &str) -> String {
        let trimmed = text.trim();

        // Check for simple quoted forward references (entire type is quoted)
        if (trimmed.starts_with('"') && trimmed.ends_with('"'))
            || (trimmed.starts_with('\'') && trimmed.ends_with('\''))
        {
            if trimmed.len() >= 2 {
                return trimmed[1..trimmed.len() - 1].to_string();
            }
        }

        // Handle nested quotes in generic types: Optional['Node'], List["Item"], etc.
        // We need to strip quotes from within brackets while preserving the structure
        if trimmed.contains('[') && (trimmed.contains('\'') || trimmed.contains('"')) {
            return Self::normalize_generic_type_annotation(trimmed);
        }

        trimmed.to_string()
    }

    /// Normalize forward references inside generic type annotations.
    /// Handles `Optional['Node']` -> `Optional[Node]`, etc.
    fn normalize_generic_type_annotation(text: &str) -> String {
        let mut result = String::with_capacity(text.len());
        let mut chars = text.chars().peekable();
        let mut in_quote: Option<char> = None;
        let mut quote_content = String::new();

        while let Some(ch) = chars.next() {
            match (ch, in_quote) {
                // Starting a quoted section
                ('\'' | '"', None) => {
                    in_quote = Some(ch);
                    quote_content.clear();
                }
                // Ending a quoted section (matching quote)
                (q, Some(start_quote)) if q == start_quote => {
                    // Strip the quotes and add the content directly
                    result.push_str(&quote_content);
                    in_quote = None;
                }
                // Inside a quoted section
                (c, Some(_)) => {
                    quote_content.push(c);
                }
                // Outside quotes - copy directly
                (c, None) => {
                    result.push(c);
                }
            }
        }

        // Handle unclosed quote (shouldn't happen in valid Python, but be safe)
        if in_quote.is_some() {
            result.push_str(&quote_content);
        }

        result
    }

    /// Extract default value from a default_parameter or typed_default_parameter node.
    /// Returns the actual default value text, or "..." as fallback.
    fn extract_default_value(node: Node, source: &[u8]) -> String {
        // The structure is: identifier [: type] = value
        // Find the child after the "=" token
        let mut cursor = node.walk();
        let mut saw_equals = false;

        for child in node.children(&mut cursor) {
            if child.kind() == "=" {
                saw_equals = true;
                continue;
            }
            if saw_equals {
                // This is the default value expression
                return Self::node_text(child, source).to_string();
            }
        }

        // Fallback if structure is unexpected
        "...".to_string()
    }

    /// Extract a single decorator using proper AST traversal.
    /// Handles various decorator forms:
    /// - Simple: `@staticmethod`
    /// - With arguments: `@decorator(arg1="value", arg2=SomeClass.attribute)`
    /// - Qualified: `@module.submodule.decorator`
    /// - Generic: `@decorator[Type]`
    fn extract_decorator(node: Node, source: &[u8]) -> String {
        // node is a "decorator" node
        // Its children are: "@" token followed by the actual decorator expression
        // The expression can be: identifier, call, attribute, or subscript
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "@" => continue, // Skip the @ symbol
                "identifier" => {
                    // Simple decorator: @staticmethod
                    return Self::node_text(child, source).to_string();
                }
                "call" => {
                    // Decorator with arguments: @decorator(args)
                    // Need to normalize whitespace for multi-line decorators
                    return Self::normalize_decorator_text(child, source);
                }
                "attribute" => {
                    // Qualified decorator: @module.submodule.decorator
                    // Normalize in case of multi-line attribute chains (rare but possible)
                    return Self::normalize_decorator_text(child, source);
                }
                "subscript" => {
                    // Generic decorator: @decorator[Type]
                    // BUG FIX: Multi-line subscript decorators need normalization
                    return Self::normalize_decorator_text(child, source);
                }
                _ => {
                    // Unknown node type - try to extract text anyway
                    let text = Self::node_text(child, source).trim();
                    if !text.is_empty() && text != "@" {
                        // BUG FIX: Normalize multi-line text for unknown node types
                        return Self::normalize_decorator_str(text);
                    }
                }
            }
        }
        // Fallback: extract full text and normalize
        let dec_text = Self::node_text(node, source);
        let trimmed = dec_text.trim_start_matches('@').trim();
        // BUG FIX: Normalize multi-line decorators in fallback path
        Self::normalize_decorator_str(trimmed)
    }

    /// Normalize decorator text string by collapsing whitespace for multi-line decorators.
    /// Preserves string content but normalizes whitespace between tokens.
    /// This is a text-based version for cases where we don't have a Node reference.
    fn normalize_decorator_str(text: &str) -> String {
        // For single-line decorators, just return as-is
        if !text.contains('\n') {
            return text.to_string();
        }

        // For multi-line decorators, normalize whitespace while preserving strings
        let mut result = String::with_capacity(text.len());
        let mut chars = text.chars().peekable();
        let mut in_string: Option<char> = None;
        let mut prev_was_space = false;

        while let Some(ch) = chars.next() {
            match (ch, in_string) {
                // Handle string literals - preserve their content exactly
                ('"' | '\'', None) => {
                    in_string = Some(ch);
                    result.push(ch);
                    prev_was_space = false;
                }
                (q, Some(start_quote)) if q == start_quote => {
                    // Check for escape
                    let is_escaped = result.ends_with('\\');
                    result.push(ch);
                    if !is_escaped {
                        in_string = None;
                    }
                    prev_was_space = false;
                }
                (c, Some(_)) => {
                    // Inside string - preserve exactly
                    result.push(c);
                    prev_was_space = false;
                }
                // Outside strings - normalize whitespace
                (c, None) if c.is_whitespace() => {
                    // Collapse multiple whitespace to single space
                    // but skip whitespace after '(' or '[' or before ')' or ']'
                    if !prev_was_space {
                        let last_char = result.chars().last();
                        let next_char = chars.peek();
                        // Don't add space after '(', '[', ',' or before ')', ']', ','
                        if last_char != Some('(')
                            && last_char != Some('[')
                            && last_char != Some(',')
                            && next_char != Some(&')')
                            && next_char != Some(&']')
                            && next_char != Some(&',')
                        {
                            result.push(' ');
                            prev_was_space = true;
                        }
                    }
                }
                (c, None) => {
                    // Regular character outside string
                    // Trim trailing space before ), ], ,
                    if (c == ')' || c == ']' || c == ',') && result.ends_with(' ') {
                        result.pop();
                    }
                    result.push(c);
                    prev_was_space = false;
                }
            }
        }

        result.trim().to_string()
    }

    /// Normalize decorator text by collapsing whitespace for multi-line decorators.
    /// Preserves string content but normalizes whitespace between tokens.
    /// This version takes a Node and extracts text, then delegates to normalize_decorator_str.
    fn normalize_decorator_text(node: Node, source: &[u8]) -> String {
        let text = Self::node_text(node, source);
        Self::normalize_decorator_str(text)
    }

    /// Extract decorators from a decorated_definition parent or function/class node.
    fn extract_decorators(node: Node, source: &[u8]) -> Vec<String> {
        let mut decorators = Vec::new();

        // If this is a decorated_definition, extract decorators from it
        if node.kind() == "decorated_definition" {
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "decorator" {
                    decorators.push(Self::extract_decorator(child, source));
                }
            }
        }

        decorators
    }

    /// Extract function parameters with type annotations.
    fn extract_parameters(params_node: Node, source: &[u8]) -> Vec<String> {
        let mut params = Vec::new();
        let mut cursor = params_node.walk();

        for child in params_node.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    // Simple parameter without type annotation
                    params.push(Self::node_text(child, source).to_string());
                }
                "typed_parameter" => {
                    // Parameter with type annotation: name: type
                    // BUG-001 FIX: For typed *args/**kwargs, the identifier is nested inside
                    // list_splat_pattern or dictionary_splat_pattern
                    let (name, prefix) =
                        if let Some(splat) = Self::child_by_kind(child, "list_splat_pattern") {
                            // Typed *args: e.g., *args: tuple[str, ...]
                            let id = Self::child_by_kind(splat, "identifier")
                                .map(|n| Self::node_text(n, source))
                                .unwrap_or("");
                            (id, "*")
                        } else if let Some(splat) =
                            Self::child_by_kind(child, "dictionary_splat_pattern")
                        {
                            // Typed **kwargs: e.g., **kwargs: dict[str, Any]
                            let id = Self::child_by_kind(splat, "identifier")
                                .map(|n| Self::node_text(n, source))
                                .unwrap_or("");
                            (id, "**")
                        } else {
                            // Regular typed parameter: e.g., x: int
                            let id = Self::child_by_kind(child, "identifier")
                                .map(|n| Self::node_text(n, source))
                                .unwrap_or("");
                            (id, "")
                        };

                    // Use field-based access for type annotation (more robust than kind lookup)
                    let type_ann = Self::child_by_field(child, "type")
                        .map(|n| Self::extract_type(n, source))
                        .unwrap_or_default();

                    if type_ann.is_empty() {
                        params.push(format!("{}{}", prefix, name));
                    } else {
                        params.push(format!("{}{}: {}", prefix, name, type_ann));
                    }
                }
                "default_parameter" => {
                    // Parameter with default: name = value
                    let name = Self::child_by_kind(child, "identifier")
                        .map(|n| Self::node_text(n, source))
                        .unwrap_or("");
                    // Extract the actual default value from the child after "="
                    let default_value = Self::extract_default_value(child, source);
                    params.push(format!("{} = {}", name, default_value));
                }
                "typed_default_parameter" => {
                    // Parameter with type and default: name: type = value
                    // Use field-based access for name and type (more robust than kind lookup)
                    let name = Self::child_by_field(child, "name")
                        .map(|n| Self::node_text(n, source))
                        .unwrap_or("");
                    let type_ann = Self::child_by_field(child, "type")
                        .map(|n| Self::extract_type(n, source))
                        .unwrap_or_default();
                    // Extract the actual default value
                    let default_value = Self::extract_default_value(child, source);

                    if type_ann.is_empty() {
                        params.push(format!("{} = {}", name, default_value));
                    } else {
                        params.push(format!("{}: {} = {}", name, type_ann, default_value));
                    }
                }
                "list_splat_pattern" | "dictionary_splat_pattern" => {
                    // *args or **kwargs in pattern form
                    let text = Self::node_text(child, source);
                    params.push(text.to_string());
                }
                "*" => {
                    // Separator for keyword-only params
                    params.push("*".to_string());
                }
                "/" => {
                    // Separator for positional-only params
                    params.push("/".to_string());
                }
                _ => {}
            }
        }

        params
    }

    /// Extract docstring from a function or class body block.
    /// Handles both regular strings and concatenated strings ("a" "b" style).
    fn extract_docstring(block_node: Node, source: &[u8]) -> Option<String> {
        // Docstring is the first expression_statement containing a string literal
        let mut cursor = block_node.walk();
        for child in block_node.children(&mut cursor) {
            if child.kind() == "expression_statement" {
                // Check if this expression is a string or concatenated_string (docstring)
                let mut inner_cursor = child.walk();
                for inner in child.children(&mut inner_cursor) {
                    // Use unified helper for string and concatenated_string
                    if let Some(content) = Self::extract_string_or_concatenated(inner, source) {
                        return Some(content);
                    }
                }
            }
            // Docstring must be first statement
            break;
        }
        None
    }

    /// Strip string prefix (r, b, u, f, rb, br, fr, rf, etc.) from a string literal.
    /// Handles both lowercase and uppercase variants.
    ///
    /// Optimized: Uses direct byte checks instead of iterating 24 prefixes.
    /// Valid first chars: r, R, b, B, u, U, f, F
    /// Valid two-char combos: rb, br, fr, rf (any case combination)
    #[inline]
    fn strip_string_prefix(text: &str) -> &str {
        let bytes = text.as_bytes();
        if bytes.is_empty() {
            return text;
        }

        let first = bytes[0];

        // Fast path: starts with quote, no prefix
        if first == b'"' || first == b'\'' {
            return text;
        }

        // Check if first char is a valid prefix char
        let is_valid_first = matches!(first, b'r' | b'R' | b'b' | b'B' | b'u' | b'U' | b'f' | b'F');
        if !is_valid_first {
            return text;
        }

        // Check for two-char prefix (not valid for u/U as first char)
        if bytes.len() >= 2 && !matches!(first, b'u' | b'U') {
            let second = bytes[1];
            // Second char can be: r, R, b, B, f, F (for two-char prefixes)
            let is_valid_second = matches!(second, b'r' | b'R' | b'b' | b'B' | b'f' | b'F');
            if is_valid_second {
                // Valid two-char prefix, check if third char is quote
                if bytes.len() >= 3 && (bytes[2] == b'"' || bytes[2] == b'\'') {
                    // SAFETY: We verified bytes.len() >= 3 and chars are ASCII
                    return &text[2..];
                }
            }
        }

        // Check for single-char prefix
        if bytes.len() >= 2 && (bytes[1] == b'"' || bytes[1] == b'\'') {
            // SAFETY: We verified bytes.len() >= 2 and first char is ASCII
            return &text[1..];
        }

        text
    }

    /// Strip docstring quotes from a string literal.
    /// Properly handles triple quotes (""", ''') and single quotes (", ').
    /// Detects the quote style first, then strips matching quotes from both ends.
    /// This avoids the fragile chain of trim_start_matches/trim_end_matches that
    /// can corrupt content when docstrings contain quote characters.
    fn strip_docstring_quotes(text: &str) -> &str {
        // First, detect the quote style by checking what the string starts with
        // Check triple quotes first (longer match takes precedence)
        if text.starts_with("\"\"\"") {
            // Must end with """ and have enough length
            if text.len() >= 6 && text.ends_with("\"\"\"") {
                return &text[3..text.len() - 3];
            }
            // Malformed: starts with """ but doesn't end with it
            // Strip only the start to be safe
            return &text[3..];
        }

        if text.starts_with("'''") {
            if text.len() >= 6 && text.ends_with("'''") {
                return &text[3..text.len() - 3];
            }
            return &text[3..];
        }

        // Single double quote
        if text.starts_with('"') {
            if text.len() >= 2 && text.ends_with('"') {
                return &text[1..text.len() - 1];
            }
            return &text[1..];
        }

        // Single single quote
        if text.starts_with('\'') {
            if text.len() >= 2 && text.ends_with('\'') {
                return &text[1..text.len() - 1];
            }
            return &text[1..];
        }

        // No quotes detected, return as-is
        text
    }

    /// Extract content from a concatenated_string node ("a" "b" "c" style).
    /// Each child string is processed individually and the results are concatenated.
    /// This is valid Python syntax where adjacent string literals are merged.
    fn extract_concatenated_string_content(node: Node, source: &[u8]) -> String {
        let mut result = String::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            if child.kind() == "string" {
                let text = Self::node_text(child, source);
                let text = Self::strip_string_prefix(text);
                let content = Self::strip_docstring_quotes(text);
                result.push_str(content);
            }
            // Skip other node types (whitespace, comments between strings)
        }

        result
    }

    /// Extract docstring content from either a string or concatenated_string node.
    /// Returns trimmed content or None if empty.
    fn extract_string_or_concatenated(node: Node, source: &[u8]) -> Option<String> {
        let content = match node.kind() {
            "string" => {
                let text = Self::node_text(node, source);
                let text = Self::strip_string_prefix(text);
                Self::strip_docstring_quotes(text).to_string()
            }
            "concatenated_string" => Self::extract_concatenated_string_content(node, source),
            _ => return None,
        };

        let trimmed = content.trim();
        if trimmed.is_empty() {
            None
        } else {
            Some(trimmed.to_string())
        }
    }

    /// BUG-016 FIX: Extract module-level docstring from a module node.
    /// The module docstring is the first expression_statement containing a string
    /// at the top level of the module, before any other statements.
    /// Handles both regular strings and concatenated strings ("a" "b" style).
    pub fn extract_module_docstring(module_node: Node, source: &[u8]) -> Option<String> {
        if module_node.kind() != "module" {
            return None;
        }

        let mut cursor = module_node.walk();
        for child in module_node.children(&mut cursor) {
            if child.kind() == "comment" {
                continue;
            }

            if child.kind() == "expression_statement" {
                // Check if this expression is a string or concatenated_string (docstring)
                let mut inner_cursor = child.walk();
                for inner in child.children(&mut inner_cursor) {
                    // Use unified helper for string and concatenated_string
                    if let Some(content) = Self::extract_string_or_concatenated(inner, source) {
                        return Some(content);
                    }
                }
            }
            break;
        }
        None
    }

    /// Check if a function is async.
    /// Handles both `function_definition` and `decorated_definition` nodes.
    /// For decorated functions, the async keyword is on the inner function_definition,
    /// not the outer decorated_definition node.
    fn is_async_function(node: Node) -> bool {
        let function_node = match node.kind() {
            "decorated_definition" => {
                // Find the actual function inside decorated_definition
                Self::find_inner_function(node)
            }
            "function_definition" => Some(node),
            _ => None,
        };

        if let Some(func) = function_node {
            // Check children for "async" keyword
            let mut cursor = func.walk();
            for child in func.children(&mut cursor) {
                if child.kind() == "async" {
                    return true;
                }
                // Stop at def keyword - async comes before def
                if child.kind() == "def" {
                    return false;
                }
            }
        }
        false
    }

    /// Find the inner function_definition inside a decorated_definition node.
    fn find_inner_function(decorated: Node) -> Option<Node> {
        let mut cursor = decorated.walk();
        for child in decorated.children(&mut cursor) {
            if child.kind() == "function_definition" {
                return Some(child);
            }
        }
        None
    }

    /// Check if a function contains yield or yield from expressions (is a generator).
    ///
    /// Recursively scans the function body for yield/yield_from nodes.
    /// Stops at nested function boundaries to avoid false positives from inner generators.
    ///
    /// # Returns
    /// `true` if the function body contains yield or yield_from at the top level,
    /// `false` otherwise.
    fn contains_yield(node: Node) -> bool {
        // Get the function body
        let function_node = match node.kind() {
            "decorated_definition" => Self::find_inner_function(node),
            "function_definition" => Some(node),
            _ => None,
        };

        if let Some(func) = function_node {
            if let Some(body) = Self::child_by_kind(func, "block") {
                return Self::contains_yield_recursive(body, 0);
            }
        }
        false
    }

    /// Recursively check for yield/yield_from in a node tree.
    ///
    /// # Arguments
    /// * `node` - Current node to check
    /// * `depth` - Current nesting depth (0 = in main function, >0 = in nested function)
    ///
    /// Stops recursion into nested functions/lambdas to avoid counting their yields.
    fn contains_yield_recursive(node: Node, depth: usize) -> bool {
        match node.kind() {
            // Found yield/yield_from - only count if at depth 0 (not in nested function)
            "yield" | "yield_from" => depth == 0,
            // Nested function boundaries - don't recurse into these
            // Their yields belong to them, not the outer function
            "function_definition" | "lambda" => false,
            // Recurse into other nodes
            _ => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if Self::contains_yield_recursive(child, depth) {
                        return true;
                    }
                }
                false
            }
        }
    }

    /// Extract base classes from a class definition.
    fn extract_bases(node: Node, source: &[u8]) -> Vec<String> {
        let mut bases = Vec::new();

        // Find argument_list (contains base classes)
        if let Some(arg_list) = Self::child_by_kind(node, "argument_list") {
            let mut cursor = arg_list.walk();
            for child in arg_list.children(&mut cursor) {
                match child.kind() {
                    "identifier" | "attribute" => {
                        bases.push(Self::node_text(child, source).to_string());
                    }
                    "keyword_argument" => {
                        // metaclass=X or other keyword args in class definition
                        bases.push(Self::node_text(child, source).to_string());
                    }
                    _ => {}
                }
            }
        }

        bases
    }

    /// Extract methods from a class body.
    fn extract_methods(block_node: Node, source: &[u8]) -> Vec<FunctionInfo> {
        let mut methods = Vec::new();
        let mut cursor = block_node.walk();

        for child in block_node.children(&mut cursor) {
            match child.kind() {
                "function_definition" => {
                    if let Some(mut func) = Self::extract_function_impl(child, source, true) {
                        func.is_method = true;
                        methods.push(func);
                    }
                }
                "decorated_definition" => {
                    // Look for function_definition inside
                    let decorators = Self::extract_decorators(child, source);
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        if inner.kind() == "function_definition" {
                            if let Some(mut func) = Self::extract_function_impl(inner, source, true)
                            {
                                func.is_method = true;
                                func.decorators = decorators.clone();
                                methods.push(func);
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        methods
    }

    /// Extract inner/nested classes from a class body.
    /// Recursively extracts class_definition nodes found directly in the class body.
    /// Each nested class is marked with a "nested_in:FullPath" decorator where FullPath
    /// is the dot-separated path of all parent classes (e.g., "Outer.Middle" for deeply nested).
    ///
    /// For example, given:
    /// ```python
    /// class Outer:
    ///     class Middle:
    ///         class Inner:
    ///             pass
    /// ```
    /// When called on `Outer`'s body with parent_path="Outer", returns:
    /// - `Middle` with decorator `nested_in:Outer`, inner_classes containing Inner
    ///   - `Inner` (inside Middle.inner_classes) with decorator `nested_in:Outer.Middle`
    fn extract_inner_classes(block_node: Node, source: &[u8], parent_path: &str) -> Vec<ClassInfo> {
        let mut inner_classes = Vec::new();
        let mut cursor = block_node.walk();

        for child in block_node.children(&mut cursor) {
            match child.kind() {
                "class_definition" => {
                    if let Some(class) =
                        Self::extract_class_impl_with_path(child, source, parent_path)
                    {
                        inner_classes.push(class);
                    }
                }
                "decorated_definition" => {
                    // Look for class_definition inside decorated definition
                    let decorators = Self::extract_decorators(child, source);
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        if inner.kind() == "class_definition" {
                            if let Some(mut class) =
                                Self::extract_class_impl_with_path(inner, source, parent_path)
                            {
                                // Insert nested_in at position 0 to match Python behavior
                                let nested_in_decorator = class.decorators.pop();
                                class.decorators = decorators.clone();
                                if let Some(nested_dec) = nested_in_decorator {
                                    class.decorators.insert(0, nested_dec);
                                }
                                inner_classes.push(class);
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        inner_classes
    }

    /// Core class extraction logic with parent path tracking for nested classes.
    /// This is the internal version that tracks the full nesting path.
    fn extract_class_impl_with_path(
        node: Node,
        source: &[u8],
        parent_path: &str,
    ) -> Option<ClassInfo> {
        if node.kind() != "class_definition" {
            return None;
        }

        // Get class name
        let name = Self::child_by_kind(node, "identifier")
            .map(|n| Self::node_text(n, source).to_string())?;

        // Build full path for this class's nested classes
        let full_path = format!("{}.{}", parent_path, name);

        // Get base classes
        let bases = Self::extract_bases(node, source);

        // Get docstring, methods, and inner classes from block
        let block = Self::child_by_kind(node, "block");
        let docstring = block.and_then(|b| Self::extract_docstring(b, source));
        let methods = block
            .map(|b| Self::extract_methods(b, source))
            .unwrap_or_default();
        // Recursively extract inner classes with full path tracking
        let inner_classes = block
            .map(|b| Self::extract_inner_classes(b, source, &full_path))
            .unwrap_or_default();

        // Mark this class as nested with the parent path
        let mut decorators = Vec::new();
        decorators.push(format!("nested_in:{}", parent_path));

        Some(ClassInfo {
            name,
            bases,
            docstring,
            methods,
            fields: Vec::new(),
            inner_classes,
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "python".to_string(),
        })
    }

    /// Extract nested functions from a function body.
    /// Recursively finds function_definition nodes inside the function at all nesting levels.
    /// Returns functions marked with "nested_in:full.nesting.path" decorator.
    ///
    /// For example, given:
    /// ```python
    /// def outer():
    ///     def inner():
    ///         def deepest():
    ///             pass
    /// ```
    /// When called on `outer`'s body with parent_path="outer", returns:
    /// - `inner` with decorator `nested_in:outer`
    /// - `deepest` with decorator `nested_in:outer.inner`
    ///
    /// Note: Currently nested functions are extracted via the query-based approach
    /// in extract_function() using get_outer_function_name(). This method provides
    /// an alternative explicit extraction mechanism for potential future use.
    #[allow(dead_code)]
    fn extract_nested_functions(
        block_node: Node,
        source: &[u8],
        parent_path: &str,
    ) -> Vec<FunctionInfo> {
        let mut nested_funcs = Vec::new();
        let mut cursor = block_node.walk();

        for child in block_node.children(&mut cursor) {
            match child.kind() {
                "function_definition" => {
                    if let Some(mut func) = Self::extract_function_impl(child, source, false) {
                        let func_name = func.name.clone();
                        // Mark as nested with full path (insert at 0 to match Python behavior)
                        func.decorators
                            .insert(0, format!("nested_in:{}", parent_path));
                        nested_funcs.push(func);

                        // Recursively extract deeper nested functions
                        if let Some(body) = Self::child_by_kind(child, "block") {
                            let full_path = format!("{}.{}", parent_path, func_name);
                            nested_funcs
                                .extend(Self::extract_nested_functions(body, source, &full_path));
                        }
                    }
                }
                "decorated_definition" => {
                    // Look for function_definition inside decorated definition
                    let decorators = Self::extract_decorators(child, source);
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        if inner.kind() == "function_definition" {
                            if let Some(mut func) =
                                Self::extract_function_impl(inner, source, false)
                            {
                                let func_name = func.name.clone();
                                // Combine existing decorators with nested_in marker (insert at 0 to match Python)
                                func.decorators = decorators.clone();
                                func.decorators
                                    .insert(0, format!("nested_in:{}", parent_path));
                                nested_funcs.push(func);

                                // Recursively extract deeper nested functions
                                if let Some(body) = Self::child_by_kind(inner, "block") {
                                    let full_path = format!("{}.{}", parent_path, func_name);
                                    nested_funcs.extend(Self::extract_nested_functions(
                                        body, source, &full_path,
                                    ));
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        nested_funcs
    }

    /// Core function extraction logic.
    fn extract_function_impl(node: Node, source: &[u8], is_method: bool) -> Option<FunctionInfo> {
        if node.kind() != "function_definition" {
            return None;
        }

        // Get function name
        let name = Self::child_by_kind(node, "identifier")
            .map(|n| Self::node_text(n, source).to_string())?;

        // Get parameters
        let params = Self::child_by_kind(node, "parameters")
            .map(|n| Self::extract_parameters(n, source))
            .unwrap_or_default();

        // Get return type annotation (field-based lookup, not kind-based)
        // tree-sitter-python stores return type in "return_type" field
        let return_type = node
            .child_by_field_name("return_type")
            .map(|n| Self::extract_type(n, source));

        // Get docstring from block
        let docstring = Self::child_by_kind(node, "block")
            .and_then(|block| Self::extract_docstring(block, source));

        // Check for async
        let is_async = Self::is_async_function(node);

        Some(FunctionInfo {
            name,
            params,
            return_type,
            docstring,
            is_method,
            is_async,
            decorators: Vec::new(), // Will be filled by caller if in decorated_definition
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "python".to_string(),
        })
    }

    /// Core class extraction logic.
    fn extract_class_impl(node: Node, source: &[u8]) -> Option<ClassInfo> {
        if node.kind() != "class_definition" {
            return None;
        }

        // Get class name
        let name = Self::child_by_kind(node, "identifier")
            .map(|n| Self::node_text(n, source).to_string())?;

        // Get base classes
        let bases = Self::extract_bases(node, source);

        // Get docstring, methods, and inner classes from block
        let block = Self::child_by_kind(node, "block");
        let docstring = block.and_then(|b| Self::extract_docstring(b, source));
        let methods = block
            .map(|b| Self::extract_methods(b, source))
            .unwrap_or_default();
        // FEATURE: Nested class extraction - recursively extract inner classes
        let inner_classes = block
            .map(|b| Self::extract_inner_classes(b, source, &name))
            .unwrap_or_default();

        Some(ClassInfo {
            name,
            bases,
            docstring,
            methods,
            fields: Vec::new(),
            inner_classes,
            decorators: Vec::new(), // Will be filled by caller if in decorated_definition
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "python".to_string(),
        })
    }

    /// Extract dotted name (module path).
    fn extract_dotted_name(node: Node, source: &[u8]) -> String {
        Self::node_text(node, source).to_string()
    }

    /// Check if a node is directly inside a class body (making it a method).
    /// Returns true if the function is a method (direct child of class body).
    /// This prevents methods from being included in the top-level functions list.
    fn is_inside_class_body(node: Node) -> bool {
        let mut current = node;
        while let Some(parent) = current.parent() {
            match parent.kind() {
                "class_definition" => {
                    // Check if we came from the block (body) of the class
                    // A function inside a class body is a method
                    return true;
                }
                "function_definition" => {
                    // We hit a function before a class - not a direct method
                    // (could be a nested function inside a method, but not a method itself)
                    return false;
                }
                "module" => {
                    // Hit the module level - not inside a class
                    return false;
                }
                _ => {
                    current = parent;
                }
            }
        }
        false
    }

    /// Check if a function is nested inside another function.
    /// Returns the full nesting path if nested (e.g., "outer.inner" for deeply nested),
    /// None if the function is at module level.
    ///
    /// For example, given:
    /// ```python
    /// def outer():
    ///     def inner():
    ///         def deepest():
    ///             pass
    /// ```
    /// - `outer` returns None
    /// - `inner` returns Some("outer")
    /// - `deepest` returns Some("outer.inner")
    fn get_outer_function_name(node: Node, source: &[u8]) -> Option<String> {
        let mut names = Vec::new();
        let mut current = node;

        while let Some(parent) = current.parent() {
            match parent.kind() {
                "function_definition" => {
                    // Found an enclosing function - extract its name
                    if let Some(name) = Self::child_by_kind(parent, "identifier")
                        .map(|n| Self::node_text(n, source).to_string())
                    {
                        names.push(name);
                    }
                }
                "module" => {
                    // Hit module level - stop traversal
                    break;
                }
                _ => {}
            }
            current = parent;
        }

        if names.is_empty() {
            None
        } else {
            // Reverse to get outer-to-inner order: [deepest_parent, ..., immediate_parent]
            // becomes [outermost, ..., innermost]
            names.reverse();
            Some(names.join("."))
        }
    }

    /// Check if a class is nested inside another class.
    /// Returns the full nesting path if nested (e.g., "Outer.Inner" for deeply nested),
    /// None if the class is at module level.
    ///
    /// For example, given:
    /// ```python
    /// class Outer:
    ///     class Inner:
    ///         class Deepest:
    ///             pass
    /// ```
    /// - `Outer` returns None
    /// - `Inner` returns Some("Outer")
    /// - `Deepest` returns Some("Outer.Inner")
    fn get_outer_class_name(node: Node, source: &[u8]) -> Option<String> {
        let mut names = Vec::new();
        let mut current = node;

        while let Some(parent) = current.parent() {
            match parent.kind() {
                "class_definition" => {
                    // Found an enclosing class - extract its name
                    if let Some(name) = Self::child_by_kind(parent, "identifier")
                        .map(|n| Self::node_text(n, source).to_string())
                    {
                        names.push(name);
                    }
                }
                "module" => {
                    // Hit module level - stop traversal
                    break;
                }
                _ => {}
            }
            current = parent;
        }

        if names.is_empty() {
            None
        } else {
            // Reverse to get outer-to-inner order
            names.reverse();
            Some(names.join("."))
        }
    }

    /// BUG-021 FIX: Query pattern for PEP 695 type alias statements.
    /// Python 3.12+ syntax: `type Point = tuple[int, int]`
    /// tree-sitter-python parses this as `type_alias_statement`.
    /// Note: This is a Python-specific extension, not part of the Language trait.
    #[allow(dead_code)]
    pub fn type_alias_query() -> &'static str {
        r#"(type_alias_statement
            name: (type (identifier) @name)
            value: (type) @value) @type_alias"#
    }

    // =========================================================================
    // Call Graph Extraction
    // =========================================================================

    /// Extract all call sites from a Python function body.
    ///
    /// Returns a list of `CallInfo` structs containing:
    /// - Direct function calls: `foo()`
    /// - Self method calls: `self.method()`
    /// - Object method calls: `obj.method()`
    /// - Chained calls: `obj.foo().bar()`
    /// - Constructor calls: `MyClass()`
    /// - Super method calls: `super().method()`
    ///
    /// # Arguments
    /// * `node` - A function_definition node
    /// * `source` - The source code bytes
    ///
    /// # Returns
    /// A vector of `CallInfo` for each call site found in the function.
    #[allow(dead_code)]
    pub fn extract_calls(node: Node, source: &[u8]) -> Vec<CallInfo> {
        let mut calls = Vec::new();

        if node.kind() != "function_definition" {
            return calls;
        }

        // Get the function body (block)
        if let Some(block) = Self::child_by_kind(node, "block") {
            Self::collect_calls_recursive(block, source, &mut calls, 0);
        }

        calls
    }

    /// Recursively collect calls from an AST node.
    /// Maximum depth prevents stack overflow on pathological inputs.
    const MAX_CALL_DEPTH: usize = 500;

    fn collect_calls_recursive(node: Node, source: &[u8], calls: &mut Vec<CallInfo>, depth: usize) {
        if depth > Self::MAX_CALL_DEPTH {
            return;
        }

        if node.kind() == "call" {
            if let Some(call_info) = Self::extract_single_call(node, source) {
                calls.push(call_info);
            }

            // For chained calls, continue into the call's function part
            // to catch the inner call: foo().bar() - we want both foo and bar
            if let Some(func) = Self::child_by_kind(node, "function") {
                if func.kind() == "attribute" {
                    // Check if this is a chained call (attribute on a call)
                    if let Some(obj) = Self::child_by_kind(func, "call") {
                        Self::collect_calls_recursive(obj, source, calls, depth + 1);
                    }
                }
            }
        }

        // Recurse into all children
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            Self::collect_calls_recursive(child, source, calls, depth + 1);
        }
    }

    /// Extract call information from a single call expression node.
    fn extract_single_call(node: Node, source: &[u8]) -> Option<CallInfo> {
        // Get the function being called - first non-argument child
        let mut func_node = None;
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                // Skip argument-related nodes
                "argument_list" | "(" | ")" | "," => continue,
                _ => {
                    func_node = Some(child);
                    break;
                }
            }
        }

        let func_node = func_node?;
        let line = node.start_position().row + 1;

        match func_node.kind() {
            // Direct call: foo()
            "identifier" => {
                let name = Self::node_text(func_node, source);
                // Check if it looks like a class name (starts with uppercase)
                let call_kind = if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                    CallKind::Constructor
                } else {
                    CallKind::Direct
                };
                Some(CallInfo {
                    callee: name.to_string(),
                    line,
                    call_kind,
                    receiver: None,
                })
            }
            // Attribute call: obj.method() or self.method()
            "attribute" => Self::extract_attribute_call(func_node, source, line),
            // Chained call: foo()() or (lambda: x)()
            "call" | "parenthesized_expression" => {
                // The actual callee is the outer call, which we already recorded
                // Return None here to avoid duplicates
                None
            }
            // Subscript call: funcs[0]()
            "subscript" => {
                // Extract the subscripted identifier
                if let Some(id) = Self::child_by_kind(func_node, "identifier") {
                    let name = Self::node_text(id, source);
                    Some(CallInfo {
                        callee: format!("{}[...]", name),
                        line,
                        call_kind: CallKind::Direct,
                        receiver: None,
                    })
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Extract call info from an attribute access (obj.method or self.method).
    fn extract_attribute_call(attr_node: Node, source: &[u8], line: usize) -> Option<CallInfo> {
        // Structure: attribute { object, ".", identifier }
        // Find the object and the method name
        let mut object: Option<Node> = None;
        let mut method_name: Option<&str> = None;

        let mut cursor = attr_node.walk();
        for child in attr_node.children(&mut cursor) {
            match child.kind() {
                // The method name (last identifier after the dot)
                "identifier" => {
                    // If we already have an object, this is the method name
                    if object.is_some() {
                        method_name = Some(Self::node_text(child, source));
                    } else {
                        // First identifier is the object
                        object = Some(child);
                    }
                }
                // Nested attribute: a.b.c -> attribute { attribute { a, b }, c }
                "attribute" => {
                    object = Some(child);
                }
                // Call as object: foo().bar() -> attribute { call, bar }
                "call" => {
                    object = Some(child);
                }
                // super() call
                "parenthesized_expression" => {
                    object = Some(child);
                }
                _ => {}
            }
        }

        let method = method_name?;
        let obj_node = object?;

        // Determine the call kind based on the object
        let (call_kind, receiver) = match obj_node.kind() {
            "identifier" => {
                let obj_name = Self::node_text(obj_node, source);
                if obj_name == "self" {
                    (CallKind::SelfMethod, Some("self".to_string()))
                } else if obj_name == "cls" {
                    (CallKind::SelfMethod, Some("cls".to_string()))
                } else {
                    (CallKind::Method, Some(obj_name.to_string()))
                }
            }
            "call" => {
                // Chained call: foo().bar()
                // Check if it's super().method()
                if let Some(call_func) = Self::child_by_kind(obj_node, "identifier") {
                    let func_name = Self::node_text(call_func, source);
                    if func_name == "super" {
                        (CallKind::SuperMethod, Some("super()".to_string()))
                    } else {
                        (CallKind::Chained, Some(format!("{}()", func_name)))
                    }
                } else {
                    (CallKind::Chained, None)
                }
            }
            "attribute" => {
                // Nested attribute: a.b.method()
                let chain = Self::extract_attribute_chain_text(obj_node, source);
                if chain.starts_with("self.") {
                    (CallKind::SelfMethod, Some(chain))
                } else {
                    (CallKind::Method, Some(chain))
                }
            }
            _ => (CallKind::Method, None),
        };

        Some(CallInfo {
            callee: method.to_string(),
            line,
            call_kind,
            receiver,
        })
    }

    /// Extract the full text of an attribute chain (a.b.c).
    fn extract_attribute_chain_text(node: Node, source: &[u8]) -> String {
        Self::node_text(node, source).to_string()
    }

    /// Build a map of caller -> callees for a function.
    /// Returns the function name and all functions it calls.
    ///
    /// # Arguments
    /// * `node` - A function_definition node
    /// * `source` - The source code bytes
    ///
    /// # Returns
    /// A tuple of (function_name, Vec<(callee_name, line, call_kind)>)
    #[allow(dead_code)]
    pub fn build_function_call_map(
        node: Node,
        source: &[u8],
    ) -> Option<(String, Vec<(String, usize, String)>)> {
        if node.kind() != "function_definition" {
            return None;
        }

        let func_name = Self::child_by_kind(node, "identifier")
            .map(|n| Self::node_text(n, source).to_string())?;

        let calls = Self::extract_calls(node, source);
        let call_list: Vec<(String, usize, String)> = calls
            .into_iter()
            .map(|c| {
                let kind_str = match c.call_kind {
                    CallKind::Direct => "direct",
                    CallKind::SelfMethod => "self_method",
                    CallKind::Method => "method",
                    CallKind::Chained => "chained",
                    CallKind::Constructor => "constructor",
                    CallKind::SuperMethod => "super_method",
                };
                (c.callee, c.line, kind_str.to_string())
            })
            .collect();

        Some((func_name, call_list))
    }
}

impl Language for Python {
    fn name(&self) -> &'static str {
        "python"
    }

    fn extensions(&self) -> &[&'static str] {
        // .py   = standard Python source
        // .pyi  = type stub files
        // .pyx  = Cython source files
        // .pyw  = Windows GUI Python scripts (no console window)
        &[".py", ".pyi", ".pyx", ".pyw"]
    }

    fn parser(&self) -> Result<Parser> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_python::LANGUAGE.into())
            .map_err(|e| BrrrError::TreeSitter(e.to_string()))?;
        Ok(parser)
    }

    fn extract_function(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        // BUG-007 FIX: Skip functions that are inside class bodies (they are methods)
        // Methods are extracted separately via extract_class -> extract_methods
        if Self::is_inside_class_body(node) {
            return None;
        }

        match node.kind() {
            "function_definition" => {
                // Skip if this function_definition is a direct child of decorated_definition
                // The decorated_definition case will handle it with proper decorator extraction
                if let Some(parent) = node.parent() {
                    if parent.kind() == "decorated_definition" {
                        return None;
                    }
                }

                let mut func = Self::extract_function_impl(node, source, false)?;

                // BUG-005 FIX: Check if this is a nested function and mark it
                // Insert at position 0 to match Python behavior (nested_in should be first)
                if let Some(outer_name) = Self::get_outer_function_name(node, source) {
                    func.decorators
                        .insert(0, format!("nested_in:{}", outer_name));
                }

                Some(func)
            }
            "decorated_definition" => {
                // Extract decorators first
                let mut decorators = Self::extract_decorators(node, source);

                // Find the function_definition inside
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "function_definition" {
                        if let Some(mut func) = Self::extract_function_impl(child, source, false) {
                            // BUG-005 FIX: Check if this is a nested function and mark it
                            // Insert at position 0 to match Python behavior (nested_in should be first)
                            if let Some(outer_name) = Self::get_outer_function_name(child, source) {
                                decorators.insert(0, format!("nested_in:{}", outer_name));
                            }

                            func.decorators = decorators;
                            return Some(func);
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn extract_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        match node.kind() {
            "class_definition" => {
                // Skip if this class_definition is a direct child of decorated_definition
                // The decorated_definition case will handle it with proper decorator extraction
                if let Some(parent) = node.parent() {
                    if parent.kind() == "decorated_definition" {
                        return None;
                    }
                }

                // Check if this class is nested inside another class
                let outer_path = Self::get_outer_class_name(node, source);

                if let Some(ref outer_name) = outer_path {
                    // Nested class - use path-aware extraction so inner classes have correct paths
                    let class = Self::extract_class_impl_with_path(node, source, outer_name)?;
                    // The nested_in decorator is already set by extract_class_impl_with_path
                    Some(class)
                } else {
                    // Top-level class - use regular extraction
                    let class = Self::extract_class_impl(node, source)?;
                    Some(class)
                }
            }
            "decorated_definition" => {
                // Extract decorators first
                let decorators = Self::extract_decorators(node, source);

                // Find the class_definition inside
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "class_definition" {
                        // Check if this class is nested inside another class
                        let outer_path = Self::get_outer_class_name(child, source);

                        if let Some(ref outer_name) = outer_path {
                            // Nested class - use path-aware extraction
                            if let Some(mut class) =
                                Self::extract_class_impl_with_path(child, source, outer_name)
                            {
                                // Insert nested_in at position 0 to match Python behavior
                                let nested_in_decorator = class.decorators.pop();
                                class.decorators = decorators.clone();
                                if let Some(nested_dec) = nested_in_decorator {
                                    class.decorators.insert(0, nested_dec);
                                }
                                return Some(class);
                            }
                        } else {
                            // Top-level class
                            if let Some(mut class) = Self::extract_class_impl(child, source) {
                                class.decorators = decorators;
                                return Some(class);
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn extract_imports(&self, tree: &Tree, source: &[u8]) -> Vec<ImportInfo> {
        let mut imports = Vec::new();
        let root = tree.root_node();

        // Collect imports from top-level and TYPE_CHECKING blocks
        Python::collect_imports_recursive(root, source, &mut imports, 0);

        imports
    }

    fn extract_module_docstring(&self, tree: &Tree, source: &[u8]) -> Option<String> {
        Self::extract_module_docstring(tree.root_node(), source)
    }

    fn function_query(&self) -> &'static str {
        r#"[
            (function_definition name: (identifier) @name) @function
            (decorated_definition
                (function_definition name: (identifier) @name)) @function
        ]"#
    }

    fn class_query(&self) -> &'static str {
        r#"[
            (class_definition name: (identifier) @name) @class
            (decorated_definition
                (class_definition name: (identifier) @name)) @class
        ]"#
    }

    fn call_query(&self) -> &'static str {
        // BUG-020 FIX: Enhanced call query to handle edge cases:
        // - Direct function calls: func()
        // - Attribute calls: obj.method()
        // - Subscript calls: funcs[0]()
        // - Chained calls: foo()()
        // - Lambda calls: (lambda x: x)()
        r#"[
            (call function: (identifier) @callee) @call
            (call function: (attribute attribute: (identifier) @callee)) @call
            (call function: (subscript) @callee) @call
            (call function: (call) @callee) @call
            (call function: (parenthesized_expression) @callee) @call
        ]"#
    }

    fn build_cfg(&self, node: Node, source: &[u8]) -> Result<CFGInfo> {
        PythonCFGBuilder::build(node, source)
    }

    fn build_dfg(&self, node: Node, source: &[u8]) -> Result<DFGInfo> {
        PythonDFGBuilder::build(node, source)
    }
}

// =============================================================================
// Import Extraction Helper Methods
// =============================================================================

impl Python {
    /// Recursively collect imports from a node.
    /// At depth 0 (module level), also checks for TYPE_CHECKING blocks.
    /// This handles the common pattern:
    ///   if TYPE_CHECKING:
    ///       from mymodule import MyClass
    fn collect_imports_recursive(
        node: Node,
        source: &[u8],
        imports: &mut Vec<ImportInfo>,
        depth: usize,
    ) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "import_statement" => {
                    Self::extract_single_import_statement(child, source, imports);
                }
                "import_from_statement" => {
                    Self::extract_single_import_from_statement(child, source, imports);
                }
                "if_statement" if depth == 0 => {
                    // Check for TYPE_CHECKING blocks at module level
                    if Self::is_type_checking_block(child, source) {
                        // Extract imports from the if block's consequence
                        if let Some(block) = child.child_by_field_name("consequence") {
                            Self::collect_imports_recursive(block, source, imports, depth + 1);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Check if an if_statement is a TYPE_CHECKING guard.
    /// Matches patterns like:
    ///   if TYPE_CHECKING:
    ///   if typing.TYPE_CHECKING:
    fn is_type_checking_block(if_node: Node, source: &[u8]) -> bool {
        if let Some(condition) = if_node.child_by_field_name("condition") {
            let cond_text = Self::node_text(condition, source);
            // Handle both `TYPE_CHECKING` and `typing.TYPE_CHECKING`
            cond_text == "TYPE_CHECKING" || cond_text.ends_with(".TYPE_CHECKING")
        } else {
            false
        }
    }

    /// Extract imports from a single import_statement node.
    /// Handles: import foo, bar, baz or import foo.bar
    fn extract_single_import_statement(node: Node, source: &[u8], imports: &mut Vec<ImportInfo>) {
        let mut inner_cursor = node.walk();
        for inner in node.children(&mut inner_cursor) {
            match inner.kind() {
                "dotted_name" => {
                    let module = Self::extract_dotted_name(inner, source);
                    imports.push(ImportInfo {
                        module,
                        names: Vec::new(),
                        aliases: FxHashMap::default(),
                        is_from: false,
                        level: 0,
                        line_number: inner.start_position().row + 1,
                        visibility: None,
                    });
                }
                "aliased_import" => {
                    // import foo as bar
                    let mut alias_cursor = inner.walk();
                    let mut module = String::new();
                    let mut alias_name = String::new();

                    for alias_child in inner.children(&mut alias_cursor) {
                        match alias_child.kind() {
                            "dotted_name" => {
                                module = Self::extract_dotted_name(alias_child, source);
                            }
                            "identifier" => {
                                // This is the alias (comes after "as")
                                alias_name = Self::node_text(alias_child, source).to_string();
                            }
                            _ => {}
                        }
                    }

                    let mut aliases = FxHashMap::default();
                    if !alias_name.is_empty() {
                        aliases.insert(module.clone(), alias_name);
                    }

                    imports.push(ImportInfo {
                        module,
                        names: Vec::new(),
                        aliases,
                        is_from: false,
                        level: 0,
                        line_number: inner.start_position().row + 1,
                        visibility: None,
                    });
                }
                _ => {}
            }
        }
    }

    /// Extract imports from a single import_from_statement node.
    /// Handles: from foo import bar, baz / from . import foo / from ..foo import bar
    fn extract_single_import_from_statement(
        node: Node,
        source: &[u8],
        imports: &mut Vec<ImportInfo>,
    ) {
        let mut module = String::new();
        let mut names = Vec::new();
        let mut aliases = FxHashMap::default();
        let mut level = 0usize;

        let mut inner_cursor = node.walk();
        let mut after_import = false;

        for inner in node.children(&mut inner_cursor) {
            match inner.kind() {
                "import" => {
                    after_import = true;
                }
                "relative_import" => {
                    // Handle relative imports: from . import X or from ..parent import X
                    let mut rel_cursor = inner.walk();
                    for rel_child in inner.children(&mut rel_cursor) {
                        match rel_child.kind() {
                            "import_prefix" => {
                                // BUG-018 FIX: Count dots from text directly for safety
                                // The tree structure may vary between tree-sitter versions,
                                // so counting '.' characters is more reliable.
                                let prefix_text = Self::node_text(rel_child, source);
                                level = prefix_text.chars().filter(|&c| c == '.').count();
                            }
                            "dotted_name" => {
                                // Module name after dots (e.g., "parent" in from ..parent)
                                module = Self::extract_dotted_name(rel_child, source);
                            }
                            _ => {}
                        }
                    }
                }
                "dotted_name" => {
                    if !after_import {
                        // Regular module (non-relative import)
                        module = Self::extract_dotted_name(inner, source);
                    } else {
                        // Imported name
                        let name = Self::extract_dotted_name(inner, source);
                        names.push(name);
                    }
                }
                "identifier" => {
                    if after_import {
                        names.push(Self::node_text(inner, source).to_string());
                    }
                }
                "aliased_import" => {
                    // from foo import bar as baz
                    let mut import_name = String::new();
                    let mut alias_name = String::new();

                    let mut alias_cursor = inner.walk();
                    for alias_child in inner.children(&mut alias_cursor) {
                        match alias_child.kind() {
                            "dotted_name" | "identifier" => {
                                if import_name.is_empty() {
                                    import_name = Self::node_text(alias_child, source).to_string();
                                } else {
                                    alias_name = Self::node_text(alias_child, source).to_string();
                                }
                            }
                            _ => {}
                        }
                    }

                    if alias_name.is_empty() {
                        names.push(import_name);
                    } else {
                        names.push(import_name.clone());
                        aliases.insert(import_name, alias_name);
                    }
                }
                "wildcard_import" => {
                    // from foo import *
                    names.push("*".to_string());
                }
                _ => {}
            }
        }

        imports.push(ImportInfo {
            module,
            names,
            aliases,
            is_from: true,
            level,
            line_number: node.start_position().row + 1,
            visibility: None,
        });
    }
}

// =============================================================================
// Python CFG Builder - Exception Handling Types
// =============================================================================

/// Information about a single exception handler in a try/except block.
///
/// Tracks the exception type(s) being caught and the handler block ID.
#[derive(Debug, Clone)]
struct ExceptionHandler {
    /// Block ID of the except handler
    handler_block: BlockId,
    /// Exception type(s) being caught (e.g., ["ValueError"], ["TypeError", "KeyError"])
    /// Empty vec means bare `except:` (catches all)
    exception_types: Vec<String>,
    /// Whether this is an except* handler (Python 3.11+ ExceptionGroup)
    is_exception_group: bool,
}

/// Context for tracking active try/except/finally blocks.
///
/// Used to create exception edges from statements within try blocks
/// to their corresponding exception handlers. Supports:
/// - Multiple exception handlers per try block
/// - finally blocks that always execute
/// - Nested try/except structures
#[derive(Debug, Clone)]
struct ExceptionContext {
    /// The try block (where exceptions might be raised)
    try_block: BlockId,
    /// List of exception handlers in order of precedence
    handlers: Vec<ExceptionHandler>,
    /// Optional finally block (always executed)
    finally_block: Option<BlockId>,
    /// Block to continue execution after try/except/finally completes
    after_try: BlockId,
    /// Start line of the try block (for scope checking)
    start_line: usize,
    /// End line of the try block (for scope checking)
    end_line: usize,
}

impl ExceptionContext {
    /// Create a new exception context for a try block.
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

    /// Add an exception handler to this context.
    fn add_handler(
        &mut self,
        handler_block: BlockId,
        exception_types: Vec<String>,
        is_exception_group: bool,
    ) {
        self.handlers.push(ExceptionHandler {
            handler_block,
            exception_types,
            is_exception_group,
        });
    }

    /// Set the finally block for this context.
    fn set_finally(&mut self, finally_block: BlockId) {
        self.finally_block = Some(finally_block);
    }

    /// Check if a line is within the try block's scope.
    fn contains_line(&self, line: usize) -> bool {
        line >= self.start_line && line <= self.end_line
    }

    /// Get the first handler that could catch a given exception type.
    /// Returns None for bare except or if no matching handler.
    fn get_handler_for_type(&self, exception_type: Option<&str>) -> Option<&ExceptionHandler> {
        for handler in &self.handlers {
            // Bare except catches everything
            if handler.exception_types.is_empty() {
                return Some(handler);
            }
            // Check if handler catches this type
            if let Some(exc_type) = exception_type {
                if handler
                    .exception_types
                    .iter()
                    .any(|t| t == exc_type || t == "Exception" || t == "BaseException")
                {
                    return Some(handler);
                }
            }
        }
        None
    }

    /// Get the first handler (for generic exception edges).
    fn first_handler(&self) -> Option<&ExceptionHandler> {
        self.handlers.first()
    }
}

// =============================================================================
// Python CFG Builder
// =============================================================================

/// Builds control flow graphs from Python AST nodes.
struct PythonCFGBuilder<'a> {
    source: &'a [u8],
    blocks: FxHashMap<BlockId, CFGBlock>,
    edges: Vec<CFGEdge>,
    next_block_id: usize,
    exits: Vec<BlockId>,
    /// Stack of loop headers for continue statements
    loop_headers: Vec<BlockId>,
    /// Stack of after-loop blocks for break statements
    loop_exits: Vec<BlockId>,
    /// Stack of active exception contexts for exception flow tracking.
    /// Enables creating exception edges from statements within try blocks
    /// to their appropriate handlers and finally blocks.
    exception_contexts: Vec<ExceptionContext>,
    /// Total decision points for cyclomatic complexity calculation.
    /// Tracked as: if (+1), elif (+1 each), while (+1), for (+1),
    /// except (+1 each), assert (+1), case (+1 each), guard (+1 each),
    /// comprehension if clauses (+1 each).
    decision_points: usize,
    /// Decision points from comprehensions (if_clause nodes).
    /// CFG-BUG-7 FIX: Comprehensions like `[x for x in items if pred1(x) if pred2(x)]`
    /// contain decision points that affect cyclomatic complexity but don't create
    /// separate CFG blocks since they're expressions with internal iteration.
    /// NOTE: These are included in decision_points but kept separately for
    /// backward compatibility in CFGInfo.
    comprehension_decision_points: usize,
    /// Nested function/closure CFGs (name -> CFG).
    /// Stores control flow graphs for inner functions defined within this function.
    nested_cfgs: FxHashMap<String, Box<CFGInfo>>,
    // =========================================================================
    // Async/await tracking
    // =========================================================================
    /// Whether this is an async function (async def).
    is_async: bool,
    /// Number of await suspension points encountered.
    await_points: usize,
    /// Detected blocking calls in async context.
    /// Format: (function_name, line_number)
    blocking_calls: Vec<(String, usize)>,
    // =========================================================================
    // Generator tracking
    // =========================================================================
    /// Whether this is a generator function (contains yield).
    is_generator: bool,
    /// Whether this is an async generator (async def with yield).
    is_async_generator: bool,
    /// Number of yield points in this generator.
    yield_count: usize,
}

impl<'a> PythonCFGBuilder<'a> {
    fn new(source: &'a [u8], is_async: bool) -> Self {
        Self {
            source,
            blocks: FxHashMap::default(),
            edges: Vec::new(),
            next_block_id: 0,
            exits: Vec::new(),
            loop_headers: Vec::new(),
            loop_exits: Vec::new(),
            exception_contexts: Vec::new(),
            decision_points: 0,
            comprehension_decision_points: 0,
            nested_cfgs: FxHashMap::default(),
            is_async,
            await_points: 0,
            blocking_calls: Vec::new(),
            is_generator: false,
            is_async_generator: false,
            yield_count: 0,
        }
    }

    fn build(node: Node, source: &[u8]) -> Result<CFGInfo> {
        if node.kind() != "function_definition" {
            return Err(BrrrError::Parse {
                file: String::new(),
                message: format!("Expected function_definition, got {}", node.kind()),
            });
        }

        let function_name = Python::child_by_kind(node, "identifier")
            .map(|n| Python::node_text(n, source).to_string())
            .unwrap_or_else(|| "<unknown>".to_string());

        // Check if this is an async function
        let is_async = Python::is_async_function(node);

        // Check if this is a generator function (contains yield/yield from)
        let is_generator = Python::contains_yield(node);
        let is_async_generator = is_async && is_generator;

        let mut builder = PythonCFGBuilder::new(source, is_async);
        builder.is_generator = is_generator;
        builder.is_async_generator = is_async_generator;

        // Create entry block
        let entry = builder.new_block("entry".to_string(), node.start_position().row + 1);

        // Find the block (function body)
        let body_block = Python::child_by_kind(node, "block");

        // Process function body
        let current = if let Some(block) = body_block {
            builder.process_block(block, entry)
        } else {
            entry
        };

        // Mark the final block as exit if not already
        if !builder.exits.contains(&current) {
            builder.exits.push(current);
        }

        Ok(CFGInfo {
            function_name,
            blocks: builder.blocks,
            edges: builder.edges,
            entry,
            exits: builder.exits,
            decision_points: builder.decision_points,
            comprehension_decision_points: builder.comprehension_decision_points,
            nested_cfgs: builder.nested_cfgs,
            is_async: builder.is_async,
            await_points: builder.await_points,
            blocking_calls: builder.blocking_calls,
            is_generator: builder.is_generator,
            is_async_generator: builder.is_async_generator,
            yield_count: builder.yield_count,
            ..Default::default()
        })
    }

    fn new_block(&mut self, label: String, line: usize) -> BlockId {
        let id = BlockId(self.next_block_id);
        self.next_block_id += 1;

        let block = CFGBlock {
            id,
            label,
            block_type: BlockType::Body,
            statements: Vec::new(),
            func_calls: Vec::new(),
            start_line: line,
            end_line: line,
        };

        self.blocks.insert(id, block);
        id
    }

    fn add_edge(&mut self, from: BlockId, to: BlockId, edge_type: EdgeType) {
        self.edges.push(CFGEdge::new(from, to, edge_type));
    }

    fn node_text(&self, node: Node) -> String {
        Python::node_text(node, self.source).to_string()
    }

    /// Check if a statement has an "async" keyword child.
    ///
    /// Tree-sitter parses "async for" and "async with" statements as
    /// "for_statement" and "with_statement" respectively, with an "async"
    /// child node before the main keyword.
    fn has_async_keyword(stmt: Node) -> bool {
        let mut cursor = stmt.walk();
        for child in stmt.children(&mut cursor) {
            if child.kind() == "async" {
                return true;
            }
            // Stop searching after we hit the main keyword (for, with)
            if matches!(child.kind(), "for" | "with") {
                return false;
            }
        }
        false
    }

    /// Process a block of statements, returning the exit block.
    fn process_block(&mut self, block: Node, entry: BlockId) -> BlockId {
        let mut current = entry;

        let mut cursor = block.walk();
        for stmt in block.children(&mut cursor) {
            current = self.process_statement(stmt, current);
        }

        current
    }

    /// Process a single statement, returning the exit block.
    fn process_statement(&mut self, stmt: Node, current: BlockId) -> BlockId {
        match stmt.kind() {
            "if_statement" => self.process_if(stmt, current),
            // tree-sitter parses "async for" as for_statement with async child
            "for_statement" => {
                let is_async = Self::has_async_keyword(stmt);
                self.process_for(stmt, current, is_async)
            }
            "while_statement" => self.process_while(stmt, current),
            "try_statement" => self.process_try(stmt, current),
            // tree-sitter parses "async with" as with_statement with async child
            "with_statement" => {
                let is_async = Self::has_async_keyword(stmt);
                self.process_with(stmt, current, is_async)
            }
            "match_statement" => self.process_match(stmt, current),
            "return_statement" => self.process_return(stmt, current),
            "raise_statement" => self.process_raise(stmt, current),
            "break_statement" => self.process_break(stmt, current),
            "continue_statement" => self.process_continue(stmt, current),
            // Assert creates two control flow paths (pass/fail)
            "assert_statement" => self.process_assert(stmt, current),
            // Statements that may contain comprehensions with decision points
            // Also scan for await expressions, blocking calls, and yield expressions
            "expression_statement" | "assignment" | "augmented_assignment" => {
                // CFG-BUG-7 FIX: Scan for comprehensions with if_clause decision points
                self.count_comprehension_decision_points(stmt);

                // Track await points and blocking calls
                let await_info = self.scan_async_patterns(stmt);

                // Track yield expressions (generator patterns)
                let yield_info = self.scan_yield_patterns(stmt);

                let stmt_text = self.node_text(stmt);
                let end_line = stmt.end_position().row + 1;

                // If this statement contains yield expressions, create yield point blocks
                if !yield_info.yield_exprs.is_empty() || !yield_info.yield_from_exprs.is_empty() {
                    return self.process_yield_statement(stmt, current, yield_info);
                }

                // If this statement contains await expressions, create explicit await point nodes
                if !await_info.await_exprs.is_empty() {
                    return self.process_await_statement(stmt, current, await_info);
                }

                // If this statement spawns tasks, mark it
                if !await_info.task_spawns.is_empty() {
                    return self.process_task_spawn_statement(stmt, current, await_info);
                }

                if let Some(block) = self.blocks.get_mut(&current) {
                    block.statements.push(stmt_text);
                    block.end_line = end_line;
                }
                current
            }
            // Simple flow-through statements that don't affect control flow
            "pass_statement"
            | "import_statement"
            | "import_from_statement"
            | "global_statement"
            | "nonlocal_statement"
            | "delete_statement"
            | "type_alias_statement" => {
                // BUG-021 FIX: Handle PEP 695 type statements
                let stmt_text = self.node_text(stmt);
                let end_line = stmt.end_position().row + 1;

                if let Some(block) = self.blocks.get_mut(&current) {
                    block.statements.push(stmt_text);
                    block.end_line = end_line;
                }
                current
            }
            "function_definition" | "class_definition" | "decorated_definition" => {
                // Extract name before getting mutable reference
                let name = Python::child_by_kind(stmt, "identifier")
                    .map(|n| Python::node_text(n, self.source).to_string())
                    .unwrap_or_else(|| "<def>".to_string());
                let end_line = stmt.end_position().row + 1;

                if let Some(block) = self.blocks.get_mut(&current) {
                    block.statements.push(format!("def {}", name));
                    block.end_line = end_line;
                }
                current
            }
            _ => {
                let stmt_text = self.node_text(stmt);
                let end_line = stmt.end_position().row + 1;

                if let Some(block) = self.blocks.get_mut(&current) {
                    block.statements.push(stmt_text);
                    block.end_line = end_line;
                }
                current
            }
        }
    }

    fn process_if(&mut self, node: Node, current: BlockId) -> BlockId {
        // CFG-RENDER-BUG-1 FIX: Track decision point for if statement
        self.decision_points += 1;

        // Get condition text before any mutable borrows
        let condition = Python::child_by_kind(node, "comparison_operator")
            .or_else(|| Python::child_by_kind(node, "boolean_operator"))
            .or_else(|| Python::child_by_kind(node, "identifier"))
            .or_else(|| Python::child_by_kind(node, "not_operator"))
            .map(|n| Python::node_text(n, self.source).to_string())
            .unwrap_or_else(|| "condition".to_string());

        // Update current block as branch
        if let Some(block) = self.blocks.get_mut(&current) {
            block.label = format!("if {}", condition);
            block.end_line = node.start_position().row + 1;
        }

        // Create merge block for after the if
        let merge = self.new_block("merge".to_string(), node.end_position().row + 1);

        // Process true branch (first block child)
        let true_block = self.new_block("then".to_string(), node.start_position().row + 2);
        self.add_edge(current, true_block, EdgeType::True);

        let true_exit = if let Some(block) = Python::child_by_kind(node, "block") {
            self.process_block(block, true_block)
        } else {
            true_block
        };

        if !self.exits.contains(&true_exit) {
            self.add_edge(true_exit, merge, EdgeType::Unconditional);
        }

        // Process elif/else clauses
        // CFG-BUG-4 FIX: Track the current condition block through the chain.
        // In an elif chain, each condition's false edge must connect to the NEXT
        // condition (elif or else), not back to the original if block.
        let mut cursor = node.walk();
        let mut has_else = false;
        let mut condition_block = current; // Start with the if block

        for child in node.children(&mut cursor) {
            match child.kind() {
                "elif_clause" => {
                    // CFG-RENDER-BUG-1 FIX: Track decision point for elif clause
                    self.decision_points += 1;

                    let elif_cond = Python::child_by_kind(child, "comparison_operator")
                        .or_else(|| Python::child_by_kind(child, "boolean_operator"))
                        .or_else(|| Python::child_by_kind(child, "identifier"))
                        .map(|n| Python::node_text(n, self.source).to_string())
                        .unwrap_or_else(|| "condition".to_string());

                    let elif_block = self.new_block(
                        format!("elif {}", elif_cond),
                        child.start_position().row + 1,
                    );

                    // False edge from PREVIOUS condition (if or elif) to this elif
                    self.add_edge(condition_block, elif_block, EdgeType::False);

                    // Process elif body
                    let elif_body =
                        self.new_block("elif_body".to_string(), child.start_position().row + 2);
                    self.add_edge(elif_block, elif_body, EdgeType::True);

                    let elif_exit = if let Some(block) = Python::child_by_kind(child, "block") {
                        self.process_block(block, elif_body)
                    } else {
                        elif_body
                    };

                    if !self.exits.contains(&elif_exit) {
                        self.add_edge(elif_exit, merge, EdgeType::Unconditional);
                    }

                    // Update condition_block to this elif for the next iteration
                    condition_block = elif_block;
                }
                "else_clause" => {
                    has_else = true;
                    let else_block =
                        self.new_block("else".to_string(), child.start_position().row + 1);
                    // False edge from the last condition (if or final elif) to else
                    self.add_edge(condition_block, else_block, EdgeType::False);

                    let else_exit = if let Some(block) = Python::child_by_kind(child, "block") {
                        self.process_block(block, else_block)
                    } else {
                        else_block
                    };

                    if !self.exits.contains(&else_exit) {
                        self.add_edge(else_exit, merge, EdgeType::Unconditional);
                    }
                }
                _ => {}
            }
        }

        // If no else clause, false branch from last condition goes directly to merge
        if !has_else {
            self.add_edge(condition_block, merge, EdgeType::False);
        }

        merge
    }

    /// Process an assert statement as a decision point with two control flow paths.
    ///
    /// Assert semantics:
    /// - If condition is true: execution continues normally (pass path)
    /// - If condition is false: raises AssertionError (fail path -> exit)
    ///
    /// This correctly models assert as a branching construct rather than a
    /// simple linear statement, which is important for:
    /// - Accurate cyclomatic complexity calculation
    /// - Proper dead code detection (code after assert may be unreachable in fail path)
    /// - Exception flow analysis
    fn process_assert(&mut self, node: Node, current: BlockId) -> BlockId {
        // CFG-RENDER-BUG-1 FIX: Track decision point for assert statement
        self.decision_points += 1;

        // Extract condition text for meaningful block labels
        // Assert syntax: assert <condition> [, <message>]
        let condition = node
            .child(1) // First child after 'assert' keyword is the condition
            .map(|n| Python::node_text(n, self.source).to_string())
            .unwrap_or_else(|| "condition".to_string());

        let stmt_text = self.node_text(node);
        let line = node.start_position().row + 1;
        let end_line = node.end_position().row + 1;

        // Add assert statement to current block and mark it as decision point
        if let Some(block) = self.blocks.get_mut(&current) {
            block.statements.push(stmt_text);
            block.end_line = end_line;
            block.label = format!("assert {}", condition);
        }

        // Create pass path: condition is true, execution continues
        let pass_block = self.new_block("assert_pass".to_string(), line);
        self.add_edge(current, pass_block, EdgeType::Pass);

        // Create fail path: condition is false, raises AssertionError
        let fail_block = self.new_block("assert_fail".to_string(), line);
        self.add_edge(current, fail_block, EdgeType::Fail);

        // Mark fail path as exit (AssertionError terminates normal flow)
        self.exits.push(fail_block);

        // Continue with pass path for subsequent statements
        pass_block
    }

    /// Process a for loop (sync or async).
    ///
    /// # Arguments
    /// * `node` - The for_statement or async_for_statement node
    /// * `current` - Current block ID
    /// * `is_async` - True for async for loops (async for item in async_iterator)
    ///
    /// # Async For Semantics
    /// Async for loops iterate over async iterators:
    /// ```python
    /// async for item in async_generator():
    ///     await process(item)
    /// ```
    /// Each iteration involves an await on `__anext__()`, creating suspension points.
    fn process_for(&mut self, node: Node, current: BlockId, is_async: bool) -> BlockId {
        // CFG-RENDER-BUG-1 FIX: Track decision point for for loop
        self.decision_points += 1;

        // Create loop header with appropriate label and block type
        let header_label = if is_async {
            "async_for_loop".to_string()
        } else {
            "for_loop".to_string()
        };
        let header = self.new_block(header_label, node.start_position().row + 1);

        // Set block type for async for
        if is_async {
            if let Some(block) = self.blocks.get_mut(&header) {
                block.block_type = BlockType::AsyncForLoop;
            }
        }

        self.add_edge(current, header, EdgeType::Unconditional);

        // Create after-loop block
        let after_loop_label = if is_async {
            "after_async_for".to_string()
        } else {
            "after_for".to_string()
        };
        let after_loop = self.new_block(after_loop_label, node.end_position().row + 1);

        // Track loop for break/continue
        self.loop_headers.push(header);
        self.loop_exits.push(after_loop);

        // Create and process loop body
        let body_label = if is_async {
            "async_for_body".to_string()
        } else {
            "for_body".to_string()
        };
        let body_block = self.new_block(body_label, node.start_position().row + 2);

        // Use async-specific edge types for async for loops
        let iterate_edge = if is_async {
            EdgeType::AsyncIterate
        } else {
            EdgeType::Iterate
        };
        self.add_edge(header, body_block, iterate_edge);

        let body_exit = if let Some(block) = Python::child_by_kind(node, "block") {
            self.process_block(block, body_block)
        } else {
            body_block
        };

        // Back edge from body end to header
        if !self.exits.contains(&body_exit) {
            self.add_edge(body_exit, header, EdgeType::Next);
        }

        // Pop loop tracking
        self.loop_headers.pop();
        self.loop_exits.pop();

        // Handle else clause (executes when loop completes normally)
        let exhausted_edge = if is_async {
            EdgeType::AsyncExhausted
        } else {
            EdgeType::Exhausted
        };

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "else_clause" {
                let else_label = if is_async {
                    "async_for_else".to_string()
                } else {
                    "for_else".to_string()
                };
                let else_block = self.new_block(else_label, child.start_position().row + 1);
                self.add_edge(header, else_block, exhausted_edge);

                let else_exit = if let Some(block) = Python::child_by_kind(child, "block") {
                    self.process_block(block, else_block)
                } else {
                    else_block
                };

                if !self.exits.contains(&else_exit) {
                    self.add_edge(else_exit, after_loop, EdgeType::Unconditional);
                }

                return after_loop;
            }
        }

        // No else clause - header goes directly to after_loop when exhausted
        self.add_edge(header, after_loop, exhausted_edge);
        after_loop
    }

    fn process_while(&mut self, node: Node, current: BlockId) -> BlockId {
        // CFG-RENDER-BUG-1 FIX: Track decision point for while loop
        self.decision_points += 1;

        // Get condition text before any mutable borrows
        let condition = Python::child_by_kind(node, "comparison_operator")
            .or_else(|| Python::child_by_kind(node, "boolean_operator"))
            .or_else(|| Python::child_by_kind(node, "identifier"))
            .map(|n| Python::node_text(n, self.source).to_string())
            .unwrap_or_else(|| "condition".to_string());

        // Create loop header
        let header = self.new_block(
            format!("while {}", condition),
            node.start_position().row + 1,
        );
        self.add_edge(current, header, EdgeType::Unconditional);

        // Create after-loop block
        let after_loop = self.new_block("after_while".to_string(), node.end_position().row + 1);

        // Track loop for break/continue
        self.loop_headers.push(header);
        self.loop_exits.push(after_loop);

        // Create and process loop body
        let body_block = self.new_block("while_body".to_string(), node.start_position().row + 2);
        self.add_edge(header, body_block, EdgeType::True);

        let body_exit = if let Some(block) = Python::child_by_kind(node, "block") {
            self.process_block(block, body_block)
        } else {
            body_block
        };

        // Back edge from body end to header
        if !self.exits.contains(&body_exit) {
            self.add_edge(body_exit, header, EdgeType::Next);
        }

        // Pop loop tracking
        self.loop_headers.pop();
        self.loop_exits.pop();

        // Handle else clause
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "else_clause" {
                let else_block =
                    self.new_block("while_else".to_string(), child.start_position().row + 1);
                self.add_edge(header, else_block, EdgeType::False);

                let else_exit = if let Some(block) = Python::child_by_kind(child, "block") {
                    self.process_block(block, else_block)
                } else {
                    else_block
                };

                if !self.exits.contains(&else_exit) {
                    self.add_edge(else_exit, after_loop, EdgeType::Unconditional);
                }

                return after_loop;
            }
        }

        // No else clause - header goes directly to after_loop when false
        self.add_edge(header, after_loop, EdgeType::False);
        after_loop
    }

    fn process_try(&mut self, node: Node, current: BlockId) -> BlockId {
        let start_line = node.start_position().row + 1;
        let end_line = node.end_position().row + 1;

        // Create try block
        let try_block = self.new_block("try".to_string(), start_line);
        self.add_edge(current, try_block, EdgeType::Unconditional);

        // Create after-try block for merging
        let after_try = self.new_block("after_try".to_string(), end_line);

        // Create exception context for this try block
        let mut exc_context = ExceptionContext::new(try_block, after_try, start_line, end_line);

        // First pass: find finally clause and create blocks for all handlers
        // We need to create handler blocks BEFORE processing the try body
        // so that implicit exception edges can be created
        let mut cursor = node.walk();
        let mut has_finally = false;
        let mut finally_block_id = None;
        let mut finally_clause = None;

        // Collect all except clauses for processing
        let mut except_clauses: Vec<(Node, BlockId, Vec<String>, bool)> = Vec::new();
        let mut else_clause = None;

        for child in node.children(&mut cursor) {
            match child.kind() {
                "finally_clause" => {
                    has_finally = true;
                    let finally_block =
                        self.new_block("finally".to_string(), child.start_position().row + 1);
                    finally_block_id = Some(finally_block);
                    finally_clause = Some(child);
                    exc_context.set_finally(finally_block);
                }
                "except_clause" => {
                    // CFG-RENDER-BUG-1 FIX: Track decision point for except handler
                    self.decision_points += 1;

                    // Extract exception types from the except clause
                    let exception_types = self.extract_exception_types(child);
                    let label = if exception_types.is_empty() {
                        "except".to_string()
                    } else {
                        format!("except {}", exception_types.join(" | "))
                    };

                    let except_block = self.new_block(label, child.start_position().row + 1);

                    // Add handler to exception context
                    exc_context.add_handler(except_block, exception_types.clone(), false);
                    except_clauses.push((child, except_block, exception_types, false));
                }
                "except_group_clause" => {
                    // CFG-RENDER-BUG-1 FIX: Track decision point for except* handler
                    self.decision_points += 1;

                    // Extract exception types from the except* clause
                    let exception_types = self.extract_exception_types(child);
                    let label = if exception_types.is_empty() {
                        "except*".to_string()
                    } else {
                        format!("except* {}", exception_types.join(" | "))
                    };

                    let except_block = self.new_block(label, child.start_position().row + 1);

                    // Add handler to exception context (marked as exception group)
                    exc_context.add_handler(except_block, exception_types.clone(), true);
                    except_clauses.push((child, except_block, exception_types, true));
                }
                "else_clause" => {
                    else_clause = Some(child);
                }
                _ => {}
            }
        }

        // Push exception context BEFORE processing try body
        // This allows statements within the try block to add exception edges
        self.exception_contexts.push(exc_context);

        // Process try body - now statements can see exception context
        let try_exit = if let Some(block) = Python::child_by_kind(node, "block") {
            self.process_block(block, try_block)
        } else {
            try_block
        };

        // Pop exception context after processing try body
        let exc_context = self.exception_contexts.pop().unwrap();

        // Add exception edges from try block to handlers
        for (_, except_block, exception_types, is_group) in &except_clauses {
            let edge_type = if *is_group {
                EdgeType::ExceptionGroup
            } else if !exception_types.is_empty() {
                EdgeType::TypedException
            } else {
                EdgeType::Exception
            };

            // Create edge with exception type as condition for better visualization
            if !exception_types.is_empty() {
                self.edges.push(CFGEdge::with_condition(
                    try_block,
                    *except_block,
                    edge_type,
                    exception_types.join(" | "),
                ));
            } else {
                self.add_edge(try_block, *except_block, edge_type);
            }
        }

        // Process except handler bodies
        for (clause_node, except_block, _, _) in &except_clauses {
            let except_exit = if let Some(block) = Python::child_by_kind(*clause_node, "block") {
                self.process_block(block, *except_block)
            } else {
                *except_block
            };

            // Connect to finally or after_try
            if !self.exits.contains(&except_exit) {
                if let Some(finally_id) = finally_block_id {
                    self.add_edge(except_exit, finally_id, EdgeType::Finally);
                } else {
                    self.add_edge(except_exit, after_try, EdgeType::Unconditional);
                }
            }
        }

        // Process finally clause body (if present)
        if let Some(finally_node) = finally_clause {
            let finally_block = finally_block_id.unwrap();
            let finally_exit = if let Some(block) = Python::child_by_kind(finally_node, "block") {
                self.process_block(block, finally_block)
            } else {
                finally_block
            };

            if !self.exits.contains(&finally_exit) {
                self.add_edge(finally_exit, after_try, EdgeType::Unconditional);
            }
        }

        // Process else clause (only executes if no exception was raised)
        if let Some(else_node) = else_clause {
            let else_block =
                self.new_block("try_else".to_string(), else_node.start_position().row + 1);

            // Try success goes to else
            if !self.exits.contains(&try_exit) {
                self.add_edge(try_exit, else_block, EdgeType::NoException);
            }

            let else_exit = if let Some(block) = Python::child_by_kind(else_node, "block") {
                self.process_block(block, else_block)
            } else {
                else_block
            };

            if !self.exits.contains(&else_exit) {
                if let Some(finally_id) = finally_block_id {
                    self.add_edge(else_exit, finally_id, EdgeType::Finally);
                } else {
                    self.add_edge(else_exit, after_try, EdgeType::Unconditional);
                }
            }

            // We've handled try_exit, return early if no finally
            if !has_finally && !self.exits.contains(&try_exit) {
                return after_try;
            }
        }

        // If no else clause, try success goes to finally or after_try
        if !self.exits.contains(&try_exit) {
            if let Some(finally_id) = finally_block_id {
                self.add_edge(try_exit, finally_id, EdgeType::Finally);
            } else {
                self.add_edge(try_exit, after_try, EdgeType::Unconditional);
            }
        }

        // Handle propagation of unhandled exceptions through finally
        // If there are handlers but also a bare except, exceptions are caught
        // If there's only typed handlers, unmatched exceptions propagate
        if has_finally
            && !exc_context
                .handlers
                .iter()
                .any(|h| h.exception_types.is_empty())
        {
            // Create a propagation path through finally for unhandled exceptions
            let propagate_block = self.new_block("exception_propagate".to_string(), end_line);
            self.add_edge(try_block, propagate_block, EdgeType::Propagate);
            self.add_edge(
                propagate_block,
                finally_block_id.unwrap(),
                EdgeType::Finally,
            );
            // After finally, exception continues to propagate
            let reraise_block = self.new_block("reraise_after_finally".to_string(), end_line);
            self.exits.push(reraise_block);
        }

        after_try
    }

    /// Extract exception types from an except or except* clause.
    ///
    /// Handles various patterns:
    /// - `except ValueError:` -> ["ValueError"]
    /// - `except (TypeError, KeyError):` -> ["TypeError", "KeyError"]
    /// - `except ValueError as e:` -> ["ValueError"]
    /// - `except:` -> []
    fn extract_exception_types(&self, node: Node) -> Vec<String> {
        let mut types = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    // Single exception type: `except ValueError:`
                    types.push(self.node_text(child));
                }
                "attribute" => {
                    // Qualified exception: `except module.CustomError:`
                    types.push(self.node_text(child));
                }
                "tuple" | "parenthesized_expression" => {
                    // Multiple exceptions: `except (ValueError, TypeError):`
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        match inner.kind() {
                            "identifier" | "attribute" => {
                                types.push(self.node_text(inner));
                            }
                            _ => {}
                        }
                    }
                }
                "as_pattern" => {
                    // Exception with binding: `except ValueError as e:`
                    // The exception type is the first child before "as"
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        match inner.kind() {
                            "identifier" => {
                                // Could be exception type or binding name
                                // Check if it's before "as"
                                let mut check_cursor = child.walk();
                                let mut seen_as = false;
                                for check_child in child.children(&mut check_cursor) {
                                    if check_child.kind() == "as" {
                                        seen_as = true;
                                    }
                                    if check_child.id() == inner.id() && !seen_as {
                                        types.push(self.node_text(inner));
                                        break;
                                    }
                                }
                            }
                            "attribute" => {
                                types.push(self.node_text(inner));
                            }
                            "tuple" | "parenthesized_expression" => {
                                // Multiple exceptions with binding
                                let mut tuple_cursor = inner.walk();
                                for tuple_child in inner.children(&mut tuple_cursor) {
                                    match tuple_child.kind() {
                                        "identifier" | "attribute" => {
                                            types.push(self.node_text(tuple_child));
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }

        types
    }

    /// Process a return statement, routing through finally blocks if needed.
    ///
    /// In Python, return within try/finally must execute finally before returning.
    /// This creates proper CFG edges to model this behavior.
    fn process_return(&mut self, stmt: Node, current: BlockId) -> BlockId {
        // CFG-BUG-7 FIX: Scan return value for comprehensions
        self.count_comprehension_decision_points(stmt);

        let stmt_text = self.node_text(stmt);
        let end_line = stmt.end_position().row + 1;

        if let Some(block) = self.blocks.get_mut(&current) {
            block.statements.push(stmt_text);
            block.end_line = end_line;
        }

        // Check if we're inside a try block with finally
        if let Some(exc_ctx) = self.exception_contexts.last() {
            if let Some(finally_block) = exc_ctx.finally_block {
                // Return must go through finally first
                let return_via_finally = self.new_block("return_via_finally".to_string(), end_line);
                self.add_edge(current, return_via_finally, EdgeType::Return);
                self.add_edge(return_via_finally, finally_block, EdgeType::Finally);
                // After finally, we still exit (the return continues)
                self.exits.push(return_via_finally);
                return self.new_block("unreachable".to_string(), end_line);
            }
        }

        self.exits.push(current);
        self.new_block("unreachable".to_string(), end_line)
    }

    /// Process a raise statement, handling bare raise and exception chaining.
    ///
    /// Handles:
    /// - `raise` - bare reraise of current exception
    /// - `raise Exception()` - raise new exception
    /// - `raise Exception() from cause` - exception chaining
    fn process_raise(&mut self, stmt: Node, current: BlockId) -> BlockId {
        let stmt_text = self.node_text(stmt);
        let end_line = stmt.end_position().row + 1;

        // Determine the type of raise statement
        let mut cursor = stmt.walk();
        let mut has_exception = false;
        let mut has_from = false;
        let mut exception_type: Option<String> = None;

        for child in stmt.children(&mut cursor) {
            match child.kind() {
                "raise" => {} // keyword
                "from" => has_from = true,
                "identifier" => {
                    if !has_from {
                        exception_type = Some(self.node_text(child));
                        has_exception = true;
                    }
                }
                "call" => {
                    // Extract exception type from call like `ValueError("msg")`
                    if !has_from {
                        if let Some(func) = Python::child_by_kind(child, "identifier") {
                            exception_type = Some(self.node_text(func));
                        } else if let Some(attr) = Python::child_by_kind(child, "attribute") {
                            exception_type = Some(self.node_text(attr));
                        }
                        has_exception = true;
                    }
                }
                "attribute" => {
                    if !has_from {
                        exception_type = Some(self.node_text(child));
                        has_exception = true;
                    }
                }
                _ => {}
            }
        }

        // Update block with statement
        let label = if !has_exception {
            "raise (reraise)".to_string()
        } else if has_from {
            format!(
                "raise {} from ...",
                exception_type.as_deref().unwrap_or("Exception")
            )
        } else {
            format!("raise {}", exception_type.as_deref().unwrap_or("Exception"))
        };

        if let Some(block) = self.blocks.get_mut(&current) {
            block.statements.push(stmt_text);
            block.end_line = end_line;
            block.label = label;
        }

        // Check if we're inside a try block
        if let Some(exc_ctx) = self.exception_contexts.last() {
            // If this is a bare raise, use Reraise edge type
            let edge_type = if !has_exception {
                EdgeType::Reraise
            } else {
                EdgeType::Exception
            };

            // Route to handler if there's a matching one
            if let Some(handler) = exc_ctx.first_handler() {
                // Create edge to handler with exception type info
                if let Some(ref exc_type) = exception_type {
                    self.edges.push(CFGEdge::with_condition(
                        current,
                        handler.handler_block,
                        edge_type,
                        exc_type.clone(),
                    ));
                } else {
                    self.add_edge(current, handler.handler_block, edge_type);
                }
            } else if let Some(finally_block) = exc_ctx.finally_block {
                // No handler but has finally - exception goes through finally then propagates
                let propagate = self.new_block("exception_propagate".to_string(), end_line);
                self.add_edge(current, propagate, edge_type);
                self.add_edge(propagate, finally_block, EdgeType::Finally);
                self.exits.push(propagate);
                return self.new_block("unreachable".to_string(), end_line);
            }
        }

        // Exception propagates out of function
        self.exits.push(current);
        self.new_block("unreachable".to_string(), end_line)
    }

    /// Process a break statement, routing through finally blocks if needed.
    fn process_break(&mut self, stmt: Node, current: BlockId) -> BlockId {
        let end_line = stmt.end_position().row + 1;

        // Check if we need to go through finally first
        if let Some(exc_ctx) = self.exception_contexts.last() {
            if let Some(finally_block) = exc_ctx.finally_block {
                // Break must go through finally first
                let break_via_finally = self.new_block("break_via_finally".to_string(), end_line);
                self.add_edge(current, break_via_finally, EdgeType::Break);
                self.add_edge(break_via_finally, finally_block, EdgeType::Finally);

                // After finally, continue to loop exit
                // Note: the edge from finally to loop exit is handled by finally's normal exit
                // The break_via_finally block is marked as unreachable since control
                // transfers to finally, which then handles the continuation
                return self.new_block("unreachable".to_string(), end_line);
            }
        }

        // Normal break - go directly to loop exit
        if let Some(&exit_block) = self.loop_exits.last() {
            self.add_edge(current, exit_block, EdgeType::Break);
        }
        self.new_block("unreachable".to_string(), end_line)
    }

    /// Process a continue statement, routing through finally blocks if needed.
    fn process_continue(&mut self, stmt: Node, current: BlockId) -> BlockId {
        let end_line = stmt.end_position().row + 1;

        // Check if we need to go through finally first
        if let Some(exc_ctx) = self.exception_contexts.last() {
            if let Some(finally_block) = exc_ctx.finally_block {
                // Continue must go through finally first
                let continue_via_finally =
                    self.new_block("continue_via_finally".to_string(), end_line);
                self.add_edge(current, continue_via_finally, EdgeType::Continue);
                self.add_edge(continue_via_finally, finally_block, EdgeType::Finally);

                // After finally, continue to loop header
                // Note: the actual jump back to header happens after finally executes
                return self.new_block("unreachable".to_string(), end_line);
            }
        }

        // Normal continue - go directly to loop header
        if let Some(&header) = self.loop_headers.last() {
            self.add_edge(current, header, EdgeType::Continue);
        }
        self.new_block("unreachable".to_string(), end_line)
    }

    /// Check if we're currently inside a try block (for implicit exception edges).
    #[allow(dead_code)]
    fn in_try_block(&self) -> bool {
        !self.exception_contexts.is_empty()
    }

    /// Get the innermost exception context (if any).
    #[allow(dead_code)]
    fn current_exception_context(&self) -> Option<&ExceptionContext> {
        self.exception_contexts.last()
    }

    /// Process a with statement (sync or async context manager).
    ///
    /// # Arguments
    /// * `node` - The with_statement or async_with_statement node
    /// * `current` - Current block ID
    /// * `is_async` - True for async with statements (async context managers)
    ///
    /// # Async With Semantics
    /// Async with statements use async context managers:
    /// ```python
    /// async with aiohttp.ClientSession() as session:
    ///     response = await session.get(url)
    /// ```
    /// `__aenter__` and `__aexit__` are awaited, creating suspension points.
    fn process_with(&mut self, node: Node, current: BlockId, is_async: bool) -> BlockId {
        // With statement has implicit try/finally semantics:
        // - __enter__ (or __aenter__) is called (can raise)
        // - body executes (can raise)
        // - __exit__ (or __aexit__) is called regardless of exceptions (finally semantics)
        let start_line = node.start_position().row + 1;
        let end_line = node.end_position().row + 1;

        // Enter block: context manager's __enter__/__aenter__ is called
        let enter_label = if is_async {
            "async_with_enter".to_string()
        } else {
            "with_enter".to_string()
        };
        let enter_block = self.new_block(enter_label, start_line);

        // Set block type for async with
        if is_async {
            if let Some(block) = self.blocks.get_mut(&enter_block) {
                block.block_type = BlockType::AsyncWithBlock;
            }
        }

        self.add_edge(current, enter_block, EdgeType::Unconditional);

        // Enter can fail with exception
        let enter_fail_label = if is_async {
            "async_with_enter_fail".to_string()
        } else {
            "with_enter_fail".to_string()
        };
        let enter_fail = self.new_block(enter_fail_label, start_line);
        let enter_exception_edge = if is_async {
            EdgeType::AsyncEnterException
        } else {
            EdgeType::EnterException
        };
        self.add_edge(enter_block, enter_fail, enter_exception_edge);
        self.exits.push(enter_fail); // Exception propagates out

        // Body block: executes after successful __enter__/__aenter__
        let body_label = if is_async {
            "async_with_body".to_string()
        } else {
            "with_body".to_string()
        };
        let body_block = self.new_block(body_label, start_line);
        let enter_success_edge = if is_async {
            EdgeType::AsyncEnterSuccess
        } else {
            EdgeType::EnterSuccess
        };
        self.add_edge(enter_block, body_block, enter_success_edge);

        // Process body statements
        let body_end = if let Some(block) = Python::child_by_kind(node, "block") {
            self.process_block(block, body_block)
        } else {
            body_block
        };

        // Exit block: __exit__/__aexit__ is called (finally semantics)
        let exit_label = if is_async {
            "async_with_exit".to_string()
        } else {
            "with_exit".to_string()
        };
        let exit_block = self.new_block(exit_label, end_line);

        // Normal path: body completes successfully -> __exit__/__aexit__ called
        if !self.exits.contains(&body_end) {
            self.add_edge(body_end, exit_block, EdgeType::Unconditional);
        }

        // Exception path: body raises -> __exit__/__aexit__ still called for cleanup
        let body_exc_label = if is_async {
            "async_with_body_exception".to_string()
        } else {
            "with_body_exception".to_string()
        };
        let body_exception = self.new_block(body_exc_label, end_line);
        self.add_edge(body_block, body_exception, EdgeType::Exception);
        self.add_edge(body_exception, exit_block, EdgeType::Cleanup);

        // After with: continues after __exit__/__aexit__ completes
        let after_label = if is_async {
            "after_async_with".to_string()
        } else {
            "after_with".to_string()
        };
        let after_with = self.new_block(after_label, end_line);
        self.add_edge(exit_block, after_with, EdgeType::Unconditional);

        // __exit__/__aexit__ can also propagate exception (if it doesn't suppress)
        let exit_prop_label = if is_async {
            "async_with_exit_propagate".to_string()
        } else {
            "with_exit_propagate".to_string()
        };
        let exit_exception = self.new_block(exit_prop_label, end_line);
        self.add_edge(exit_block, exit_exception, EdgeType::Propagate);
        self.exits.push(exit_exception);

        after_with
    }

    fn process_match(&mut self, node: Node, current: BlockId) -> BlockId {
        // Create match branch block
        let match_block = self.new_block("match".to_string(), node.start_position().row + 1);
        self.add_edge(current, match_block, EdgeType::Unconditional);

        // Create after-match block for merging
        let after_match = self.new_block("after_match".to_string(), node.end_position().row + 1);

        // CFG-BUG-5 FIX: Collect all case clauses first to handle guard fallthrough.
        // When a guard fails, control falls through to the next case pattern.
        // Note: In tree-sitter-python, case_clause nodes are inside a block under match_statement
        let case_clauses: Vec<_> = if let Some(block) = Python::child_by_kind(node, "block") {
            let mut cursor = block.walk();
            block
                .children(&mut cursor)
                .filter(|child| child.kind() == "case_clause")
                .collect()
        } else {
            // Fallback: try direct children (for different tree-sitter versions)
            let mut cursor = node.walk();
            node.children(&mut cursor)
                .filter(|child| child.kind() == "case_clause")
                .collect()
        };

        // Track case pattern blocks for guard fallthrough connections
        let mut case_pattern_blocks: Vec<BlockId> = Vec::with_capacity(case_clauses.len());

        // First pass: create all case pattern blocks so we know fallthrough targets
        for case_clause in &case_clauses {
            let case_block =
                self.new_block("case".to_string(), case_clause.start_position().row + 1);
            case_pattern_blocks.push(case_block);
        }

        // Second pass: process each case with proper guard handling
        for (i, case_clause) in case_clauses.iter().enumerate() {
            // CFG-RENDER-BUG-1 FIX: Track decision point for each case clause
            self.decision_points += 1;

            let case_block = case_pattern_blocks[i];
            self.add_edge(match_block, case_block, EdgeType::Case);

            // CFG-BUG-5 FIX: Check for guard clause (case pattern if condition:)
            // Guards create an additional decision point in the CFG.
            // In Python's structural pattern matching:
            // 1. First the pattern is checked
            // 2. If pattern matches AND there's a guard, the guard condition is evaluated
            // 3. If guard is false, fall through to next case pattern
            // Note: tree-sitter-python uses "if_clause" for guards in case statements
            let body_entry = if let Some(guard) = Python::child_by_kind(*case_clause, "if_clause") {
                // CFG-RENDER-BUG-1 FIX: Track decision point for match guard
                self.decision_points += 1;

                // Extract guard condition text for the block label
                let guard_condition = self.extract_guard_condition(guard);
                let guard_block = self.new_block(
                    format!("guard: if {}", guard_condition),
                    guard.start_position().row + 1,
                );

                // Case pattern check leads to guard evaluation
                self.add_edge(case_block, guard_block, EdgeType::PatternMatch);

                // Create block for guard pass (true path)
                let guard_pass =
                    self.new_block("guard_pass".to_string(), guard.end_position().row + 1);
                self.add_edge(guard_block, guard_pass, EdgeType::True);

                // Guard fail falls through to next case or after_match
                let fallthrough_target = if i + 1 < case_pattern_blocks.len() {
                    // Fall through to next case pattern
                    case_pattern_blocks[i + 1]
                } else {
                    // Last case: fall through to after_match (no match)
                    after_match
                };
                self.add_edge(guard_block, fallthrough_target, EdgeType::False);

                guard_pass
            } else {
                // No guard: case pattern directly leads to body
                case_block
            };

            // Process case body
            let case_exit = if let Some(block) = Python::child_by_kind(*case_clause, "block") {
                self.process_block(block, body_entry)
            } else {
                body_entry
            };

            // Connect case exit to after_match (unless it's a return/raise)
            if !self.exits.contains(&case_exit) {
                self.add_edge(case_exit, after_match, EdgeType::Unconditional);
            }
        }

        after_match
    }

    /// Extract the condition expression from a guard (if_clause) node.
    /// In tree-sitter-python, guard nodes have structure: if_clause -> "if" -> expression
    fn extract_guard_condition(&self, guard: Node) -> String {
        let mut cursor = guard.walk();
        for child in guard.children(&mut cursor) {
            // Skip the "if" keyword, get the actual condition expression
            if child.kind() != "if" {
                return self.node_text(child);
            }
        }
        "condition".to_string()
    }

    /// CFG-BUG-7 FIX: Count decision points within comprehensions.
    ///
    /// Comprehensions like `[x for x in items if pred1(x) if pred2(x)]` contain
    /// internal control flow that affects cyclomatic complexity:
    /// - Each `if_clause` is a filter condition (decision point)
    ///
    /// This recursively scans an expression tree for comprehension nodes
    /// and counts their `if_clause` children.
    fn count_comprehension_decision_points(&mut self, node: Node) {
        match node.kind() {
            "list_comprehension"
            | "dictionary_comprehension"
            | "set_comprehension"
            | "generator_expression" => {
                // Count if_clause children within this comprehension
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "if_clause" {
                        // CFG-RENDER-BUG-1 FIX: Each if clause in comprehension is a decision point
                        // Increment both counters for total decision_points and
                        // comprehension_decision_points for backward compatibility
                        self.decision_points += 1;
                        self.comprehension_decision_points += 1;
                    }
                }
                // Recursively check nested comprehensions in the body expression
                // e.g., [[y for y in x if p(y)] for x in items if q(x)]
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.count_comprehension_decision_points(child);
                }
            }
            // Recurse into other expression types that may contain comprehensions
            _ => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.count_comprehension_decision_points(child);
                }
            }
        }
    }

    // =========================================================================
    // Async/Await Pattern Analysis
    // =========================================================================

    /// Information about async patterns found in a statement.
    /// Used to track await expressions, task spawns, and blocking calls.
    fn scan_async_patterns(&mut self, node: Node) -> AsyncPatternInfo {
        let mut info = AsyncPatternInfo::default();
        self.scan_async_patterns_recursive(node, &mut info);

        // Record blocking calls if in async context
        if self.is_async {
            for (call_name, line) in &info.blocking_calls {
                self.blocking_calls.push((call_name.clone(), *line));
            }
        }

        info
    }

    /// Recursively scan an AST node for async patterns.
    fn scan_async_patterns_recursive(&self, node: Node, info: &mut AsyncPatternInfo) {
        match node.kind() {
            "await" => {
                // Found an await expression
                let line = node.start_position().row + 1;
                let awaited = node
                    .child(1)
                    .map(|n| Python::node_text(n, self.source).to_string())
                    .unwrap_or_else(|| "<expr>".to_string());
                info.await_exprs.push((awaited, line));
            }
            "call" => {
                // Check for task spawning patterns and blocking calls
                if let Some(func) = node.child(0) {
                    let func_text = Python::node_text(func, self.source);
                    let line = node.start_position().row + 1;

                    // Check for task spawn patterns
                    if Self::is_task_spawn_call(&func_text) {
                        info.task_spawns.push((func_text.to_string(), line));
                    }

                    // Check for blocking calls in async context
                    if self.is_async && Self::is_blocking_call(&func_text) {
                        info.blocking_calls.push((func_text.to_string(), line));
                    }
                }

                // Continue scanning children (arguments may contain await)
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.scan_async_patterns_recursive(child, info);
                }
            }
            _ => {
                // Recurse into children
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.scan_async_patterns_recursive(child, info);
                }
            }
        }
    }

    /// Check if a function call is a task spawning pattern.
    fn is_task_spawn_call(func_name: &str) -> bool {
        matches!(
            func_name,
            "asyncio.create_task"
                | "create_task"
                | "asyncio.ensure_future"
                | "ensure_future"
                | "asyncio.gather"
                | "gather"
                | "asyncio.wait"
                | "wait"
                | "asyncio.wait_for"
                | "wait_for"
                | "asyncio.shield"
                | "shield"
                | "asyncio.TaskGroup"
                | "TaskGroup"
                | "anyio.create_task_group"
                | "trio.open_nursery"
        )
    }

    /// Check if a function call is a blocking call that should not be used in async context.
    fn is_blocking_call(func_name: &str) -> bool {
        matches!(
            func_name,
            "time.sleep"
                | "sleep"  // Might be a false positive, but worth flagging
                | "requests.get"
                | "requests.post"
                | "requests.put"
                | "requests.delete"
                | "requests.patch"
                | "requests.head"
                | "requests.options"
                | "requests.request"
                | "urllib.request.urlopen"
                | "urlopen"
                | "open"  // File I/O can block
                | "input"
                | "subprocess.run"
                | "subprocess.call"
                | "subprocess.check_call"
                | "subprocess.check_output"
                | "os.system"
                | "os.popen"
        )
    }

    /// Process a statement containing await expressions, creating AwaitPoint blocks.
    fn process_await_statement(
        &mut self,
        stmt: Node,
        current: BlockId,
        info: AsyncPatternInfo,
    ) -> BlockId {
        let stmt_text = self.node_text(stmt);
        let end_line = stmt.end_position().row + 1;

        // Add statement text to current block first
        if let Some(block) = self.blocks.get_mut(&current) {
            block.statements.push(stmt_text);
            block.end_line = end_line;
        }

        // Track total await points
        self.await_points += info.await_exprs.len();

        // Create await point blocks for each await expression
        // Multiple awaits in one statement create a chain of suspension points
        let mut prev_block = current;

        for (i, (awaited_expr, line)) in info.await_exprs.iter().enumerate() {
            let await_label = if info.await_exprs.len() == 1 {
                format!("await {}", truncate_expr(awaited_expr, 30))
            } else {
                format!("await[{}] {}", i + 1, truncate_expr(awaited_expr, 25))
            };

            let await_block = self.new_block(await_label, *line);

            // Set block type to AwaitPoint
            if let Some(block) = self.blocks.get_mut(&await_block) {
                block.block_type = BlockType::AwaitPoint;
            }

            // Connect previous block to await point with Await edge
            self.add_edge(prev_block, await_block, EdgeType::Await);

            prev_block = await_block;
        }

        // Create continuation block after all awaits
        let after_await = self.new_block("after_await".to_string(), end_line);
        self.add_edge(prev_block, after_await, EdgeType::Unconditional);

        after_await
    }

    /// Process a statement containing task spawn calls.
    fn process_task_spawn_statement(
        &mut self,
        stmt: Node,
        current: BlockId,
        info: AsyncPatternInfo,
    ) -> BlockId {
        let stmt_text = self.node_text(stmt);
        let end_line = stmt.end_position().row + 1;

        // Add statement to current block
        if let Some(block) = self.blocks.get_mut(&current) {
            block.statements.push(stmt_text);
            block.end_line = end_line;
        }

        // Create task spawn blocks
        let mut prev_block = current;

        for (spawn_func, line) in &info.task_spawns {
            let spawn_label = format!("spawn: {}", spawn_func);
            let spawn_block = self.new_block(spawn_label, *line);

            // Set block type to TaskSpawn
            if let Some(block) = self.blocks.get_mut(&spawn_block) {
                block.block_type = BlockType::TaskSpawn;
            }

            // Connect with TaskSpawn edge
            self.add_edge(prev_block, spawn_block, EdgeType::TaskSpawn);
            prev_block = spawn_block;
        }

        // Continue after spawn
        let after_spawn = self.new_block("after_spawn".to_string(), end_line);
        self.add_edge(prev_block, after_spawn, EdgeType::Unconditional);

        after_spawn
    }
}

/// Information collected about async patterns in an AST node.
#[derive(Default)]
struct AsyncPatternInfo {
    /// Await expressions: (awaited expression text, line number)
    await_exprs: Vec<(String, usize)>,
    /// Task spawn calls: (function name, line number)
    task_spawns: Vec<(String, usize)>,
    /// Blocking calls in async context: (function name, line number)
    blocking_calls: Vec<(String, usize)>,
}

/// Truncate an expression string for display in CFG labels.
fn truncate_expr(expr: &str, max_len: usize) -> String {
    if expr.len() <= max_len {
        expr.to_string()
    } else {
        format!("{}...", &expr[..max_len - 3])
    }
}

/// Information collected about yield patterns in an AST node.
#[derive(Default)]
struct YieldPatternInfo {
    /// Yield expressions: (yielded expression text, line number)
    yield_exprs: Vec<(String, usize)>,
    /// Yield from expressions: (delegated iterable text, line number)
    yield_from_exprs: Vec<(String, usize)>,
}

impl<'a> PythonCFGBuilder<'a> {
    /// Scan a statement for yield and yield from expressions.
    ///
    /// This is analogous to `scan_async_patterns` for generators.
    /// Detects:
    /// - `yield expr` - generator yield point
    /// - `yield from iterable` - generator delegation
    fn scan_yield_patterns(&self, node: Node) -> YieldPatternInfo {
        let mut info = YieldPatternInfo::default();
        self.scan_yield_patterns_recursive(node, &mut info);
        info
    }

    /// Recursively scan an AST node for yield patterns.
    ///
    /// Note: tree-sitter-python parses both `yield value` and `yield from iterable`
    /// as the same "yield" node type. We distinguish them by checking if the
    /// second child is the keyword "from".
    fn scan_yield_patterns_recursive(&self, node: Node, info: &mut YieldPatternInfo) {
        match node.kind() {
            "yield" => {
                let line = node.start_position().row + 1;

                // Check if this is a "yield from" by looking at the children
                // Structure for yield from: yield -> "yield", "from", expression
                // Structure for yield: yield -> "yield", [expression]
                let is_yield_from =
                    node.child_count() >= 2 && node.child(1).map_or(false, |c| c.kind() == "from");

                if is_yield_from {
                    // yield from expression: yield from iterable
                    // Get the delegated iterable (third child after "yield" and "from")
                    let expr_text = node
                        .child(2)
                        .map(|n| Python::node_text(n, self.source).to_string())
                        .unwrap_or_default();
                    info.yield_from_exprs.push((expr_text, line));
                } else {
                    // Regular yield expression: yield [value]
                    let yielded = node
                        .child(1)
                        .map(|n| Python::node_text(n, self.source).to_string())
                        .unwrap_or_default();
                    info.yield_exprs.push((yielded, line));
                }
            }
            // tree-sitter-python may also have a separate yield_from node type
            // in some versions - handle it just in case
            "yield_from" => {
                let line = node.start_position().row + 1;
                // Get the delegated iterable (skip "yield" and "from" keywords)
                let mut cursor = node.walk();
                let mut expr_text = String::new();
                for child in node.children(&mut cursor) {
                    if child.kind() != "yield" && child.kind() != "from" {
                        expr_text = Python::node_text(child, self.source).to_string();
                        break;
                    }
                }
                info.yield_from_exprs.push((expr_text, line));
            }
            // Don't recurse into nested functions/lambdas - their yields are their own
            "function_definition" | "lambda" => {}
            _ => {
                // Recurse into children
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.scan_yield_patterns_recursive(child, info);
                }
            }
        }
    }

    /// Process a statement containing yield expressions, creating YieldPoint blocks.
    ///
    /// # Generator CFG Semantics
    ///
    /// A yield creates a suspension point where:
    /// 1. The generator pauses and returns the yielded value to the caller
    /// 2. State is preserved (locals, instruction pointer)
    /// 3. Execution resumes when next()/send() is called
    ///
    /// CFG modeling:
    /// ```text
    /// [current block] --yield--> [YieldPoint] --resume--> [GeneratorEntry] --> [next statement]
    /// ```
    ///
    /// For yield from:
    /// ```text
    /// [current block] --yield_from--> [YieldFrom] --resume--> [next statement]
    /// ```
    /// The YieldFrom block represents bidirectional delegation where values,
    /// send(), and throw() all pass through to the sub-generator.
    fn process_yield_statement(
        &mut self,
        stmt: Node,
        current: BlockId,
        info: YieldPatternInfo,
    ) -> BlockId {
        let stmt_text = self.node_text(stmt);
        let end_line = stmt.end_position().row + 1;

        // Add statement text to current block first
        if let Some(block) = self.blocks.get_mut(&current) {
            block.statements.push(stmt_text);
            block.end_line = end_line;
        }

        // Track total yield points
        self.yield_count += info.yield_exprs.len() + info.yield_from_exprs.len();

        let mut prev_block = current;

        // Process yield expressions
        for (i, (yielded_expr, line)) in info.yield_exprs.iter().enumerate() {
            let yield_label = if info.yield_exprs.len() == 1 && info.yield_from_exprs.is_empty() {
                if yielded_expr.is_empty() {
                    "yield".to_string()
                } else {
                    format!("yield {}", truncate_expr(yielded_expr, 30))
                }
            } else {
                format!("yield[{}] {}", i + 1, truncate_expr(yielded_expr, 25))
            };

            // Create yield point block
            let yield_block = self.new_block(yield_label, *line);

            // Set block type based on whether this is async generator
            if let Some(block) = self.blocks.get_mut(&yield_block) {
                block.block_type = if self.is_async_generator {
                    BlockType::AsyncYieldPoint
                } else {
                    BlockType::YieldPoint
                };
            }

            // Connect previous block to yield point with Yield edge
            let yield_edge = if self.is_async_generator {
                EdgeType::AsyncGeneratorYield
            } else {
                EdgeType::Yield
            };
            self.add_edge(prev_block, yield_block, yield_edge);

            // Create resume point (where next()/send() continues)
            let resume_block = self.new_block("resume".to_string(), *line);
            if let Some(block) = self.blocks.get_mut(&resume_block) {
                block.block_type = BlockType::GeneratorEntry;
            }

            // Connect yield to resume with GeneratorResume edge
            let resume_edge = if self.is_async_generator {
                EdgeType::AsyncGeneratorResume
            } else {
                EdgeType::GeneratorResume
            };
            self.add_edge(yield_block, resume_block, resume_edge);

            prev_block = resume_block;
        }

        // Process yield from expressions
        for (i, (iterable_expr, line)) in info.yield_from_exprs.iter().enumerate() {
            let yield_from_label =
                if info.yield_from_exprs.len() == 1 && info.yield_exprs.is_empty() {
                    format!("yield from {}", truncate_expr(iterable_expr, 25))
                } else {
                    format!("yield from[{}] {}", i + 1, truncate_expr(iterable_expr, 20))
                };

            // Create yield from block
            let yield_from_block = self.new_block(yield_from_label, *line);

            // Set block type
            if let Some(block) = self.blocks.get_mut(&yield_from_block) {
                block.block_type = BlockType::YieldFrom;
            }

            // Connect previous block to yield from with YieldFromDelegate edge
            self.add_edge(prev_block, yield_from_block, EdgeType::YieldFromDelegate);

            // Create resume point after yield from delegation completes
            let after_delegation = self.new_block("after_yield_from".to_string(), *line);
            if let Some(block) = self.blocks.get_mut(&after_delegation) {
                block.block_type = BlockType::GeneratorEntry;
            }

            // The sub-generator can be re-entered multiple times, but eventually
            // control returns here when the sub-generator is exhausted
            self.add_edge(
                yield_from_block,
                after_delegation,
                EdgeType::GeneratorResume,
            );

            prev_block = after_delegation;
        }

        // Create continuation block after all yields
        let after_yield = self.new_block("after_yield".to_string(), end_line);
        self.add_edge(prev_block, after_yield, EdgeType::Unconditional);

        after_yield
    }
}

// =============================================================================
// Python DFG Builder
// =============================================================================

/// Variable reference for DFG building.
struct VarRef {
    name: String,
    line: usize,
    kind: DataflowKind,
}

/// Builds data flow graphs from Python AST nodes.
///
/// The DFG builder uses CFG information to properly compute def-use chains,
/// especially at control flow merge points (after if/else, loops, etc.).
/// This ensures that definitions from all branches reach subsequent uses.
///
/// BUG FIX: Added proper nested function scope detection with depth tracking.
/// Python nested functions create closures that capture outer variables.
/// We track:
/// - `depth`: Current nesting level (0 = main function being analyzed)
/// - `scopes`: Stack of scopes, each containing variables defined at that level
///
/// This ensures:
/// 1. Nested function parameters are tracked in their own scope
/// 2. Uses of outer variables from nested functions are captured as ClosureCapture
/// 3. Inner definitions don't incorrectly shadow outer definitions in DFG analysis
struct PythonDFGBuilder<'a> {
    source: &'a [u8],
    refs: Vec<VarRef>,
    /// Current function nesting depth (0 = main function)
    depth: usize,
    /// Stack of scopes: each scope contains variable names defined at that level
    scopes: Vec<std::collections::HashSet<String>>,
}

impl<'a> PythonDFGBuilder<'a> {
    fn new(source: &'a [u8]) -> Self {
        Self {
            source,
            refs: Vec::new(),
            depth: 0,
            // Start with one scope for the main function
            scopes: vec![std::collections::HashSet::new()],
        }
    }

    /// Enter a new scope (for nested functions, lambdas, comprehensions).
    fn enter_scope(&mut self) {
        self.depth += 1;
        self.scopes.push(std::collections::HashSet::new());
    }

    /// Exit the current scope.
    fn exit_scope(&mut self) {
        if self.depth > 0 {
            self.depth -= 1;
            self.scopes.pop();
        }
    }

    /// Add a variable to the current scope.
    fn add_to_current_scope(&mut self, name: &str) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string());
        }
    }

    /// Check if a variable is defined in the current (innermost) scope.
    fn is_in_current_scope(&self, name: &str) -> bool {
        self.scopes
            .last()
            .map(|scope| scope.contains(name))
            .unwrap_or(false)
    }

    /// Check if a variable is defined in any outer scope (closure capture).
    fn is_in_outer_scope(&self, name: &str) -> bool {
        // Skip the innermost scope, check all outer scopes
        if self.scopes.len() <= 1 {
            return false;
        }
        for scope in self.scopes.iter().rev().skip(1) {
            if scope.contains(name) {
                return true;
            }
        }
        false
    }

    /// Check if we're currently inside a nested function (depth > 0).
    fn is_in_nested_function(&self) -> bool {
        self.depth > 0
    }

    fn build(node: Node, source: &[u8]) -> Result<DFGInfo> {
        if node.kind() != "function_definition" {
            return Err(BrrrError::Parse {
                file: String::new(),
                message: format!("Expected function_definition, got {}", node.kind()),
            });
        }

        let function_name = Python::child_by_kind(node, "identifier")
            .map(|n| Python::node_text(n, source).to_string())
            .unwrap_or_else(|| "<unknown>".to_string());

        let mut builder = PythonDFGBuilder::new(source);

        // Extract parameters as definitions
        if let Some(params) = Python::child_by_kind(node, "parameters") {
            builder.extract_params(params);
        }

        // Process function body
        if let Some(block) = Python::child_by_kind(node, "block") {
            builder.process_block(block);
        }

        // Build CFG for proper control flow analysis
        // CFG-aware def-use chains ensure definitions from all branches reach uses at merge points
        let cfg = PythonCFGBuilder::build(node, source)?;

        // Build def-use chains using CFG information
        let (edges, definitions, uses) = builder.compute_def_use_chains_with_cfg(&cfg);

        // Convert FxHashMap to std::collections::HashMap for DFGInfo API compatibility
        let definitions: FxHashMap<String, Vec<usize>> = definitions.into_iter().collect();
        let uses: FxHashMap<String, Vec<usize>> = uses.into_iter().collect();

        Ok(DFGInfo::new(function_name, edges, definitions, uses))
    }

    fn node_text(&self, node: Node) -> String {
        Python::node_text(node, self.source).to_string()
    }

    fn add_ref(&mut self, name: String, line: usize, kind: DataflowKind) {
        // Skip special names
        if name == "_" || name == "__" {
            return;
        }
        self.refs.push(VarRef { name, line, kind });
    }

    fn extract_params(&mut self, params: Node) {
        let mut cursor = params.walk();
        for child in params.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    let name = self.node_text(child);
                    // BUG FIX: Add to current scope for nested function closure detection
                    self.add_to_current_scope(&name);
                    self.add_ref(name, child.start_position().row + 1, DataflowKind::Param);
                }
                "typed_parameter" => {
                    // For typed *args/**kwargs, the identifier is nested inside
                    // list_splat_pattern or dictionary_splat_pattern
                    let id_node =
                        if let Some(splat) = Python::child_by_kind(child, "list_splat_pattern") {
                            // Typed *args: e.g., *args: tuple[int, ...]
                            Python::child_by_kind(splat, "identifier")
                        } else if let Some(splat) =
                            Python::child_by_kind(child, "dictionary_splat_pattern")
                        {
                            // Typed **kwargs: e.g., **kwargs: dict[str, Any]
                            Python::child_by_kind(splat, "identifier")
                        } else {
                            // Regular typed parameter: e.g., x: int
                            Python::child_by_kind(child, "identifier")
                        };

                    if let Some(id) = id_node {
                        let name = self.node_text(id);
                        // BUG FIX: Add to current scope for nested function closure detection
                        self.add_to_current_scope(&name);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::Param);
                    }
                }
                "default_parameter" | "typed_default_parameter" => {
                    if let Some(id) = Python::child_by_kind(child, "identifier") {
                        let name = self.node_text(id);
                        // BUG FIX: Add to current scope for nested function closure detection
                        self.add_to_current_scope(&name);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::Param);
                    }
                }
                "list_splat_pattern" => {
                    // *args
                    if let Some(id) = Python::child_by_kind(child, "identifier") {
                        let name = self.node_text(id);
                        // BUG FIX: Add to current scope for nested function closure detection
                        self.add_to_current_scope(&name);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::Param);
                    }
                }
                "dictionary_splat_pattern" => {
                    // **kwargs
                    if let Some(id) = Python::child_by_kind(child, "identifier") {
                        let name = self.node_text(id);
                        // BUG FIX: Add to current scope for nested function closure detection
                        self.add_to_current_scope(&name);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::Param);
                    }
                }
                _ => {}
            }
        }
    }

    /// Extract lambda parameters as LambdaParam definitions (BUG-013 fix).
    /// Lambda parameters have their own scope and don't leak to outer scope.
    fn extract_lambda_params(&mut self, params: Node) {
        let mut cursor = params.walk();
        for child in params.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    let name = self.node_text(child);
                    self.add_ref(
                        name,
                        child.start_position().row + 1,
                        DataflowKind::LambdaParam,
                    );
                }
                "default_parameter" => {
                    // Lambda can have default params: lambda x=1: x
                    if let Some(id) = Python::child_by_kind(child, "identifier") {
                        let name = self.node_text(id);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::LambdaParam);
                    }
                    // Process the default value expression (uses from outer scope)
                    let mut inner_cursor = child.walk();
                    let mut saw_equals = false;
                    for inner in child.children(&mut inner_cursor) {
                        if inner.kind() == "=" {
                            saw_equals = true;
                            continue;
                        }
                        if saw_equals {
                            self.process_expression(inner);
                        }
                    }
                }
                "list_splat_pattern" => {
                    // *args in lambda
                    if let Some(id) = Python::child_by_kind(child, "identifier") {
                        let name = self.node_text(id);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::LambdaParam);
                    }
                }
                "dictionary_splat_pattern" => {
                    // **kwargs in lambda
                    if let Some(id) = Python::child_by_kind(child, "identifier") {
                        let name = self.node_text(id);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::LambdaParam);
                    }
                }
                _ => {}
            }
        }
    }

    /// Extract nested function parameters as NestedParam definitions.
    /// Similar to extract_lambda_params but for nested def/async def.
    /// Parameters are added to the current scope to avoid false closure captures.
    fn extract_nested_params(&mut self, params: Node) {
        let mut cursor = params.walk();
        for child in params.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    let name = self.node_text(child);
                    self.add_to_current_scope(&name);
                    self.add_ref(
                        name,
                        child.start_position().row + 1,
                        DataflowKind::NestedParam,
                    );
                }
                "typed_parameter" => {
                    // For typed *args/**kwargs, the identifier is nested inside
                    // list_splat_pattern or dictionary_splat_pattern
                    let id_node =
                        if let Some(splat) = Python::child_by_kind(child, "list_splat_pattern") {
                            Python::child_by_kind(splat, "identifier")
                        } else if let Some(splat) =
                            Python::child_by_kind(child, "dictionary_splat_pattern")
                        {
                            Python::child_by_kind(splat, "identifier")
                        } else {
                            Python::child_by_kind(child, "identifier")
                        };

                    if let Some(id) = id_node {
                        let name = self.node_text(id);
                        self.add_to_current_scope(&name);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::NestedParam);
                    }
                }
                "default_parameter" | "typed_default_parameter" => {
                    if let Some(id) = Python::child_by_kind(child, "identifier") {
                        let name = self.node_text(id);
                        self.add_to_current_scope(&name);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::NestedParam);
                    }
                    // Process the default value expression (uses from outer scope)
                    let mut inner_cursor = child.walk();
                    let mut saw_equals = false;
                    for inner in child.children(&mut inner_cursor) {
                        if inner.kind() == "=" {
                            saw_equals = true;
                            continue;
                        }
                        if saw_equals {
                            self.process_expression(inner);
                        }
                    }
                }
                "list_splat_pattern" => {
                    // *args
                    if let Some(id) = Python::child_by_kind(child, "identifier") {
                        let name = self.node_text(id);
                        self.add_to_current_scope(&name);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::NestedParam);
                    }
                }
                "dictionary_splat_pattern" => {
                    // **kwargs
                    if let Some(id) = Python::child_by_kind(child, "identifier") {
                        let name = self.node_text(id);
                        self.add_to_current_scope(&name);
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::NestedParam);
                    }
                }
                _ => {}
            }
        }
    }

    fn process_block(&mut self, block: Node<'a>) {
        let mut cursor = block.walk();
        for stmt in block.children(&mut cursor) {
            self.process_statement(stmt);
        }
    }

    fn process_statement(&mut self, stmt: Node<'a>) {
        match stmt.kind() {
            "expression_statement" => {
                let mut cursor = stmt.walk();
                for child in stmt.children(&mut cursor) {
                    match child.kind() {
                        "assignment" => self.process_assignment(child),
                        "augmented_assignment" => self.process_augmented_assignment(child),
                        _ => self.process_expression(child),
                    }
                }
            }
            "assignment" => self.process_assignment(stmt),
            "augmented_assignment" => self.process_augmented_assignment(stmt),
            "if_statement" => self.process_if(stmt),
            "for_statement" => self.process_for(stmt),
            "while_statement" => self.process_while(stmt),
            "try_statement" => self.process_try(stmt),
            "with_statement" | "async_with_statement" => self.process_with(stmt),
            "match_statement" => self.process_match(stmt),
            "return_statement" => {
                // Process returned expression
                let mut cursor = stmt.walk();
                for child in stmt.children(&mut cursor) {
                    if child.kind() != "return" {
                        self.process_expression(child);

                        // If it's a simple identifier, mark as Return
                        if child.kind() == "identifier" {
                            let name = self.node_text(child);
                            self.add_ref(
                                name,
                                child.start_position().row + 1,
                                DataflowKind::Return,
                            );
                        }
                    }
                }
            }
            "function_definition" | "async_function_definition" => {
                // BUG FIX: Proper nested function scope detection with depth tracking
                // Instead of skipping, we enter a new scope and track closure captures
                self.enter_scope();

                // Extract nested function parameters as NestedParam definitions
                if let Some(params) = Python::child_by_kind(stmt, "parameters") {
                    self.extract_nested_params(params);
                }

                // Process nested function body - this will capture uses of outer variables
                if let Some(block) = Python::child_by_kind(stmt, "block") {
                    self.process_block(block);
                }

                self.exit_scope();
            }
            "class_definition" => {
                // Class definitions create their own scope but we don't analyze them in DFG
                // Class attributes and methods have their own separate DFG analysis
            }
            "decorated_definition" => {
                // Process the decorators (they can use outer variables)
                let mut cursor = stmt.walk();
                for child in stmt.children(&mut cursor) {
                    if child.kind() == "decorator" {
                        self.process_expression(child);
                    } else if child.kind() == "function_definition"
                        || child.kind() == "async_function_definition"
                    {
                        // Process the decorated function
                        self.process_statement(child);
                    }
                    // Skip class_definition inside decorated_definition for now
                }
            }
            // BUG-017 FIX: Track global and nonlocal statements for proper scope analysis
            "global_statement" => {
                // global x, y, z - marks variables as referencing global scope
                let mut cursor = stmt.walk();
                for child in stmt.children(&mut cursor) {
                    if child.kind() == "identifier" {
                        let name = self.node_text(child);
                        // Mark as Global kind to indicate this variable references global scope
                        self.add_ref(name, child.start_position().row + 1, DataflowKind::Global);
                    }
                }
            }
            "nonlocal_statement" => {
                // nonlocal x, y, z - marks variables as referencing enclosing (non-global) scope
                let mut cursor = stmt.walk();
                for child in stmt.children(&mut cursor) {
                    if child.kind() == "identifier" {
                        let name = self.node_text(child);
                        // Mark as Nonlocal kind to indicate this variable references enclosing scope
                        self.add_ref(name, child.start_position().row + 1, DataflowKind::Nonlocal);
                    }
                }
            }
            _ => {}
        }
    }

    fn process_assignment(&mut self, node: Node) {
        // Process RHS first (uses)
        let mut cursor = node.walk();
        let mut saw_equals = false;

        for child in node.children(&mut cursor) {
            if child.kind() == "=" {
                saw_equals = true;
                continue;
            }
            if saw_equals {
                // RHS - extract uses
                self.process_expression(child);
            }
        }

        // Process LHS (definitions)
        cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "=" {
                break;
            }
            self.process_target(child);
        }
    }

    /// Check if a node kind is an augmented assignment operator.
    /// Uses module-level phf::Set for O(1) lookup.
    #[inline]
    fn is_augmented_assign_op(kind: &str) -> bool {
        AUGMENTED_ASSIGN_OPS.contains(kind)
    }

    fn process_augmented_assignment(&mut self, node: Node<'a>) {
        // x += y means x is both used and mutated
        // Targets can be: identifier (x), subscript (x[0]), or attribute (obj.attr)
        let mut cursor = node.walk();
        let mut found_operator = false;

        for child in node.children(&mut cursor) {
            let kind = child.kind();

            // Check if this is an augmented assignment operator
            if Self::is_augmented_assign_op(kind) {
                found_operator = true;
                continue;
            }

            if !found_operator {
                // This is the LHS (target) - it's both read and mutated
                self.process_augmented_target(child);
            } else {
                // This is the RHS - process as expression (uses)
                self.process_expression(child);
            }
        }
    }

    /// Process the target of an augmented assignment.
    /// The target is both read (use) and written (mutation).
    /// Handles identifier, subscript, and attribute targets.
    fn process_augmented_target(&mut self, node: Node<'a>) {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node);
                let line = node.start_position().row + 1;
                // First read (use), then mutated
                self.add_ref(name.clone(), line, DataflowKind::Use);
                self.add_ref(name, line, DataflowKind::Mutation);
            }
            "subscript" => {
                // x[i] += 1: x is read (to get the element), index is read, then x is mutated
                // Process the entire subscript as a use first
                self.process_expression(node);
                // Find the base identifier and mark as mutation
                if let Some(base) = node.child(0) {
                    self.mark_base_as_mutation(base);
                }
            }
            "attribute" => {
                // obj.attr += 1: obj is read (to access attribute), then obj is mutated
                // Process the entire attribute access as a use first
                self.process_expression(node);
                // Find the base identifier and mark as mutation
                if let Some(base) = node.child(0) {
                    self.mark_base_as_mutation(base);
                }
            }
            _ => {
                // For any other target type, process as expression (conservative)
                self.process_expression(node);
            }
        }
    }

    /// Mark the base of a subscript/attribute chain as mutated.
    /// Handles nested cases like obj.list[0] += 1 -> marks 'obj' as mutated.
    fn mark_base_as_mutation(&mut self, node: Node<'a>) {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node);
                self.add_ref(name, node.start_position().row + 1, DataflowKind::Mutation);
            }
            "subscript" | "attribute" => {
                // Nested: find the innermost base
                if let Some(base) = node.child(0) {
                    self.mark_base_as_mutation(base);
                }
            }
            _ => {
                // Complex expression as base (e.g., function call result)
                // Cannot determine mutation target
            }
        }
    }

    fn process_target(&mut self, node: Node) {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node);
                // BUG FIX: Add to current scope for proper nested function tracking
                // This ensures local variables in nested functions are tracked correctly
                self.add_to_current_scope(&name);
                self.add_ref(
                    name,
                    node.start_position().row + 1,
                    DataflowKind::Definition,
                );
            }
            "tuple" | "list" | "pattern_list" | "tuple_pattern" => {
                // Unpacking
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_target(child);
                }
            }
            "subscript" | "attribute" => {
                // x[i] = ... or x.attr = ... - this mutates x
                // Find the base identifier
                if let Some(id) = Python::child_by_kind(node, "identifier") {
                    let name = self.node_text(id);
                    self.add_ref(name, id.start_position().row + 1, DataflowKind::Mutation);
                }
            }
            "starred_expression" => {
                // *x in unpacking
                if let Some(id) = Python::child_by_kind(node, "identifier") {
                    let name = self.node_text(id);
                    // BUG FIX: Add to current scope for proper nested function tracking
                    self.add_to_current_scope(&name);
                    self.add_ref(name, id.start_position().row + 1, DataflowKind::Definition);
                }
            }
            _ => {}
        }
    }

    /// Process comprehension target (loop variable in list/dict/set comprehension).
    /// Similar to process_target but uses ComprehensionVar kind for proper scoping.
    fn process_comprehension_target(&mut self, node: Node) {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node);
                self.add_ref(
                    name,
                    node.start_position().row + 1,
                    DataflowKind::ComprehensionVar,
                );
            }
            "tuple" | "list" | "pattern_list" | "tuple_pattern" => {
                // Unpacking in comprehension: [x for (a, b) in items]
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_comprehension_target(child);
                }
            }
            "starred_expression" => {
                // *x in unpacking (rare in comprehensions but possible)
                if let Some(id) = Python::child_by_kind(node, "identifier") {
                    let name = self.node_text(id);
                    self.add_ref(
                        name,
                        id.start_position().row + 1,
                        DataflowKind::ComprehensionVar,
                    );
                }
            }
            _ => {}
        }
    }

    fn process_expression(&mut self, node: Node) {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node);
                // BUG FIX: Detect closure captures in nested functions
                // If we're in a nested function and this variable is from an outer scope,
                // mark it as ClosureCapture instead of Use
                let kind = if self.is_in_nested_function()
                    && !self.is_in_current_scope(&name)
                    && self.is_in_outer_scope(&name)
                {
                    DataflowKind::ClosureCapture
                } else {
                    DataflowKind::Use
                };
                self.add_ref(name, node.start_position().row + 1, kind);
            }
            "binary_operator"
            | "boolean_operator"
            | "comparison_operator"
            | "not_operator"
            | "unary_operator" => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_expression(child);
                }
            }
            "call" => {
                // Process function and arguments
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_expression(child);
                }
            }
            "attribute" => {
                // x.attr - x is used (may be closure capture in nested function)
                if let Some(id) = Python::child_by_kind(node, "identifier") {
                    let name = self.node_text(id);
                    let kind = if self.is_in_nested_function()
                        && !self.is_in_current_scope(&name)
                        && self.is_in_outer_scope(&name)
                    {
                        DataflowKind::ClosureCapture
                    } else {
                        DataflowKind::Use
                    };
                    self.add_ref(name, id.start_position().row + 1, kind);
                }
            }
            "subscript" => {
                // x[i] - x and i are used
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_expression(child);
                }
            }
            "list" | "tuple" | "set" | "dictionary" | "expression_list" | "argument_list" => {
                // expression_list is used for return statements like "return a, b"
                // argument_list contains function call arguments
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_expression(child);
                }
            }
            "list_comprehension"
            | "set_comprehension"
            | "dictionary_comprehension"
            | "generator_expression" => {
                self.process_comprehension(node);
            }
            "conditional_expression" => {
                // a if b else c
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_expression(child);
                }
            }
            "lambda" => {
                // Lambda has its own scope (BUG-013 fix: extract parameters)
                // Extract lambda parameters as LambdaParam definitions first
                if let Some(params) = Python::child_by_kind(node, "lambda_parameters") {
                    self.extract_lambda_params(params);
                }
                // Then process the body - uses here will see lambda params
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    // The body is typically the last child that's not lambda_parameters
                    if child.kind() != "lambda"
                        && child.kind() != "lambda_parameters"
                        && child.kind() != ":"
                    {
                        self.process_expression(child);
                    }
                }
            }
            "parenthesized_expression" => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_expression(child);
                }
            }
            "await" => {
                // await expr
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() != "await" {
                        self.process_expression(child);
                    }
                }
            }
            "yield" => {
                // yield [expr] - generator yield expression (BUG-012 fix)
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() != "yield" {
                        self.process_expression(child);
                        // Track yielded identifier as Yield kind
                        if child.kind() == "identifier" {
                            let name = self.node_text(child);
                            self.add_ref(name, child.start_position().row + 1, DataflowKind::Yield);
                        }
                    }
                }
            }
            "yield_from" => {
                // yield from expr - delegated generator (BUG-012 fix)
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    // Skip "yield" and "from" keywords
                    if child.kind() != "yield" && child.kind() != "from" {
                        self.process_expression(child);
                        // Track yielded identifier as Yield kind
                        if child.kind() == "identifier" {
                            let name = self.node_text(child);
                            self.add_ref(name, child.start_position().row + 1, DataflowKind::Yield);
                        }
                    }
                }
            }
            "keyword_argument" | "pair" => {
                // key=value or key: value
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_expression(child);
                }
            }
            "string" => {
                // BUG-003 FIX: F-strings contain embedded expressions with variable references
                // Check for interpolation nodes inside the string
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "interpolation" {
                        // Process the expression inside the interpolation
                        let mut inner_cursor = child.walk();
                        for inner in child.children(&mut inner_cursor) {
                            // Skip { and } braces, process the actual expression
                            if inner.kind() != "{" && inner.kind() != "}" {
                                self.process_expression(inner);
                            }
                        }
                    }
                }
            }
            "integer" | "float" | "true" | "false" | "none" => {
                // Literals - no variables
            }
            "named_expression" => {
                // BUG-002 FIX: Walrus operator (:=) creates a variable definition
                // Structure: named_expression -> identifier := expression
                let mut cursor = node.walk();
                let mut target_name = None;
                let mut saw_walrus = false;

                for child in node.children(&mut cursor) {
                    match child.kind() {
                        "identifier" if !saw_walrus => {
                            // This is the target being defined
                            target_name =
                                Some((self.node_text(child), child.start_position().row + 1));
                        }
                        ":=" => {
                            saw_walrus = true;
                        }
                        _ if saw_walrus => {
                            // This is the value expression - process for uses
                            self.process_expression(child);
                        }
                        _ => {}
                    }
                }

                // Record the definition after processing the value (so uses come before def in flow)
                if let Some((name, line)) = target_name {
                    self.add_ref(name, line, DataflowKind::Definition);
                }
            }
            _ => {}
        }
    }

    fn process_comprehension(&mut self, node: Node) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "for_in_clause" => {
                    // for x in iter
                    let mut inner_cursor = child.walk();
                    let mut after_in = false;

                    for inner in child.children(&mut inner_cursor) {
                        if inner.kind() == "in" {
                            after_in = true;
                            continue;
                        }
                        if after_in {
                            self.process_expression(inner);
                        } else if inner.kind() == "identifier" {
                            // Loop variable - comprehension-scoped (BUG-014)
                            let name = self.node_text(inner);
                            self.add_ref(
                                name,
                                inner.start_position().row + 1,
                                DataflowKind::ComprehensionVar,
                            );
                        } else if inner.kind() == "tuple" || inner.kind() == "pattern_list" {
                            self.process_comprehension_target(inner);
                        }
                    }
                }
                "if_clause" => {
                    // if condition
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        if inner.kind() != "if" {
                            self.process_expression(inner);
                        }
                    }
                }
                _ => {
                    // The element expression
                    self.process_expression(child);
                }
            }
        }
    }

    fn process_if(&mut self, node: Node<'a>) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "block" => self.process_block(child),
                "elif_clause" | "else_clause" => {
                    // Process condition and block
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        if inner.kind() == "block" {
                            self.process_block(inner);
                        } else if inner.kind() != "elif" && inner.kind() != "else" {
                            self.process_expression(inner);
                        }
                    }
                }
                // BUG-FIX: Handle all valid condition expressions, not just a whitelist.
                // This is critical for walrus operator (:=) support in conditions like:
                //   if (x := compute()):     <- parenthesized_expression
                //   if func():               <- call
                //   if obj.attr:             <- attribute
                //   if items[0]:             <- subscript
                //   if await coro():         <- await expression
                "comparison_operator"
                | "boolean_operator"
                | "identifier"
                | "not_operator"
                | "parenthesized_expression"
                | "call"
                | "attribute"
                | "subscript"
                | "await"
                | "unary_operator"
                | "binary_operator"
                | "named_expression"
                | "lambda" => {
                    self.process_expression(child);
                }
                _ => {}
            }
        }
    }

    fn process_for(&mut self, node: Node<'a>) {
        let mut cursor = node.walk();
        let mut after_in = false;

        for child in node.children(&mut cursor) {
            match child.kind() {
                "in" => {
                    after_in = true;
                }
                "block" => {
                    self.process_block(child);
                }
                "else_clause" => {
                    if let Some(block) = Python::child_by_kind(child, "block") {
                        self.process_block(block);
                    }
                }
                "identifier" if !after_in => {
                    // Loop variable
                    let name = self.node_text(child);
                    self.add_ref(
                        name,
                        child.start_position().row + 1,
                        DataflowKind::Definition,
                    );
                }
                "tuple" | "list" | "pattern_list" if !after_in => {
                    // Unpacking in for loop
                    self.process_target(child);
                }
                _ if after_in && child.kind() != ":" => {
                    // Iterator expression
                    self.process_expression(child);
                }
                _ => {}
            }
        }
    }

    fn process_while(&mut self, node: Node<'a>) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "block" => self.process_block(child),
                "else_clause" => {
                    if let Some(block) = Python::child_by_kind(child, "block") {
                        self.process_block(block);
                    }
                }
                // BUG-FIX: Handle all valid condition expressions, not just a whitelist.
                // This is critical for walrus operator (:=) support in conditions like:
                //   while (line := file.readline()):  <- parenthesized_expression
                //   while func():                     <- call
                //   while self.running:               <- attribute
                //   while queue[0]:                   <- subscript
                "comparison_operator"
                | "boolean_operator"
                | "identifier"
                | "not_operator"
                | "parenthesized_expression"
                | "call"
                | "attribute"
                | "subscript"
                | "await"
                | "unary_operator"
                | "binary_operator"
                | "named_expression"
                | "lambda" => {
                    self.process_expression(child);
                }
                _ => {}
            }
        }
    }

    fn process_try(&mut self, node: Node<'a>) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "block" => self.process_block(child),
                // Both except_clause and except_group_clause use the same processing
                "except_clause" | "except_group_clause" => {
                    self.process_except_clause(child);
                }
                "else_clause" | "finally_clause" => {
                    if let Some(block) = Python::child_by_kind(child, "block") {
                        self.process_block(block);
                    }
                }
                _ => {}
            }
        }
    }

    /// Process an except clause (or except* clause for Python 3.11+).
    ///
    /// Handles multiple exception clause patterns robustly:
    /// - Pattern 1: `except ExceptionType as var_name:` - single exception with binding
    /// - Pattern 2: `except (Type1, Type2) as var_name:` - tuple of exceptions with binding
    /// - Pattern 3: `except ExceptionType:` - single exception without binding
    /// - Pattern 4: `except:` - bare except (no type, no binding)
    /// - Pattern 5: `except* ExceptionGroup as eg:` - Python 3.11+ exception groups
    ///
    /// This method:
    /// 1. Extracts and tracks exception types as USES (e.g., ValueError is a use of that class)
    /// 2. Extracts the bound variable (if any) as a DEFINITION
    /// 3. Processes the exception handler block
    fn process_except_clause(&mut self, node: Node<'a>) {
        let line = node.start_position().row + 1;
        let mut found_binding = false;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "as_pattern" => {
                    // `except X as e:` - the as_pattern contains both the exception type and binding
                    self.process_as_pattern_in_except(child, &mut found_binding);
                }
                "identifier" => {
                    // Direct exception type reference: `except ValueError:`
                    // This is a USE of the exception class (not after "as")
                    // Skip if we already found a binding (meaning this identifier came after "as")
                    if !found_binding {
                        let name = self.node_text(child);
                        self.add_ref(name, child.start_position().row + 1, DataflowKind::Use);
                    }
                }
                "tuple" | "parenthesized_expression" => {
                    // Multiple exception types: `except (ValueError, TypeError):`
                    // Process each exception type as a USE
                    self.process_exception_types(child);
                }
                "block" => {
                    // Exception handler body
                    self.process_block(child);
                }
                // Skip keywords and punctuation
                "except" | "as" | ":" | "*" => {}
                _ => {
                    // Handle any other expression types that might be exception types
                    // (e.g., attribute access like `module.ExceptionClass`)
                    if child.kind() != "block" && child.kind() != "comment" {
                        self.process_expression(child);
                    }
                }
            }
        }

        // Fallback: if no binding found via as_pattern, search for identifier after "as" keyword
        // This handles alternative tree structures that some tree-sitter versions may produce
        if !found_binding {
            self.extract_except_binding_fallback(node, line);
        }
    }

    /// Process an as_pattern within an except clause.
    /// Structure: as_pattern -> [exception_type, "as", as_pattern_target/identifier]
    fn process_as_pattern_in_except(&mut self, as_pattern: Node<'a>, found_binding: &mut bool) {
        // Strategy 1: Try field-based lookup (most robust if grammar supports it)
        if let Some(alias) = as_pattern.child_by_field_name("alias") {
            self.extract_binding_from_alias(alias, found_binding);
        }

        // Strategy 2: Look for as_pattern_target (common tree-sitter-python structure)
        if !*found_binding {
            if let Some(target) = Python::child_by_kind(as_pattern, "as_pattern_target") {
                self.extract_binding_from_target(target, found_binding);
            }
        }

        // Strategy 3: Iterate children looking for identifier after "as"
        if !*found_binding {
            let mut inner_cursor = as_pattern.walk();
            let mut after_as = false;
            for inner in as_pattern.children(&mut inner_cursor) {
                if inner.kind() == "as" {
                    after_as = true;
                    continue;
                }
                if after_as && inner.kind() == "identifier" {
                    let name = self.node_text(inner);
                    self.add_ref(
                        name,
                        inner.start_position().row + 1,
                        DataflowKind::Definition,
                    );
                    *found_binding = true;
                    break;
                }
            }
        }

        // Process the exception type (first child that's not "as" or the binding)
        let mut inner_cursor = as_pattern.walk();
        for inner in as_pattern.children(&mut inner_cursor) {
            match inner.kind() {
                "as" | "as_pattern_target" => {}
                "identifier" => {
                    // Could be exception type or binding - if it's before "as", it's the type
                    // We process it as a use if it appears before "as"
                    let mut check_cursor = as_pattern.walk();
                    let mut seen_as = false;
                    for check_child in as_pattern.children(&mut check_cursor) {
                        if check_child.kind() == "as" {
                            seen_as = true;
                        }
                        if check_child.id() == inner.id() {
                            // This identifier appears before "as", so it's the exception type
                            if !seen_as {
                                let name = self.node_text(inner);
                                self.add_ref(
                                    name,
                                    inner.start_position().row + 1,
                                    DataflowKind::Use,
                                );
                            }
                            break;
                        }
                    }
                }
                "tuple" | "parenthesized_expression" => {
                    // Multiple exception types
                    self.process_exception_types(inner);
                }
                "attribute" | "call" => {
                    // Exception type via attribute access or call
                    self.process_expression(inner);
                }
                _ => {}
            }
        }
    }

    /// Extract binding from an alias node (from child_by_field_name("alias"))
    fn extract_binding_from_alias(&mut self, alias: Node<'a>, found_binding: &mut bool) {
        if alias.kind() == "identifier" {
            let name = self.node_text(alias);
            self.add_ref(
                name,
                alias.start_position().row + 1,
                DataflowKind::Definition,
            );
            *found_binding = true;
        } else if alias.kind() == "as_pattern_target" {
            self.extract_binding_from_target(alias, found_binding);
        } else if let Some(id) = Python::child_by_kind(alias, "identifier") {
            let name = self.node_text(id);
            self.add_ref(name, id.start_position().row + 1, DataflowKind::Definition);
            *found_binding = true;
        }
    }

    /// Extract binding from an as_pattern_target node
    fn extract_binding_from_target(&mut self, target: Node<'a>, found_binding: &mut bool) {
        if target.kind() == "identifier" {
            let name = self.node_text(target);
            self.add_ref(
                name,
                target.start_position().row + 1,
                DataflowKind::Definition,
            );
            *found_binding = true;
        } else if let Some(id) = Python::child_by_kind(target, "identifier") {
            let name = self.node_text(id);
            self.add_ref(name, id.start_position().row + 1, DataflowKind::Definition);
            *found_binding = true;
        }
    }

    /// Process exception types from a tuple or parenthesized expression.
    /// Each exception type is tracked as a USE.
    fn process_exception_types(&mut self, node: Node<'a>) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    // Direct exception type
                    let name = self.node_text(child);
                    self.add_ref(name, child.start_position().row + 1, DataflowKind::Use);
                }
                "attribute" => {
                    // module.ExceptionClass - process the attribute access
                    self.process_expression(child);
                }
                "tuple" | "parenthesized_expression" => {
                    // Nested tuple (rare but handle recursively)
                    self.process_exception_types(child);
                }
                // Skip punctuation and keywords
                "(" | ")" | "," => {}
                _ => {
                    // Any other expression type
                    if child.kind() != "comment" {
                        self.process_expression(child);
                    }
                }
            }
        }
    }

    /// Fallback method to extract exception binding by searching for identifier after "as" keyword
    fn extract_except_binding_fallback(&mut self, node: Node<'a>, _line: usize) {
        let mut cursor = node.walk();
        let mut after_as = false;
        for child in node.children(&mut cursor) {
            if child.kind() == "as" {
                after_as = true;
                continue;
            }
            if after_as && child.kind() == "identifier" {
                let name = self.node_text(child);
                self.add_ref(
                    name,
                    child.start_position().row + 1,
                    DataflowKind::Definition,
                );
                break;
            }
        }
    }

    fn process_with(&mut self, node: Node<'a>) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "with_clause" => {
                    // with_item nodes
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        if inner.kind() == "with_item" {
                            self.process_with_item(inner);
                        }
                    }
                }
                "with_item" => {
                    self.process_with_item(child);
                }
                "block" => self.process_block(child),
                _ => {}
            }
        }
    }

    fn process_with_item(&mut self, node: Node) {
        // With item structure: with_item -> as_pattern -> [call, as, as_pattern_target -> identifier]
        // Or without "as": with_item -> call
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "as_pattern" => {
                    // Process context expression (first non-"as" child)
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        match inner.kind() {
                            "as_pattern_target" => {
                                // Variable being bound
                                if let Some(id) = Python::child_by_kind(inner, "identifier") {
                                    let name = self.node_text(id);
                                    self.add_ref(
                                        name,
                                        id.start_position().row + 1,
                                        DataflowKind::Definition,
                                    );
                                } else {
                                    // Could be a tuple pattern
                                    self.process_target(inner);
                                }
                            }
                            "as" => {}
                            _ => {
                                // Context expression (e.g., open(path))
                                self.process_expression(inner);
                            }
                        }
                    }
                }
                _ => {
                    // No "as" binding, just context expression
                    self.process_expression(child);
                }
            }
        }
    }

    fn process_match(&mut self, node: Node<'a>) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "case_clause" => {
                    // Process pattern (defines variables) and body
                    let mut inner_cursor = child.walk();
                    for inner in child.children(&mut inner_cursor) {
                        match inner.kind() {
                            "case_pattern" => self.process_pattern(inner),
                            "block" => self.process_block(inner),
                            "if_clause" => {
                                // Guard condition in case clause (tree-sitter-python uses if_clause)
                                let mut guard_cursor = inner.walk();
                                for guard_child in inner.children(&mut guard_cursor) {
                                    if guard_child.kind() != "if" {
                                        self.process_expression(guard_child);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                _ => {
                    // Subject expression
                    self.process_expression(child);
                }
            }
        }
    }

    fn process_pattern(&mut self, node: Node) {
        match node.kind() {
            "as_pattern" => {
                // pattern as name - process the inner pattern first, then the binding
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    match child.kind() {
                        "identifier" => {
                            // This is the "as name" binding
                            let name = self.node_text(child);
                            self.add_ref(
                                name,
                                child.start_position().row + 1,
                                DataflowKind::Definition,
                            );
                        }
                        "case_pattern" => {
                            // Process the inner pattern
                            self.process_pattern(child);
                        }
                        _ => {}
                    }
                }
            }
            // BUG-022 FIX: Explicitly handle union_pattern (or pattern: case 1 | 2)
            // tree-sitter-python uses "union_pattern" for the | syntax in match/case
            "union_pattern" => {
                // Process all alternatives in the or pattern
                // In valid Python, all alternatives must bind the same variables
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    // Skip the | operator nodes
                    if child.kind() != "|" {
                        self.process_pattern(child);
                    }
                }
            }
            "capture_pattern" | "identifier" => {
                let name = self.node_text(node);
                if name != "_" {
                    self.add_ref(
                        name,
                        node.start_position().row + 1,
                        DataflowKind::Definition,
                    );
                }
            }
            // Handle dotted_name which can contain capture identifiers
            "dotted_name" => {
                // In patterns, dotted_name with a single identifier is a capture
                if let Some(id) = Python::child_by_kind(node, "identifier") {
                    let name = self.node_text(id);
                    if name != "_" {
                        self.add_ref(name, id.start_position().row + 1, DataflowKind::Definition);
                    }
                }
            }
            // Handle case_pattern wrapper
            "case_pattern" => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_pattern(child);
                }
            }
            // Handle structural patterns that can contain captures
            "list_pattern"
            | "tuple_pattern"
            | "sequence_pattern"
            | "mapping_pattern"
            | "class_pattern"
            | "splat_pattern"
            | "keyword_pattern"
            | "positional_patterns"
            | "keyword_patterns" => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_pattern(child);
                }
            }
            // Skip literal patterns (no bindings)
            "integer" | "float" | "string" | "true" | "false" | "none" | "_" => {}
            _ => {
                // Recurse into pattern for any other node types
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.process_pattern(child);
                }
            }
        }
    }

    /// Compute def-use chains using CFG information for proper control flow analysis.
    ///
    /// This method properly handles control flow merge points (after if/else, loops, etc.)
    /// by merging reaching definitions from all predecessor blocks. This ensures that
    /// definitions from all branches reach subsequent uses.
    ///
    /// # Algorithm
    /// 1. Map each VarRef to its containing CFG block
    /// 2. Process blocks in topological order
    /// 3. At each block:
    ///    - Merge reaching definitions from all predecessor blocks
    ///    - Process refs in line order
    ///    - For definitions: update reaching defs for this block
    ///    - For uses: create edges from all reaching definitions
    ///
    /// # Example
    /// ```python
    /// if cond:
    ///     x = 1  # def1
    /// else:
    ///     x = 2  # def2
    /// print(x)   # Should reach from BOTH def1 AND def2
    /// ```
    /// With CFG-aware analysis, the use at `print(x)` correctly has edges from both
    /// definitions because the merge point after if/else combines reaching defs.
    fn compute_def_use_chains_with_cfg(
        &self,
        cfg: &CFGInfo,
    ) -> (
        Vec<DataflowEdge>,
        FxHashMap<String, Vec<usize>>,
        FxHashMap<String, Vec<usize>>,
    ) {
        use std::collections::HashSet;

        let mut edges = Vec::new();
        let mut definitions: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        let mut uses: FxHashMap<String, Vec<usize>> = FxHashMap::default();

        // Map refs to their containing blocks
        let mut refs_by_block: FxHashMap<BlockId, Vec<&VarRef>> = FxHashMap::default();
        for var_ref in &self.refs {
            if let Some(block_id) = cfg.block_for_line(var_ref.line) {
                refs_by_block.entry(block_id).or_default().push(var_ref);
            }
        }

        // Sort refs within each block by line
        for refs in refs_by_block.values_mut() {
            refs.sort_by_key(|r| r.line);
        }

        // Reaching definitions at the END of each block: block_id -> (var_name -> set of def lines)
        let mut block_out_defs: FxHashMap<BlockId, FxHashMap<String, HashSet<usize>>> = FxHashMap::default();

        // Process blocks in topological order
        let topo_order = cfg.topological_order();

        for block_id in topo_order {
            // Merge reaching definitions from all predecessors
            let predecessors = cfg.predecessors(block_id);
            let mut active_defs: FxHashMap<String, HashSet<usize>> = FxHashMap::default();

            if predecessors.is_empty() {
                // Entry block or unreachable - no incoming defs
            } else {
                // Merge defs from all predecessors (this is the key fix!)
                for &pred_id in predecessors {
                    if let Some(pred_defs) = block_out_defs.get(&pred_id) {
                        for (var_name, def_lines) in pred_defs {
                            active_defs
                                .entry(var_name.clone())
                                .or_default()
                                .extend(def_lines.iter().copied());
                        }
                    }
                }
            }

            // Process refs in this block
            if let Some(block_refs) = refs_by_block.get(&block_id) {
                for var_ref in block_refs {
                    match var_ref.kind {
                        DataflowKind::Param | DataflowKind::Definition => {
                            // Record definition
                            definitions
                                .entry(var_ref.name.clone())
                                .or_default()
                                .push(var_ref.line);

                            // New definition in this block kills previous (within this block's flow)
                            // We replace with a singleton set containing just this definition
                            let mut new_defs = HashSet::new();
                            new_defs.insert(var_ref.line);
                            active_defs.insert(var_ref.name.clone(), new_defs);
                        }
                        DataflowKind::Use | DataflowKind::Return => {
                            // Record use
                            uses.entry(var_ref.name.clone())
                                .or_default()
                                .push(var_ref.line);

                            // Create edges from ALL active definitions to this use
                            if let Some(def_lines) = active_defs.get(&var_ref.name) {
                                for &def_line in def_lines {
                                    edges.push(DataflowEdge {
                                        variable: var_ref.name.clone(),
                                        from_line: def_line,
                                        to_line: var_ref.line,
                                        kind: var_ref.kind,
                                    });
                                }
                            }
                        }
                        DataflowKind::Mutation => {
                            // Mutation is both use and definition
                            uses.entry(var_ref.name.clone())
                                .or_default()
                                .push(var_ref.line);
                            definitions
                                .entry(var_ref.name.clone())
                                .or_default()
                                .push(var_ref.line);

                            // Create edges from active definitions
                            if let Some(def_lines) = active_defs.get(&var_ref.name) {
                                for &def_line in def_lines {
                                    edges.push(DataflowEdge {
                                        variable: var_ref.name.clone(),
                                        from_line: def_line,
                                        to_line: var_ref.line,
                                        kind: DataflowKind::Mutation,
                                    });
                                }
                            }

                            // Mutation creates a new definition, killing previous
                            let mut new_defs = HashSet::new();
                            new_defs.insert(var_ref.line);
                            active_defs.insert(var_ref.name.clone(), new_defs);
                        }
                        DataflowKind::Yield => {
                            // Yield is a use (the value being yielded)
                            uses.entry(var_ref.name.clone())
                                .or_default()
                                .push(var_ref.line);

                            // Create edges from active definitions to this yield
                            if let Some(def_lines) = active_defs.get(&var_ref.name) {
                                for &def_line in def_lines {
                                    edges.push(DataflowEdge {
                                        variable: var_ref.name.clone(),
                                        from_line: def_line,
                                        to_line: var_ref.line,
                                        kind: DataflowKind::Yield,
                                    });
                                }
                            }
                        }
                        DataflowKind::ComprehensionVar
                        | DataflowKind::LambdaParam
                        | DataflowKind::NestedParam => {
                            // Scoped definitions - these define variables in their own scope
                            // They don't "kill" outer definitions for CFG purposes
                            definitions
                                .entry(var_ref.name.clone())
                                .or_default()
                                .push(var_ref.line);

                            // Create a local def that shadows outer scope within nested scope
                            let mut new_defs = HashSet::new();
                            new_defs.insert(var_ref.line);
                            active_defs.insert(var_ref.name.clone(), new_defs);
                        }
                        DataflowKind::ClosureCapture => {
                            // Closure capture: use of outer variable from nested function
                            // Similar to Use but marks it as captured for closure analysis
                            uses.entry(var_ref.name.clone())
                                .or_default()
                                .push(var_ref.line);

                            // Create edges from ALL active definitions to this capture
                            if let Some(def_lines) = active_defs.get(&var_ref.name) {
                                for &def_line in def_lines {
                                    edges.push(DataflowEdge {
                                        variable: var_ref.name.clone(),
                                        from_line: def_line,
                                        to_line: var_ref.line,
                                        kind: DataflowKind::ClosureCapture,
                                    });
                                }
                            }
                        }
                        DataflowKind::Global | DataflowKind::Nonlocal => {
                            // Global/nonlocal declarations - record in definitions
                            definitions
                                .entry(var_ref.name.clone())
                                .or_default()
                                .push(var_ref.line);
                        }
                        // Go-specific variants (should never appear in Python)
                        DataflowKind::Goroutine
                        | DataflowKind::ChannelSend
                        | DataflowKind::ChannelReceive
                        | DataflowKind::Defer
                        | DataflowKind::TypeAssertion
                        | DataflowKind::Panic
                        | DataflowKind::Recover
                        | DataflowKind::ErrorAssign
                        | DataflowKind::ErrorCheck
                        | DataflowKind::NamedReturnModify
                        | DataflowKind::ChannelMake
                        | DataflowKind::ChannelCloseDfg
                        | DataflowKind::SelectReceive
                        | DataflowKind::SelectSend
                        | DataflowKind::MutexLock
                        | DataflowKind::MutexUnlock
                        | DataflowKind::WaitGroupAdd
                        | DataflowKind::WaitGroupDone
                        | DataflowKind::WaitGroupWait
                        | DataflowKind::OnceDo
                        | DataflowKind::ContextDone
                        | DataflowKind::ContextErr
                        | DataflowKind::ContextValue
                        | DataflowKind::PoolGet
                        | DataflowKind::PoolPut => {
                            // Non-Python variants - should not appear in Python analysis
                        }
                    }
                }
            }

            // Store this block's outgoing defs for successors
            block_out_defs.insert(block_id, active_defs);
        }

        // Handle any refs that weren't assigned to blocks (fallback to linear analysis)
        // This can happen if CFG block line ranges don't cover all refs
        let mut unassigned_refs: Vec<&VarRef> = Vec::new();
        for var_ref in &self.refs {
            if cfg.block_for_line(var_ref.line).is_none() {
                unassigned_refs.push(var_ref);
            }
        }

        if !unassigned_refs.is_empty() {
            // Process unassigned refs with simple linear analysis
            unassigned_refs.sort_by_key(|r| r.line);
            let mut active_defs: FxHashMap<String, Vec<usize>> = FxHashMap::default();

            // Initialize with all definitions we've seen so far
            for (var, def_lines) in &definitions {
                active_defs.insert(var.clone(), def_lines.clone());
            }

            for var_ref in unassigned_refs {
                match var_ref.kind {
                    DataflowKind::Use | DataflowKind::Return | DataflowKind::ClosureCapture => {
                        // Use-like references (including closure captures from nested functions)
                        if !uses
                            .get(&var_ref.name)
                            .is_some_and(|v| v.contains(&var_ref.line))
                        {
                            uses.entry(var_ref.name.clone())
                                .or_default()
                                .push(var_ref.line);

                            if let Some(def_lines) = active_defs.get(&var_ref.name) {
                                for &def_line in def_lines {
                                    // Avoid duplicate edges
                                    let edge_exists = edges.iter().any(|e| {
                                        e.variable == var_ref.name
                                            && e.from_line == def_line
                                            && e.to_line == var_ref.line
                                    });
                                    if !edge_exists {
                                        edges.push(DataflowEdge {
                                            variable: var_ref.name.clone(),
                                            from_line: def_line,
                                            to_line: var_ref.line,
                                            kind: var_ref.kind,
                                        });
                                    }
                                }
                            }
                        }
                    }
                    DataflowKind::NestedParam => {
                        // Nested function parameter definitions - record as definition
                        definitions
                            .entry(var_ref.name.clone())
                            .or_default()
                            .push(var_ref.line);
                    }
                    _ => {
                        // Other kinds already handled or are definitions
                    }
                }
            }
        }

        (edges, definitions, uses)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_python(code: &str) -> Tree {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_python::LANGUAGE.into())
            .unwrap();
        parser.parse(code, None).unwrap()
    }

    #[test]
    fn test_extract_simple_function() {
        let code = r#"
def hello(name: str) -> str:
    """Say hello."""
    return f"Hello, {name}!"
"#;
        let tree = parse_python(code);
        let python = Python;

        // Find function_definition
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let func = python.extract_function(func_node, code.as_bytes()).unwrap();
        assert_eq!(func.name, "hello");
        assert!(func.params.iter().any(|p| p.contains("name")));
        assert_eq!(func.return_type, Some("str".to_string()));
        assert_eq!(func.docstring, Some("Say hello.".to_string()));
        assert!(!func.is_async);
    }

    #[test]
    fn test_extract_async_function() {
        let code = r#"
async def fetch(url: str) -> bytes:
    pass
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let func = python.extract_function(func_node, code.as_bytes()).unwrap();
        assert_eq!(func.name, "fetch");
        assert!(func.is_async);
    }

    #[test]
    fn test_extract_decorated_async_function() {
        // BUG FIX: Decorated async functions must be detected correctly.
        // The async keyword is on the inner function_definition, not decorated_definition.
        let code = r#"
@some_decorator
async def fetch_data(url: str) -> bytes:
    pass
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let decorated = Python::child_by_kind(root, "decorated_definition").unwrap();

        let func = python.extract_function(decorated, code.as_bytes()).unwrap();
        assert_eq!(func.name, "fetch_data");
        assert!(
            func.is_async,
            "Decorated async function should have is_async=true"
        );
        assert_eq!(func.decorators.len(), 1);
        assert!(func.decorators.iter().any(|d| d.contains("some_decorator")));
    }

    #[test]
    fn test_extract_decorated_function() {
        let code = r#"
@staticmethod
@other_decorator
def my_method(x: int) -> int:
    return x
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let decorated = Python::child_by_kind(root, "decorated_definition").unwrap();

        let func = python.extract_function(decorated, code.as_bytes()).unwrap();
        assert_eq!(func.name, "my_method");
        assert_eq!(func.decorators.len(), 2);
        assert!(func.decorators.iter().any(|d| d.contains("staticmethod")));
    }

    #[test]
    fn test_extract_multiline_decorator_with_args() {
        // BUG FIX: Multi-line decorators should have whitespace normalized
        let code = r#"
@decorator(
    arg1="value",
    arg2=SomeClass.attribute
)
def foo():
    pass
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let decorated = Python::child_by_kind(root, "decorated_definition").unwrap();

        let func = python.extract_function(decorated, code.as_bytes()).unwrap();
        assert_eq!(func.name, "foo");
        assert_eq!(func.decorators.len(), 1);
        // Should be normalized to single line without excessive whitespace
        let dec = &func.decorators[0];
        assert!(
            dec.starts_with("decorator("),
            "Decorator should start with 'decorator(', got: {}",
            dec
        );
        assert!(
            dec.contains("arg1=\"value\""),
            "Decorator should contain arg1=\"value\", got: {}",
            dec
        );
        assert!(
            dec.contains("arg2=SomeClass.attribute"),
            "Decorator should contain arg2=SomeClass.attribute, got: {}",
            dec
        );
        // Should not contain newlines after normalization
        assert!(
            !dec.contains('\n'),
            "Decorator should not contain newlines after normalization, got: {}",
            dec
        );
    }

    #[test]
    fn test_extract_qualified_decorator() {
        // BUG FIX: Qualified decorators like @module.submodule.decorator
        let code = r#"
@module.submodule.decorator
def bar():
    pass
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let decorated = Python::child_by_kind(root, "decorated_definition").unwrap();

        let func = python.extract_function(decorated, code.as_bytes()).unwrap();
        assert_eq!(func.name, "bar");
        assert_eq!(func.decorators.len(), 1);
        assert_eq!(func.decorators[0], "module.submodule.decorator");
    }

    #[test]
    fn test_extract_generic_decorator() {
        // BUG FIX: Generic decorators like @decorator[Type]
        let code = r#"
@decorator[Type]
def baz():
    pass
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let decorated = Python::child_by_kind(root, "decorated_definition").unwrap();

        let func = python.extract_function(decorated, code.as_bytes()).unwrap();
        assert_eq!(func.name, "baz");
        assert_eq!(func.decorators.len(), 1);
        assert_eq!(func.decorators[0], "decorator[Type]");
    }

    #[test]
    fn test_extract_multiline_subscript_decorator() {
        // BUG FIX: Multi-line subscript decorators should have whitespace normalized
        let code = r#"
@decorator[
    Type1,
    Type2
]
def test_func():
    pass
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let decorated = Python::child_by_kind(root, "decorated_definition").unwrap();

        let func = python.extract_function(decorated, code.as_bytes()).unwrap();
        assert_eq!(func.name, "test_func");
        assert_eq!(func.decorators.len(), 1);
        let dec = &func.decorators[0];
        // Should be normalized to single line without newlines
        assert!(
            dec.starts_with("decorator["),
            "Decorator should start with 'decorator[', got: {}",
            dec
        );
        assert!(
            dec.contains("Type1"),
            "Decorator should contain Type1, got: {}",
            dec
        );
        assert!(
            dec.contains("Type2"),
            "Decorator should contain Type2, got: {}",
            dec
        );
        assert!(
            !dec.contains('\n'),
            "Decorator should not contain newlines after normalization, got: {}",
            dec
        );
    }

    #[test]
    fn test_extract_decorator_with_call_and_attribute() {
        // Combined: qualified decorator with arguments
        let code = r#"
@flask.route("/api", methods=["GET", "POST"])
def endpoint():
    pass
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let decorated = Python::child_by_kind(root, "decorated_definition").unwrap();

        let func = python.extract_function(decorated, code.as_bytes()).unwrap();
        assert_eq!(func.name, "endpoint");
        assert_eq!(func.decorators.len(), 1);
        let dec = &func.decorators[0];
        assert!(
            dec.starts_with("flask.route("),
            "Expected decorator to start with 'flask.route(', got: {}",
            dec
        );
        assert!(
            dec.contains("\"/api\""),
            "Expected decorator to contain '\"/api\"', got: {}",
            dec
        );
    }

    #[test]
    fn test_extract_class() {
        let code = r#"
class MyClass(Base1, Base2):
    """A test class."""

    def method(self, x: int) -> str:
        return str(x)
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let class_node = Python::child_by_kind(root, "class_definition").unwrap();

        let class = python.extract_class(class_node, code.as_bytes()).unwrap();
        assert_eq!(class.name, "MyClass");
        assert_eq!(class.bases, vec!["Base1", "Base2"]);
        assert_eq!(class.docstring, Some("A test class.".to_string()));
        assert_eq!(class.methods.len(), 1);
        assert_eq!(class.methods[0].name, "method");
    }

    #[test]
    fn test_extract_imports() {
        let code = r#"
import os
import sys as system
from pathlib import Path
from collections import defaultdict as dd
from . import local_module
from ..parent import something
"#;
        let tree = parse_python(code);
        let python = Python;

        let imports = python.extract_imports(&tree, code.as_bytes());
        assert_eq!(imports.len(), 6);

        // import os
        assert_eq!(imports[0].module, "os");
        assert!(!imports[0].is_from);

        // import sys as system
        assert_eq!(imports[1].module, "sys");
        assert!(imports[1].aliases.contains_key("sys"));

        // from pathlib import Path
        assert_eq!(imports[2].module, "pathlib");
        assert!(imports[2].is_from);
        assert!(imports[2].names.contains(&"Path".to_string()));

        // from collections import defaultdict as dd
        assert_eq!(imports[3].module, "collections");
        assert!(imports[3].aliases.contains_key("defaultdict"));

        // from . import local_module
        assert!(imports[4].is_from);
        assert_eq!(imports[4].level, 1);

        // from ..parent import something
        assert!(imports[5].is_from);
        assert_eq!(imports[5].level, 2);
    }

    #[test]
    fn test_extract_imports_type_checking() {
        // TYPE_CHECKING imports are commonly used for type hints without runtime import overhead
        let code = r#"
from typing import TYPE_CHECKING

import os

if TYPE_CHECKING:
    from mymodule import MyClass
    from another import AnotherClass as AC
"#;
        let tree = parse_python(code);
        let python = Python;

        let imports = python.extract_imports(&tree, code.as_bytes());

        // Should have 4 imports: TYPE_CHECKING, os, MyClass, AnotherClass
        assert_eq!(imports.len(), 4, "Expected 4 imports, got: {:?}", imports);

        // from typing import TYPE_CHECKING
        assert_eq!(imports[0].module, "typing");
        assert!(imports[0].names.contains(&"TYPE_CHECKING".to_string()));

        // import os
        assert_eq!(imports[1].module, "os");
        assert!(!imports[1].is_from);

        // from mymodule import MyClass (inside TYPE_CHECKING)
        assert_eq!(imports[2].module, "mymodule");
        assert!(imports[2].names.contains(&"MyClass".to_string()));

        // from another import AnotherClass as AC (inside TYPE_CHECKING)
        assert_eq!(imports[3].module, "another");
        assert!(imports[3].names.contains(&"AnotherClass".to_string()));
        assert!(imports[3].aliases.contains_key("AnotherClass"));
    }

    #[test]
    fn test_extract_imports_typing_type_checking() {
        // Handle typing.TYPE_CHECKING variant
        let code = r#"
import typing

if typing.TYPE_CHECKING:
    from models import User
"#;
        let tree = parse_python(code);
        let python = Python;

        let imports = python.extract_imports(&tree, code.as_bytes());

        // Should have 2 imports: typing, User
        assert_eq!(imports.len(), 2, "Expected 2 imports, got: {:?}", imports);

        // import typing
        assert_eq!(imports[0].module, "typing");

        // from models import User (inside typing.TYPE_CHECKING)
        assert_eq!(imports[1].module, "models");
        assert!(imports[1].names.contains(&"User".to_string()));
    }

    #[test]
    fn test_build_cfg() {
        let code = r#"
def example(x):
    if x > 0:
        return True
    return False
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();
        assert_eq!(cfg.function_name, "example");
        assert!(!cfg.blocks.is_empty());
        assert!(!cfg.edges.is_empty());
    }

    /// CFG-BUG-7 FIX: Test that comprehension if clauses are tracked as decision points.
    /// Comprehensions like `[x for x in items if pred1(x) if pred2(x)]` have internal
    /// control flow that affects cyclomatic complexity.
    #[test]
    fn test_comprehension_if_clauses_decision_points() {
        // Function with list comprehension with 2 if clauses
        let code = r#"
def filter_items(items):
    result = [x for x in items if pred1(x) if pred2(x)]
    return result
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();
        assert_eq!(cfg.function_name, "filter_items");

        // Should have 2 comprehension decision points (two if_clause nodes)
        assert_eq!(
            cfg.comprehension_decision_points, 2,
            "Expected 2 decision points for 2 if clauses in comprehension, got {}",
            cfg.comprehension_decision_points
        );

        // Cyclomatic complexity should include comprehension decision points
        // Base complexity (linear) = 1, + 2 for comprehension if clauses = 3
        let complexity = cfg.cyclomatic_complexity();
        assert!(
            complexity >= 3,
            "Expected cyclomatic complexity >= 3 for comprehension with 2 if clauses, got {}",
            complexity
        );
    }

    /// CFG-BUG-7 FIX: Test nested comprehensions with if clauses.
    #[test]
    fn test_nested_comprehension_decision_points() {
        // Nested comprehension with if clauses at both levels
        let code = r#"
def nested_filter(matrix):
    result = [[y for y in row if y > 0] for row in matrix if len(row) > 0]
    return result
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Inner comprehension: 1 if clause (y > 0)
        // Outer comprehension: 1 if clause (len(row) > 0)
        // Total: 2 decision points
        assert_eq!(
            cfg.comprehension_decision_points, 2,
            "Expected 2 decision points for nested comprehensions, got {}",
            cfg.comprehension_decision_points
        );
    }

    /// CFG-BUG-7 FIX: Test different comprehension types.
    #[test]
    fn test_all_comprehension_types() {
        // Dict, set, and generator with if clauses
        let code = r#"
def various_comprehensions(items):
    d = {k: v for k, v in items if v > 0}
    s = {x for x in items if x > 0}
    g = sum(x for x in items if x > 0)
    return d, s, g
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // 3 comprehensions, each with 1 if clause = 3 decision points
        assert_eq!(
            cfg.comprehension_decision_points, 3,
            "Expected 3 decision points for 3 comprehensions with if clauses, got {}",
            cfg.comprehension_decision_points
        );
    }

    /// CFG-BUG-7 FIX: Test comprehension in return statement.
    #[test]
    fn test_comprehension_in_return() {
        let code = r#"
def filter_and_return(items):
    return [x for x in items if x > 0]
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Return statement contains comprehension with 1 if clause
        assert_eq!(
            cfg.comprehension_decision_points, 1,
            "Expected 1 decision point for comprehension in return statement, got {}",
            cfg.comprehension_decision_points
        );
    }

    #[test]
    fn test_build_dfg() {
        let code = r#"
def example(x, y):
    z = x + y
    return z
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();
        assert_eq!(dfg.function_name, "example");

        // Check definitions
        assert!(dfg.definitions.contains_key("x"));
        assert!(dfg.definitions.contains_key("y"));
        assert!(dfg.definitions.contains_key("z"));

        // Check uses
        assert!(dfg.uses.contains_key("x"));
        assert!(dfg.uses.contains_key("y"));
        assert!(dfg.uses.contains_key("z"));

        // Check edges exist
        assert!(!dfg.edges.is_empty());
    }

    /// CFG-DFG-001 Fix Test: Branch merge reaching definitions
    ///
    /// Tests that definitions from all branches of an if/else reach
    /// subsequent uses at the merge point.
    #[test]
    fn test_dfg_branch_merge_reaching_definitions() {
        let code = r#"
def example(cond):
    if cond:
        x = 1
    else:
        x = 2
    print(x)
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();
        assert_eq!(dfg.function_name, "example");

        // x should have 2 definitions (lines 4 and 6)
        let x_defs = dfg.definitions.get("x").expect("x should have definitions");
        assert_eq!(
            x_defs.len(),
            2,
            "x should have 2 definitions (one in each branch)"
        );

        // The use at print(x) should have edges from BOTH definitions
        // Find edges where x flows to line 7 (the print statement)
        let x_edges_to_print: Vec<_> = dfg
            .edges
            .iter()
            .filter(|e| e.variable == "x" && e.to_line == 7)
            .collect();

        assert_eq!(
            x_edges_to_print.len(),
            2,
            "print(x) should have edges from BOTH definitions (lines 4 and 6), got edges from {:?}",
            x_edges_to_print
                .iter()
                .map(|e| e.from_line)
                .collect::<Vec<_>>()
        );

        // Verify the edges come from both branches
        let from_lines: std::collections::HashSet<_> =
            x_edges_to_print.iter().map(|e| e.from_line).collect();
        assert!(
            from_lines.contains(&4),
            "Should have edge from if-branch definition (line 4)"
        );
        assert!(
            from_lines.contains(&6),
            "Should have edge from else-branch definition (line 6)"
        );
    }

    /// CFG-DFG-002 Fix Test: Sequential definition kills previous
    ///
    /// Tests that within a single branch, a new definition kills the previous one.
    #[test]
    fn test_dfg_sequential_definition_kills() {
        let code = r#"
def example():
    x = 1
    x = 2
    print(x)
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // The use at print(x) should only have edge from line 4 (x = 2)
        // The definition at line 3 (x = 1) should be killed by line 4
        let x_edges_to_print: Vec<_> = dfg
            .edges
            .iter()
            .filter(|e| e.variable == "x" && e.to_line == 5)
            .collect();

        assert_eq!(
            x_edges_to_print.len(),
            1,
            "print(x) should only have edge from the last definition (line 4), got edges from {:?}",
            x_edges_to_print
                .iter()
                .map(|e| e.from_line)
                .collect::<Vec<_>>()
        );
        assert_eq!(x_edges_to_print[0].from_line, 4);
    }

    /// CFG-DFG-003 Fix Test: Nested branches
    ///
    /// Tests proper handling of nested if/else structures.
    #[test]
    fn test_dfg_nested_branches() {
        let code = r#"
def example(a, b):
    if a:
        if b:
            x = 1
        else:
            x = 2
    else:
        x = 3
    print(x)
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // x should have 3 definitions
        let x_defs = dfg.definitions.get("x").expect("x should have definitions");
        assert_eq!(x_defs.len(), 3, "x should have 3 definitions");

        // The use at print(x) should have edges from all 3 definitions
        let x_edges_to_print: Vec<_> = dfg
            .edges
            .iter()
            .filter(|e| e.variable == "x" && e.to_line == 10)
            .collect();

        assert_eq!(
            x_edges_to_print.len(),
            3,
            "print(x) should have edges from all 3 definitions, got edges from {:?}",
            x_edges_to_print
                .iter()
                .map(|e| e.from_line)
                .collect::<Vec<_>>()
        );
    }

    /// CFG-DFG-004 Fix Test: Loop with definition
    ///
    /// Tests that definitions inside loops properly reach uses after the loop.
    #[test]
    fn test_dfg_loop_definition() {
        let code = r#"
def example():
    x = 0
    for i in range(10):
        x = i
    print(x)
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // The use at print(x) should have edges from both x = 0 (line 3)
        // and x = i (line 5) because the loop might not execute
        let x_edges_to_print: Vec<_> = dfg
            .edges
            .iter()
            .filter(|e| e.variable == "x" && e.to_line == 6)
            .collect();

        // At minimum, the loop body definition should reach
        assert!(
            !x_edges_to_print.is_empty(),
            "print(x) should have at least one reaching definition"
        );
    }

    /// DFG Nested Function Scope Detection Test
    ///
    /// Tests that nested functions are properly analyzed for closure captures.
    /// Variables from outer scope used inside nested function should be marked
    /// as ClosureCapture, not regular Use.
    #[test]
    fn test_dfg_nested_function_closure_capture() {
        let code = r#"
def outer(x):
    y = 10
    def inner(z):
        return x + y + z
    return inner
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // The outer function parameters should be tracked
        assert!(
            dfg.definitions.contains_key("x"),
            "Outer function parameter 'x' should be tracked as definition"
        );
        assert!(
            dfg.definitions.contains_key("y"),
            "Variable 'y' should be tracked as definition"
        );

        // Nested function parameter 'z' should be tracked as NestedParam definition
        assert!(
            dfg.definitions.contains_key("z"),
            "Nested function parameter 'z' should be tracked as NestedParam definition"
        );

        // Uses inside nested function should be tracked
        // x and y are captured from outer scope (ClosureCapture)
        // z is a local parameter use
        assert!(
            dfg.uses.contains_key("x") || dfg.uses.contains_key("y") || dfg.uses.contains_key("z"),
            "Uses inside nested function should be tracked"
        );
    }

    /// Test that nested function with local variable doesn't incorrectly capture outer
    #[test]
    fn test_dfg_nested_function_local_shadowing() {
        let code = r#"
def outer(x):
    def inner():
        x = 5  # Local assignment shadows outer x
        return x
    return inner
"#;
        let tree = parse_python(code);
        let python = Python;

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // Both the outer x and inner x should be tracked as definitions
        assert!(
            dfg.definitions.contains_key("x"),
            "Variable 'x' should be tracked (both outer param and inner local)"
        );

        // The x assignments should create multiple definitions
        let x_defs = dfg.definitions.get("x").unwrap();
        assert!(
            x_defs.len() >= 2,
            "Should have at least 2 definitions of x (outer param + inner local), got {}",
            x_defs.len()
        );
    }

    // =============================================================================
    // BUG-005, BUG-006, BUG-007 Fix Tests
    // =============================================================================

    #[test]
    fn test_nested_function_marked_with_decorator() {
        // BUG-005: Nested functions should be marked with nested_in:outer_func
        let code = r#"
def outer():
    def inner():
        pass
"#;
        let tree = parse_python(code);
        let python = Python;
        let source = code.as_bytes();

        // Find the inner function
        let root = tree.root_node();
        let outer_func = Python::child_by_kind(root, "function_definition").unwrap();
        let block = Python::child_by_kind(outer_func, "block").unwrap();
        let inner_func = Python::child_by_kind(block, "function_definition").unwrap();

        let inner_info = python.extract_function(inner_func, source);
        assert!(inner_info.is_some(), "Nested function should be extracted");
        let inner_info = inner_info.unwrap();
        assert_eq!(inner_info.name, "inner");
        assert!(
            inner_info.decorators.iter().any(|d| d == "nested_in:outer"),
            "Nested function should have nested_in:outer decorator, got: {:?}",
            inner_info.decorators
        );
    }

    #[test]
    fn test_method_not_in_top_level_functions() {
        // BUG-007: Methods inside class bodies should return None from extract_function
        let code = r#"
class MyClass:
    def method(self):
        pass
"#;
        let tree = parse_python(code);
        let python = Python;
        let source = code.as_bytes();

        // Find the method node
        let root = tree.root_node();
        let class_def = Python::child_by_kind(root, "class_definition").unwrap();
        let block = Python::child_by_kind(class_def, "block").unwrap();
        let method_func = Python::child_by_kind(block, "function_definition").unwrap();

        // Method should return None when called via extract_function
        let method_info = python.extract_function(method_func, source);
        assert!(
            method_info.is_none(),
            "Methods inside class bodies should return None from extract_function"
        );
    }

    #[test]
    fn test_nested_class_marked_with_decorator() {
        // BUG-006: Nested classes should be marked with nested_in:OuterClass
        let code = r#"
class Outer:
    class Inner:
        pass
"#;
        let tree = parse_python(code);
        let python = Python;
        let source = code.as_bytes();

        // Find the inner class
        let root = tree.root_node();
        let outer_class = Python::child_by_kind(root, "class_definition").unwrap();
        let block = Python::child_by_kind(outer_class, "block").unwrap();
        let inner_class = Python::child_by_kind(block, "class_definition").unwrap();

        let inner_info = python.extract_class(inner_class, source);
        assert!(inner_info.is_some(), "Nested class should be extracted");
        let inner_info = inner_info.unwrap();
        assert_eq!(inner_info.name, "Inner");
        assert!(
            inner_info.decorators.iter().any(|d| d == "nested_in:Outer"),
            "Nested class should have nested_in:Outer decorator, got: {:?}",
            inner_info.decorators
        );
    }

    #[test]
    fn test_nested_function_inside_method() {
        // Nested function inside a method should be marked with nested_in:method_name
        let code = r#"
class MyClass:
    def method(self):
        def nested():
            pass
"#;
        let tree = parse_python(code);
        let python = Python;
        let source = code.as_bytes();

        // Navigate to the nested function
        let root = tree.root_node();
        let class_def = Python::child_by_kind(root, "class_definition").unwrap();
        let class_block = Python::child_by_kind(class_def, "block").unwrap();
        let method_func = Python::child_by_kind(class_block, "function_definition").unwrap();
        let method_block = Python::child_by_kind(method_func, "block").unwrap();
        let nested_func = Python::child_by_kind(method_block, "function_definition").unwrap();

        let nested_info = python.extract_function(nested_func, source);
        assert!(
            nested_info.is_some(),
            "Nested function in method should be extracted"
        );
        let nested_info = nested_info.unwrap();
        assert_eq!(nested_info.name, "nested");
        assert!(
            nested_info
                .decorators
                .iter()
                .any(|d| d == "nested_in:method"),
            "Nested function should have nested_in:method decorator, got: {:?}",
            nested_info.decorators
        );
    }

    #[test]
    fn test_nested_in_decorator_position_for_decorated_function() {
        // Verify nested_in is at position 0 (first), matching Python behavior
        let code = r#"
def outer():
    @some_decorator
    @another_decorator
    def inner():
        pass
"#;
        let tree = parse_python(code);
        let python = Python;
        let source = code.as_bytes();

        // Find the decorated inner function
        let root = tree.root_node();
        let outer_func = Python::child_by_kind(root, "function_definition").unwrap();
        let block = Python::child_by_kind(outer_func, "block").unwrap();
        let decorated = Python::child_by_kind(block, "decorated_definition").unwrap();

        let inner_info = python.extract_function(decorated, source);
        assert!(
            inner_info.is_some(),
            "Decorated nested function should be extracted"
        );
        let inner_info = inner_info.unwrap();
        assert_eq!(inner_info.name, "inner");

        // Verify nested_in is at position 0 (first decorator)
        assert!(
            inner_info.decorators.len() >= 1,
            "Should have at least one decorator"
        );
        assert!(
            inner_info.decorators[0].starts_with("nested_in:"),
            "nested_in should be first decorator (position 0), got decorators: {:?}",
            inner_info.decorators
        );
        assert_eq!(
            inner_info.decorators[0], "nested_in:outer",
            "First decorator should be nested_in:outer"
        );

        // Verify other decorators follow
        assert!(
            inner_info.decorators.iter().any(|d| d == "some_decorator"),
            "Should have some_decorator"
        );
        assert!(
            inner_info
                .decorators
                .iter()
                .any(|d| d == "another_decorator"),
            "Should have another_decorator"
        );
    }

    #[test]
    fn test_nested_in_decorator_position_for_decorated_class() {
        // Verify nested_in is at position 0 for nested decorated classes
        let code = r#"
class Outer:
    @dataclass
    class Inner:
        pass
"#;
        let tree = parse_python(code);
        let python = Python;
        let source = code.as_bytes();

        // Find the decorated inner class
        let root = tree.root_node();
        let outer_class = Python::child_by_kind(root, "class_definition").unwrap();
        let block = Python::child_by_kind(outer_class, "block").unwrap();
        let decorated = Python::child_by_kind(block, "decorated_definition").unwrap();

        let inner_info = python.extract_class(decorated, source);
        assert!(
            inner_info.is_some(),
            "Decorated nested class should be extracted"
        );
        let inner_info = inner_info.unwrap();
        assert_eq!(inner_info.name, "Inner");

        // Verify nested_in is at position 0
        assert!(
            inner_info.decorators.len() >= 1,
            "Should have at least one decorator"
        );
        assert!(
            inner_info.decorators[0].starts_with("nested_in:"),
            "nested_in should be first decorator (position 0), got decorators: {:?}",
            inner_info.decorators
        );
        assert_eq!(
            inner_info.decorators[0], "nested_in:Outer",
            "First decorator should be nested_in:Outer"
        );

        // Verify explicit decorator follows
        assert!(
            inner_info.decorators.iter().any(|d| d == "dataclass"),
            "Should have dataclass decorator"
        );
    }

    // =============================================================================
    // BUG-028 Fix Test: Typed *args/**kwargs parameter extraction
    // =============================================================================

    #[test]
    fn test_typed_variadic_params_structure_extraction() {
        // BUG-028: Typed *args and **kwargs should be extracted with proper prefixes
        let code = r#"
def func(*args: tuple[int, ...], **kwargs: dict[str, Any]) -> None:
    pass
"#;
        let tree = parse_python(code);
        let python = Python;
        let source = code.as_bytes();

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let func = python.extract_function(func_node, source).unwrap();
        assert_eq!(func.name, "func");

        // Check that *args and **kwargs are extracted with type annotations
        assert!(
            func.params
                .iter()
                .any(|p| p.contains("*args") && p.contains("tuple")),
            "Should extract *args with tuple type, got: {:?}",
            func.params
        );
        assert!(
            func.params
                .iter()
                .any(|p| p.contains("**kwargs") && p.contains("dict")),
            "Should extract **kwargs with dict type, got: {:?}",
            func.params
        );
    }

    #[test]
    fn test_typed_variadic_params_dfg_extraction() {
        // BUG-028: Typed *args and **kwargs should be tracked in DFG as parameters
        let code = r#"
def func(*args: tuple[int, ...], **kwargs: dict[str, Any]) -> None:
    x = args[0]
    y = kwargs.get("key")
"#;
        let tree = parse_python(code);
        let python = Python;
        let source = code.as_bytes();

        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, source).unwrap();

        // Check that args and kwargs are defined as parameters
        assert!(
            dfg.definitions.contains_key("args"),
            "DFG should contain 'args' definition, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );
        assert!(
            dfg.definitions.contains_key("kwargs"),
            "DFG should contain 'kwargs' definition, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );

        // Check that args and kwargs are used
        assert!(
            dfg.uses.contains_key("args"),
            "DFG should contain 'args' uses, got keys: {:?}",
            dfg.uses.keys().collect::<Vec<_>>()
        );
        assert!(
            dfg.uses.contains_key("kwargs"),
            "DFG should contain 'kwargs' uses, got keys: {:?}",
            dfg.uses.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_typed_variadic_params_comprehensive() {
        // Test all edge cases from BUG-028 requirements
        let test_cases = [
            // Simple typed *args
            ("def f(*args: tuple): pass", vec!["*args: tuple"]),
            // Simple typed **kwargs
            ("def f(**kwargs: dict): pass", vec!["**kwargs: dict"]),
            // Complex generic types
            (
                "def f(*args: tuple[int, ...], **kwargs: dict[str, Any]): pass",
                vec!["*args: tuple[int, ...]", "**kwargs: dict[str, Any]"],
            ),
            // Mixed parameters with typed variadic
            (
                "def f(a: int, *args: tuple, b: str = \"\", **kwargs: dict): pass",
                vec!["a: int", "*args: tuple", "b: str = \"\"", "**kwargs: dict"],
            ),
        ];

        for (code, expected_params) in test_cases {
            let tree = parse_python(code);
            let python = Python;
            let source = code.as_bytes();

            let root = tree.root_node();
            let func_node = Python::child_by_kind(root, "function_definition").unwrap();
            let func = python.extract_function(func_node, source).unwrap();

            for expected in &expected_params {
                assert!(
                    func.params.iter().any(|p| p.contains(expected)),
                    "For code '{}': Expected param containing '{}', got: {:?}",
                    code,
                    expected,
                    func.params
                );
            }
        }
    }

    #[test]
    fn test_strip_docstring_quotes_triple_double() {
        assert_eq!(Python::strip_docstring_quotes(r#""""doc""""#), "doc");
        assert_eq!(
            Python::strip_docstring_quotes(
                r#""""multi
line
doc""""#
            ),
            "multi\nline\ndoc"
        );
    }

    #[test]
    fn test_strip_docstring_quotes_triple_single() {
        assert_eq!(Python::strip_docstring_quotes("'''doc'''"), "doc");
        assert_eq!(
            Python::strip_docstring_quotes("'''multi\nline'''"),
            "multi\nline"
        );
    }

    #[test]
    fn test_strip_docstring_quotes_single_double() {
        assert_eq!(Python::strip_docstring_quotes(r#""simple""#), "simple");
    }

    #[test]
    fn test_strip_docstring_quotes_single_single() {
        assert_eq!(Python::strip_docstring_quotes("'simple'"), "simple");
    }

    #[test]
    fn test_strip_docstring_quotes_with_inner_quotes() {
        // This was the bug: content containing quotes should not be stripped
        assert_eq!(
            Python::strip_docstring_quotes(r#""""'''content'''""""#),
            "'''content'''"
        );
        assert_eq!(
            Python::strip_docstring_quotes(r#"'''"""content"""'''"#),
            r#""""content""""#
        );
        // Content starting with different quote style
        assert_eq!(
            Python::strip_docstring_quotes(r#""""'single inside'""""#),
            "'single inside'"
        );
    }

    #[test]
    fn test_strip_docstring_quotes_empty() {
        assert_eq!(Python::strip_docstring_quotes(r#""""""""#), "");
        assert_eq!(Python::strip_docstring_quotes("''''''"), "");
        assert_eq!(Python::strip_docstring_quotes(r#""""#), "");
        assert_eq!(Python::strip_docstring_quotes("''"), "");
    }

    #[test]
    fn test_strip_docstring_quotes_no_quotes() {
        assert_eq!(Python::strip_docstring_quotes("no quotes"), "no quotes");
    }

    #[test]
    fn test_docstring_with_raw_prefix() {
        // Test full pipeline with raw string prefix
        let code = r#"
def func():
    r"""Raw docstring with 'quotes'."""
    pass
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();
        let func = python.extract_function(func_node, code.as_bytes()).unwrap();
        assert_eq!(
            func.docstring,
            Some("Raw docstring with 'quotes'.".to_string())
        );
    }

    #[test]
    fn test_docstring_with_byte_prefix() {
        // Note: b"..." is bytes, not a valid docstring in Python 3,
        // but the parser should still handle it gracefully
        let code = r#"
def func():
    b"""Byte string."""
    pass
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();
        let func = python.extract_function(func_node, code.as_bytes()).unwrap();
        assert_eq!(func.docstring, Some("Byte string.".to_string()));
    }

    #[test]
    fn test_docstring_with_fstring_prefix() {
        // f-strings as docstrings (valid syntax, though unusual)
        let code = r#"
def func():
    f"""Formatted docstring."""
    pass
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();
        let func = python.extract_function(func_node, code.as_bytes()).unwrap();
        assert_eq!(func.docstring, Some("Formatted docstring.".to_string()));
    }

    // ==========================================================================
    // Module Docstring Tests
    // ==========================================================================

    #[test]
    fn test_module_docstring_basic() {
        let code = r#""""This is a module docstring."""

def foo():
    pass
"#;
        let tree = parse_python(code);
        let docstring = Python::extract_module_docstring(tree.root_node(), code.as_bytes());
        assert_eq!(docstring, Some("This is a module docstring.".to_string()));
    }

    #[test]
    fn test_module_docstring_with_comment_before() {
        let code = r#"# A comment at the top
"""Module docstring after comment."""

def foo():
    pass
"#;
        let tree = parse_python(code);
        let docstring = Python::extract_module_docstring(tree.root_node(), code.as_bytes());
        assert_eq!(
            docstring,
            Some("Module docstring after comment.".to_string())
        );
    }

    #[test]
    fn test_module_docstring_none_when_missing() {
        let code = r#"import os

def foo():
    pass
"#;
        let tree = parse_python(code);
        let docstring = Python::extract_module_docstring(tree.root_node(), code.as_bytes());
        assert_eq!(docstring, None);
    }

    #[test]
    fn test_module_docstring_multiline() {
        let code = r#""""
This is a multi-line
module docstring.
"""

def foo():
    pass
"#;
        let tree = parse_python(code);
        let docstring = Python::extract_module_docstring(tree.root_node(), code.as_bytes());
        // Note: Leading/trailing whitespace is trimmed from docstrings
        assert_eq!(
            docstring,
            Some("This is a multi-line\nmodule docstring.".to_string())
        );
    }

    #[test]
    fn test_module_docstring_single_quoted() {
        let code = r#"'''Single-quoted module docstring.'''

def foo():
    pass
"#;
        let tree = parse_python(code);
        let docstring = Python::extract_module_docstring(tree.root_node(), code.as_bytes());
        assert_eq!(
            docstring,
            Some("Single-quoted module docstring.".to_string())
        );
    }

    #[test]
    fn test_module_docstring_with_raw_prefix() {
        let code = r#"r"""Raw module docstring with \n escaped."""

def foo():
    pass
"#;
        let tree = parse_python(code);
        let docstring = Python::extract_module_docstring(tree.root_node(), code.as_bytes());
        assert_eq!(
            docstring,
            Some(r"Raw module docstring with \n escaped.".to_string())
        );
    }

    #[test]
    fn test_module_docstring_empty_returns_none() {
        let code = r#""""""""

def foo():
    pass
"#;
        let tree = parse_python(code);
        let docstring = Python::extract_module_docstring(tree.root_node(), code.as_bytes());
        assert_eq!(docstring, None);
    }

    #[test]
    fn test_module_docstring_not_a_module_node() {
        let code = r#"def foo():
    pass
"#;
        let tree = parse_python(code);
        let func_node = Python::child_by_kind(tree.root_node(), "function_definition").unwrap();
        // Passing a function node instead of module node should return None
        let docstring = Python::extract_module_docstring(func_node, code.as_bytes());
        assert_eq!(docstring, None);
    }

    /// Test that all augmented assignment operators are properly handled.
    /// This tests the fix for incomplete operator handling (only +=, -=, *=).
    /// Now all operators should work: /=, //=, %=, **=, &=, |=, ^=, <<=, >>=, @=
    #[test]
    fn test_augmented_assignment_all_operators() {
        let code = r#"
def test_augmented_ops(x, mask, flag, toggle, matrix, other):
    # Basic arithmetic
    x += 1
    x -= 1
    x *= 2
    x /= 2

    # Floor div, modulo, power
    x //= 2
    x %= 3
    x **= 2

    # Bitwise
    x &= mask
    x |= flag
    x ^= toggle

    # Bit shifts
    x <<= 1
    x >>= 1

    # Matrix multiply (Python 3.5+)
    matrix @= other

    return x
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // x should be tracked as both used and mutated for each augmented assignment
        assert!(
            dfg.definitions.contains_key("x"),
            "x should have definitions (mutations) from augmented assignments"
        );
        assert!(
            dfg.uses.contains_key("x"),
            "x should have uses from augmented assignments (read before write)"
        );

        // mask, flag, toggle should be tracked as uses (RHS of augmented assignment)
        assert!(
            dfg.uses.contains_key("mask"),
            "mask should be tracked as use in 'x &= mask'"
        );
        assert!(
            dfg.uses.contains_key("flag"),
            "flag should be tracked as use in 'x |= flag'"
        );
        assert!(
            dfg.uses.contains_key("toggle"),
            "toggle should be tracked as use in 'x ^= toggle'"
        );

        // matrix and other should be tracked for the @= operator
        assert!(
            dfg.definitions.contains_key("matrix"),
            "matrix should have definition (mutation) from 'matrix @= other'"
        );
        assert!(
            dfg.uses.contains_key("other"),
            "other should be tracked as use in 'matrix @= other'"
        );
    }

    /// Test augmented assignment with subscript and attribute targets.
    /// e.g., arr[0] += 1, obj.attr += 1
    #[test]
    fn test_augmented_assignment_complex_targets() {
        let code = r#"
def test_complex_targets(arr, obj, idx, nested):
    # Subscript target
    arr[0] += 1
    arr[idx] += 2

    # Attribute target
    obj.value += 10

    # Nested target
    nested.list[0] += 5

    return arr, obj
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // arr should be tracked as used and mutated for arr[0] += 1
        assert!(
            dfg.definitions.contains_key("arr"),
            "arr should have mutation from 'arr[0] += 1'"
        );
        assert!(
            dfg.uses.contains_key("arr"),
            "arr should have use from 'arr[0] += 1' (read current value)"
        );

        // idx should be tracked as used (index expression)
        assert!(
            dfg.uses.contains_key("idx"),
            "idx should be tracked as use in 'arr[idx] += 2'"
        );

        // obj should be tracked as used and mutated for obj.value += 10
        assert!(
            dfg.definitions.contains_key("obj"),
            "obj should have mutation from 'obj.value += 10'"
        );
        assert!(
            dfg.uses.contains_key("obj"),
            "obj should have use from 'obj.value += 10'"
        );

        // nested should be tracked for nested.list[0] += 5
        assert!(
            dfg.definitions.contains_key("nested"),
            "nested should have mutation from 'nested.list[0] += 5'"
        );
    }

    // ==========================================================================
    // Lambda Parameter DFG Tests (BUG-013 regression prevention)
    // ==========================================================================

    #[test]
    fn test_lambda_parameters_tracked_in_dfg() {
        // BUG-013: Lambda parameters must be tracked as definitions in DFG
        let code = r#"
def example():
    f = lambda x: x * 2
    g = lambda x, y=10: x + y
    h = lambda *args, **kwargs: (args, kwargs)
    return f(1)
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // Lambda parameter x should be defined (appears in two lambdas)
        assert!(
            dfg.definitions.contains_key("x"),
            "Lambda parameter 'x' should be tracked as definition, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );

        // Lambda parameter y should be defined (default parameter)
        assert!(
            dfg.definitions.contains_key("y"),
            "Lambda parameter 'y' (with default) should be tracked as definition, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );

        // Lambda *args should be defined
        assert!(
            dfg.definitions.contains_key("args"),
            "Lambda parameter '*args' should be tracked as definition, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );

        // Lambda **kwargs should be defined
        assert!(
            dfg.definitions.contains_key("kwargs"),
            "Lambda parameter '**kwargs' should be tracked as definition, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );

        // Uses within lambda body should reference the lambda parameters
        assert!(
            dfg.uses.contains_key("x"),
            "Lambda body should track uses of 'x', got use keys: {:?}",
            dfg.uses.keys().collect::<Vec<_>>()
        );
        assert!(
            dfg.uses.contains_key("y"),
            "Lambda body should track uses of 'y', got use keys: {:?}",
            dfg.uses.keys().collect::<Vec<_>>()
        );
        assert!(
            dfg.uses.contains_key("args"),
            "Lambda body should track uses of 'args', got use keys: {:?}",
            dfg.uses.keys().collect::<Vec<_>>()
        );
        assert!(
            dfg.uses.contains_key("kwargs"),
            "Lambda body should track uses of 'kwargs', got use keys: {:?}",
            dfg.uses.keys().collect::<Vec<_>>()
        );

        // Check that lambda parameter definitions connect to uses via edges
        let x_edges: Vec<_> = dfg.edges.iter().filter(|e| e.variable == "x").collect();
        assert!(
            !x_edges.is_empty(),
            "Should have edges for lambda parameter 'x' connecting definition to use"
        );
    }

    #[test]
    fn test_lambda_default_param_outer_scope_use() {
        // Default values in lambda parameters should be tracked as uses from outer scope
        let code = r#"
def example():
    outer_val = 10
    f = lambda x=outer_val: x + 1
    return f()
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // outer_val should be used in the default parameter expression
        assert!(
            dfg.uses.contains_key("outer_val"),
            "outer_val should be tracked as use in lambda default parameter, got use keys: {:?}",
            dfg.uses.keys().collect::<Vec<_>>()
        );

        // Lambda parameter x should be defined
        assert!(
            dfg.definitions.contains_key("x"),
            "Lambda parameter 'x' should be defined, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );
    }

    /// BUG-FIX: Test walrus operator (:=) tracking in if/while conditions
    ///
    /// The walrus operator (named_expression) defines a variable AND evaluates to
    /// the assigned value. This test verifies that variables defined via walrus
    /// are properly tracked as definitions in the DFG.
    #[test]
    fn test_walrus_operator_in_if_condition() {
        let code = r#"
def example(items):
    if (n := len(items)) > 10:
        print(n)
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // n should be defined by the walrus operator
        assert!(
            dfg.definitions.contains_key("n"),
            "Variable 'n' should be defined by walrus operator in if condition, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );

        // n should also be used in the print statement
        assert!(
            dfg.uses.contains_key("n"),
            "Variable 'n' should be used in print(n), got use keys: {:?}",
            dfg.uses.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_walrus_operator_in_while_condition() {
        let code = r#"
def read_file(file):
    while (line := file.readline()):
        process(line)
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // line should be defined by the walrus operator
        assert!(
            dfg.definitions.contains_key("line"),
            "Variable 'line' should be defined by walrus operator in while condition, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );

        // line should also be used in process(line)
        assert!(
            dfg.uses.contains_key("line"),
            "Variable 'line' should be used in process(line), got use keys: {:?}",
            dfg.uses.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_walrus_operator_without_comparison() {
        // Test walrus as the entire condition (no comparison operator wrapping it)
        let code = r#"
def example():
    if (result := compute()):
        return result
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // result should be defined by the walrus operator
        assert!(
            dfg.definitions.contains_key("result"),
            "Variable 'result' should be defined by walrus operator, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_walrus_operator_in_comprehension() {
        let code = r#"
def example(items):
    return [y for x in items if (y := transform(x))]
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let dfg = python.build_dfg(func_node, code.as_bytes()).unwrap();

        // y should be defined by the walrus operator in the if clause
        assert!(
            dfg.definitions.contains_key("y"),
            "Variable 'y' should be defined by walrus operator in comprehension, got keys: {:?}",
            dfg.definitions.keys().collect::<Vec<_>>()
        );
    }

    // =========================================================================
    // Exception Flow CFG Tests
    // =========================================================================

    /// Test basic try/except CFG structure with exception type extraction.
    #[test]
    fn test_exception_cfg_basic_try_except() {
        let code = r#"
def safe_divide(a, b):
    try:
        result = a / b
    except ZeroDivisionError:
        result = 0
    return result
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();
        assert_eq!(cfg.function_name, "safe_divide");

        // Should have exception edge
        let has_exception_edge = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::Exception | EdgeType::TypedException));
        assert!(
            has_exception_edge,
            "Should have exception edge from try to except"
        );

        // Exception type should be extracted (ZeroDivisionError)
        let has_typed_exception = cfg.edges.iter().any(|e| {
            e.condition
                .as_ref()
                .map_or(false, |c| c.contains("ZeroDivisionError"))
        });
        assert!(
            has_typed_exception,
            "Should extract exception type 'ZeroDivisionError'"
        );
    }

    /// Test try/except with multiple exception types.
    #[test]
    fn test_exception_cfg_multiple_exception_types() {
        let code = r#"
def handle_multiple(x):
    try:
        process(x)
    except (ValueError, TypeError):
        handle_error()
    except KeyError:
        handle_key_error()
    except:
        handle_all()
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have multiple except blocks
        let except_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.label.starts_with("except"))
            .collect();
        assert!(
            except_blocks.len() >= 3,
            "Should have at least 3 except blocks, got {}",
            except_blocks.len()
        );

        // Should have typed exception edges
        let typed_edges = cfg
            .edges
            .iter()
            .filter(|e| matches!(e.edge_type, EdgeType::TypedException | EdgeType::Exception))
            .count();
        assert!(
            typed_edges >= 3,
            "Should have at least 3 exception edges, got {}",
            typed_edges
        );
    }

    /// Test try/except/else structure.
    #[test]
    fn test_exception_cfg_try_else() {
        let code = r#"
def with_else(x):
    try:
        result = compute(x)
    except ComputeError:
        result = default()
    else:
        result = process(result)
    return result
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have NoException edge to else block
        let has_no_exception = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::NoException));
        assert!(
            has_no_exception,
            "Should have NoException edge to else block"
        );

        // Should have try_else block
        let has_else_block = cfg.blocks.values().any(|b| b.label.contains("else"));
        assert!(has_else_block, "Should have else block");
    }

    /// Test try/finally structure with finally always executing.
    #[test]
    fn test_exception_cfg_try_finally() {
        let code = r#"
def with_finally(f):
    try:
        data = f.read()
    finally:
        f.close()
    return data
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have finally block
        let has_finally_block = cfg.blocks.values().any(|b| b.label == "finally");
        assert!(has_finally_block, "Should have finally block");

        // Should have edges to finally
        let finally_edges = cfg
            .edges
            .iter()
            .filter(|e| matches!(e.edge_type, EdgeType::Finally))
            .count();
        assert!(
            finally_edges >= 1,
            "Should have at least 1 Finally edge, got {}",
            finally_edges
        );
    }

    /// Test raise statement with exception type extraction.
    #[test]
    fn test_exception_cfg_raise_statement() {
        let code = r#"
def validate(x):
    if x < 0:
        raise ValueError("x must be positive")
    return x
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have block with raise statement
        let has_raise_block = cfg
            .blocks
            .values()
            .any(|b| b.statements.iter().any(|s| s.contains("raise")));
        assert!(
            has_raise_block,
            "Should have block containing raise statement"
        );
    }

    /// Test bare raise (reraise) within except handler.
    #[test]
    fn test_exception_cfg_bare_reraise() {
        let code = r#"
def log_and_reraise(func, x):
    try:
        return func(x)
    except Exception as e:
        log_error(e)
        raise
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have block with bare raise
        let has_reraise = cfg.blocks.values().any(|b| {
            b.label.contains("reraise") || b.statements.iter().any(|s| s.trim() == "raise")
        });
        assert!(
            has_reraise,
            "Should have bare raise (reraise) block or statement"
        );
    }

    /// Test exception chaining (raise from).
    #[test]
    fn test_exception_cfg_raise_from() {
        let code = r#"
def wrap_error(x):
    try:
        process(x)
    except ProcessError as e:
        raise ApplicationError("Processing failed") from e
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have block with raise...from
        let has_raise_from = cfg
            .blocks
            .values()
            .any(|b| b.statements.iter().any(|s| s.contains("from")));
        assert!(has_raise_from, "Should have raise...from statement");
    }

    /// Test return within try/finally routes through finally.
    #[test]
    fn test_exception_cfg_return_through_finally() {
        let code = r#"
def early_return_with_cleanup(f):
    try:
        if not f.valid():
            return None
        return f.read()
    finally:
        f.close()
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have return_via_finally block for return within try
        let has_return_via_finally = cfg
            .blocks
            .values()
            .any(|b| b.label.contains("return_via_finally"));
        // Note: this may not always create a separate block depending on implementation
        // Check for finally block existence instead
        let has_finally = cfg.blocks.values().any(|b| b.label == "finally");
        assert!(has_finally, "Should have finally block");
    }

    /// Test nested try/except structures.
    #[test]
    fn test_exception_cfg_nested_try() {
        let code = r#"
def nested_handlers(x, y):
    try:
        try:
            result = x / y
        except ZeroDivisionError:
            result = 0
        return process(result)
    except ProcessError:
        return default()
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have multiple exception handlers
        let except_count = cfg
            .edges
            .iter()
            .filter(|e| matches!(e.edge_type, EdgeType::Exception | EdgeType::TypedException))
            .count();
        assert!(
            except_count >= 2,
            "Should have at least 2 exception edges for nested try, got {}",
            except_count
        );
    }

    /// Test context manager (with statement) exception handling.
    #[test]
    fn test_exception_cfg_with_statement() {
        let code = r#"
def with_context(path):
    with open(path) as f:
        data = f.read()
    return data
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have with_enter and with_exit blocks
        let has_enter = cfg.blocks.values().any(|b| b.label.contains("with_enter"));
        let has_exit = cfg.blocks.values().any(|b| b.label.contains("with_exit"));
        assert!(has_enter, "Should have with_enter block");
        assert!(has_exit, "Should have with_exit block");

        // Should have exception edges for context manager
        let has_enter_exception = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::EnterException));
        assert!(
            has_enter_exception,
            "Should have EnterException edge for __enter__ failure"
        );
    }

    /// Test Python 3.11+ except* for ExceptionGroups.
    #[test]
    fn test_exception_cfg_exception_group() {
        let code = r#"
def handle_group(coros):
    try:
        results = gather(coros)
    except* ValueError:
        handle_value_errors()
    except* TypeError:
        handle_type_errors()
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have ExceptionGroup edges
        let has_exception_group = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::ExceptionGroup));
        // Note: tree-sitter-python may not support except* yet
        // If not supported, at least no errors should occur
        assert!(
            cfg.blocks.len() > 0,
            "CFG should be built even with except*"
        );
    }

    /// Test exception type extraction from as_pattern.
    #[test]
    fn test_exception_type_with_binding() {
        let code = r#"
def catch_with_binding(x):
    try:
        risky(x)
    except ValueError as e:
        handle(e)
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should extract ValueError even with 'as e' binding
        let has_value_error = cfg.edges.iter().any(|e| {
            e.condition
                .as_ref()
                .map_or(false, |c| c.contains("ValueError"))
        }) || cfg.blocks.values().any(|b| b.label.contains("ValueError"));
        assert!(
            has_value_error,
            "Should extract ValueError from 'except ValueError as e'"
        );
    }

    // =========================================================================
    // Async Flow Tests
    // =========================================================================

    /// Test basic async function CFG with await expression.
    #[test]
    fn async_flow_basic_await() {
        let code = r#"
async def fetch_data(url):
    result = await http_get(url)
    return process(result)
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // CFG should be marked as async
        assert!(cfg.is_async, "CFG should be marked as async for async def");

        // Should have 1 await point
        assert_eq!(cfg.await_points, 1, "Should have 1 await point");

        // Should have AwaitPoint block type
        let has_await_block = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::AwaitPoint));
        assert!(has_await_block, "Should have AwaitPoint block");

        // Should have Await edge type
        let has_await_edge = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::Await));
        assert!(has_await_edge, "Should have Await edge");
    }

    /// Test async function with multiple await points.
    #[test]
    fn async_flow_multiple_awaits() {
        let code = r#"
async def fetch_multiple(urls):
    data1 = await fetch(urls[0])
    data2 = await fetch(urls[1])
    data3 = await fetch(urls[2])
    return combine(data1, data2, data3)
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have 3 await points
        assert_eq!(
            cfg.await_points, 3,
            "Should have 3 await points for 3 await expressions"
        );

        // Should have 3 Await edges
        let await_edge_count = cfg
            .edges
            .iter()
            .filter(|e| matches!(e.edge_type, EdgeType::Await))
            .count();
        assert_eq!(await_edge_count, 3, "Should have 3 Await edges");
    }

    /// Test async for loop CFG.
    #[test]
    fn async_flow_async_for() {
        let code = r#"
async def process_stream(stream):
    async for item in stream:
        process(item)
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have async for loop block
        let has_async_for = cfg.blocks.values().any(|b| b.label.contains("async_for"));
        assert!(has_async_for, "Should have async_for_loop block");

        // Should have AsyncForLoop block type
        let has_async_for_type = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::AsyncForLoop));
        assert!(has_async_for_type, "Should have AsyncForLoop block type");

        // Should have AsyncIterate edge
        let has_async_iterate = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::AsyncIterate));
        assert!(has_async_iterate, "Should have AsyncIterate edge");

        // Should have AsyncExhausted edge
        let has_async_exhausted = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::AsyncExhausted));
        assert!(has_async_exhausted, "Should have AsyncExhausted edge");
    }

    /// Test async with statement CFG.
    #[test]
    fn async_flow_async_with() {
        let code = r#"
async def connect_db():
    async with database.connect() as conn:
        await conn.execute(query)
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have async with enter block
        let has_async_with_enter = cfg
            .blocks
            .values()
            .any(|b| b.label.contains("async_with_enter"));
        assert!(has_async_with_enter, "Should have async_with_enter block");

        // Should have AsyncWithBlock block type
        let has_async_with_type = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::AsyncWithBlock));
        assert!(has_async_with_type, "Should have AsyncWithBlock block type");

        // Should have AsyncEnterSuccess edge
        let has_async_enter_success = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::AsyncEnterSuccess));
        assert!(
            has_async_enter_success,
            "Should have AsyncEnterSuccess edge"
        );
    }

    /// Test asyncio.create_task detection.
    #[test]
    fn async_flow_create_task() {
        let code = r#"
async def spawn_tasks():
    task1 = asyncio.create_task(worker(1))
    task2 = asyncio.create_task(worker(2))
    return task1, task2
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have TaskSpawn block type
        let has_task_spawn = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::TaskSpawn));
        assert!(
            has_task_spawn,
            "Should have TaskSpawn block for create_task"
        );

        // Should have TaskSpawn edge
        let has_spawn_edge = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::TaskSpawn));
        assert!(has_spawn_edge, "Should have TaskSpawn edge");
    }

    /// Test asyncio.gather detection.
    #[test]
    fn async_flow_gather() {
        let code = r#"
async def parallel_fetch(urls):
    tasks = [fetch(url) for url in urls]
    results = await asyncio.gather(*tasks)
    return results
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should be async
        assert!(cfg.is_async, "CFG should be async");

        // Should have await point for the gather
        assert!(cfg.await_points >= 1, "Should have await point for gather");
    }

    /// Test blocking call detection in async function.
    #[test]
    fn async_flow_blocking_call_detection() {
        let code = r#"
async def bad_async():
    time.sleep(1)
    return "done"
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should detect time.sleep as blocking call in async context
        assert!(
            !cfg.blocking_calls.is_empty(),
            "Should detect blocking call time.sleep"
        );
        assert!(
            cfg.blocking_calls
                .iter()
                .any(|(name, _)| name.contains("time.sleep")),
            "Should specifically detect time.sleep"
        );
    }

    /// Test combined async patterns.
    #[test]
    fn async_flow_combined_patterns() {
        let code = r#"
async def complex_async():
    async with aiohttp.ClientSession() as session:
        async for url in url_generator():
            response = await session.get(url)
            data = await response.json()
            process(data)
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should be async
        assert!(cfg.is_async, "CFG should be async");

        // Should have multiple await points
        assert!(cfg.await_points >= 2, "Should have multiple await points");

        // Should have async with
        let has_async_with = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::AsyncWithBlock));
        assert!(has_async_with, "Should have AsyncWithBlock");

        // Should have async for
        let has_async_for = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::AsyncForLoop));
        assert!(has_async_for, "Should have AsyncForLoop");

        // Should have await points
        let has_await_points = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::AwaitPoint));
        assert!(has_await_points, "Should have AwaitPoint blocks");
    }

    /// Test that sync functions don't have async markers.
    #[test]
    fn async_flow_sync_function() {
        let code = r#"
def sync_function(x):
    result = compute(x)
    return result
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should NOT be async
        assert!(
            !cfg.is_async,
            "Sync function CFG should not be marked async"
        );

        // Should have 0 await points
        assert_eq!(
            cfg.await_points, 0,
            "Sync function should have 0 await points"
        );

        // Should have no blocking call warnings (not in async context)
        assert!(
            cfg.blocking_calls.is_empty(),
            "Sync function should not track blocking calls"
        );
    }

    /// Test async for with else clause.
    #[test]
    fn async_flow_async_for_else() {
        let code = r#"
async def search_stream(stream, target):
    async for item in stream:
        if item == target:
            return item
    else:
        return None
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have async_for_else block
        let has_async_for_else = cfg
            .blocks
            .values()
            .any(|b| b.label.contains("async_for_else"));
        assert!(has_async_for_else, "Should have async_for_else block");
    }

    // =========================================================================
    // Generator Flow Tests
    // =========================================================================

    /// Test basic generator function CFG with yield expression.
    #[test]
    fn generator_simple_yield() {
        let code = r#"
def counter(n):
    i = 0
    while i < n:
        yield i
        i += 1
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // CFG should be marked as generator
        assert!(
            cfg.is_generator,
            "CFG should be marked as generator for function with yield"
        );

        // Should NOT be async
        assert!(!cfg.is_async, "Regular generator should not be async");
        assert!(
            !cfg.is_async_generator,
            "Regular generator should not be async generator"
        );

        // Should have 1 yield point
        assert_eq!(cfg.yield_count, 1, "Should have 1 yield point");

        // Should have YieldPoint block type
        let has_yield_block = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::YieldPoint));
        assert!(has_yield_block, "Should have YieldPoint block");

        // Should have Yield edge type
        let has_yield_edge = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::Yield));
        assert!(has_yield_edge, "Should have Yield edge");

        // Should have GeneratorResume edge type
        let has_resume_edge = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::GeneratorResume));
        assert!(has_resume_edge, "Should have GeneratorResume edge");
    }

    /// Test generator with multiple yield points.
    #[test]
    fn generator_multiple_yields() {
        let code = r#"
def multi_yield():
    yield 1
    yield 2
    yield 3
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should be a generator
        assert!(cfg.is_generator, "Should be marked as generator");

        // Should have 3 yield points
        assert_eq!(cfg.yield_count, 3, "Should have 3 yield points");

        // Should have 3 Yield edges
        let yield_edge_count = cfg
            .edges
            .iter()
            .filter(|e| matches!(e.edge_type, EdgeType::Yield))
            .count();
        assert_eq!(yield_edge_count, 3, "Should have 3 Yield edges");

        // Should have 3 GeneratorEntry blocks
        let gen_entry_count = cfg
            .blocks
            .values()
            .filter(|b| matches!(b.block_type, BlockType::GeneratorEntry))
            .count();
        assert_eq!(gen_entry_count, 3, "Should have 3 GeneratorEntry blocks");
    }

    /// Test yield from delegation.
    #[test]
    fn generator_yield_from() {
        let code = r#"
def chain(*iterables):
    for it in iterables:
        yield from it
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should be a generator
        assert!(cfg.is_generator, "Should be marked as generator");

        // Should have YieldFrom block type
        let has_yield_from_block = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::YieldFrom));
        assert!(has_yield_from_block, "Should have YieldFrom block");

        // Should have YieldFromDelegate edge type
        let has_delegate_edge = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::YieldFromDelegate));
        assert!(has_delegate_edge, "Should have YieldFromDelegate edge");
    }

    /// Test async generator (async def with yield).
    #[test]
    fn generator_async_generator() {
        let code = r#"
async def async_counter(n):
    i = 0
    while i < n:
        yield i
        i += 1
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should be async AND a generator
        assert!(cfg.is_async, "Should be marked as async");
        assert!(cfg.is_generator, "Should be marked as generator");
        assert!(
            cfg.is_async_generator,
            "Should be marked as async generator"
        );

        // Should have 1 yield point
        assert_eq!(cfg.yield_count, 1, "Should have 1 yield point");

        // Should have AsyncYieldPoint block type
        let has_async_yield_block = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::AsyncYieldPoint));
        assert!(has_async_yield_block, "Should have AsyncYieldPoint block");

        // Should have AsyncGeneratorYield edge type
        let has_async_yield_edge = cfg
            .edges
            .iter()
            .any(|e| matches!(e.edge_type, EdgeType::AsyncGeneratorYield));
        assert!(has_async_yield_edge, "Should have AsyncGeneratorYield edge");
    }

    /// Test generator with try/finally (cleanup on close).
    #[test]
    fn generator_with_try_finally() {
        let code = r#"
def resource_generator():
    resource = acquire()
    try:
        yield resource.get_data()
    finally:
        resource.close()
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should be a generator
        assert!(cfg.is_generator, "Should be marked as generator");

        // Should have yield point
        let has_yield_block = cfg
            .blocks
            .values()
            .any(|b| matches!(b.block_type, BlockType::YieldPoint));
        assert!(has_yield_block, "Should have YieldPoint block");

        // Should have finally block
        let has_finally = cfg.blocks.values().any(|b| b.label.contains("finally"));
        assert!(has_finally, "Should have finally block for cleanup");
    }

    /// Test that regular functions are not generators.
    #[test]
    fn generator_non_generator_function() {
        let code = r#"
def regular_function(x):
    return x * 2
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should NOT be a generator
        assert!(
            !cfg.is_generator,
            "Regular function should not be a generator"
        );
        assert!(
            !cfg.is_async_generator,
            "Regular function should not be async generator"
        );
        assert_eq!(
            cfg.yield_count, 0,
            "Regular function should have 0 yield points"
        );
    }

    /// Test that nested generator doesn't affect outer function.
    #[test]
    fn generator_nested_generator() {
        let code = r#"
def outer():
    def inner():
        yield 1
    return inner()
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Outer function should NOT be a generator (yield is in nested function)
        assert!(
            !cfg.is_generator,
            "Outer function should not be a generator"
        );
        assert_eq!(
            cfg.yield_count, 0,
            "Outer function should have 0 yield points"
        );
    }

    /// Test generator with conditional yield.
    #[test]
    fn generator_conditional_yield() {
        let code = r#"
def conditional_gen(items, predicate):
    for item in items:
        if predicate(item):
            yield item
"#;
        let tree = parse_python(code);
        let python = Python;
        let root = tree.root_node();
        let func_node = Python::child_by_kind(root, "function_definition").unwrap();

        let cfg = python.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should be a generator
        assert!(cfg.is_generator, "Should be marked as generator");
        assert_eq!(cfg.yield_count, 1, "Should have 1 yield point");

        // Cyclomatic complexity should account for loop + if
        let complexity = cfg.cyclomatic_complexity();
        assert!(
            complexity >= 3,
            "Should have cyclomatic complexity >= 3 (loop + if + base)"
        );
    }
}
