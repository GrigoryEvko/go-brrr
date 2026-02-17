//! TORCH_LIBRARY macro detector.
//!
//! Detects:
//! - `TORCH_LIBRARY(namespace, m) { m.def("op_schema"); }` -- operator schema registration
//! - `TORCH_LIBRARY_IMPL(namespace, dispatch_key, m) { m.impl("op", fn); }` -- impl registration
//! - `TORCH_LIBRARY_FRAGMENT(namespace, m) { ... }` -- additional registrations (def + impl)
//! - `STABLE_TORCH_LIBRARY_FRAGMENT(namespace, m) { ... }` -- stable ABI variant
//! - `m.fallback(...)` -- dispatch key fallback handlers

use tree_sitter::Tree;

use crate::bindings::detector::BindingDetector;
use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::types::FunctionRef;
use crate::error::Result;

pub struct TorchLibraryDetector;

impl BindingDetector for TorchLibraryDetector {
    fn system(&self) -> BindingSystem {
        BindingSystem::TorchLibrary
    }

    fn applicable_languages(&self) -> &[&'static str] {
        &["cpp"]
    }

    fn quick_check(&self, source: &[u8], _language: &str) -> bool {
        memchr::memmem::find(source, b"TORCH_LIBRARY").is_some()
    }

    fn detect(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
        _language: &str,
    ) -> Result<Vec<BindingDeclaration>> {
        let mut declarations = Vec::new();
        collect_torch_library(&tree.root_node(), source, file_path, &mut declarations);
        Ok(declarations)
    }
}

/// Classify which TORCH_LIBRARY macro variant this function_definition represents.
enum MacroKind {
    /// TORCH_LIBRARY_IMPL(namespace, dispatch_key, m) -- impl registrations
    Impl {
        namespace: String,
        dispatch_key: String,
    },
    /// TORCH_LIBRARY(ns, m), TORCH_LIBRARY_FRAGMENT(ns, m), STABLE_TORCH_LIBRARY_FRAGMENT(ns, m)
    /// These can contain both m.def() and m.impl() calls.
    Library { namespace: String },
}

fn collect_torch_library(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
) {
    // TORCH_LIBRARY macros are parsed by tree-sitter-cpp as function_definition
    // because the macro expands to something like:
    //   void TORCH_LIBRARY_init_##ns(torch::Library& m) { ... }
    if node.kind() == "function_definition" {
        if let Some(kind) = classify_macro(node, source) {
            if let Some(body) = node.child_by_field_name("body") {
                match &kind {
                    MacroKind::Impl {
                        namespace,
                        dispatch_key,
                    } => {
                        collect_body_calls(
                            &body,
                            source,
                            file_path,
                            declarations,
                            namespace,
                            Some(dispatch_key.as_str()),
                        );
                    }
                    MacroKind::Library { namespace } => {
                        collect_body_calls(
                            &body,
                            source,
                            file_path,
                            declarations,
                            namespace,
                            None,
                        );
                    }
                }
            }
            return;
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_torch_library(&child, source, file_path, declarations);
    }
}

/// Classify a function_definition node as a TORCH_LIBRARY macro variant.
fn classify_macro(node: &tree_sitter::Node, source: &[u8]) -> Option<MacroKind> {
    let text = node.utf8_text(source).ok()?;

    if text.starts_with("TORCH_LIBRARY_IMPL") {
        // TORCH_LIBRARY_IMPL(namespace, DispatchKey, m) { ... }
        let (namespace, dispatch_key) = parse_macro_args_2(text)?;
        Some(MacroKind::Impl {
            namespace,
            dispatch_key,
        })
    } else if text.starts_with("TORCH_LIBRARY_FRAGMENT")
        || text.starts_with("TORCH_LIBRARY(")
        || text.starts_with("STABLE_TORCH_LIBRARY_FRAGMENT")
    {
        let namespace = parse_macro_args_1(text)?;
        Some(MacroKind::Library { namespace })
    } else {
        None
    }
}

/// Collect all m.def(), m.impl(), and m.fallback() calls inside a TORCH_LIBRARY body.
/// Unified handler: TORCH_LIBRARY and TORCH_LIBRARY_FRAGMENT can contain both def and impl.
fn collect_body_calls(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    namespace: &str,
    dispatch_key: Option<&str>,
) {
    if node.kind() == "call_expression" {
        if let Some(method) = get_method_call_name(node, source) {
            match method.as_str() {
                "def" => {
                    handle_m_def(node, source, file_path, declarations, namespace);
                    return;
                }
                "impl" => {
                    handle_m_impl(
                        node,
                        source,
                        file_path,
                        declarations,
                        namespace,
                        dispatch_key,
                    );
                    return;
                }
                "fallback" => {
                    handle_m_fallback(
                        node,
                        source,
                        file_path,
                        declarations,
                        namespace,
                        dispatch_key,
                    );
                    return;
                }
                _ => {}
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_body_calls(
            &child,
            source,
            file_path,
            declarations,
            namespace,
            dispatch_key,
        );
    }
}

/// Extract the method name from `m.def(...)`, `m.impl(...)`, etc.
fn get_method_call_name(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let func = node.child_by_field_name("function")?;
    if func.kind() != "field_expression" {
        return None;
    }
    let field = func.child_by_field_name("field")?;
    field.utf8_text(source).ok().map(|s| s.to_string())
}

/// Handle `m.def("op_schema")` or `m.def(TORCH_SELECTIVE_SCHEMA("op_schema"))`.
fn handle_m_def(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    namespace: &str,
) {
    if let Some(schema) = find_first_string_deep(node, source) {
        let exposed = build_exposed_name(namespace, &schema);
        let text = node.utf8_text(source).unwrap_or("");
        declarations.push(BindingDeclaration {
            system: BindingSystem::TorchLibrary,
            direction: BindingDirection::Dispatch,
            exposed_name: exposed,
            host_function: None,
            target_function: None,
            declaration_file: file_path.to_string(),
            declaration_line: node.start_position().row + 1,
            module_name: Some(namespace.to_string()),
            class_name: None,
            raw_pattern: Some(truncate(text, 200)),
            confidence: 1.0,
        });
    }
}

/// Handle `m.impl("op", fn)` or `m.impl(TORCH_SELECTIVE_NAME("op"), TORCH_FN(fn))`.
fn handle_m_impl(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    namespace: &str,
    dispatch_key: Option<&str>,
) {
    let args = match node.child_by_field_name("arguments") {
        Some(a) => a,
        None => return,
    };

    let real_args = collect_real_args(&args);
    if real_args.is_empty() {
        return;
    }

    // First arg: op name (string_literal or macro wrapping a string)
    let op_name = match extract_string_from_node(&real_args[0], source) {
        Some(name) => name,
        None => return,
    };

    // Second arg: implementation function reference
    let impl_fn = if real_args.len() >= 2 {
        extract_impl_function(&real_args[1], source)
    } else {
        None
    };

    let exposed = build_exposed_name(namespace, &op_name);
    let text = node.utf8_text(source).unwrap_or("");

    declarations.push(BindingDeclaration {
        system: BindingSystem::TorchLibrary,
        direction: BindingDirection::Dispatch,
        exposed_name: exposed,
        host_function: impl_fn.map(|name| FunctionRef {
            file: String::new(),
            name,
            qualified_name: None,
        }),
        target_function: None,
        declaration_file: file_path.to_string(),
        declaration_line: node.start_position().row + 1,
        module_name: Some(namespace.to_string()),
        class_name: dispatch_key.map(|s| s.to_string()),
        raw_pattern: Some(truncate(text, 200)),
        confidence: 1.0,
    });
}

/// Handle `m.fallback(...)` inside TORCH_LIBRARY_IMPL.
fn handle_m_fallback(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    namespace: &str,
    dispatch_key: Option<&str>,
) {
    let args = match node.child_by_field_name("arguments") {
        Some(a) => a,
        None => return,
    };

    let real_args = collect_real_args(&args);
    let fallback_fn = if !real_args.is_empty() {
        extract_fallback_function(&real_args[0], source)
    } else {
        None
    };

    let text = node.utf8_text(source).unwrap_or("");

    declarations.push(BindingDeclaration {
        system: BindingSystem::TorchLibrary,
        direction: BindingDirection::Dispatch,
        exposed_name: format!("{}::__fallback__", namespace),
        host_function: fallback_fn.map(|name| FunctionRef {
            file: String::new(),
            name,
            qualified_name: None,
        }),
        target_function: None,
        declaration_file: file_path.to_string(),
        declaration_line: node.start_position().row + 1,
        module_name: Some(namespace.to_string()),
        class_name: dispatch_key.map(|s| s.to_string()),
        raw_pattern: Some(truncate(text, 200)),
        confidence: 0.8,
    });
}

// ---------------------------------------------------------------------------
// String extraction
// ---------------------------------------------------------------------------

/// Recursively find the first string_literal in a call's arguments subtree.
/// Handles: direct strings, TORCH_SELECTIVE_SCHEMA("..."), torch::schema("...", ...).
fn find_first_string_deep(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let args = node.child_by_field_name("arguments")?;
    find_string_in_subtree(&args, source)
}

/// Recursively search for the first string_literal in a node subtree.
fn find_string_in_subtree(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    if node.kind() == "string_literal" {
        return node
            .utf8_text(source)
            .ok()
            .map(|s| s.trim_matches('"').to_string());
    }
    if node.kind() == "string_content" {
        return node.utf8_text(source).ok().map(|s| s.to_string());
    }
    // "foo" "bar" -> tree-sitter concatenated_string
    if node.kind() == "concatenated_string" {
        let mut result = String::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "string_literal" {
                if let Ok(s) = child.utf8_text(source) {
                    result.push_str(s.trim_matches('"'));
                }
            }
        }
        if !result.is_empty() {
            return Some(result);
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(s) = find_string_in_subtree(&child, source) {
            return Some(s);
        }
    }
    None
}

/// Extract a string from a node (direct string_literal or macro wrapping one).
fn extract_string_from_node(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    if node.kind() == "string_literal" {
        return node
            .utf8_text(source)
            .ok()
            .map(|s| s.trim_matches('"').to_string());
    }
    find_string_in_subtree(node, source)
}

/// Collect non-punctuation children of an argument_list (the real arguments).
fn collect_real_args<'a>(args: &'a tree_sitter::Node) -> Vec<tree_sitter::Node<'a>> {
    let mut result = Vec::new();
    let mut cursor = args.walk();
    for child in args.children(&mut cursor) {
        match child.kind() {
            "(" | ")" | "," => continue,
            _ => result.push(child),
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Implementation function extraction
// ---------------------------------------------------------------------------

/// Extract the implementation function name from the second argument of m.impl().
/// Handles: direct identifiers, TORCH_FN(fn), torch::dispatch(key, TORCH_FN(fn)),
/// torch::CppFunction::makeFallthrough() (returns None), makeFromBoxedFunction<&fn>(),
/// and lambda expressions (returns None).
fn extract_impl_function(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let text = node.utf8_text(source).ok()?;
    let text = text.trim();

    // Fallthrough is not a real function binding
    if text.contains("makeFallthrough") {
        return None;
    }

    // Lambda -- no extractable function name
    if node.kind() == "lambda_expression" || text.starts_with('[') {
        return None;
    }

    // TORCH_FN(some::function) -> "some::function"
    if let Some(inner) = unwrap_torch_fn(node, source) {
        return Some(inner);
    }

    // torch::dispatch(key, TORCH_FN(fn)) -> dig into the TORCH_FN
    if text.starts_with("torch::dispatch") || text.contains("::dispatch(") {
        if let Some(inner) = find_torch_fn_in_subtree(node, source) {
            return Some(inner);
        }
    }

    // torch::CppFunction::makeFromBoxedFunction<&fn>()
    if text.contains("makeFromBoxedFunction") {
        return extract_template_function_ref(text);
    }

    // Direct function reference
    match node.kind() {
        "qualified_identifier" | "identifier" => {
            let name = strip_address_of(text);
            if !name.is_empty() {
                return Some(name);
            }
        }
        _ => {}
    }

    // Simple reference without parens/braces/brackets
    let cleaned = strip_address_of(text);
    if !cleaned.is_empty()
        && !cleaned.contains('(')
        && !cleaned.contains('{')
        && !cleaned.contains('[')
    {
        return Some(cleaned);
    }

    None
}

/// Unwrap `TORCH_FN(something)` to return the inner function name.
fn unwrap_torch_fn(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    if node.kind() != "call_expression" {
        return None;
    }
    let func = node.child_by_field_name("function")?;
    let func_text = func.utf8_text(source).ok()?;
    if func_text != "TORCH_FN" {
        return None;
    }
    let args = node.child_by_field_name("arguments")?;
    let real = collect_real_args(&args);
    real.first().and_then(|inner| {
        inner
            .utf8_text(source)
            .ok()
            .map(|s| strip_address_of(s))
    })
}

/// Recursively find a TORCH_FN(...) call and extract its argument.
fn find_torch_fn_in_subtree(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    if let Some(result) = unwrap_torch_fn(node, source) {
        return Some(result);
    }
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(result) = find_torch_fn_in_subtree(&child, source) {
            return Some(result);
        }
    }
    None
}

/// Extract function reference from `makeFromBoxedFunction<&functionName>()`.
fn extract_template_function_ref(text: &str) -> Option<String> {
    let start = text.find('<')?;
    let end = text.find('>')?;
    if end <= start + 1 {
        return None;
    }
    let inner = text[start + 1..end].trim().trim_start_matches('&').trim();
    if !inner.is_empty() {
        Some(inner.to_string())
    } else {
        None
    }
}

/// Extract fallback function from m.fallback(...) argument.
fn extract_fallback_function(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let text = node.utf8_text(source).ok()?;
    let text = text.trim();

    if text.contains("makeFallthrough") {
        return Some("__fallthrough__".to_string());
    }

    if text.contains("makeFromBoxedFunction") {
        return extract_template_function_ref(text);
    }

    // Macro constant like AUTOGRAD_FALLBACK or direct identifier
    if node.kind() == "identifier" || node.kind() == "qualified_identifier" {
        return Some(text.to_string());
    }

    if let Some(inner) = find_torch_fn_in_subtree(node, source) {
        return Some(inner);
    }

    None
}

// ---------------------------------------------------------------------------
// Name construction
// ---------------------------------------------------------------------------

/// Build the exposed name from namespace + operator name.
/// Avoids double-namespace (e.g., "aten::aten::foo") when the schema string
/// already contains a namespace prefix.
fn build_exposed_name(namespace: &str, raw_name: &str) -> String {
    // Strip signature part after first '('
    let base = raw_name.split('(').next().unwrap_or(raw_name).trim();

    // If the name already has a namespace prefix, use it as-is
    if let Some(pos) = base.find("::") {
        let existing_ns = &base[..pos];
        let op_part = &base[pos + 2..];
        if !existing_ns.is_empty() && !op_part.is_empty() {
            return format!("{}::{}", existing_ns, op_part);
        }
    }

    format!("{}::{}", namespace, base)
}

// ---------------------------------------------------------------------------
// Macro argument parsing
// ---------------------------------------------------------------------------

/// Parse first two arguments: `MACRO(arg1, arg2, ...)`.
fn parse_macro_args_2(text: &str) -> Option<(String, String)> {
    let inner = extract_macro_arg_text(text)?;
    let parts: Vec<&str> = inner.splitn(3, ',').collect();
    if parts.len() >= 2 {
        Some((parts[0].trim().to_string(), parts[1].trim().to_string()))
    } else {
        None
    }
}

/// Parse first argument: `MACRO(arg1, ...)`.
fn parse_macro_args_1(text: &str) -> Option<String> {
    let inner = extract_macro_arg_text(text)?;
    let first = inner.split(',').next()?.trim();
    if first.is_empty() {
        None
    } else {
        Some(first.to_string())
    }
}

/// Extract text between the first balanced `(...)` pair.
fn extract_macro_arg_text(text: &str) -> Option<String> {
    let open = text.find('(')?;
    let mut depth = 0;
    for (i, ch) in text[open..].char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(text[open + 1..open + i].to_string());
                }
            }
            _ => {}
        }
    }
    None
}

/// Strip address-of operator and surrounding parentheses from function references.
/// Handles patterns like `(&some::func)`, `&some::func`, `(some::func)`.
fn strip_address_of(s: &str) -> String {
    let mut s = s.trim();
    // Strip outer parens: (&fn) or (fn)
    if s.starts_with('(') && s.ends_with(')') {
        s = &s[1..s.len() - 1];
        s = s.trim();
    }
    // Strip address-of
    if s.starts_with('&') {
        s = &s[1..];
        s = s.trim();
    }
    s.to_string()
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() > max {
        let end = s
            .char_indices()
            .take_while(|(i, _)| *i < max)
            .last()
            .map(|(i, c)| i + c.len_utf8())
            .unwrap_or(max.min(s.len()));
        format!("{}...", &s[..end])
    } else {
        s.to_string()
    }
}
