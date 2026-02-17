//! TORCH_LIBRARY macro detector.
//!
//! Detects:
//! - `TORCH_LIBRARY(namespace, m) { m.def("op", ...); }` — operator schema registration
//! - `TORCH_LIBRARY_IMPL(namespace, dispatch_key, m) { m.impl("op", impl_fn); }`
//! - `TORCH_LIBRARY_FRAGMENT(namespace, m) { ... }` — additional registrations

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

fn collect_torch_library(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
) {
    // TORCH_LIBRARY and friends are parsed by tree-sitter-cpp as function_definition
    // because the macro expands to `void TORCH_LIBRARY_init_##ns(torch::Library& m)`
    if node.kind() == "function_definition" {
        if let Ok(text) = node.utf8_text(source) {
            if text.starts_with("TORCH_LIBRARY_IMPL") {
                // TORCH_LIBRARY_IMPL(namespace, DispatchKey, m) { m.impl(...) }
                let meta = parse_torch_library_impl_macro(text);
                if let Some((namespace, dispatch_key)) = meta {
                    if let Some(body) = node.child_by_field_name("body") {
                        collect_m_impl_calls(
                            &body,
                            source,
                            file_path,
                            declarations,
                            &namespace,
                            Some(&dispatch_key),
                        );
                    }
                }
                return;
            } else if text.starts_with("TORCH_LIBRARY_FRAGMENT") || text.starts_with("TORCH_LIBRARY(") {
                // TORCH_LIBRARY(namespace, m) { m.def(...) }
                let namespace = parse_torch_library_namespace(text);
                if let Some(body) = node.child_by_field_name("body") {
                    collect_m_def_calls(
                        &body,
                        source,
                        file_path,
                        declarations,
                        namespace.as_deref().unwrap_or("unknown"),
                    );
                }
                return;
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_torch_library(&child, source, file_path, declarations);
    }
}

/// Collect `m.def("op_schema")` calls inside TORCH_LIBRARY body.
fn collect_m_def_calls(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    namespace: &str,
) {
    if node.kind() == "call_expression" {
        if let Ok(text) = node.utf8_text(source) {
            if text.contains(".def(") {
                // Extract the op schema string (first argument)
                if let Some(op_name) = extract_first_string_arg(node, source) {
                    // op_name might be "add.Tensor" (schema) or just "add"
                    let base_name = op_name.split('(').next().unwrap_or(&op_name).trim();
                    declarations.push(BindingDeclaration {
                        system: BindingSystem::TorchLibrary,
                        direction: BindingDirection::Dispatch,
                        exposed_name: format!("{}::{}", namespace, base_name),
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
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_m_def_calls(&child, source, file_path, declarations, namespace);
    }
}

/// Collect `m.impl("op_name", impl_fn)` calls inside TORCH_LIBRARY_IMPL body.
fn collect_m_impl_calls(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    namespace: &str,
    dispatch_key: Option<&str>,
) {
    if node.kind() == "call_expression" {
        if let Ok(text) = node.utf8_text(source) {
            if text.contains(".impl(") {
                if let Some(op_name) = extract_first_string_arg(node, source) {
                    // Try to extract the implementation function reference
                    let impl_fn = extract_second_arg_ref(node, source);

                    declarations.push(BindingDeclaration {
                        system: BindingSystem::TorchLibrary,
                        direction: BindingDirection::Dispatch,
                        exposed_name: format!("{}::{}", namespace, op_name),
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
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_m_impl_calls(&child, source, file_path, declarations, namespace, dispatch_key);
    }
}

fn extract_first_string_arg(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let args = node.child_by_field_name("arguments")?;
    let mut cursor = args.walk();
    for child in args.children(&mut cursor) {
        if child.kind() == "string_literal" || child.kind() == "string_content" {
            return child.utf8_text(source).ok().map(|s| {
                s.trim_matches('"').to_string()
            });
        }
    }
    None
}

fn extract_second_arg_ref(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let args = node.child_by_field_name("arguments")?;
    let mut cursor = args.walk();
    let children: Vec<_> = args.children(&mut cursor).collect();

    // Skip parentheses and first arg, find second non-comma argument
    let mut arg_count = 0;
    for child in &children {
        if child.kind() == "(" || child.kind() == ")" || child.kind() == "," {
            continue;
        }
        arg_count += 1;
        if arg_count == 2 {
            // This is the impl function reference
            return child.utf8_text(source).ok().map(|s| {
                s.trim_start_matches('&').trim().to_string()
            });
        }
    }
    None
}

/// Parse `TORCH_LIBRARY_IMPL(namespace, DispatchKey, m)` to extract namespace and key.
fn parse_torch_library_impl_macro(text: &str) -> Option<(String, String)> {
    let start = text.find('(')?;
    let end = text.find(')')?;
    let inner = &text[start + 1..end];
    let parts: Vec<&str> = inner.split(',').collect();
    if parts.len() >= 2 {
        Some((parts[0].trim().to_string(), parts[1].trim().to_string()))
    } else {
        None
    }
}

/// Parse `TORCH_LIBRARY(namespace, m)` to extract namespace.
fn parse_torch_library_namespace(text: &str) -> Option<String> {
    let start = text.find('(')?;
    let end = text.find(')')?;
    let inner = &text[start + 1..end];
    let parts: Vec<&str> = inner.split(',').collect();
    if !parts.is_empty() {
        Some(parts[0].trim().to_string())
    } else {
        None
    }
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() > max {
        format!("{}...", &s[..max])
    } else {
        s.to_string()
    }
}
