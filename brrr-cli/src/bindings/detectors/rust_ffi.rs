//! Rust FFI binding detector.
//!
//! Detects:
//! - `extern "C" { fn name(...); }` — foreign function imports
//! - `#[no_mangle] pub extern "C" fn name(...)` — function exports

use tree_sitter::Tree;

use crate::bindings::detector::BindingDetector;
use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::types::FunctionRef;
use crate::error::Result;

pub struct RustFfiDetector;

impl BindingDetector for RustFfiDetector {
    fn system(&self) -> BindingSystem {
        BindingSystem::RustFfi
    }

    fn applicable_languages(&self) -> &[&'static str] {
        &["rust"]
    }

    fn quick_check(&self, source: &[u8], _language: &str) -> bool {
        memchr::memmem::find(source, b"extern").is_some()
    }

    fn detect(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
        _language: &str,
    ) -> Result<Vec<BindingDeclaration>> {
        let mut declarations = Vec::new();
        let root = tree.root_node();

        let mut cursor = root.walk();
        for node in root.children(&mut cursor) {
            match node.kind() {
                // extern "C" { fn foo(...); }
                "foreign_mod_item" => {
                    let abi = get_abi(&node, source);
                    if abi.as_deref() != Some("C") && abi.as_deref() != Some("system") {
                        continue;
                    }
                    // Walk children inside the extern block
                    let mut inner = node.walk();
                    for child in node.children(&mut inner) {
                        if child.kind() == "foreign_mod_body" {
                            let mut body_cursor = child.walk();
                            for item in child.children(&mut body_cursor) {
                                if item.kind() == "function_signature_item" {
                                    if let Some(name) = get_fn_name(&item, source) {
                                        declarations.push(BindingDeclaration {
                                            system: BindingSystem::RustFfi,
                                            direction: BindingDirection::Import,
                                            exposed_name: name.clone(),
                                            host_function: None,
                                            target_function: Some(FunctionRef {
                                                file: String::new(),
                                                name: name.clone(),
                                                qualified_name: None,
                                            }),
                                            declaration_file: file_path.to_string(),
                                            declaration_line: item.start_position().row + 1,
                                            module_name: None,
                                            class_name: None,
                                            raw_pattern: node_text(&item, source),
                                            confidence: 1.0,
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
                // #[no_mangle] pub extern "C" fn foo(...)
                "function_item" | "attributed_item" => {
                    let func_node = if node.kind() == "attributed_item" {
                        // Check for #[no_mangle] attribute
                        if !has_no_mangle_attr(&node, source) {
                            continue;
                        }
                        // The actual function is a child
                        node.children(&mut node.walk())
                            .find(|c| c.kind() == "function_item")
                    } else {
                        if !has_no_mangle_attr_on_fn(&node, source) {
                            continue;
                        }
                        Some(node)
                    };
                    let Some(func_node) = func_node else {
                        continue;
                    };

                    // Check for extern "C" qualifier
                    let has_extern_c = func_node
                        .children(&mut func_node.walk())
                        .any(|c| {
                            c.kind() == "extern_modifier"
                                && node_text_str(&c, source)
                                    .map(|t| t.contains("\"C\"") || t.contains("\"system\""))
                                    .unwrap_or(false)
                        });

                    if !has_extern_c {
                        continue;
                    }

                    if let Some(name) = get_fn_name(&func_node, source) {
                        declarations.push(BindingDeclaration {
                            system: BindingSystem::RustFfi,
                            direction: BindingDirection::Export,
                            exposed_name: name.clone(),
                            host_function: Some(FunctionRef {
                                file: file_path.to_string(),
                                name: name.clone(),
                                qualified_name: None,
                            }),
                            target_function: None,
                            declaration_file: file_path.to_string(),
                            declaration_line: func_node.start_position().row + 1,
                            module_name: None,
                            class_name: None,
                            raw_pattern: node_text(&func_node, source).map(|t| {
                                // Truncate to first line for readability
                                t.lines().next().unwrap_or(&t).to_string()
                            }),
                            confidence: 1.0,
                        });
                    }
                }
                _ => {}
            }
        }

        Ok(declarations)
    }
}

fn get_abi(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "extern_modifier" {
            // Extract ABI string from extern modifier
            let text = node_text_str(&child, source)?;
            if text.contains("\"C\"") {
                return Some("C".to_string());
            } else if text.contains("\"system\"") {
                return Some("system".to_string());
            }
        }
    }
    None
}

fn get_fn_name(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "identifier" || child.kind() == "name" {
            return node_text_str(&child, source).map(|s| s.to_string());
        }
    }
    None
}

fn has_no_mangle_attr(attributed_item: &tree_sitter::Node, source: &[u8]) -> bool {
    let mut cursor = attributed_item.walk();
    for child in attributed_item.children(&mut cursor) {
        if child.kind() == "attribute_item" || child.kind() == "attribute" {
            if let Some(text) = node_text_str(&child, source) {
                if text.contains("no_mangle") {
                    return true;
                }
            }
        }
    }
    false
}

fn has_no_mangle_attr_on_fn(_node: &tree_sitter::Node, _source: &[u8]) -> bool {
    // For bare function_item nodes (not wrapped in attributed_item),
    // there's no attribute to check. Return false.
    false
}

fn node_text<'a>(node: &tree_sitter::Node, source: &'a [u8]) -> Option<String> {
    node.utf8_text(source).ok().map(|s| s.to_string())
}

fn node_text_str<'a>(node: &tree_sitter::Node, source: &'a [u8]) -> Option<&'a str> {
    node.utf8_text(source).ok()
}
