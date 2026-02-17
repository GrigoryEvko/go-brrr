//! napi-rs binding detector.
//!
//! Detects `#[napi]` attribute on Rust functions/structs/impl blocks,
//! which exports them to Node.js via N-API.

use tree_sitter::Tree;

use crate::bindings::detector::BindingDetector;
use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::types::FunctionRef;
use crate::error::Result;

pub struct NapiDetector;

impl BindingDetector for NapiDetector {
    fn system(&self) -> BindingSystem {
        BindingSystem::NapiRs
    }

    fn applicable_languages(&self) -> &[&'static str] {
        &["rust"]
    }

    fn quick_check(&self, source: &[u8], _language: &str) -> bool {
        memchr::memmem::find(source, b"#[napi").is_some()
    }

    fn detect(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
        _language: &str,
    ) -> Result<Vec<BindingDeclaration>> {
        let mut declarations = Vec::new();
        collect_napi_items(&tree.root_node(), source, file_path, &mut declarations);
        Ok(declarations)
    }
}

fn collect_napi_items(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
) {
    if node.kind() == "attributed_item" {
        let has_napi = node.children(&mut node.walk()).any(|c| {
            (c.kind() == "attribute_item" || c.kind() == "attribute")
                && c.utf8_text(source)
                    .ok()
                    .map(|t| t.contains("napi"))
                    .unwrap_or(false)
        });

        if has_napi {
            // Find the inner item (function_item, struct_item, impl_item)
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                match child.kind() {
                    "function_item" => {
                        if let Some(name) = child
                            .child_by_field_name("name")
                            .and_then(|n| n.utf8_text(source).ok())
                        {
                            declarations.push(BindingDeclaration {
                                system: BindingSystem::NapiRs,
                                direction: BindingDirection::Export,
                                exposed_name: name.to_string(),
                                host_function: Some(FunctionRef {
                                    file: file_path.to_string(),
                                    name: name.to_string(),
                                    qualified_name: None,
                                }),
                                target_function: None,
                                declaration_file: file_path.to_string(),
                                declaration_line: child.start_position().row + 1,
                                module_name: None,
                                class_name: None,
                                raw_pattern: child.utf8_text(source).ok().map(|s| {
                                    s.lines().next().unwrap_or(s).to_string()
                                }),
                                confidence: 1.0,
                            });
                        }
                    }
                    "struct_item" => {
                        if let Some(name) = child
                            .child_by_field_name("name")
                            .and_then(|n| n.utf8_text(source).ok())
                        {
                            declarations.push(BindingDeclaration {
                                system: BindingSystem::NapiRs,
                                direction: BindingDirection::Export,
                                exposed_name: name.to_string(),
                                host_function: Some(FunctionRef {
                                    file: file_path.to_string(),
                                    name: name.to_string(),
                                    qualified_name: None,
                                }),
                                target_function: None,
                                declaration_file: file_path.to_string(),
                                declaration_line: child.start_position().row + 1,
                                module_name: None,
                                class_name: Some(name.to_string()),
                                raw_pattern: child.utf8_text(source).ok().map(|s| {
                                    s.lines().next().unwrap_or(s).to_string()
                                }),
                                confidence: 1.0,
                            });
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_napi_items(&child, source, file_path, declarations);
    }
}
