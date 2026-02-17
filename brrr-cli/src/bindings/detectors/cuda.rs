//! CUDA dispatch macro detector.
//!
//! Detects:
//! - `REGISTER_DISPATCH(stub_name, &kernel_impl)` — kernel registration
//! - `DECLARE_DISPATCH(fn_type, stub_name)` — dispatch stub declaration
//! - `DEFINE_DISPATCH(stub_name)` — dispatch stub definition

use tree_sitter::Tree;

use crate::bindings::detector::BindingDetector;
use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::types::FunctionRef;
use crate::error::Result;

pub struct CudaDispatchDetector;

impl BindingDetector for CudaDispatchDetector {
    fn system(&self) -> BindingSystem {
        BindingSystem::CudaDispatch
    }

    fn applicable_languages(&self) -> &[&'static str] {
        &["cpp", "c"]
    }

    fn quick_check(&self, source: &[u8], _language: &str) -> bool {
        memchr::memmem::find(source, b"REGISTER_DISPATCH").is_some()
            || memchr::memmem::find(source, b"DEFINE_DISPATCH").is_some()
            || memchr::memmem::find(source, b"DECLARE_DISPATCH").is_some()
    }

    fn detect(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
        _language: &str,
    ) -> Result<Vec<BindingDeclaration>> {
        let mut declarations = Vec::new();
        collect_dispatch_macros(&tree.root_node(), source, file_path, &mut declarations);
        Ok(declarations)
    }
}

fn collect_dispatch_macros(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
) {
    // tree-sitter-cpp sees these macros as call_expression nodes
    if node.kind() == "call_expression" || node.kind() == "expression_statement" {
        if let Ok(text) = node.utf8_text(source) {
            let text = text.trim();

            if let Some(rest) = text.strip_prefix("REGISTER_DISPATCH(") {
                // REGISTER_DISPATCH(stub_name, &kernel_impl)
                if let Some(closing) = rest.rfind(')') {
                    let args = &rest[..closing];
                    let parts: Vec<&str> = args.splitn(2, ',').collect();
                    if parts.len() == 2 {
                        let stub_name = parts[0].trim().to_string();
                        let kernel_ref = parts[1].trim().trim_start_matches('&').trim().to_string();

                        declarations.push(BindingDeclaration {
                            system: BindingSystem::CudaDispatch,
                            direction: BindingDirection::Dispatch,
                            exposed_name: stub_name.clone(),
                            host_function: Some(FunctionRef {
                                file: String::new(),
                                name: kernel_ref,
                                qualified_name: None,
                            }),
                            target_function: None,
                            declaration_file: file_path.to_string(),
                            declaration_line: node.start_position().row + 1,
                            module_name: None,
                            class_name: None,
                            raw_pattern: Some(text.to_string()),
                            confidence: 1.0,
                        });
                    }
                }
            } else if let Some(rest) = text.strip_prefix("DEFINE_DISPATCH(") {
                // DEFINE_DISPATCH(stub_name);
                if let Some(closing) = rest.find(')') {
                    let stub_name = rest[..closing].trim().to_string();
                    declarations.push(BindingDeclaration {
                        system: BindingSystem::CudaDispatch,
                        direction: BindingDirection::Dispatch,
                        exposed_name: stub_name,
                        host_function: None,
                        target_function: None,
                        declaration_file: file_path.to_string(),
                        declaration_line: node.start_position().row + 1,
                        module_name: None,
                        class_name: None,
                        raw_pattern: Some(text.to_string()),
                        confidence: 1.0,
                    });
                }
            } else if let Some(rest) = text.strip_prefix("DECLARE_DISPATCH(") {
                // DECLARE_DISPATCH(fn_type, stub_name)
                if let Some(closing) = rest.rfind(')') {
                    let args = &rest[..closing];
                    let parts: Vec<&str> = args.splitn(2, ',').collect();
                    if parts.len() == 2 {
                        let stub_name = parts[1].trim().to_string();
                        declarations.push(BindingDeclaration {
                            system: BindingSystem::CudaDispatch,
                            direction: BindingDirection::Dispatch,
                            exposed_name: stub_name,
                            host_function: None,
                            target_function: None,
                            declaration_file: file_path.to_string(),
                            declaration_line: node.start_position().row + 1,
                            module_name: None,
                            class_name: None,
                            raw_pattern: Some(text.to_string()),
                            confidence: 1.0,
                        });
                    }
                }
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_dispatch_macros(&child, source, file_path, declarations);
    }
}
