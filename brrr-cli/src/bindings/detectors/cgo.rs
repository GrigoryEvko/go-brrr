//! CGo binding detector.
//!
//! Detects:
//! - `import "C"` pseudo-import enabling CGo mode
//! - `C.func_name()` calls to C functions
//! - `//export FuncName` comments exporting Go functions to C

use tree_sitter::Tree;

use crate::bindings::detector::BindingDetector;
use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::types::FunctionRef;
use crate::error::Result;

pub struct CGoDetector;

impl BindingDetector for CGoDetector {
    fn system(&self) -> BindingSystem {
        BindingSystem::CGo
    }

    fn applicable_languages(&self) -> &[&'static str] {
        &["go"]
    }

    fn quick_check(&self, source: &[u8], _language: &str) -> bool {
        memchr::memmem::find(source, b"\"C\"").is_some()
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

        // Check if file has `import "C"`
        let has_cgo = has_import_c(&root, source);
        if !has_cgo {
            return Ok(declarations);
        }

        // Scan for `//export FuncName` comments in source text
        let source_str = std::str::from_utf8(source).unwrap_or("");
        for (line_idx, line) in source_str.lines().enumerate() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("//export ") {
                let func_name = rest.trim();
                if !func_name.is_empty() && func_name.chars().all(|c| c.is_alphanumeric() || c == '_') {
                    declarations.push(BindingDeclaration {
                        system: BindingSystem::CGo,
                        direction: BindingDirection::Export,
                        exposed_name: func_name.to_string(),
                        host_function: Some(FunctionRef {
                            file: file_path.to_string(),
                            name: func_name.to_string(),
                            qualified_name: None,
                        }),
                        target_function: None,
                        declaration_file: file_path.to_string(),
                        declaration_line: line_idx + 1,
                        module_name: None,
                        class_name: None,
                        raw_pattern: Some(trimmed.to_string()),
                        confidence: 1.0,
                    });
                }
            }
        }

        // Walk AST for C.func_name() calls
        collect_c_calls(&root, source, file_path, &mut declarations);

        Ok(declarations)
    }
}

fn has_import_c(root: &tree_sitter::Node, source: &[u8]) -> bool {
    let mut cursor = root.walk();
    for node in root.children(&mut cursor) {
        if node.kind() == "import_declaration" {
            let mut inner = node.walk();
            for child in node.children(&mut inner) {
                if child.kind() == "import_spec" || child.kind() == "interpreted_string_literal" {
                    if let Ok(text) = child.utf8_text(source) {
                        if text.trim_matches('"') == "C" || text == "\"C\"" {
                            return true;
                        }
                    }
                }
            }
        }
    }
    false
}

fn collect_c_calls(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
) {
    if node.kind() == "call_expression" {
        // Look for C.func_name pattern
        if let Some(func_node) = node.child_by_field_name("function") {
            if func_node.kind() == "selector_expression" {
                let operand = func_node.child_by_field_name("operand");
                let field = func_node.child_by_field_name("field");
                if let (Some(op), Some(f)) = (operand, field) {
                    if let (Ok(op_text), Ok(f_text)) = (op.utf8_text(source), f.utf8_text(source)) {
                        if op_text == "C" {
                            declarations.push(BindingDeclaration {
                                system: BindingSystem::CGo,
                                direction: BindingDirection::Import,
                                exposed_name: f_text.to_string(),
                                host_function: None,
                                target_function: Some(FunctionRef {
                                    file: String::new(),
                                    name: f_text.to_string(),
                                    qualified_name: None,
                                }),
                                declaration_file: file_path.to_string(),
                                declaration_line: node.start_position().row + 1,
                                module_name: None,
                                class_name: None,
                                raw_pattern: node.utf8_text(source).ok().map(|s| s.to_string()),
                                confidence: 1.0,
                            });
                        }
                    }
                }
            }
        }
    }

    // Recurse into children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_c_calls(&child, source, file_path, declarations);
    }
}
