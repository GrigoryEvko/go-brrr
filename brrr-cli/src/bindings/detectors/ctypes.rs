//! ctypes binding detector.
//!
//! Detects Python code that loads C shared libraries via ctypes:
//! - `lib = ctypes.CDLL("libfoo.so")` / `ctypes.WinDLL(...)` / `ctypes.cdll.LoadLibrary(...)`
//! - `lib.func_name(args)` — C function calls through the library handle
//! - `lib.func_name.argtypes` / `.restype` — type annotations

use tree_sitter::Tree;

use crate::bindings::detector::BindingDetector;
use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::types::FunctionRef;
use crate::error::Result;

pub struct CtypesDetector;

impl BindingDetector for CtypesDetector {
    fn system(&self) -> BindingSystem {
        BindingSystem::Ctypes
    }

    fn applicable_languages(&self) -> &[&'static str] {
        &["python"]
    }

    fn quick_check(&self, source: &[u8], _language: &str) -> bool {
        memchr::memmem::find(source, b"ctypes").is_some()
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

        // Phase 1: Find CDLL/WinDLL/OleDLL variable assignments
        let mut lib_vars: Vec<String> = Vec::new();
        collect_cdll_vars(&root, source, &mut lib_vars);

        if lib_vars.is_empty() {
            return Ok(declarations);
        }

        // Phase 2: Find attribute calls on lib vars (lib.func_name(...))
        collect_ctypes_calls(&root, source, file_path, &lib_vars, &mut declarations);

        Ok(declarations)
    }
}

/// Collect variable names assigned from ctypes.CDLL/WinDLL/OleDLL/cdll.LoadLibrary.
fn collect_cdll_vars(node: &tree_sitter::Node, source: &[u8], vars: &mut Vec<String>) {
    // Pattern: identifier = ctypes.CDLL("...")
    if node.kind() == "assignment" || node.kind() == "expression_statement" {
        let target_node = if node.kind() == "assignment" {
            node.child_by_field_name("left")
        } else {
            // expression_statement may contain an assignment
            node.child(0).and_then(|c| {
                if c.kind() == "assignment" {
                    c.child_by_field_name("left")
                } else {
                    None
                }
            })
        };
        let value_node = if node.kind() == "assignment" {
            node.child_by_field_name("right")
        } else {
            node.child(0).and_then(|c| {
                if c.kind() == "assignment" {
                    c.child_by_field_name("right")
                } else {
                    None
                }
            })
        };

        if let (Some(target), Some(value)) = (target_node, value_node) {
            if target.kind() == "identifier" {
                if let Ok(value_text) = value.utf8_text(source) {
                    if is_cdll_call(value_text) {
                        if let Ok(var_name) = target.utf8_text(source) {
                            vars.push(var_name.to_string());
                        }
                    }
                }
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_cdll_vars(&child, source, vars);
    }
}

fn is_cdll_call(text: &str) -> bool {
    text.contains("ctypes.CDLL")
        || text.contains("ctypes.WinDLL")
        || text.contains("ctypes.OleDLL")
        || text.contains("ctypes.PyDLL")
        || text.contains("ctypes.cdll.LoadLibrary")
        || text.contains("ctypes.windll.LoadLibrary")
        || text.contains("CDLL(")
        || text.contains("WinDLL(")
}

/// Collect lib.func_name() calls where lib is a known CDLL variable.
fn collect_ctypes_calls(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    lib_vars: &[String],
    declarations: &mut Vec<BindingDeclaration>,
) {
    if node.kind() == "call" {
        if let Some(func) = node.child_by_field_name("function") {
            if func.kind() == "attribute" {
                let obj = func.child_by_field_name("object");
                let attr = func.child_by_field_name("attribute");
                if let (Some(obj), Some(attr)) = (obj, attr) {
                    if let (Ok(obj_text), Ok(attr_text)) = (obj.utf8_text(source), attr.utf8_text(source))
                    {
                        if lib_vars.iter().any(|v| v == obj_text) {
                            // Skip ctypes-internal methods
                            if !is_ctypes_builtin(attr_text) {
                                declarations.push(BindingDeclaration {
                                    system: BindingSystem::Ctypes,
                                    direction: BindingDirection::Import,
                                    exposed_name: attr_text.to_string(),
                                    host_function: None,
                                    target_function: Some(FunctionRef {
                                        file: String::new(),
                                        name: attr_text.to_string(),
                                        qualified_name: None,
                                    }),
                                    declaration_file: file_path.to_string(),
                                    declaration_line: node.start_position().row + 1,
                                    module_name: None,
                                    class_name: None,
                                    raw_pattern: node.utf8_text(source).ok().map(|s| s.to_string()),
                                    confidence: 0.9,
                                });
                            }
                        }
                    }
                }
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_ctypes_calls(&child, source, file_path, lib_vars, declarations);
    }
}

fn is_ctypes_builtin(attr: &str) -> bool {
    matches!(
        attr,
        "LoadLibrary" | "argtypes" | "restype" | "errcheck" | "__getattr__"
    )
}
