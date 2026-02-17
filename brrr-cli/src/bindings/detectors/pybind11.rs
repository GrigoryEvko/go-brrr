//! pybind11/nanobind binding detector.
//!
//! Detects C++ code that exposes functions/classes to Python:
//! - `PYBIND11_MODULE(name, m) { ... }` and `NB_MODULE(name, m) { ... }`
//! - `m.def("py_name", &cpp_func)` — function binding
//! - `py::class_<T>(m, "PyName").def("method", &T::method)` — class binding
//! - `.def(py::init<...>())` — constructor binding
//! - `.def_readwrite("attr", &T::member)` — property binding

use tree_sitter::Tree;

use crate::bindings::detector::BindingDetector;
use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::types::FunctionRef;
use crate::error::Result;

pub struct Pybind11Detector;

impl BindingDetector for Pybind11Detector {
    fn system(&self) -> BindingSystem {
        BindingSystem::Pybind11
    }

    fn applicable_languages(&self) -> &[&'static str] {
        &["cpp"]
    }

    fn quick_check(&self, source: &[u8], _language: &str) -> bool {
        memchr::memmem::find(source, b"PYBIND11_MODULE").is_some()
            || memchr::memmem::find(source, b"pybind11").is_some()
            || memchr::memmem::find(source, b"py::module").is_some()
            || memchr::memmem::find(source, b"py::class_").is_some()
            || memchr::memmem::find(source, b"NB_MODULE").is_some()
            || memchr::memmem::find(source, b"nanobind").is_some()
            || memchr::memmem::find(source, b".def(").is_some()
                && memchr::memmem::find(source, b"py::").is_some()
    }

    fn detect(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
        _language: &str,
    ) -> Result<Vec<BindingDeclaration>> {
        let mut declarations = Vec::new();
        collect_pybind_bindings(&tree.root_node(), source, file_path, &mut declarations, None);
        Ok(declarations)
    }
}

fn collect_pybind_bindings(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    module_name: Option<&str>,
) {
    let kind = node.kind();

    // Detect PYBIND11_MODULE(name, m) { ... } — tree-sitter-cpp sees as function_definition
    if kind == "function_definition" {
        if let Some(text) = node.utf8_text(source).ok() {
            if text.starts_with("PYBIND11_MODULE") || text.starts_with("NB_MODULE") {
                // Extract module name from the macro arguments
                let mod_name = extract_macro_first_arg(node, source)
                    .unwrap_or_else(|| "unknown".to_string());

                // Walk the body for .def() and py::class_<> calls
                if let Some(body) = node.child_by_field_name("body") {
                    collect_pybind_bindings(
                        &body,
                        source,
                        file_path,
                        declarations,
                        Some(&mod_name),
                    );
                }
                return;
            }
        }
    }

    // Detect m.def("python_name", &cpp_func) and variants
    if kind == "call_expression" {
        if let Some(text) = node.utf8_text(source).ok() {
            // .def("name", ...) or .def_readwrite("name", ...) or .def_readonly(...)
            if text.contains(".def(") || text.contains(".def_readwrite(") || text.contains(".def_readonly(") || text.contains(".def_static(") {
                if let Some(decl) = parse_def_call(node, source, file_path, module_name) {
                    declarations.push(decl);
                }
            }

            // py::class_<CppType>(m, "PyName") — extract class binding context
            if text.contains("py::class_") || text.contains("nb::class_") {
                if let Some(class_info) = parse_class_binding(node, source) {
                    // Walk the chained .def() calls on this class
                    collect_chained_defs(
                        node,
                        source,
                        file_path,
                        declarations,
                        module_name,
                        Some(&class_info),
                    );
                    return;
                }
            }
        }
    }

    // Recurse
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_pybind_bindings(&child, source, file_path, declarations, module_name);
    }
}

/// Parse `m.def("python_name", &cpp_function)` style calls.
fn parse_def_call(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    module_name: Option<&str>,
) -> Option<BindingDeclaration> {
    let args = node.child_by_field_name("arguments")?;
    let mut arg_cursor = args.walk();
    let arg_children: Vec<_> = args.children(&mut arg_cursor).collect();

    // First string argument is the Python-visible name
    let py_name = arg_children.iter().find_map(|c| {
        if c.kind() == "string_literal" || c.kind() == "string_content" {
            c.utf8_text(source).ok().map(|s| s.trim_matches('"').to_string())
        } else {
            None
        }
    })?;

    // Second argument is typically &cpp_func or &Class::method or a lambda
    let cpp_ref = arg_children.iter().find_map(|c| {
        if c.kind() == "pointer_expression" || c.kind() == "unary_expression" {
            // &cpp_function or &Class::method
            c.utf8_text(source)
                .ok()
                .map(|s| s.trim_start_matches('&').trim().to_string())
        } else {
            None
        }
    });

    // Extract class::method if present
    let (class_name, func_name) = if let Some(ref cpp) = cpp_ref {
        if cpp.contains("::") {
            let parts: Vec<&str> = cpp.rsplitn(2, "::").collect();
            (Some(parts[1].to_string()), parts[0].to_string())
        } else {
            (None, cpp.clone())
        }
    } else {
        (None, py_name.clone())
    };

    Some(BindingDeclaration {
        system: BindingSystem::Pybind11,
        direction: BindingDirection::Export,
        exposed_name: py_name,
        host_function: cpp_ref.as_ref().map(|name| FunctionRef {
            file: String::new(),
            name: func_name,
            qualified_name: Some(name.clone()),
        }),
        target_function: None,
        declaration_file: file_path.to_string(),
        declaration_line: node.start_position().row + 1,
        module_name: module_name.map(|s| s.to_string()),
        class_name,
        raw_pattern: node.utf8_text(source).ok().map(|s| {
            // Truncate long patterns
            if s.len() > 200 {
                format!("{}...", &s[..200])
            } else {
                s.to_string()
            }
        }),
        confidence: 1.0,
    })
}

struct ClassBindingInfo {
    #[allow(dead_code)]
    cpp_type: String,
    py_name: String,
}

/// Parse `py::class_<CppType>(m, "PyName")`.
fn parse_class_binding(node: &tree_sitter::Node, source: &[u8]) -> Option<ClassBindingInfo> {
    let text = node.utf8_text(source).ok()?;

    // Extract template parameter: py::class_<CppType>
    let cpp_type = text
        .find("class_<")
        .and_then(|start| {
            let rest = &text[start + 7..];
            rest.find('>').map(|end| rest[..end].trim().to_string())
        })?;

    // Extract Python name from arguments
    let args = node.child_by_field_name("arguments")?;
    let py_name = args.children(&mut args.walk()).find_map(|c| {
        if c.kind() == "string_literal" || c.kind() == "string_content" {
            c.utf8_text(source).ok().map(|s| s.trim_matches('"').to_string())
        } else {
            None
        }
    })?;

    Some(ClassBindingInfo { cpp_type, py_name })
}

/// Walk chained `.def()` calls on a py::class_ expression.
fn collect_chained_defs(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    module_name: Option<&str>,
    class_info: Option<&ClassBindingInfo>,
) {
    // In tree-sitter-cpp, chained calls like `py::class_<T>(...).def(...)` are nested:
    // call_expression(call_expression(...).def, args)
    // Walk the parent chain looking for .def() calls
    let mut current = *node;
    loop {
        let parent = current.parent();
        match parent {
            Some(p) if p.kind() == "call_expression" || p.kind() == "field_expression" => {
                if p.kind() == "call_expression" {
                    if let Some(text) = p.utf8_text(source).ok() {
                        if text.contains(".def(") && !text.starts_with("py::class_") && !text.starts_with("nb::class_") {
                            if let Some(mut decl) = parse_def_call(&p, source, file_path, module_name) {
                                if let Some(info) = class_info {
                                    decl.class_name = Some(info.py_name.clone());
                                }
                                declarations.push(decl);
                            }
                        }
                    }
                }
                current = p;
            }
            _ => break,
        }
    }
}

/// Extract the first argument from a macro-like call: `MACRO(first, second) { ... }`.
fn extract_macro_first_arg(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    // tree-sitter-cpp treats PYBIND11_MODULE(name, m) as function declarator
    let declarator = node.child_by_field_name("declarator")?;
    let params = declarator.child_by_field_name("parameters")?;
    let mut cursor = params.walk();
    for child in params.children(&mut cursor) {
        if child.kind() == "parameter_declaration" || child.kind() == "identifier" {
            if let Ok(text) = child.utf8_text(source) {
                let name = text.trim();
                if !name.is_empty() && name != "(" && name != ")" && name != "," {
                    return Some(name.to_string());
                }
            }
        }
    }
    None
}
