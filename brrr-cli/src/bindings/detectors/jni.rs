//! JNI binding detector.
//!
//! Detects:
//! - Java side: `native ReturnType methodName(args);`
//! - C/C++ side: `JNIEXPORT jtype JNICALL Java_pkg_Class_method(JNIEnv*, ...)`

use tree_sitter::Tree;

use crate::bindings::detector::BindingDetector;
use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::types::FunctionRef;
use crate::error::Result;

pub struct JniDetector;

impl BindingDetector for JniDetector {
    fn system(&self) -> BindingSystem {
        BindingSystem::Jni
    }

    fn applicable_languages(&self) -> &[&'static str] {
        &["java", "c", "cpp"]
    }

    fn quick_check(&self, source: &[u8], language: &str) -> bool {
        match language {
            "java" => memchr::memmem::find(source, b"native ").is_some(),
            "c" | "cpp" => {
                memchr::memmem::find(source, b"JNIEXPORT").is_some()
                    || memchr::memmem::find(source, b"Java_").is_some()
            }
            _ => false,
        }
    }

    fn detect(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
        language: &str,
    ) -> Result<Vec<BindingDeclaration>> {
        match language {
            "java" => detect_java_native(tree, source, file_path),
            "c" | "cpp" => detect_jni_c_impl(tree, source, file_path),
            _ => Ok(Vec::new()),
        }
    }
}

/// Detect `native` method declarations in Java.
fn detect_java_native(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
) -> Result<Vec<BindingDeclaration>> {
    let mut declarations = Vec::new();
    collect_java_native(&tree.root_node(), source, file_path, &mut declarations, None);
    Ok(declarations)
}

fn collect_java_native(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    class_name: Option<&str>,
) {
    match node.kind() {
        "class_declaration" => {
            let name = node
                .child_by_field_name("name")
                .and_then(|n| n.utf8_text(source).ok());
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "class_body" {
                    let mut body_cursor = child.walk();
                    for item in child.children(&mut body_cursor) {
                        collect_java_native(&item, source, file_path, declarations, name);
                    }
                }
            }
            return;
        }
        "method_declaration" => {
            // Check for `native` modifier
            let has_native = node.children(&mut node.walk()).any(|c| {
                c.kind() == "modifiers"
                    && c.children(&mut c.walk())
                        .any(|m| m.utf8_text(source).ok() == Some("native"))
            });

            if has_native {
                let method_name = node
                    .child_by_field_name("name")
                    .and_then(|n| n.utf8_text(source).ok());

                if let Some(name) = method_name {
                    declarations.push(BindingDeclaration {
                        system: BindingSystem::Jni,
                        direction: BindingDirection::Import,
                        exposed_name: name.to_string(),
                        host_function: None,
                        target_function: None, // Will be resolved to Java_pkg_Class_method
                        declaration_file: file_path.to_string(),
                        declaration_line: node.start_position().row + 1,
                        module_name: None,
                        class_name: class_name.map(|s| s.to_string()),
                        raw_pattern: node.utf8_text(source).ok().map(|s| {
                            s.lines().next().unwrap_or(s).to_string()
                        }),
                        confidence: 1.0,
                    });
                }
            }
        }
        _ => {}
    }

    // Recurse (but not into class bodies — handled above)
    if node.kind() != "class_declaration" {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            collect_java_native(&child, source, file_path, declarations, class_name);
        }
    }
}

/// Detect JNI function implementations in C/C++ (Java_pkg_Class_method pattern).
fn detect_jni_c_impl(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
) -> Result<Vec<BindingDeclaration>> {
    let mut declarations = Vec::new();
    collect_jni_c_functions(&tree.root_node(), source, file_path, &mut declarations);
    Ok(declarations)
}

fn collect_jni_c_functions(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
) {
    if node.kind() == "function_definition" || node.kind() == "declaration" {
        // Look for function name starting with "Java_"
        if let Some(name) = extract_function_name(node, source) {
            if name.starts_with("Java_") {
                // Parse JNI name: Java_<package>_<Class>_<method>
                let parts: Vec<&str> = name.splitn(4, '_').collect();
                let (class_name, method_name) = if parts.len() >= 4 {
                    // Java_pkg_Class_method
                    (Some(parts[2].to_string()), parts[3].to_string())
                } else if parts.len() == 3 {
                    // Java_Class_method (no package)
                    (Some(parts[1].to_string()), parts[2].to_string())
                } else {
                    (None, name.clone())
                };

                declarations.push(BindingDeclaration {
                    system: BindingSystem::Jni,
                    direction: BindingDirection::Export,
                    exposed_name: method_name,
                    host_function: Some(FunctionRef {
                        file: file_path.to_string(),
                        name,
                        qualified_name: None,
                    }),
                    target_function: None,
                    declaration_file: file_path.to_string(),
                    declaration_line: node.start_position().row + 1,
                    module_name: None,
                    class_name,
                    raw_pattern: node.utf8_text(source).ok().map(|s| {
                        s.lines().next().unwrap_or(s).to_string()
                    }),
                    confidence: 1.0,
                });
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_jni_c_functions(&child, source, file_path, declarations);
    }
}

fn extract_function_name(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    // For function_definition or declaration, find the declarator -> identifier
    let declarator = node.child_by_field_name("declarator")?;
    find_identifier(&declarator, source)
}

fn find_identifier(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    if node.kind() == "identifier" || node.kind() == "field_identifier" {
        return node.utf8_text(source).ok().map(|s| s.to_string());
    }
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(name) = find_identifier(&child, source) {
            return Some(name);
        }
    }
    None
}
