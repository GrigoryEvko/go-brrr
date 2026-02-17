//! JNI binding detector.
//!
//! Detects:
//! - Java side: `native ReturnType methodName(args);`
//! - C/C++ side: `JNIEXPORT jtype JNICALL Java_pkg_Class_method(JNIEnv*, ...)`
//!
//! Tree-sitter Java parses `native` as a keyword node inside `modifiers`.
//! Tree-sitter C parses `JNIEXPORT`/`JNICALL` as separate type_identifiers;
//! the actual function name (`Java_...`) is an identifier inside the
//! function_declarator of the second declaration/function_definition node.

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

// ---------------------------------------------------------------------------
// Java side: detect `native` method declarations
// ---------------------------------------------------------------------------

/// Detect `native` method declarations in Java.
fn detect_java_native(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
) -> Result<Vec<BindingDeclaration>> {
    let mut declarations = Vec::new();
    let package_name = extract_package_name(&tree.root_node(), source);
    collect_java_native(
        &tree.root_node(),
        source,
        file_path,
        &mut declarations,
        None,
        package_name.as_deref(),
    );
    Ok(declarations)
}

/// Extract the Java package name from `package com.example;` declarations.
fn extract_package_name(root: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let mut cursor = root.walk();
    for child in root.children(&mut cursor) {
        if child.kind() == "package_declaration" {
            let mut inner_cursor = child.walk();
            for grandchild in child.children(&mut inner_cursor) {
                match grandchild.kind() {
                    "scoped_identifier" | "identifier" => {
                        return grandchild.utf8_text(source).ok().map(|s| s.to_string());
                    }
                    _ => {}
                }
            }
        }
    }
    None
}

fn collect_java_native(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    class_name: Option<&str>,
    package_name: Option<&str>,
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
                        collect_java_native(
                            &item,
                            source,
                            file_path,
                            declarations,
                            name,
                            package_name,
                        );
                    }
                }
            }
            return;
        }
        "method_declaration" => {
            // Check for `native` keyword node inside `modifiers`.
            // Tree-sitter Java parses `native` as a named node of kind "native".
            let has_native = has_modifier(node, source, "native");

            if has_native {
                let method_name = node
                    .child_by_field_name("name")
                    .and_then(|n| n.utf8_text(source).ok());

                if let Some(name) = method_name {
                    let fq_class = match (package_name, class_name) {
                        (Some(pkg), Some(cls)) => Some(format!("{}.{}", pkg, cls)),
                        (None, Some(cls)) => Some(cls.to_string()),
                        _ => None,
                    };

                    declarations.push(BindingDeclaration {
                        system: BindingSystem::Jni,
                        direction: BindingDirection::Import,
                        exposed_name: name.to_string(),
                        host_function: None,
                        target_function: None,
                        declaration_file: file_path.to_string(),
                        declaration_line: node.start_position().row + 1,
                        module_name: package_name.map(|s| s.to_string()),
                        class_name: fq_class,
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

    // Recurse into non-class nodes (class bodies are handled above)
    if node.kind() != "class_declaration" {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            collect_java_native(
                &child, source, file_path, declarations, class_name, package_name,
            );
        }
    }
}

/// Check whether a method_declaration has a specific modifier keyword.
///
/// Tree-sitter Java CST for modifiers:
///   modifiers
///     public       <- keyword node of kind "public"
///     static       <- keyword node of kind "static"
///     native       <- keyword node of kind "native"
fn has_modifier(method_node: &tree_sitter::Node, source: &[u8], modifier: &str) -> bool {
    let mut cursor = method_node.walk();
    for child in method_node.children(&mut cursor) {
        if child.kind() == "modifiers" {
            let mut mod_cursor = child.walk();
            for m in child.children(&mut mod_cursor) {
                // Check by node kind (tree-sitter parses keywords as named nodes)
                if m.kind() == modifier {
                    return true;
                }
                // Fallback: check text content
                if let Ok(text) = m.utf8_text(source) {
                    if text == modifier {
                        return true;
                    }
                }
            }
        }
    }
    false
}

// ---------------------------------------------------------------------------
// C/C++ side: detect JNI function implementations
// ---------------------------------------------------------------------------

/// Detect JNI function implementations in C/C++ (`Java_pkg_Class_method` pattern).
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
        if let Some(name) = extract_function_name(node, source) {
            if name.starts_with("Java_") {
                let parsed = parse_jni_name(&name);

                declarations.push(BindingDeclaration {
                    system: BindingSystem::Jni,
                    direction: BindingDirection::Export,
                    exposed_name: parsed.method_name.clone(),
                    host_function: Some(FunctionRef {
                        file: file_path.to_string(),
                        name: name.clone(),
                        qualified_name: None,
                    }),
                    target_function: None,
                    declaration_file: file_path.to_string(),
                    declaration_line: node.start_position().row + 1,
                    module_name: parsed.package_name,
                    class_name: parsed.fully_qualified_class,
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

/// Parsed components of a JNI function name.
struct JniParsedName {
    method_name: String,
    package_name: Option<String>,
    fully_qualified_class: Option<String>,
}

/// Parse a JNI function name into its components.
///
/// JNI naming: `Java_<pkg1>_<pkg2>_..._<ClassName>_<methodName>`
/// where dots are replaced by underscores. Class names start with uppercase
/// by convention; the method name is always the last segment.
///
/// Overloaded methods use `__` suffix: `Java_pkg_Class_method__I`
fn parse_jni_name(jni_name: &str) -> JniParsedName {
    // Strip "Java_" prefix
    let rest = &jni_name[5..];

    // Strip overload suffix (everything after `__`)
    let rest = match rest.find("__") {
        Some(pos) => &rest[..pos],
        None => rest,
    };

    let segments: Vec<&str> = rest.split('_').collect();

    if segments.is_empty() {
        return JniParsedName {
            method_name: rest.to_string(),
            package_name: None,
            fully_qualified_class: None,
        };
    }

    if segments.len() == 1 {
        return JniParsedName {
            method_name: segments[0].to_string(),
            package_name: None,
            fully_qualified_class: None,
        };
    }

    // Method name is always the last segment
    let method_name = segments[segments.len() - 1].to_string();
    let prefix_segments = &segments[..segments.len() - 1];

    // Find class name: scan backwards for first uppercase-starting segment
    let mut class_idx = None;
    for (i, seg) in prefix_segments.iter().enumerate().rev() {
        if seg.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
            class_idx = Some(i);
            break;
        }
    }

    match class_idx {
        Some(idx) => {
            let class_name = prefix_segments[idx];
            let package_parts = &prefix_segments[..idx];

            let package_name = if package_parts.is_empty() {
                None
            } else {
                Some(package_parts.join("."))
            };

            let fq_class = match &package_name {
                Some(pkg) => Some(format!("{}.{}", pkg, class_name)),
                None => Some(class_name.to_string()),
            };

            JniParsedName {
                method_name,
                package_name,
                fully_qualified_class: fq_class,
            }
        }
        None => {
            // No uppercase found; treat second-to-last as class (best effort)
            if prefix_segments.len() >= 2 {
                let class_name = prefix_segments[prefix_segments.len() - 1];
                let package_parts = &prefix_segments[..prefix_segments.len() - 1];
                let package_name = if package_parts.is_empty() {
                    None
                } else {
                    Some(package_parts.join("."))
                };
                let fq_class = match &package_name {
                    Some(pkg) => Some(format!("{}.{}", pkg, class_name)),
                    None => Some(class_name.to_string()),
                };
                JniParsedName {
                    method_name,
                    package_name,
                    fully_qualified_class: fq_class,
                }
            } else {
                JniParsedName {
                    method_name,
                    package_name: None,
                    fully_qualified_class: Some(prefix_segments[0].to_string()),
                }
            }
        }
    }
}

/// Extract the function name from a function_definition or declaration node.
fn extract_function_name(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let declarator = node.child_by_field_name("declarator")?;
    find_declarator_name(&declarator, source)
}

/// Find the function/variable name within a declarator node hierarchy.
///
/// Follows the `declarator` field chain (function_declarator -> pointer_declarator
/// -> identifier) before falling back to DFS.
fn find_declarator_name(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    if node.kind() == "identifier" || node.kind() == "field_identifier" {
        return node.utf8_text(source).ok().map(|s| s.to_string());
    }

    // Follow the declarator field chain first
    if let Some(inner) = node.child_by_field_name("declarator") {
        if let Some(name) = find_declarator_name(&inner, source) {
            return Some(name);
        }
    }

    // Fallback: direct identifier children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "identifier" || child.kind() == "field_identifier" {
            return child.utf8_text(source).ok().map(|s| s.to_string());
        }
    }

    // Deep fallback
    let mut cursor2 = node.walk();
    for child in node.children(&mut cursor2) {
        if let Some(name) = find_declarator_name(&child, source) {
            return Some(name);
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_jni_name_with_package() {
        let parsed = parse_jni_name("Java_com_example_MyClass_nativeMethod");
        assert_eq!(parsed.method_name, "nativeMethod");
        assert_eq!(parsed.package_name.as_deref(), Some("com.example"));
        assert_eq!(
            parsed.fully_qualified_class.as_deref(),
            Some("com.example.MyClass")
        );
    }

    #[test]
    fn test_parse_jni_name_no_package() {
        let parsed = parse_jni_name("Java_MyClass_compute");
        assert_eq!(parsed.method_name, "compute");
        assert_eq!(parsed.package_name, None);
        assert_eq!(parsed.fully_qualified_class.as_deref(), Some("MyClass"));
    }

    #[test]
    fn test_parse_jni_name_deep_package() {
        let parsed = parse_jni_name("Java_org_apache_commons_MyUtil_doWork");
        assert_eq!(parsed.method_name, "doWork");
        assert_eq!(parsed.package_name.as_deref(), Some("org.apache.commons"));
        assert_eq!(
            parsed.fully_qualified_class.as_deref(),
            Some("org.apache.commons.MyUtil")
        );
    }

    #[test]
    fn test_parse_jni_name_overloaded() {
        let parsed = parse_jni_name("Java_com_example_MyClass_method__I");
        assert_eq!(parsed.method_name, "method");
        assert_eq!(parsed.package_name.as_deref(), Some("com.example"));
        assert_eq!(
            parsed.fully_qualified_class.as_deref(),
            Some("com.example.MyClass")
        );
    }

    #[test]
    fn test_parse_jni_name_overloaded_string() {
        let parsed =
            parse_jni_name("Java_com_example_MyClass_method__Ljava_lang_String_2");
        assert_eq!(parsed.method_name, "method");
        assert_eq!(
            parsed.fully_qualified_class.as_deref(),
            Some("com.example.MyClass")
        );
    }

    #[test]
    fn test_parse_jni_name_single_segment() {
        let parsed = parse_jni_name("Java_init");
        assert_eq!(parsed.method_name, "init");
        assert_eq!(parsed.package_name, None);
        assert_eq!(parsed.fully_qualified_class, None);
    }
}
