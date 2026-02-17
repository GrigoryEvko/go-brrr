//! napi-rs binding detector.
//!
//! Detects `#[napi]` attribute on Rust functions/structs/impl blocks,
//! which exports them to Node.js via N-API.
//!
//! Tree-sitter Rust parses `#[napi]` as an `attribute_item` sibling
//! of the decorated item (NOT as a parent `attributed_item`).
//! Example CST for `#[napi] pub fn add(...)`:
//!   source_file
//!     attribute_item          <-- #[napi]
//!     function_item           <-- pub fn add(...)

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

/// Convert Rust snake_case to JavaScript camelCase.
///
/// napi-rs automatically converts function names: `my_function` -> `myFunction`.
fn snake_to_camel(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut capitalize_next = false;

    for ch in s.chars() {
        if ch == '_' {
            capitalize_next = !result.is_empty();
        } else if capitalize_next {
            result.extend(ch.to_uppercase());
            capitalize_next = false;
        } else {
            result.push(ch);
        }
    }

    result
}

/// Extract a custom JS name from `#[napi(js_name = "customName")]` attribute text.
///
/// Returns `None` if no `js_name` parameter is present.
fn extract_js_name(attr_text: &str) -> Option<String> {
    let idx = attr_text.find("js_name")?;
    let rest = &attr_text[idx + 7..];
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('=')?;
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('"')?;
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

/// Check if an `attribute_item` node is a `#[napi...]` attribute.
fn is_napi_attribute(node: &tree_sitter::Node, source: &[u8]) -> bool {
    if node.kind() != "attribute_item" {
        return false;
    }
    // The attribute_item contains an `attribute` child whose first child
    // is an `identifier` with text "napi"
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "attribute" {
            if let Some(ident) = child.child(0) {
                if ident.kind() == "identifier" {
                    if let Ok(text) = ident.utf8_text(source) {
                        return text == "napi";
                    }
                }
            }
        }
    }
    false
}

/// Get the full attribute text for extracting parameters like js_name.
fn get_napi_attr_text<'a>(node: &tree_sitter::Node, source: &'a [u8]) -> Option<&'a str> {
    if node.kind() != "attribute_item" {
        return None;
    }
    node.utf8_text(source).ok()
}

/// Scan children of a container node (source_file, declaration_list, etc.)
/// looking for `attribute_item` nodes followed by decorated items.
///
/// In tree-sitter Rust, attributes are siblings of their targets:
///   attribute_item      <- #[napi]
///   function_item       <- the decorated function
fn collect_napi_items(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
) {
    let mut cursor = node.walk();
    let children: Vec<tree_sitter::Node> = node.children(&mut cursor).collect();

    let mut i = 0;
    while i < children.len() {
        let child = &children[i];

        if is_napi_attribute(child, source) {
            let attr_text = get_napi_attr_text(child, source).unwrap_or("");
            let custom_js_name = extract_js_name(attr_text);

            // Look at the next sibling for the decorated item
            if i + 1 < children.len() {
                let item = &children[i + 1];
                match item.kind() {
                    "function_item" => {
                        emit_function_binding(
                            item,
                            source,
                            file_path,
                            declarations,
                            custom_js_name.as_deref(),
                            None,
                        );
                        i += 2;
                        continue;
                    }
                    "struct_item" => {
                        emit_struct_binding(
                            item,
                            source,
                            file_path,
                            declarations,
                            custom_js_name.as_deref(),
                        );
                        i += 2;
                        continue;
                    }
                    "impl_item" => {
                        let impl_type_name = item
                            .child_by_field_name("type")
                            .and_then(|n| n.utf8_text(source).ok())
                            .map(|s| s.to_string());

                        collect_napi_impl_methods(
                            item,
                            source,
                            file_path,
                            declarations,
                            impl_type_name.as_deref(),
                        );
                        i += 2;
                        continue;
                    }
                    _ => {}
                }
            }
        }

        // For impl_item without a top-level #[napi], still check for inner
        // #[napi] methods (standalone #[napi] on methods inside a plain impl block)
        if child.kind() == "impl_item" {
            let impl_type_name = child
                .child_by_field_name("type")
                .and_then(|n| n.utf8_text(source).ok())
                .map(|s| s.to_string());

            collect_napi_impl_methods(
                child,
                source,
                file_path,
                declarations,
                impl_type_name.as_deref(),
            );
        }

        // Recurse into mod_item bodies
        if child.kind() == "mod_item" {
            if let Some(body) = child.child_by_field_name("body") {
                collect_napi_items(&body, source, file_path, declarations);
            }
        }

        i += 1;
    }
}

/// Scan methods inside an `impl` block for `#[napi]` attributes.
fn collect_napi_impl_methods(
    impl_node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    class_name: Option<&str>,
) {
    let body = match impl_node.child_by_field_name("body") {
        Some(b) => b,
        None => return,
    };

    let mut cursor = body.walk();
    let children: Vec<tree_sitter::Node> = body.children(&mut cursor).collect();

    let mut i = 0;
    while i < children.len() {
        let child = &children[i];

        if is_napi_attribute(child, source) {
            let attr_text = get_napi_attr_text(child, source).unwrap_or("");
            let custom_js_name = extract_js_name(attr_text);

            if i + 1 < children.len() {
                let item = &children[i + 1];
                if item.kind() == "function_item" {
                    emit_function_binding(
                        item,
                        source,
                        file_path,
                        declarations,
                        custom_js_name.as_deref(),
                        class_name,
                    );
                    i += 2;
                    continue;
                }
            }
        }

        i += 1;
    }
}

/// Emit a BindingDeclaration for a `#[napi]`-decorated function.
fn emit_function_binding(
    func_node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    custom_js_name: Option<&str>,
    class_name: Option<&str>,
) {
    let rust_name = match func_node
        .child_by_field_name("name")
        .and_then(|n| n.utf8_text(source).ok())
    {
        Some(n) => n,
        None => return,
    };

    // JS-visible name: explicit js_name overrides, else snake_case -> camelCase
    let js_name = custom_js_name
        .map(|s| s.to_string())
        .unwrap_or_else(|| snake_to_camel(rust_name));

    declarations.push(BindingDeclaration {
        system: BindingSystem::NapiRs,
        direction: BindingDirection::Export,
        exposed_name: js_name,
        host_function: Some(FunctionRef {
            file: file_path.to_string(),
            name: rust_name.to_string(),
            qualified_name: None,
        }),
        target_function: None,
        declaration_file: file_path.to_string(),
        declaration_line: func_node.start_position().row + 1,
        module_name: None,
        class_name: class_name.map(|s| s.to_string()),
        raw_pattern: func_node.utf8_text(source).ok().map(|s| {
            s.lines().next().unwrap_or(s).to_string()
        }),
        confidence: 1.0,
    });
}

/// Emit a BindingDeclaration for a `#[napi]`-decorated struct.
fn emit_struct_binding(
    struct_node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
    custom_js_name: Option<&str>,
) {
    let rust_name = match struct_node
        .child_by_field_name("name")
        .and_then(|n| n.utf8_text(source).ok())
    {
        Some(n) => n,
        None => return,
    };

    // Struct names are PascalCase in both Rust and JS, kept as-is
    let js_name = custom_js_name
        .map(|s| s.to_string())
        .unwrap_or_else(|| rust_name.to_string());

    declarations.push(BindingDeclaration {
        system: BindingSystem::NapiRs,
        direction: BindingDirection::Export,
        exposed_name: js_name,
        host_function: Some(FunctionRef {
            file: file_path.to_string(),
            name: rust_name.to_string(),
            qualified_name: None,
        }),
        target_function: None,
        declaration_file: file_path.to_string(),
        declaration_line: struct_node.start_position().row + 1,
        module_name: None,
        class_name: Some(rust_name.to_string()),
        raw_pattern: struct_node.utf8_text(source).ok().map(|s| {
            s.lines().next().unwrap_or(s).to_string()
        }),
        confidence: 1.0,
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_snake_to_camel() {
        assert_eq!(snake_to_camel("add"), "add");
        assert_eq!(snake_to_camel("my_function"), "myFunction");
        assert_eq!(snake_to_camel("get_user_name"), "getUserName");
        assert_eq!(snake_to_camel("a"), "a");
        assert_eq!(snake_to_camel(""), "");
        assert_eq!(snake_to_camel("already_camel_case"), "alreadyCamelCase");
    }

    #[test]
    fn test_extract_js_name() {
        assert_eq!(
            extract_js_name(r#"#[napi(js_name = "customName")]"#),
            Some("customName".to_string())
        );
        assert_eq!(
            extract_js_name(r#"#[napi(js_name="noSpaces")]"#),
            Some("noSpaces".to_string())
        );
        assert_eq!(extract_js_name("#[napi]"), None);
        assert_eq!(extract_js_name("#[napi(constructor)]"), None);
        assert_eq!(extract_js_name("#[napi(object)]"), None);
    }
}
