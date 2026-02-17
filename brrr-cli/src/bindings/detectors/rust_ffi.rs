//! Rust FFI binding detector.
//!
//! Detects:
//! - `extern "C" { fn name(...); }` -- foreign function imports
//! - `#[no_mangle] pub extern "C" fn name(...)` -- function exports
//! - `extern "system" { ... }` -- Windows ABI imports
//!
//! Tree-sitter Rust CST layout:
//!
//!   extern "C" block (import):
//!     foreign_mod_item
//!       extern_modifier  ("extern \"C\"")
//!       body: declaration_list
//!         function_signature_item  (fn name(...) -> T;)
//!
//!   #[no_mangle] export:
//!     attribute_item       <-- #[no_mangle]  (sibling, NOT parent)
//!     function_item        <-- pub extern "C" fn name(...)
//!       visibility_modifier
//!       function_modifiers
//!         extern_modifier  ("extern \"C\"")
//!       name: identifier
//!       ...

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
        collect_ffi_items(&tree.root_node(), source, file_path, &mut declarations);
        Ok(declarations)
    }
}

/// Recursively scan a container node for FFI declarations.
///
/// Handles:
/// - `foreign_mod_item` (extern "C" { ... } blocks) at any nesting level
/// - Sibling `attribute_item` + `function_item` pairs for #[no_mangle] exports
/// - Recurses into `mod_item`, `impl_item`, `unsafe` blocks, etc.
fn collect_ffi_items(
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

        match child.kind() {
            // ----------------------------------------------------------
            // extern "C" { fn name(...); } -- foreign function imports
            // ----------------------------------------------------------
            "foreign_mod_item" => {
                let abi = get_abi(child, source);
                if abi.as_deref() == Some("C") || abi.as_deref() == Some("system") {
                    collect_extern_block_imports(child, source, file_path, declarations);
                }
            }

            // ----------------------------------------------------------
            // #[no_mangle] attribute -- check if next sibling is an export
            // ----------------------------------------------------------
            "attribute_item" => {
                if is_no_mangle_attr(child, source) {
                    if i + 1 < children.len() {
                        let next = &children[i + 1];
                        if next.kind() == "function_item" {
                            if has_extern_c_modifier(next, source) {
                                emit_export(next, source, file_path, declarations);
                                i += 2;
                                continue;
                            }
                        }
                    }
                }
            }

            // ----------------------------------------------------------
            // Recurse into nested containers
            // ----------------------------------------------------------
            "mod_item" => {
                if let Some(body) = child.child_by_field_name("body") {
                    collect_ffi_items(&body, source, file_path, declarations);
                }
            }
            "impl_item" => {
                if let Some(body) = child.child_by_field_name("body") {
                    collect_ffi_items(&body, source, file_path, declarations);
                }
            }

            _ => {}
        }

        i += 1;
    }
}

/// Collect function_signature_items from inside a foreign_mod_item's body.
///
/// The body is a `declaration_list` node (field name: "body").
fn collect_extern_block_imports(
    foreign_mod: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
) {
    let body = match foreign_mod.child_by_field_name("body") {
        Some(b) => b,
        None => return,
    };

    let mut cursor = body.walk();
    for item in body.children(&mut cursor) {
        if item.kind() == "function_signature_item" {
            if let Some(name) = get_fn_name(&item, source) {
                declarations.push(BindingDeclaration {
                    system: BindingSystem::RustFfi,
                    direction: BindingDirection::Import,
                    exposed_name: name.clone(),
                    host_function: None,
                    target_function: Some(FunctionRef {
                        file: String::new(),
                        name,
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

/// Emit an export declaration for a #[no_mangle] extern "C" function.
fn emit_export(
    func_node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
) {
    let name = match get_fn_name(func_node, source) {
        Some(n) => n,
        None => return,
    };

    declarations.push(BindingDeclaration {
        system: BindingSystem::RustFfi,
        direction: BindingDirection::Export,
        exposed_name: name.clone(),
        host_function: Some(FunctionRef {
            file: file_path.to_string(),
            name,
            qualified_name: None,
        }),
        target_function: None,
        declaration_file: file_path.to_string(),
        declaration_line: func_node.start_position().row + 1,
        module_name: None,
        class_name: None,
        raw_pattern: node_text(func_node, source).map(|t| {
            t.lines().next().unwrap_or(&t).to_string()
        }),
        confidence: 1.0,
    });
}

/// Extract the ABI string from a foreign_mod_item or extern_modifier.
///
/// Returns "C" for `extern "C"`, "system" for `extern "system"`, None otherwise.
fn get_abi(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "extern_modifier" {
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

/// Get the function name from a function_item or function_signature_item.
///
/// Uses the "name" field first (field-based access), then falls back to
/// scanning for identifier children.
fn get_fn_name(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    // Prefer field-based access
    if let Some(name_node) = node.child_by_field_name("name") {
        return node_text_str(&name_node, source).map(|s| s.to_string());
    }
    // Fallback: first identifier child
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "identifier" {
            return node_text_str(&child, source).map(|s| s.to_string());
        }
    }
    None
}

/// Check if an attribute_item is `#[no_mangle]`.
fn is_no_mangle_attr(node: &tree_sitter::Node, source: &[u8]) -> bool {
    if node.kind() != "attribute_item" {
        return false;
    }
    node_text_str(node, source)
        .map(|t| t.contains("no_mangle"))
        .unwrap_or(false)
}

/// Check if a function_item has an `extern "C"` or `extern "system"` modifier.
///
/// Tree-sitter Rust CST for `pub extern "C" fn name(...)`:
///   function_item
///     visibility_modifier (pub)
///     function_modifiers
///       extern_modifier (extern "C")
///     fn
///     name: identifier
///     ...
fn has_extern_c_modifier(func_node: &tree_sitter::Node, source: &[u8]) -> bool {
    let mut cursor = func_node.walk();
    for child in func_node.children(&mut cursor) {
        if child.kind() == "function_modifiers" {
            let mut inner = child.walk();
            for grandchild in child.children(&mut inner) {
                if grandchild.kind() == "extern_modifier" {
                    if let Some(text) = node_text_str(&grandchild, source) {
                        if text.contains("\"C\"") || text.contains("\"system\"") {
                            return true;
                        }
                    }
                }
            }
            return false;
        }
        // Also check direct extern_modifier (some tree-sitter versions)
        if child.kind() == "extern_modifier" {
            if let Some(text) = node_text_str(&child, source) {
                if text.contains("\"C\"") || text.contains("\"system\"") {
                    return true;
                }
            }
        }
    }
    false
}

fn node_text(node: &tree_sitter::Node, source: &[u8]) -> Option<String> {
    node.utf8_text(source).ok().map(|s| s.to_string())
}

fn node_text_str<'a>(node: &tree_sitter::Node, source: &'a [u8]) -> Option<&'a str> {
    node.utf8_text(source).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_rust(source: &[u8]) -> Tree {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .unwrap();
        parser.parse(source, None).unwrap()
    }

    #[test]
    fn test_extern_c_imports() {
        let source = br#"
extern "C" {
    fn strlen(s: *const u8) -> usize;
    fn malloc(size: usize) -> *mut u8;
}
"#;
        let tree = parse_rust(source);
        let detector = RustFfiDetector;
        let decls = detector.detect(&tree, source, "test.rs", "rust").unwrap();

        assert_eq!(decls.len(), 2, "Expected 2 imports, got {:?}",
            decls.iter().map(|d| &d.exposed_name).collect::<Vec<_>>());
        assert_eq!(decls[0].exposed_name, "strlen");
        assert_eq!(decls[0].direction, BindingDirection::Import);
        assert_eq!(decls[1].exposed_name, "malloc");
        assert_eq!(decls[1].direction, BindingDirection::Import);
    }

    #[test]
    fn test_extern_system_imports() {
        let source = br#"
extern "system" {
    fn GetLastError() -> u32;
}
"#;
        let tree = parse_rust(source);
        let detector = RustFfiDetector;
        let decls = detector.detect(&tree, source, "test.rs", "rust").unwrap();

        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "GetLastError");
        assert_eq!(decls[0].direction, BindingDirection::Import);
    }

    #[test]
    fn test_no_mangle_export() {
        let source = br#"
#[no_mangle]
pub extern "C" fn my_export(x: i32) -> i32 {
    x + 1
}
"#;
        let tree = parse_rust(source);
        let detector = RustFfiDetector;
        let decls = detector.detect(&tree, source, "test.rs", "rust").unwrap();

        assert_eq!(decls.len(), 1, "Expected 1 export, got {:?}",
            decls.iter().map(|d| &d.exposed_name).collect::<Vec<_>>());
        assert_eq!(decls[0].exposed_name, "my_export");
        assert_eq!(decls[0].direction, BindingDirection::Export);
        assert_eq!(decls[0].host_function.as_ref().unwrap().file, "test.rs");
    }

    #[test]
    fn test_mixed_imports_and_exports() {
        let source = br#"
extern "C" {
    fn c_library_func(x: i32) -> i32;
}

#[no_mangle]
pub extern "C" fn rust_export(x: i32) -> i32 {
    c_library_func(x)
}
"#;
        let tree = parse_rust(source);
        let detector = RustFfiDetector;
        let decls = detector.detect(&tree, source, "test.rs", "rust").unwrap();

        assert_eq!(decls.len(), 2);

        let imports: Vec<_> = decls.iter().filter(|d| d.direction == BindingDirection::Import).collect();
        let exports: Vec<_> = decls.iter().filter(|d| d.direction == BindingDirection::Export).collect();

        assert_eq!(imports.len(), 1);
        assert_eq!(imports[0].exposed_name, "c_library_func");

        assert_eq!(exports.len(), 1);
        assert_eq!(exports[0].exposed_name, "rust_export");
    }

    #[test]
    fn test_no_mangle_without_extern_c_is_skipped() {
        let source = br#"
#[no_mangle]
pub fn not_ffi(x: i32) -> i32 {
    x + 1
}
"#;
        let tree = parse_rust(source);
        let detector = RustFfiDetector;
        let decls = detector.detect(&tree, source, "test.rs", "rust").unwrap();

        // no extern "C" modifier -> not detected as FFI
        assert_eq!(decls.len(), 0);
    }

    #[test]
    fn test_extern_c_in_mod() {
        let source = br#"
mod ffi {
    extern "C" {
        fn inner_import(x: f64) -> f64;
    }
}
"#;
        let tree = parse_rust(source);
        let detector = RustFfiDetector;
        let decls = detector.detect(&tree, source, "test.rs", "rust").unwrap();

        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "inner_import");
    }

    #[test]
    fn test_link_section_with_no_mangle() {
        // #[link_section] is sometimes used alongside #[no_mangle]; should still detect
        let source = br#"
#[no_mangle]
pub extern "C" fn plugin_entry() -> i32 {
    42
}
"#;
        let tree = parse_rust(source);
        let detector = RustFfiDetector;
        let decls = detector.detect(&tree, source, "test.rs", "rust").unwrap();

        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "plugin_entry");
    }
}
