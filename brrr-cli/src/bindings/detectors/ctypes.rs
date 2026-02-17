//! ctypes binding detector.
//!
//! Detects Python code that loads C shared libraries via ctypes:
//! - `lib = ctypes.CDLL("libfoo.so")` / `ctypes.WinDLL(...)` / `ctypes.cdll.LoadLibrary(...)`
//! - `lib.func_name(args)` -- C function calls through the library handle
//! - `lib.func_name.argtypes` / `.restype` -- type annotations declaring C signatures
//! - `ctypes.windll.kernel32.SetErrorMode(...)` -- direct access without variable
//! - `self.lib = ctypes.WinDLL(...)` -- instance attribute library handles

use std::collections::HashSet;

use tree_sitter::Tree;

use crate::bindings::detector::BindingDetector;
use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::types::FunctionRef;
use crate::error::Result;

pub struct CtypesDetector;

/// A tracked library handle: the variable name/expression and the library it loads.
struct LibVar {
    /// How the variable is referenced in code (e.g., "kernel32", "self.kernel32", "lib")
    access_text: String,
    /// The library name extracted from the CDLL/WinDLL/LoadLibrary call argument.
    /// e.g., "kernel32.dll", "libnvidia-ml.so.1", or empty if unknown.
    library_name: String,
}

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

        // Phase 1: Collect CDLL/WinDLL/OleDLL variable assignments
        let mut lib_vars: Vec<LibVar> = Vec::new();
        collect_cdll_vars(&root, source, &mut lib_vars);

        // Phase 2: Find function calls on tracked lib vars (lib.func_name(...))
        // AND direct ctypes.windll/cdll attribute calls (no variable needed)
        let mut seen: HashSet<(String, usize)> = HashSet::new();
        collect_ctypes_calls(&root, source, file_path, &lib_vars, &mut declarations, &mut seen);

        // Phase 3: Find argtypes/restype annotations (lib.func.argtypes = [...])
        collect_type_annotations(
            &root,
            source,
            file_path,
            &lib_vars,
            &mut declarations,
            &mut seen,
        );

        Ok(declarations)
    }
}

/// Extract the library name string from a CDLL/WinDLL call's first argument.
///
/// For `ctypes.CDLL("kernel32.dll")`, extracts "kernel32.dll".
/// For `CDLL(None)` or `CDLL(some_var)`, returns empty string.
fn extract_library_name(call_node: &tree_sitter::Node, source: &[u8]) -> String {
    let args = match call_node.child_by_field_name("arguments") {
        Some(a) => a,
        None => return String::new(),
    };
    let count = args.named_child_count();
    for i in 0..count {
        let child = match args.named_child(i as u32) {
            Some(c) => c,
            None => continue,
        };
        if child.kind() == "keyword_argument" {
            continue;
        }
        if child.kind() == "string" {
            if let Ok(text) = child.utf8_text(source) {
                let trimmed = text.trim_matches(|c| c == '"' || c == '\'');
                return trimmed.to_string();
            }
        }
        // Non-string first positional arg (variable, None, etc.)
        return String::new();
    }
    String::new()
}

/// Collect variable names assigned from ctypes.CDLL/WinDLL/OleDLL/cdll.LoadLibrary.
///
/// Handles both simple assignments (`lib = ctypes.CDLL(...)`) and attribute
/// assignments (`self.lib = ctypes.WinDLL(...)`).
fn collect_cdll_vars(node: &tree_sitter::Node, source: &[u8], vars: &mut Vec<LibVar>) {
    if node.kind() == "assignment" {
        let target = node.child_by_field_name("left");
        let value = node.child_by_field_name("right");

        if let (Some(target), Some(value)) = (target, value) {
            if let Ok(value_text) = value.utf8_text(source) {
                if is_cdll_call(value_text) {
                    // Accept both plain identifiers and attribute access (self.xxx)
                    if target.kind() == "identifier" || target.kind() == "attribute" {
                        if let Ok(var_name) = target.utf8_text(source) {
                            let lib_name = if value.kind() == "call" {
                                extract_library_name(&value, source)
                            } else {
                                String::new()
                            };
                            vars.push(LibVar {
                                access_text: var_name.to_string(),
                                library_name: lib_name,
                            });
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

/// Check if text represents a ctypes library-loading call.
fn is_cdll_call(text: &str) -> bool {
    text.contains("ctypes.CDLL")
        || text.contains("ctypes.WinDLL")
        || text.contains("ctypes.OleDLL")
        || text.contains("ctypes.PyDLL")
        || text.contains("ctypes.cdll.LoadLibrary")
        || text.contains("ctypes.windll.LoadLibrary")
        || text.contains("CDLL(")
        || text.contains("WinDLL(")
        || text.contains("OleDLL(")
        || text.contains("PyDLL(")
}

/// Create a BindingDeclaration for a detected C function call/annotation.
fn make_declaration(
    func_name: &str,
    lib_name: &str,
    file_path: &str,
    line: usize,
    raw: Option<String>,
    confidence: f64,
) -> BindingDeclaration {
    BindingDeclaration {
        system: BindingSystem::Ctypes,
        direction: BindingDirection::Import,
        exposed_name: func_name.to_string(),
        host_function: None,
        target_function: Some(FunctionRef {
            file: String::new(),
            name: func_name.to_string(),
            qualified_name: None,
        }),
        declaration_file: file_path.to_string(),
        declaration_line: line,
        module_name: if lib_name.is_empty() {
            None
        } else {
            Some(lib_name.to_string())
        },
        class_name: None,
        raw_pattern: raw,
        confidence,
    }
}

/// Check if an attribute chain matches `ctypes.windll.<lib>` or `ctypes.cdll.<lib>`.
///
/// Returns `Some(library_name)` if matched, where library_name is the final
/// attribute (e.g., "shell32" from `ctypes.windll.shell32`).
fn match_ctypes_preloaded_lib<'a>(
    node: &tree_sitter::Node,
    source: &'a [u8],
) -> Option<&'a str> {
    // Expected structure:
    //   attribute(object=attribute(object=identifier("ctypes"), attr="windll"|"cdll"), attr=<lib>)
    if node.kind() != "attribute" {
        return None;
    }
    let obj = node.child_by_field_name("object")?;
    let lib_name_node = node.child_by_field_name("attribute")?;
    let lib_name = lib_name_node.utf8_text(source).ok()?;

    if obj.kind() != "attribute" {
        return None;
    }
    let ctypes_node = obj.child_by_field_name("object")?;
    let loader_node = obj.child_by_field_name("attribute")?;

    let ctypes_text = ctypes_node.utf8_text(source).ok()?;
    let loader_text = loader_node.utf8_text(source).ok()?;

    if ctypes_text == "ctypes" && (loader_text == "windll" || loader_text == "cdll") {
        Some(lib_name)
    } else {
        None
    }
}

/// Check if an attribute chain matches `ctypes.pythonapi`.
///
/// `ctypes.pythonapi` is a pre-loaded library handle for the Python C API.
/// Pattern: `ctypes.pythonapi.func(...)` -- the object is `ctypes.pythonapi`
/// and the attribute is the C function name.
///
/// Returns `true` if the node is `ctypes.pythonapi`.
fn is_ctypes_pythonapi(node: &tree_sitter::Node, source: &[u8]) -> bool {
    if node.kind() != "attribute" {
        return false;
    }
    let obj = match node.child_by_field_name("object") {
        Some(o) => o,
        None => return false,
    };
    let attr = match node.child_by_field_name("attribute") {
        Some(a) => a,
        None => return false,
    };

    let obj_text = obj.utf8_text(source).ok().unwrap_or("");
    let attr_text = attr.utf8_text(source).ok().unwrap_or("");

    obj_text == "ctypes" && attr_text == "pythonapi"
}

/// Collect C function calls through ctypes library handles.
///
/// Handles three patterns:
/// 1. `lib_var.func_name(...)` -- tracked variable from Phase 1
/// 2. `ctypes.windll.<lib>.func_name(...)` -- direct preloaded library access
/// 3. `ctypes.cdll.<lib>.func_name(...)` -- direct preloaded library access
fn collect_ctypes_calls(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    lib_vars: &[LibVar],
    declarations: &mut Vec<BindingDeclaration>,
    seen: &mut HashSet<(String, usize)>,
) {
    if node.kind() == "call" {
        if let Some(func) = node.child_by_field_name("function") {
            if func.kind() == "attribute" {
                let obj = func.child_by_field_name("object");
                let attr = func.child_by_field_name("attribute");
                if let (Some(obj), Some(attr)) = (obj, attr) {
                    if let (Ok(obj_text), Ok(attr_text)) =
                        (obj.utf8_text(source), attr.utf8_text(source))
                    {
                        let line = node.start_position().row + 1;

                        // Pattern 1: tracked lib variable call (lib.func(...) or self.lib.func(...))
                        if let Some(lib_var) = lib_vars.iter().find(|v| v.access_text == obj_text) {
                            if !is_ctypes_builtin(attr_text) {
                                let key = (attr_text.to_string(), line);
                                if seen.insert(key) {
                                    let raw = node
                                        .utf8_text(source)
                                        .ok()
                                        .map(|s| truncate_raw(s));
                                    declarations.push(make_declaration(
                                        attr_text,
                                        &lib_var.library_name,
                                        file_path,
                                        line,
                                        raw,
                                        0.9,
                                    ));
                                }
                            }
                        }

                        // Pattern 2: ctypes.windll.<lib>.func(...) / ctypes.cdll.<lib>.func(...)
                        if let Some(lib_name) = match_ctypes_preloaded_lib(&obj, source) {
                            if !is_ctypes_builtin(attr_text) {
                                let key = (attr_text.to_string(), line);
                                if seen.insert(key) {
                                    let raw = node
                                        .utf8_text(source)
                                        .ok()
                                        .map(|s| truncate_raw(s));
                                    declarations.push(make_declaration(
                                        attr_text,
                                        lib_name,
                                        file_path,
                                        line,
                                        raw,
                                        0.85,
                                    ));
                                }
                            }
                        }

                        // Pattern 3: ctypes.pythonapi.func(...)
                        if is_ctypes_pythonapi(&obj, source) {
                            if !is_ctypes_builtin(attr_text) {
                                let key = (attr_text.to_string(), line);
                                if seen.insert(key) {
                                    let raw = node
                                        .utf8_text(source)
                                        .ok()
                                        .map(|s| truncate_raw(s));
                                    declarations.push(make_declaration(
                                        attr_text,
                                        "pythonapi",
                                        file_path,
                                        line,
                                        raw,
                                        0.85,
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_ctypes_calls(&child, source, file_path, lib_vars, declarations, seen);
    }
}

/// Collect C function names from argtypes/restype annotations.
///
/// Pattern: `lib.func_name.argtypes = [...]` or `lib.func_name.restype = ...`
/// These declare C function signatures without necessarily calling the function.
fn collect_type_annotations(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    lib_vars: &[LibVar],
    declarations: &mut Vec<BindingDeclaration>,
    seen: &mut HashSet<(String, usize)>,
) {
    if node.kind() == "assignment" {
        if let Some(left) = node.child_by_field_name("left") {
            // Expected: attribute(object=attribute(lib_var, func_name), "argtypes"|"restype")
            if left.kind() == "attribute" {
                if let Some(ann_node) = left.child_by_field_name("attribute") {
                    if let Ok(ann_text) = ann_node.utf8_text(source) {
                        if ann_text == "argtypes" || ann_text == "restype" || ann_text == "errcheck"
                        {
                            if let Some(func_attr) = left.child_by_field_name("object") {
                                if func_attr.kind() == "attribute" {
                                    let lib_obj = func_attr.child_by_field_name("object");
                                    let func_node = func_attr.child_by_field_name("attribute");

                                    if let (Some(lib_obj), Some(func_node)) = (lib_obj, func_node)
                                    {
                                        if let (Ok(lib_text), Ok(func_text)) =
                                            (lib_obj.utf8_text(source), func_node.utf8_text(source))
                                        {
                                            // Check tracked lib vars
                                            let matched_lib = lib_vars
                                                .iter()
                                                .find(|v| v.access_text == lib_text)
                                                .map(|v| v.library_name.as_str());

                                            // Also check ctypes.pythonapi and ctypes.windll/cdll preloaded
                                            let lib_name = matched_lib
                                                .or_else(|| {
                                                    if is_ctypes_pythonapi(&lib_obj, source) {
                                                        Some("pythonapi")
                                                    } else {
                                                        match_ctypes_preloaded_lib(&lib_obj, source)
                                                    }
                                                });

                                            if let Some(lib_name) = lib_name {
                                                let line = node.start_position().row + 1;
                                                let key = (func_text.to_string(), line);
                                                if seen.insert(key) {
                                                    let raw = node
                                                        .utf8_text(source)
                                                        .ok()
                                                        .map(|s| truncate_raw(s));
                                                    declarations.push(make_declaration(
                                                        func_text, lib_name, file_path, line, raw,
                                                        0.8,
                                                    ));
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_type_annotations(&child, source, file_path, lib_vars, declarations, seen);
    }
}

/// Check if an attribute name is a ctypes-internal method/property, not a C function.
fn is_ctypes_builtin(attr: &str) -> bool {
    matches!(
        attr,
        "LoadLibrary" | "__getattr__" | "__getitem__" | "_handle" | "_name"
    )
}

/// Truncate raw pattern text to a reasonable length for storage.
fn truncate_raw(s: &str) -> String {
    if s.len() > 200 {
        format!("{}...", &s[..200])
    } else {
        s.to_string()
    }
}
