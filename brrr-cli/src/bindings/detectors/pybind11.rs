//! pybind11/nanobind binding detector.
//!
//! Detects C++ code that exposes functions/classes to Python:
//! - `PYBIND11_MODULE(name, m) { ... }` and `NB_MODULE(name, m) { ... }`
//! - `m.def("py_name", &cpp_func)` — function binding
//! - `m.def("py_name", func)` — function binding without & prefix
//! - `m.def("py_name", py::overload_cast<T>(&Cls::method))` — overload binding
//! - `m.def("py_name", torch::wrap_pybind_function(func))` — wrapped binding
//! - `m.def("py_name", [](args) { ... })` — lambda binding
//! - `py::class_<T>(m, "PyName").def("method", &T::method)` — class binding
//! - `.def(py::init<...>())` — constructor binding
//! - `.def_static("name", &func)` — static method binding
//! - `.def_readwrite("attr", &T::member)` — read-write property binding
//! - `.def_readonly("attr", &T::member)` — read-only property binding
//! - `.def_property("name", getter, setter)` — property binding
//! - `.def_property_readonly("name", &getter)` — read-only property binding

use tree_sitter::{Node, Tree};

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
            || (memchr::memmem::find(source, b".def(").is_some()
                && memchr::memmem::find(source, b"py::").is_some())
    }

    fn detect(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
        _language: &str,
    ) -> Result<Vec<BindingDeclaration>> {
        let mut declarations = Vec::new();
        let ctx = DetectContext { source, file_path };
        collect_bindings(&tree.root_node(), &ctx, &mut declarations, None, None);
        Ok(declarations)
    }
}

/// Shared context to avoid passing many parameters through recursion.
struct DetectContext<'a> {
    source: &'a [u8],
    file_path: &'a str,
}

/// All `.def*` method names we recognize as pybind11 binding declarations.
const DEF_METHODS: &[&str] = &[
    "def",
    "def_static",
    "def_readwrite",
    "def_readonly",
    "def_property",
    "def_property_readonly",
    "def_property_readonly_static",
    "def_buffer",
];

/// Check whether a field_identifier text is a pybind11 def method.
fn is_def_method(name: &str) -> bool {
    DEF_METHODS.contains(&name)
}

/// Recursively collect binding declarations from the AST.
///
/// Walks the tree looking for:
/// 1. PYBIND11_MODULE / NB_MODULE macro (function_definition with macro name)
/// 2. call_expressions whose function is a field_expression with a def method name
///
/// `class_ctx` carries the current py::class_ info when processing chained .def() calls.
fn collect_bindings(
    node: &Node,
    ctx: &DetectContext,
    declarations: &mut Vec<BindingDeclaration>,
    module_name: Option<&str>,
    class_ctx: Option<&ClassBindingInfo>,
) {
    let kind = node.kind();

    // 1. Detect PYBIND11_MODULE(name, m) { ... }
    if kind == "function_definition" {
        if let Some(declarator) = node.child_by_field_name("declarator") {
            let decl_name = get_declarator_name(&declarator, ctx.source);
            if decl_name.as_deref() == Some("PYBIND11_MODULE")
                || decl_name.as_deref() == Some("NB_MODULE")
            {
                let mod_name = extract_macro_first_arg(node, ctx.source)
                    .unwrap_or_else(|| "unknown".to_string());

                if let Some(body) = node.child_by_field_name("body") {
                    collect_bindings(&body, ctx, declarations, Some(&mod_name), None);
                }
                return;
            }
        }
    }

    // 2. Detect call_expressions: m.def("name", ...) or chained py::class_<T>(m, "N").def(...)
    if kind == "call_expression" {
        if let Some(func_node) = node.child_by_field_name("function") {
            // Check if this is a .def*() call by inspecting the field_identifier directly
            if func_node.kind() == "field_expression" {
                if let Some(field_name) = get_field_name(&func_node, ctx.source) {
                    if is_def_method(&field_name) {
                        // Determine class context: either inherited from parent chain,
                        // or extracted from the receiver if it's a py::class_ expression.
                        let local_class = class_ctx
                            .cloned()
                            .or_else(|| extract_class_from_chain(&func_node, ctx));

                        if let Some(decl) = parse_def_call(
                            node,
                            ctx,
                            module_name,
                            local_class.as_ref(),
                            &field_name,
                        ) {
                            declarations.push(decl);
                        }

                        // Do NOT recurse into this call_expression's children normally.
                        // Instead, walk only the receiver subtree to find chained calls
                        // below us (e.g., py::class_<T>(...).def(...).def(...) -- each
                        // .def() wraps the previous). Pass class context down the chain.
                        if let Some(recv) = func_node.child_by_field_name("argument") {
                            collect_bindings(
                                &recv,
                                ctx,
                                declarations,
                                module_name,
                                local_class.as_ref(),
                            );
                        }
                        return;
                    }
                }
            }

            // Check if this is a standalone py::class_<T>(m, "Name") without chained .def()
            if is_class_constructor_call(&func_node, ctx.source) {
                // No chained methods -- nothing to extract. Fall through to recurse.
            }
        }
    }

    // 3. Recurse into children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_bindings(&child, ctx, declarations, module_name, class_ctx);
    }
}

/// Parse a `.def*("python_name", ...)` call into a BindingDeclaration.
///
/// Handles multiple patterns for the second argument:
/// - `&function` or `&Class::method` (pointer_expression)
/// - `function` or `Class::method` (identifier / qualified_identifier without &)
/// - `py::overload_cast<T>(&Class::method)` (function ref nested in wrapper call)
/// - `torch::wrap_pybind_function(func)` (function ref nested in wrapper call)
/// - `[](args) { ... }` (lambda -- no host function to resolve)
/// - `py::init<...>()` (constructor -- special case)
fn parse_def_call(
    node: &Node,
    ctx: &DetectContext,
    module_name: Option<&str>,
    class_ctx: Option<&ClassBindingInfo>,
    def_method: &str,
) -> Option<BindingDeclaration> {
    let args = node.child_by_field_name("arguments")?;

    // Collect non-punctuation argument children
    let arg_nodes = collect_arg_nodes(&args);

    // For py::init<>() constructor bindings: .def(py::init<...>()) has no string name
    if def_method == "def" && arg_nodes.len() >= 1 {
        let first_text = arg_nodes[0].utf8_text(ctx.source).ok().unwrap_or("");
        if first_text.contains("py::init") || first_text.contains("nb::init") {
            return make_constructor_decl(node, ctx, module_name, class_ctx);
        }
    }

    // First string argument is the Python-visible name
    let py_name = arg_nodes
        .iter()
        .find_map(|c| extract_string_literal(c, ctx.source))?;

    // Find the C++ function reference from the remaining (non-string) arguments
    let func_args: Vec<_> = arg_nodes
        .iter()
        .filter(|c| {
            !matches!(
                c.kind(),
                "string_literal" | "string_content" | "raw_string_literal" | "concatenated_string"
            )
        })
        .collect();

    let cpp_ref = extract_function_ref_from_args(&func_args, ctx);

    // Extract class::method if present in the C++ reference
    let (extracted_class, func_name) = if let Some(ref cpp) = cpp_ref {
        split_qualified_name(cpp)
    } else {
        (None, py_name.clone())
    };

    // Class name: prefer class context from py::class_ chain, then extracted from reference
    let class_name = class_ctx.map(|c| c.py_name.clone()).or(extracted_class);

    // Confidence: lower for lambda-only bindings (no resolvable host function)
    let confidence = if cpp_ref.is_some() { 1.0 } else { 0.8 };

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
        declaration_file: ctx.file_path.to_string(),
        declaration_line: node.start_position().row + 1,
        module_name: module_name.map(|s| s.to_string()),
        class_name,
        raw_pattern: truncated_text(node, ctx.source, 200),
        confidence,
    })
}

/// Create a constructor binding declaration for `.def(py::init<...>())`.
fn make_constructor_decl(
    node: &Node,
    ctx: &DetectContext,
    module_name: Option<&str>,
    class_ctx: Option<&ClassBindingInfo>,
) -> Option<BindingDeclaration> {
    let class_name = class_ctx.map(|c| c.py_name.clone())?;
    Some(BindingDeclaration {
        system: BindingSystem::Pybind11,
        direction: BindingDirection::Export,
        exposed_name: "__init__".to_string(),
        host_function: None,
        target_function: None,
        declaration_file: ctx.file_path.to_string(),
        declaration_line: node.start_position().row + 1,
        module_name: module_name.map(|s| s.to_string()),
        class_name: Some(class_name),
        raw_pattern: truncated_text(node, ctx.source, 200),
        confidence: 0.9,
    })
}

/// Extract a C++ function reference from the argument nodes of a .def() call.
///
/// Tries multiple strategies in order:
/// 1. Direct `&function` or `&Class::method` (pointer_expression)
/// 2. Direct `function` or `ns::function` (identifier / qualified_identifier)
/// 3. Recursive search inside wrapper calls: `py::overload_cast<T>(&f)`,
///    `torch::wrap_pybind_function(f)`, etc.
///
/// Returns `None` for lambda expressions (no named function to resolve).
fn extract_function_ref_from_args(args: &[&Node], ctx: &DetectContext) -> Option<String> {
    for arg in args {
        if let Some(name) = extract_function_ref_from_node(arg, ctx) {
            return Some(name);
        }
    }
    None
}

/// Extract a function reference from a single AST node.
///
/// Handles:
/// - `pointer_expression`: `&func` or `&Cls::method`
/// - `identifier`: `func` (function passed by name without &)
/// - `qualified_identifier`: `ns::func` or `Cls::method` (without &)
/// - `call_expression`: recursively search inside wrapper calls
///   like `py::overload_cast<T>(&Cls::method)` or `wrap_pybind_function(f)`
fn extract_function_ref_from_node(node: &Node, ctx: &DetectContext) -> Option<String> {
    match node.kind() {
        "pointer_expression" | "unary_expression" => {
            // &function or &Class::method
            let text = node.utf8_text(ctx.source).ok()?;
            let name = text.trim_start_matches('&').trim();
            if name.is_empty() {
                None
            } else {
                Some(name.to_string())
            }
        }

        "identifier" => {
            // function passed without & prefix
            let text = node.utf8_text(ctx.source).ok()?;
            let name = text.trim();
            if name.is_empty() || is_likely_keyword(name) {
                None
            } else {
                Some(name.to_string())
            }
        }

        "qualified_identifier" => {
            // ns::func or Cls::method (without &)
            let text = node.utf8_text(ctx.source).ok()?;
            let name = text.trim();
            if name.is_empty() {
                None
            } else {
                Some(name.to_string())
            }
        }

        "call_expression" => {
            // Wrapper calls like py::overload_cast<T>(&f) or wrap_pybind_function(f)
            // Recursively search the arguments of the wrapper for a function ref.
            if let Some(inner_args) = node.child_by_field_name("arguments") {
                let inner_nodes = collect_arg_nodes(&inner_args);
                for inner in &inner_nodes {
                    if let Some(name) = extract_function_ref_from_node(inner, ctx) {
                        return Some(name);
                    }
                }
            }
            None
        }

        _ => None,
    }
}

/// Check if a string is a C++ keyword or common non-function identifier
/// that should not be treated as a function reference.
fn is_likely_keyword(name: &str) -> bool {
    matches!(
        name,
        "true" | "false" | "nullptr" | "this" | "void" | "int" | "float" | "double"
            | "char" | "bool" | "auto" | "const" | "static" | "return" | "if" | "else"
            | "for" | "while" | "do" | "switch" | "case" | "break" | "continue"
            | "class" | "struct" | "enum" | "namespace" | "using" | "typedef"
            | "template" | "typename" | "virtual" | "override" | "public" | "private"
            | "protected" | "new" | "delete" | "throw" | "try" | "catch"
    )
}

/// Split a qualified C++ name into (class_or_namespace, method_name).
///
/// Examples:
/// - "at::vitals::torchVitalEnabled" -> (Some("at::vitals"), "torchVitalEnabled")
/// - "WeakTensorRef::expired" -> (Some("WeakTensorRef"), "expired")
/// - "simple_func" -> (None, "simple_func")
fn split_qualified_name(name: &str) -> (Option<String>, String) {
    if let Some(pos) = name.rfind("::") {
        let prefix = &name[..pos];
        let suffix = &name[pos + 2..];
        (Some(prefix.to_string()), suffix.to_string())
    } else {
        (None, name.to_string())
    }
}

/// Suffixes that indicate a py::class_ equivalent template.
/// PyTorch defines aliases like `shared_ptr_class_<T>` = `py::class_<T, std::shared_ptr<T>>`.
const CLASS_TEMPLATE_SUFFIXES: &[&str] = &[
    "class_",
    "shared_ptr_class_",
    "intrusive_ptr_class_",
    "intrusive_ptr_no_gil_destructor_class_",
    "intrusive_ptr_no_gil_destructor_trampoline_class_",
];

/// Check if a node is a py::class_<T> or equivalent constructor call.
///
/// Recognizes:
/// - `py::class_<T>` / `nb::class_<T>` (qualified_identifier with template_argument_list)
/// - `shared_ptr_class_<T>` (template_function -- PyTorch alias for py::class_)
/// - `intrusive_ptr_class_<T>` and variants
fn is_class_constructor_call(func_node: &Node, source: &[u8]) -> bool {
    let text = match func_node.utf8_text(source).ok() {
        Some(t) => t,
        None => return false,
    };
    match func_node.kind() {
        "qualified_identifier" => {
            text.starts_with("py::class_") || text.starts_with("nb::class_")
        }
        "template_function" => {
            CLASS_TEMPLATE_SUFFIXES
                .iter()
                .any(|suffix| text.starts_with(suffix))
        }
        _ => false,
    }
}

/// Extract py::class_ info by walking the receiver chain of a .def() call.
///
/// For `py::class_<T>(m, "Name").def("method", ...)`, the AST is:
/// ```text
/// call_expression (.def call)
///   function: field_expression
///     argument: call_expression (py::class_<T>(m, "Name"))  <-- we look here
///     field: "def"
/// ```
///
/// Walks down the `argument` of field_expressions until it finds a py::class_
/// call_expression, then extracts the class binding info.
fn extract_class_from_chain(field_expr: &Node, ctx: &DetectContext) -> Option<ClassBindingInfo> {
    let mut current = field_expr.child_by_field_name("argument")?;

    loop {
        match current.kind() {
            "call_expression" => {
                // Check if this call is py::class_<T>(m, "Name")
                if let Some(func) = current.child_by_field_name("function") {
                    if is_class_constructor_call(&func, ctx.source) {
                        return parse_class_binding(&current, ctx);
                    }
                }
                // Otherwise, might be another chained .def() call -- walk deeper
                if let Some(func) = current.child_by_field_name("function") {
                    if func.kind() == "field_expression" {
                        current = func.child_by_field_name("argument")?;
                        continue;
                    }
                }
                return None;
            }
            "field_expression" => {
                current = current.child_by_field_name("argument")?;
            }
            _ => return None,
        }
    }
}

/// Information about a py::class_<T> binding registration.
#[derive(Clone)]
struct ClassBindingInfo {
    #[allow(dead_code)]
    cpp_type: String,
    py_name: String,
}

/// Parse `py::class_<CppType>(m, "PyName")` or `py::class_<CppType, Base>(m, "PyName")`.
///
/// Also handles PyTorch aliases like `shared_ptr_class_<CppType>(m, "PyName")`.
fn parse_class_binding(node: &Node, ctx: &DetectContext) -> Option<ClassBindingInfo> {
    let func = node.child_by_field_name("function")?;
    let func_text = func.utf8_text(ctx.source).ok()?;

    // Extract template parameter by finding the first `<` after a `class_` suffix.
    // Handles: py::class_<T>, shared_ptr_class_<T>, intrusive_ptr_class_<T>, etc.
    let cpp_type = find_template_type_param(func_text)?;

    // Extract Python name from arguments
    let args = node.child_by_field_name("arguments")?;
    let py_name = collect_arg_nodes(&args)
        .iter()
        .find_map(|c| extract_string_literal(c, ctx.source))?;

    Some(ClassBindingInfo { cpp_type, py_name })
}

/// Extract the first template type parameter from a class_ pattern.
///
/// Given `py::class_<Foo, Bar>` -> "Foo"
/// Given `shared_ptr_class_<::c10d::Reducer>` -> "::c10d::Reducer"
fn find_template_type_param(text: &str) -> Option<String> {
    // Find "class_<" in the text (works for py::class_<, shared_ptr_class_<, etc.)
    let class_pos = text.find("class_<")?;
    let rest = &text[class_pos + 7..]; // skip "class_<"
    // Take up to first comma or > to handle py::class_<T, Base>
    let end = rest
        .find(|c: char| c == ',' || c == '>')
        .unwrap_or(rest.len());
    // Trim leading `::` for global-scope types (::c10d::Reducer -> c10d::Reducer)
    let t = rest[..end].trim().trim_start_matches("::");
    if t.is_empty() {
        None
    } else {
        Some(t.to_string())
    }
}

/// Get the name from a function declarator.
fn get_declarator_name(declarator: &Node, source: &[u8]) -> Option<String> {
    if declarator.kind() == "function_declarator" {
        if let Some(inner) = declarator.child_by_field_name("declarator") {
            if inner.kind() == "identifier" {
                return inner.utf8_text(source).ok().map(|s| s.to_string());
            }
        }
    }
    if declarator.kind() == "identifier" {
        return declarator.utf8_text(source).ok().map(|s| s.to_string());
    }
    None
}

/// Get the field name from a field_expression node.
fn get_field_name(field_expr: &Node, source: &[u8]) -> Option<String> {
    let field = field_expr.child_by_field_name("field")?;
    field.utf8_text(source).ok().map(|s| s.to_string())
}

/// Extract the first argument from PYBIND11_MODULE(name, m) { ... }.
///
/// tree-sitter-cpp treats it as a function_definition where the first
/// parameter's type name is actually the module name.
fn extract_macro_first_arg(node: &Node, source: &[u8]) -> Option<String> {
    let declarator = node.child_by_field_name("declarator")?;
    let params = declarator.child_by_field_name("parameters")?;
    let mut cursor = params.walk();
    for child in params.children(&mut cursor) {
        match child.kind() {
            "parameter_declaration" => {
                // tree-sitter sees the module name as a type_identifier
                if let Some(type_node) = child.child_by_field_name("type") {
                    if let Ok(text) = type_node.utf8_text(source) {
                        let name = text.trim();
                        if !name.is_empty() {
                            return Some(name.to_string());
                        }
                    }
                }
                // Fallback: use entire parameter text
                if let Ok(text) = child.utf8_text(source) {
                    let name = text.trim();
                    if !name.is_empty() && name != "(" && name != ")" && name != "," {
                        return Some(name.to_string());
                    }
                }
            }
            "identifier" => {
                if let Ok(text) = child.utf8_text(source) {
                    let name = text.trim();
                    if !name.is_empty() && name != "(" && name != ")" && name != "," {
                        return Some(name.to_string());
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// Collect non-punctuation child nodes from an argument_list.
fn collect_arg_nodes<'a>(args: &'a Node) -> Vec<Node<'a>> {
    let mut cursor = args.walk();
    args.children(&mut cursor)
        .filter(|c| {
            let k = c.kind();
            k != "(" && k != ")" && k != "," && k != "comment"
        })
        .collect()
}

/// Extract the string content from a string_literal node.
fn extract_string_literal(node: &Node, source: &[u8]) -> Option<String> {
    match node.kind() {
        "string_literal" | "string_content" => {
            let text = node.utf8_text(source).ok()?;
            Some(text.trim_matches('"').to_string())
        }
        "concatenated_string" => {
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "string_literal" || child.kind() == "string_content" {
                    return extract_string_literal(&child, source);
                }
            }
            None
        }
        _ => None,
    }
}

/// Truncate node text for raw_pattern field.
fn truncated_text(node: &Node, source: &[u8], max_len: usize) -> Option<String> {
    node.utf8_text(source).ok().map(|s| {
        if s.len() > max_len {
            format!("{}...", &s[..max_len])
        } else {
            s.to_string()
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tree_sitter::Parser;

    fn parse_cpp(source: &str) -> Tree {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_cpp::LANGUAGE.into())
            .expect("Failed to set C++ language");
        parser
            .parse(source.as_bytes(), None)
            .expect("Failed to parse")
    }

    fn detect_bindings(source: &str) -> Vec<BindingDeclaration> {
        let tree = parse_cpp(source);
        let detector = Pybind11Detector;
        detector
            .detect(&tree, source.as_bytes(), "test.cpp", "cpp")
            .expect("Detection failed")
    }

    #[test]
    fn test_simple_def_with_address_of() {
        let decls = detect_bindings(
            r#"
            void initModule(py::module& m) {
                m.def("_initCrashHandler", &_initCrashHandler);
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "_initCrashHandler");
        let hf = decls[0].host_function.as_ref().unwrap();
        assert_eq!(hf.name, "_initCrashHandler");
        assert_eq!(hf.qualified_name.as_deref(), Some("_initCrashHandler"));
    }

    #[test]
    fn test_def_with_qualified_name() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                m.def("_demangle", &c10::demangle);
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "_demangle");
        let hf = decls[0].host_function.as_ref().unwrap();
        assert_eq!(hf.name, "demangle");
        assert_eq!(hf.qualified_name.as_deref(), Some("c10::demangle"));
    }

    #[test]
    fn test_def_with_deeply_qualified_name() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                m.def("vitals_enabled", &at::vitals::torchVitalEnabled);
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "vitals_enabled");
        let hf = decls[0].host_function.as_ref().unwrap();
        assert_eq!(hf.name, "torchVitalEnabled");
        assert_eq!(
            hf.qualified_name.as_deref(),
            Some("at::vitals::torchVitalEnabled")
        );
    }

    #[test]
    fn test_def_with_lambda() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                m.def("_set_cached", [](bool enabled) { do_something(enabled); });
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "_set_cached");
        assert!(decls[0].host_function.is_none());
        assert!(decls[0].confidence < 1.0);
    }

    #[test]
    fn test_def_without_address_of() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                m.def("bar", foo);
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "bar");
        let hf = decls[0].host_function.as_ref().unwrap();
        assert_eq!(hf.name, "foo");
    }

    #[test]
    fn test_overload_cast() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                m.def("method", py::overload_cast<int>(&Cls::method));
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "method");
        let hf = decls[0].host_function.as_ref().unwrap();
        assert_eq!(hf.name, "method");
        assert_eq!(hf.qualified_name.as_deref(), Some("Cls::method"));
    }

    #[test]
    fn test_wrap_pybind_function() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                m.def("init_num_threads", torch::wrap_pybind_function(at::init_num_threads));
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "init_num_threads");
        let hf = decls[0].host_function.as_ref().unwrap();
        assert_eq!(hf.name, "init_num_threads");
        assert_eq!(
            hf.qualified_name.as_deref(),
            Some("at::init_num_threads")
        );
    }

    #[test]
    fn test_class_chain_def() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                py::class_<WeakTensorRef>(m, "_WeakTensorRef")
                    .def("expired", &WeakTensorRef::expired);
            }
        "#,
        );
        let method_decls: Vec<_> = decls
            .iter()
            .filter(|d| d.exposed_name == "expired")
            .collect();
        assert_eq!(method_decls.len(), 1);
        assert_eq!(
            method_decls[0].class_name.as_deref(),
            Some("_WeakTensorRef")
        );
        let hf = method_decls[0].host_function.as_ref().unwrap();
        assert_eq!(hf.name, "expired");
    }

    #[test]
    fn test_class_chain_multiple_defs() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                py::class_<TensorGeometry>(m, "TensorGeometry")
                    .def("sizes", &TensorGeometry::sizes)
                    .def("strides", &TensorGeometry::strides)
                    .def("storage_offset", &TensorGeometry::storage_offset);
            }
        "#,
        );
        assert_eq!(decls.len(), 3);
        for d in &decls {
            assert_eq!(d.class_name.as_deref(), Some("TensorGeometry"));
        }
        let names: Vec<&str> = decls.iter().map(|d| d.exposed_name.as_str()).collect();
        assert!(names.contains(&"sizes"));
        assert!(names.contains(&"strides"));
        assert!(names.contains(&"storage_offset"));
    }

    #[test]
    fn test_class_chain_with_init() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                py::class_<WeakTensorRef>(m, "_WeakTensorRef")
                    .def(py::init([](int x) { return WeakTensorRef(); }))
                    .def("expired", &WeakTensorRef::expired);
            }
        "#,
        );
        let init_decls: Vec<_> = decls
            .iter()
            .filter(|d| d.exposed_name == "__init__")
            .collect();
        assert_eq!(init_decls.len(), 1);
        assert_eq!(
            init_decls[0].class_name.as_deref(),
            Some("_WeakTensorRef")
        );

        let method_decls: Vec<_> = decls
            .iter()
            .filter(|d| d.exposed_name == "expired")
            .collect();
        assert_eq!(method_decls.len(), 1);
    }

    #[test]
    fn test_def_property_readonly() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                py::class_<InputMetadata>(m, "_InputMetadata")
                    .def_property_readonly("device", &InputMetadata::device);
            }
        "#,
        );
        let prop_decls: Vec<_> = decls
            .iter()
            .filter(|d| d.exposed_name == "device")
            .collect();
        assert_eq!(prop_decls.len(), 1);
        assert_eq!(
            prop_decls[0].class_name.as_deref(),
            Some("_InputMetadata")
        );
        let hf = prop_decls[0].host_function.as_ref().unwrap();
        assert_eq!(hf.name, "device");
    }

    #[test]
    fn test_def_static() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                py::class_<Foo>(m, "Foo")
                    .def_static("create", &Foo::create);
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "create");
        assert_eq!(decls[0].class_name.as_deref(), Some("Foo"));
    }

    #[test]
    fn test_def_readwrite() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                py::class_<Foo>(m, "Foo")
                    .def_readwrite("value", &Foo::value);
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "value");
        assert_eq!(decls[0].class_name.as_deref(), Some("Foo"));
    }

    #[test]
    fn test_pybind11_module() {
        let decls = detect_bindings(
            r#"
            PYBIND11_MODULE(torch_module, m) {
                m.def("foo", &bar);
                m.def("baz", &qux);
            }
        "#,
        );
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].module_name.as_deref(), Some("torch_module"));
        assert_eq!(decls[1].module_name.as_deref(), Some("torch_module"));
    }

    #[test]
    fn test_multiline_def_with_lambda() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                m.def(
                    "set_vital",
                    [](const std::string& vital,
                       const std::string& attr) { return true; });
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "set_vital");
    }

    #[test]
    fn test_no_duplicate_declarations() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                py::class_<Event>(m, "Event")
                    .def("name", &Event::name)
                    .def("device", &Event::device);
            }
        "#,
        );
        assert_eq!(decls.len(), 2);
        let names: Vec<&str> = decls.iter().map(|d| d.exposed_name.as_str()).collect();
        assert_eq!(names.iter().filter(|&&n| n == "name").count(), 1);
        assert_eq!(names.iter().filter(|&&n| n == "device").count(), 1);
    }

    #[test]
    fn test_def_with_docstring() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                m.def("init_threads",
                      torch::wrap_pybind_function(at::init_num_threads),
                      R"(Initialize threads.)");
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "init_threads");
        let hf = decls[0].host_function.as_ref().unwrap();
        assert_eq!(hf.qualified_name.as_deref(), Some("at::init_num_threads"));
    }

    #[test]
    fn test_mixed_module_and_class() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                m.def("global_func", &global_func);
                py::class_<MyClass>(m, "MyClass")
                    .def("method", &MyClass::method);
            }
        "#,
        );
        assert_eq!(decls.len(), 2);

        let global = decls
            .iter()
            .find(|d| d.exposed_name == "global_func")
            .unwrap();
        assert!(global.class_name.is_none());

        let method = decls.iter().find(|d| d.exposed_name == "method").unwrap();
        assert_eq!(method.class_name.as_deref(), Some("MyClass"));
    }

    #[test]
    fn test_long_def_readonly_chain() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                py::class_<cudaDeviceProp>(m, "_CudaDeviceProperties")
                    .def_readonly("name", &cudaDeviceProp::name)
                    .def_readonly("major", &cudaDeviceProp::major)
                    .def_readonly("minor", &cudaDeviceProp::minor)
                    .def_property_readonly(
                        "clock_rate",
                        [](const cudaDeviceProp&) { return 42; });
            }
        "#,
        );
        assert_eq!(decls.len(), 4, "Expected 4 declarations, got {:?}", decls.iter().map(|d| &d.exposed_name).collect::<Vec<_>>());

        // The three def_readonly should have host_function
        let name = decls.iter().find(|d| d.exposed_name == "name").unwrap();
        assert!(name.host_function.is_some(), "def_readonly should have host_function");
        assert_eq!(name.host_function.as_ref().unwrap().qualified_name.as_deref(), Some("cudaDeviceProp::name"));

        let major = decls.iter().find(|d| d.exposed_name == "major").unwrap();
        assert!(major.host_function.is_some());

        // The def_property_readonly with lambda should NOT have host_function
        let clock = decls.iter().find(|d| d.exposed_name == "clock_rate").unwrap();
        assert!(clock.host_function.is_none(), "Lambda property should not have host_function");

        // All should have class context
        for d in &decls {
            assert_eq!(d.class_name.as_deref(), Some("_CudaDeviceProperties"), "Missing class for {}", d.exposed_name);
        }
    }

    #[test]
    fn test_shared_ptr_class_alias() {
        let decls = detect_bindings(
            r#"
            template <typename T>
            using shared_ptr_class_ = py::class_<T, std::shared_ptr<T>>;

            void init(py::module& module) {
                shared_ptr_class_<::c10d::Reducer>(module, "Reducer")
                    .def("prepare_for_forward", &::c10d::Reducer::prepare_for_forward)
                    .def("prepare_for_backward", &::c10d::Reducer::prepare_for_backward);
            }
        "#,
        );
        assert_eq!(decls.len(), 2, "Expected 2 declarations, got {:?}", decls.iter().map(|d| &d.exposed_name).collect::<Vec<_>>());
        for d in &decls {
            assert_eq!(d.class_name.as_deref(), Some("Reducer"), "Missing class for {}", d.exposed_name);
            assert!(d.host_function.is_some(), "Missing host_function for {}", d.exposed_name);
        }
        let prep_fwd = decls.iter().find(|d| d.exposed_name == "prepare_for_forward").unwrap();
        assert_eq!(
            prep_fwd.host_function.as_ref().unwrap().qualified_name.as_deref(),
            Some("::c10d::Reducer::prepare_for_forward")
        );
    }

    #[test]
    fn test_def_property_readonly_with_lambda() {
        let decls = detect_bindings(
            r#"
            void init(py::module& m) {
                py::class_<Meta>(m, "_Meta")
                    .def_property_readonly("dtype", [](const Meta& m) { return m.dtype(); });
            }
        "#,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "dtype");
        assert_eq!(decls[0].class_name.as_deref(), Some("_Meta"));
        assert!(decls[0].host_function.is_none());
    }
}
