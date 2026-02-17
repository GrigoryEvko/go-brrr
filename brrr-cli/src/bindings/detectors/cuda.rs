//! CUDA dispatch macro detector for PyTorch's ATen dispatch system.
//!
//! Detects:
//! - `REGISTER_DISPATCH(stub_name, &kernel_impl)` -- kernel registration (links stub to impl)
//! - `REGISTER_ARCH_DISPATCH(stub_name, DEFAULT, &kernel_impl)` -- arch-specific dispatch
//! - `ALSO_REGISTER_AVX512_DISPATCH(stub_name, &kernel_impl)` -- AVX512 variant
//! - `DECLARE_DISPATCH(fn_type, stub_name)` -- dispatch stub declaration (header)
//! - `DEFINE_DISPATCH(stub_name)` -- dispatch stub definition (creates variable)

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
            || memchr::memmem::find(source, b"REGISTER_ARCH_DISPATCH").is_some()
            || memchr::memmem::find(source, b"ALSO_REGISTER_AVX512_DISPATCH").is_some()
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

/// Extract the content between balanced parentheses starting at position 0.
/// Returns the inner content (excluding the outer parens) if balanced.
fn extract_balanced_parens(s: &str) -> Option<&str> {
    if !s.starts_with('(') {
        return None;
    }
    let mut depth = 0i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(&s[1..i]);
                }
            }
            _ => {}
        }
    }
    None
}

/// Split macro arguments respecting parenthesis nesting.
/// Only splits on commas at depth 0 (the outermost level).
fn split_args(args: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;

    for (i, ch) in args.char_indices() {
        match ch {
            '(' | '<' => depth += 1,
            ')' | '>' => depth -= 1,
            ',' if depth == 0 => {
                result.push(&args[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    result.push(&args[start..]);
    result
}

/// Clean a kernel reference: strip `&`, whitespace, and newlines.
fn clean_kernel_ref(raw: &str) -> String {
    let s: String = raw
        .chars()
        .filter(|c| !c.is_ascii_whitespace())
        .collect();
    s.trim_start_matches('&').to_string()
}

fn collect_dispatch_macros(
    node: &tree_sitter::Node,
    source: &[u8],
    file_path: &str,
    declarations: &mut Vec<BindingDeclaration>,
) {
    let kind = node.kind();

    // Match call_expression (most dispatch macros parse as function calls).
    // Do NOT also match expression_statement -- it wraps call_expression and
    // would cause every declaration to be emitted twice.
    if kind == "call_expression" {
        if let Ok(text) = node.utf8_text(source) {
            let text = text.trim();
            try_parse_dispatch_macro(text, file_path, node.start_position().row + 1, declarations);
        }
    }
    // tree-sitter-cpp cannot parse DECLARE_DISPATCH with inline function
    // pointer types (e.g. void(*)(A&, const B&)) as call_expression.
    // It produces an ERROR node wrapping a function_declarator instead.
    // Handle the ERROR node directly to catch these cases.
    else if kind == "ERROR" {
        if let Ok(text) = node.utf8_text(source) {
            let text = text.trim();
            // Only attempt DECLARE_DISPATCH here to avoid double-processing
            // macros that already parsed as call_expression.
            if text.starts_with("DECLARE_DISPATCH") {
                try_parse_dispatch_macro(
                    text,
                    file_path,
                    node.start_position().row + 1,
                    declarations,
                );
                // Return early -- do not recurse into children of this ERROR
                // node, since the function_declarator child has the same text
                // and would cause duplicate detection.
                return;
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_dispatch_macros(&child, source, file_path, declarations);
    }
}

/// Dispatch macro prefixes and their argument structures.
enum MacroKind {
    /// REGISTER_DISPATCH(stub_name, &kernel_impl) -- 2 args
    Register,
    /// REGISTER_ARCH_DISPATCH(stub_name, arch_tag, &kernel_impl) -- 3 args
    RegisterArch,
    /// ALSO_REGISTER_AVX512_DISPATCH(stub_name, &kernel_impl) -- 2 args
    AlsoRegisterAvx512,
    /// DEFINE_DISPATCH(stub_name) -- 1 arg
    Define,
    /// DECLARE_DISPATCH(fn_type, stub_name) -- 2+ args (fn_type may contain commas)
    Declare,
}

fn try_parse_dispatch_macro(
    text: &str,
    file_path: &str,
    line: usize,
    declarations: &mut Vec<BindingDeclaration>,
) {
    // Identify macro kind and extract the parenthesized argument string.
    // Order matters: ALSO_REGISTER_AVX512_DISPATCH and REGISTER_ARCH_DISPATCH
    // must be checked before REGISTER_DISPATCH since they share prefix structure.
    let (kind, args_str) =
        if let Some(rest) = text.strip_prefix("ALSO_REGISTER_AVX512_DISPATCH") {
            if let Some(inner) = extract_balanced_parens(rest) {
                (MacroKind::AlsoRegisterAvx512, inner)
            } else {
                return;
            }
        } else if let Some(rest) = text.strip_prefix("REGISTER_ARCH_DISPATCH") {
            if let Some(inner) = extract_balanced_parens(rest) {
                (MacroKind::RegisterArch, inner)
            } else {
                return;
            }
        } else if let Some(rest) = text.strip_prefix("REGISTER_DISPATCH") {
            if let Some(inner) = extract_balanced_parens(rest) {
                (MacroKind::Register, inner)
            } else {
                return;
            }
        } else if let Some(rest) = text.strip_prefix("DEFINE_DISPATCH") {
            if let Some(inner) = extract_balanced_parens(rest) {
                (MacroKind::Define, inner)
            } else {
                return;
            }
        } else if let Some(rest) = text.strip_prefix("DECLARE_DISPATCH") {
            if let Some(inner) = extract_balanced_parens(rest) {
                (MacroKind::Declare, inner)
            } else {
                return;
            }
        } else {
            return;
        };

    match kind {
        MacroKind::Register | MacroKind::AlsoRegisterAvx512 => {
            // REGISTER_DISPATCH(stub_name, &kernel_impl)
            let parts = split_args(args_str);
            if parts.len() == 2 {
                let stub_name = parts[0].trim();
                let kernel_raw = parts[1].trim();

                // Skip nullptr registrations (no actual kernel)
                if kernel_raw == "nullptr" {
                    return;
                }

                let kernel_name = clean_kernel_ref(kernel_raw);
                if stub_name.is_empty() || kernel_name.is_empty() {
                    return;
                }

                declarations.push(BindingDeclaration {
                    system: BindingSystem::CudaDispatch,
                    direction: BindingDirection::Dispatch,
                    exposed_name: stub_name.to_string(),
                    host_function: Some(FunctionRef {
                        file: String::new(),
                        name: kernel_name,
                        qualified_name: None,
                    }),
                    target_function: None,
                    declaration_file: file_path.to_string(),
                    declaration_line: line,
                    module_name: None,
                    class_name: None,
                    raw_pattern: Some(text.to_string()),
                    confidence: 1.0,
                });
            }
        }
        MacroKind::RegisterArch => {
            // REGISTER_ARCH_DISPATCH(stub_name, arch_tag, &kernel_impl)
            let parts = split_args(args_str);
            if parts.len() == 3 {
                let stub_name = parts[0].trim();
                let kernel_raw = parts[2].trim();

                // Skip nullptr / arch-specific null patterns like
                // ((void*)(fn) ? nullptr : nullptr)
                let kernel_clean: String = kernel_raw
                    .chars()
                    .filter(|c| !c.is_ascii_whitespace())
                    .collect();
                if kernel_clean == "nullptr"
                    || kernel_clean.contains("nullptr")
                    || kernel_clean.is_empty()
                {
                    return;
                }

                let kernel_name = clean_kernel_ref(kernel_raw);
                if stub_name.is_empty() || kernel_name.is_empty() {
                    return;
                }

                declarations.push(BindingDeclaration {
                    system: BindingSystem::CudaDispatch,
                    direction: BindingDirection::Dispatch,
                    exposed_name: stub_name.to_string(),
                    host_function: Some(FunctionRef {
                        file: String::new(),
                        name: kernel_name,
                        qualified_name: None,
                    }),
                    target_function: None,
                    declaration_file: file_path.to_string(),
                    declaration_line: line,
                    module_name: None,
                    class_name: None,
                    raw_pattern: Some(text.to_string()),
                    confidence: 1.0,
                });
            }
        }
        MacroKind::Define => {
            // DEFINE_DISPATCH(stub_name)
            let stub_name = args_str.trim();
            if stub_name.is_empty() {
                return;
            }

            declarations.push(BindingDeclaration {
                system: BindingSystem::CudaDispatch,
                direction: BindingDirection::Dispatch,
                exposed_name: stub_name.to_string(),
                host_function: None,
                target_function: None,
                declaration_file: file_path.to_string(),
                declaration_line: line,
                module_name: None,
                class_name: None,
                raw_pattern: Some(text.to_string()),
                confidence: 0.5,
            });
        }
        MacroKind::Declare => {
            // DECLARE_DISPATCH(fn_type, stub_name)
            // fn_type can contain commas (e.g., void(*)(TensorIterator&, const Scalar&))
            // The stub_name is always the LAST argument after the final top-level comma.
            let parts = split_args(args_str);
            if parts.len() >= 2 {
                let stub_name = parts.last().unwrap().trim();
                if stub_name.is_empty() {
                    return;
                }

                declarations.push(BindingDeclaration {
                    system: BindingSystem::CudaDispatch,
                    direction: BindingDirection::Dispatch,
                    exposed_name: stub_name.to_string(),
                    host_function: None,
                    target_function: None,
                    declaration_file: file_path.to_string(),
                    declaration_line: line,
                    module_name: None,
                    class_name: None,
                    raw_pattern: Some(text.to_string()),
                    confidence: 0.5,
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_balanced_parens() {
        assert_eq!(
            extract_balanced_parens("(stub, &kernel)"),
            Some("stub, &kernel")
        );
        assert_eq!(
            extract_balanced_parens("(void(*)(int, float), stub)"),
            Some("void(*)(int, float), stub")
        );
        assert_eq!(extract_balanced_parens("(stub)"), Some("stub"));
        assert_eq!(extract_balanced_parens("stub)"), None);
        assert_eq!(extract_balanced_parens("(unclosed"), None);
    }

    #[test]
    fn test_split_args_simple() {
        let parts = split_args("stub_name, &kernel_impl");
        assert_eq!(parts, vec!["stub_name", " &kernel_impl"]);
    }

    #[test]
    fn test_split_args_function_pointer() {
        // DECLARE_DISPATCH(void(*)(TensorIterator&, const c10::Scalar&), fill_stub)
        let parts = split_args("void(*)(TensorIterator&, const c10::Scalar&), fill_stub");
        assert_eq!(
            parts,
            vec![
                "void(*)(TensorIterator&, const c10::Scalar&)",
                " fill_stub"
            ]
        );
    }

    #[test]
    fn test_split_args_three() {
        let parts = split_args("stub_name, DEFAULT, &kernel_impl");
        assert_eq!(parts, vec!["stub_name", " DEFAULT", " &kernel_impl"]);
    }

    #[test]
    fn test_clean_kernel_ref() {
        assert_eq!(clean_kernel_ref("&kernel_impl"), "kernel_impl");
        assert_eq!(clean_kernel_ref("kernel_impl"), "kernel_impl");
        assert_eq!(
            clean_kernel_ref("&CPU_CAPABILITY::my_kernel"),
            "CPU_CAPABILITY::my_kernel"
        );
        assert_eq!(
            clean_kernel_ref("&cpublas::cpublas_gemm_impl"),
            "cpublas::cpublas_gemm_impl"
        );
        assert_eq!(
            clean_kernel_ref("\n    &shifted_chebyshev_polynomial_t_kernel"),
            "shifted_chebyshev_polynomial_t_kernel"
        );
    }

    #[test]
    fn test_register_dispatch_basic() {
        let mut decls = Vec::new();
        try_parse_dispatch_macro(
            "REGISTER_DISPATCH(threshold_stub, &threshold_kernel)",
            "test.cpp",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "threshold_stub");
        assert_eq!(
            decls[0].host_function.as_ref().unwrap().name,
            "threshold_kernel"
        );
        assert_eq!(decls[0].confidence, 1.0);
    }

    #[test]
    fn test_register_dispatch_no_ampersand() {
        let mut decls = Vec::new();
        try_parse_dispatch_macro(
            "REGISTER_DISPATCH(ldexp_stub, ldexp_kernel)",
            "test.cpp",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(
            decls[0].host_function.as_ref().unwrap().name,
            "ldexp_kernel"
        );
    }

    #[test]
    fn test_register_dispatch_nullptr() {
        let mut decls = Vec::new();
        try_parse_dispatch_macro(
            "REGISTER_DISPATCH(mean_stub, nullptr)",
            "test.cpp",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 0);
    }

    #[test]
    fn test_register_dispatch_multiline() {
        let mut decls = Vec::new();
        try_parse_dispatch_macro(
            "REGISTER_DISPATCH(\n    shifted_chebyshev_polynomial_t_stub,\n    &shifted_chebyshev_polynomial_t_kernel)",
            "test.cpp",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(
            decls[0].exposed_name,
            "shifted_chebyshev_polynomial_t_stub"
        );
        assert_eq!(
            decls[0].host_function.as_ref().unwrap().name,
            "shifted_chebyshev_polynomial_t_kernel"
        );
    }

    #[test]
    fn test_register_dispatch_namespaced() {
        let mut decls = Vec::new();
        try_parse_dispatch_macro(
            "REGISTER_DISPATCH(cpublas::gemm_stub, &cpublas::cpublas_gemm_impl)",
            "test.cpp",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "cpublas::gemm_stub");
        assert_eq!(
            decls[0].host_function.as_ref().unwrap().name,
            "cpublas::cpublas_gemm_impl"
        );
    }

    #[test]
    fn test_register_arch_dispatch() {
        let mut decls = Vec::new();
        try_parse_dispatch_macro(
            "REGISTER_ARCH_DISPATCH(cholesky_stub, DEFAULT, &cholesky_kernel)",
            "test.cpp",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "cholesky_stub");
        assert_eq!(
            decls[0].host_function.as_ref().unwrap().name,
            "cholesky_kernel"
        );
    }

    #[test]
    fn test_also_register_avx512() {
        let mut decls = Vec::new();
        try_parse_dispatch_macro(
            "ALSO_REGISTER_AVX512_DISPATCH(atan2_stub, &atan2_kernel)",
            "test.cpp",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "atan2_stub");
        assert_eq!(
            decls[0].host_function.as_ref().unwrap().name,
            "atan2_kernel"
        );
    }

    #[test]
    fn test_define_dispatch() {
        let mut decls = Vec::new();
        try_parse_dispatch_macro(
            "DEFINE_DISPATCH(threshold_stub)",
            "test.cpp",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "threshold_stub");
        assert!(decls[0].host_function.is_none());
        assert_eq!(decls[0].confidence, 0.5);
    }

    #[test]
    fn test_declare_dispatch_simple() {
        let mut decls = Vec::new();
        try_parse_dispatch_macro(
            "DECLARE_DISPATCH(threshold_fn, threshold_stub)",
            "test.h",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "threshold_stub");
        assert!(decls[0].host_function.is_none());
        assert_eq!(decls[0].confidence, 0.5);
    }

    #[test]
    fn test_declare_dispatch_function_pointer_type() {
        let mut decls = Vec::new();
        try_parse_dispatch_macro(
            "DECLARE_DISPATCH(void(*)(TensorIterator&, const c10::Scalar&), fill_stub)",
            "test.h",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].exposed_name, "fill_stub");
    }

    #[test]
    fn test_register_arch_dispatch_nullptr() {
        let mut decls = Vec::new();
        // Pattern from DispatchStub.h AVX512 disabled case
        try_parse_dispatch_macro(
            "REGISTER_ARCH_DISPATCH(name, CPU_CAPABILITY, ((void*)(fn) ? nullptr : nullptr))",
            "test.cpp",
            10,
            &mut decls,
        );
        assert_eq!(decls.len(), 0);
    }

    /// Integration test: parse real C++ with tree-sitter and verify no duplicates
    #[test]
    fn test_tree_sitter_no_duplicates() {
        let source = br#"
DEFINE_DISPATCH(add_stub);
DEFINE_DISPATCH(sub_stub);
REGISTER_DISPATCH(add_stub, &add_kernel);
REGISTER_DISPATCH(sub_stub, &sub_kernel);
"#;
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&tree_sitter_cpp::LANGUAGE.into())
            .unwrap();
        let tree = parser.parse(source, None).unwrap();

        let detector = CudaDispatchDetector;
        let decls = detector
            .detect(&tree, source, "test.cpp", "cpp")
            .unwrap();

        // Should be exactly 4: 2 DEFINE + 2 REGISTER (no duplicates!)
        assert_eq!(decls.len(), 4, "got {} declarations: {:?}", decls.len(),
            decls.iter().map(|d| &d.raw_pattern).collect::<Vec<_>>());

        // Verify REGISTER_DISPATCH entries have host_function
        let register_decls: Vec<_> = decls.iter().filter(|d| d.host_function.is_some()).collect();
        assert_eq!(register_decls.len(), 2);

        // Verify DEFINE_DISPATCH entries have no host_function and lower confidence
        let define_decls: Vec<_> = decls
            .iter()
            .filter(|d| d.host_function.is_none())
            .collect();
        assert_eq!(define_decls.len(), 2);
        for d in &define_decls {
            assert_eq!(d.confidence, 0.5);
        }
    }

    /// Integration test: multi-line REGISTER_DISPATCH with tree-sitter
    #[test]
    fn test_tree_sitter_multiline_register() {
        let source = br#"
REGISTER_DISPATCH(
    shifted_chebyshev_polynomial_t_stub,
    &shifted_chebyshev_polynomial_t_kernel);
"#;
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&tree_sitter_cpp::LANGUAGE.into())
            .unwrap();
        let tree = parser.parse(source, None).unwrap();

        let detector = CudaDispatchDetector;
        let decls = detector
            .detect(&tree, source, "test.cpp", "cpp")
            .unwrap();

        assert_eq!(decls.len(), 1);
        assert_eq!(
            decls[0].exposed_name,
            "shifted_chebyshev_polynomial_t_stub"
        );
        assert_eq!(
            decls[0].host_function.as_ref().unwrap().name,
            "shifted_chebyshev_polynomial_t_kernel"
        );
    }

    /// Integration test: DECLARE_DISPATCH with function pointer type containing commas
    #[test]
    fn test_tree_sitter_declare_with_fnptr() {
        let source = br#"
DECLARE_DISPATCH(void(*)(TensorIterator&, const c10::Scalar&), fill_stub);
DECLARE_DISPATCH(padding_fn, reflection_pad1d_kernel);
"#;
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&tree_sitter_cpp::LANGUAGE.into())
            .unwrap();
        let tree = parser.parse(source, None).unwrap();

        let detector = CudaDispatchDetector;
        let decls = detector
            .detect(&tree, source, "test.h", "cpp")
            .unwrap();

        // Both should be detected with correct stub names
        let names: Vec<&str> = decls.iter().map(|d| d.exposed_name.as_str()).collect();
        assert!(
            names.contains(&"fill_stub"),
            "Expected fill_stub in {:?}",
            names
        );
        assert!(
            names.contains(&"reflection_pad1d_kernel"),
            "Expected reflection_pad1d_kernel in {:?}",
            names
        );
    }
}
