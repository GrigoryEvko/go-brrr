//! Cross-file resolution for binding declarations.
//!
//! After per-file detection, each BindingDeclaration may have partial function
//! references (name only, no file). The resolver uses the FunctionIndex to
//! populate full FunctionRef values.
//!
//! Resolution strategies (tried in order for host functions):
//! 1. Exact qualified name match
//! 2. Qualified name with module-stem prefix from declaration file
//! 3. Suffix matching on qualified name components
//! 4. Class::method lookup via the class_method index
//! 5. Same-file lookup (prefer functions defined in the same file)
//! 6. Same-directory preference for ambiguous simple-name matches
//! 7. Simple name lookup (accept unique match or best proximity match)
//! 8. Suffix-based qualified name matching (fallback for namespace mismatch)
//! 9. Metadata-based synthesis (class_name + exposed_name when host_function is absent)

use std::path::Path;

use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::indexer::FunctionIndex;
use crate::callgraph::types::FunctionRef;

/// Resolve cross-file binding references using the function index.
pub fn resolve_bindings(declarations: &mut [BindingDeclaration], index: &FunctionIndex) {
    for decl in declarations.iter_mut() {
        // Phase 1: resolve existing partial references (name -> full FunctionRef)
        resolve_host_function(decl, index);

        // Phase 1.5: validate that host resolution matches the expected host language.
        // For pybind11/CUDA/TorchLibrary, the host language is always C/C++.
        // If Phase 1 resolved to a non-C++ file (e.g., .pyi stub), discard the
        // result so Phase 2 can try a better match or leave it unresolved.
        if let Some(ref hf) = decl.host_function {
            let host_must_be_cpp = matches!(
                decl.system,
                BindingSystem::Pybind11
                    | BindingSystem::CudaDispatch
                    | BindingSystem::TorchLibrary
            );
            if host_must_be_cpp && !hf.file.is_empty() && !is_cpp_file(&hf.file) {
                decl.host_function = None;
            }
        }

        // Phase 2: synthesize host_function from metadata when detector didn't provide one
        resolve_host_from_metadata(decl, index);
        // Phase 3: resolve target function references
        resolve_target_function(decl, index);
    }
}

// ---------------------------------------------------------------------------
// Name normalization
// ---------------------------------------------------------------------------

/// Normalize a C++ function reference name for lookup.
///
/// Strips leading `&`, leading `::` (global scope qualifier), template
/// parameters `<...>`, and surrounding whitespace.
fn normalize_cpp_name(name: &str) -> String {
    let s = name
        .trim()
        .trim_start_matches('&')
        .trim()
        .trim_start_matches("::");
    strip_template_params(s)
}

/// Remove template parameters from a name.
/// `foo<int, float>` -> `foo`, `Cls<T>::method` -> `Cls::method`.
fn strip_template_params(name: &str) -> String {
    let mut result = String::with_capacity(name.len());
    let mut depth = 0u32;
    for ch in name.chars() {
        match ch {
            '<' => depth += 1,
            '>' => {
                if depth > 0 {
                    depth -= 1;
                }
            }
            _ if depth == 0 => result.push(ch),
            _ => {}
        }
    }
    result
}

/// Split a C++ qualified name into (namespace_parts, leaf_name).
/// `at::native::add` -> (["at", "native"], "add")
/// `add` -> ([], "add")
fn split_cpp_qualified(name: &str) -> (Vec<&str>, &str) {
    let parts: Vec<&str> = name.split("::").collect();
    if parts.len() <= 1 {
        (vec![], parts.first().copied().unwrap_or(""))
    } else {
        let (prefix, leaf) = parts.split_at(parts.len() - 1);
        (prefix.to_vec(), leaf[0])
    }
}

/// Extract the file stem (module name) from a file path.
fn file_stem(path: &str) -> Option<&str> {
    Path::new(path).file_stem().and_then(|s| s.to_str())
}

/// Extract the parent directory path from a file path.
fn parent_dir(path: &str) -> Option<&str> {
    Path::new(path).parent().and_then(|p| p.to_str())
}

/// Check if a file path refers to a C/C++/CUDA source or header file.
fn is_cpp_file(path: &str) -> bool {
    let ext = Path::new(path)
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or("");
    matches!(
        ext,
        "c" | "cc" | "cpp" | "cxx" | "h" | "hh" | "hpp" | "hxx" | "cu" | "cuh"
    )
}

// ---------------------------------------------------------------------------
// Disambiguation: pick the best match from multiple candidates
// ---------------------------------------------------------------------------

/// Count the number of shared path components between two file paths.
///
/// Compares from the start of each path, counting common directory components.
/// Returns 0 if paths share no common prefix.
fn shared_path_depth(a: &str, b: &str) -> usize {
    let a_parts: Vec<&str> = Path::new(a).components().map(|c| c.as_os_str().to_str().unwrap_or("")).collect();
    let b_parts: Vec<&str> = Path::new(b).components().map(|c| c.as_os_str().to_str().unwrap_or("")).collect();
    a_parts.iter().zip(b_parts.iter()).take_while(|(x, y)| x == y).count()
}

/// Pick the best candidate from multiple matches, using file proximity.
///
/// Preference order:
/// 1. Same file as declaration_file
/// 2. Same directory as declaration_file
/// 3. Deepest shared path prefix (most path components in common)
/// 4. Shortest file path as final tiebreaker
fn pick_best_candidate<'a>(
    candidates: &[&'a FunctionRef],
    declaration_file: &str,
) -> Option<&'a FunctionRef> {
    if candidates.is_empty() {
        return None;
    }
    if candidates.len() == 1 {
        return Some(candidates[0]);
    }

    // 1. Same file
    for c in candidates {
        if c.file == declaration_file {
            return Some(c);
        }
    }

    // 2. Same directory
    let decl_dir = parent_dir(declaration_file);
    if let Some(dd) = decl_dir {
        let same_dir: Vec<_> = candidates
            .iter()
            .filter(|c| parent_dir(&c.file) == Some(dd))
            .copied()
            .collect();
        if same_dir.len() == 1 {
            return Some(same_dir[0]);
        }
        if same_dir.len() > 1 {
            return same_dir
                .into_iter()
                .min_by(|a, b| a.file.len().cmp(&b.file.len()).then_with(|| a.file.cmp(&b.file)));
        }
    }

    // 3. Deepest shared path prefix -- prefer candidates in nearby directories
    //    over candidates closer to root but in unrelated directories
    candidates
        .iter()
        .max_by(|a, b| {
            let depth_a = shared_path_depth(&a.file, declaration_file);
            let depth_b = shared_path_depth(&b.file, declaration_file);
            depth_a.cmp(&depth_b)
                .then_with(|| b.file.len().cmp(&a.file.len()))
                .then_with(|| a.file.cmp(&b.file))
        })
        .copied()
}

// ---------------------------------------------------------------------------
// Qualified name lookup strategies
// ---------------------------------------------------------------------------

/// Try multiple qualified name variants for C/C++ bindings.
///
/// The FunctionIndex stores C/C++ qualified names as `module_stem::Class::method`
/// where module_stem is the file basename. But binding declarations provide
/// names like `at::native::softmax_kernel` or just `MyClass::method`.
fn try_qualified_lookup<'a>(
    qname: &str,
    declaration_file: &str,
    index: &'a FunctionIndex,
) -> Option<&'a FunctionRef> {
    let normalized = normalize_cpp_name(qname);

    // Strategy 1: Exact match
    if let Some(fref) = index.lookup_qualified(&normalized) {
        return Some(fref);
    }

    let (parts, leaf) = split_cpp_qualified(&normalized);

    // Strategy 2: Prepend declaration file's module stem
    if let Some(stem) = file_stem(declaration_file) {
        let with_stem = format!("{}::{}", stem, normalized);
        if let Some(fref) = index.lookup_qualified(&with_stem) {
            return Some(fref);
        }
    }

    // Strategy 3: Try each namespace component as module stem
    for &part in &parts {
        let variant = format!("{}::{}", part, leaf);
        if let Some(fref) = index.lookup_qualified(&variant) {
            return Some(fref);
        }
    }

    // Strategy 4: Try last two components for deeply nested namespaces
    if parts.len() >= 2 {
        let last_two = format!("{}::{}", parts[parts.len() - 1], leaf);
        if let Some(fref) = index.lookup_qualified(&last_two) {
            return Some(fref);
        }
    }

    // Strategy 5: Suffix-based lookup -- find any qualified name that ends with
    // our normalized name at a separator boundary. This handles cases where the
    // index has a longer prefix we don't know about (e.g., file stem or extra
    // namespace layers).
    if normalized.contains("::") {
        let suffix_matches = index.lookup_by_suffix(&normalized);
        if let Some(best) = pick_best_candidate(&suffix_matches, declaration_file) {
            return Some(best);
        }
    }

    None
}

/// Try class::method lookup with multiple class name variants.
fn try_class_method_lookup<'a>(
    class_name: &str,
    method_name: &str,
    declaration_file: &str,
    index: &'a FunctionIndex,
) -> Option<&'a FunctionRef> {
    let normalized_method = normalize_cpp_name(method_name);
    let normalized_class = normalize_cpp_name(class_name);

    // Try exact class::method
    let candidates = index.lookup_method(&normalized_class, &normalized_method);
    if let Some(best) = pick_best_candidate(&candidates, declaration_file) {
        return Some(best);
    }

    // Try with just the last component of class name
    if normalized_class.contains("::") {
        if let Some(last_part) = normalized_class.rsplit("::").next() {
            let candidates = index.lookup_method(last_part, &normalized_method);
            if let Some(best) = pick_best_candidate(&candidates, declaration_file) {
                return Some(best);
            }
        }
    }

    None
}

/// Try same-file lookup: find a function defined in the same file as the declaration.
fn try_same_file_lookup<'a>(
    name: &str,
    declaration_file: &str,
    index: &'a FunctionIndex,
) -> Option<&'a FunctionRef> {
    index.lookup_in_file(declaration_file, name)
}

// ---------------------------------------------------------------------------
// Host function resolution
// ---------------------------------------------------------------------------

/// Try to resolve a partial host_function (name-only) to a full FunctionRef.
fn resolve_host_function(decl: &mut BindingDeclaration, index: &FunctionIndex) {
    let host = match decl.host_function.as_ref() {
        Some(h) if h.file.is_empty() => h,
        _ => return,
    };

    let raw_name = host.name.clone();
    let normalized_name = normalize_cpp_name(&raw_name);
    let declaration_file = &decl.declaration_file;

    // Strategy 1: Qualified name lookup with multiple variants
    if let Some(ref qname) = host.qualified_name {
        if let Some(fref) = try_qualified_lookup(qname, declaration_file, index) {
            decl.host_function = Some(fref.clone());
            return;
        }
    }

    // Strategy 2: If the name itself contains "::", treat it as a qualified name
    if normalized_name.contains("::") {
        if let Some(fref) = try_qualified_lookup(&normalized_name, declaration_file, index) {
            decl.host_function = Some(fref.clone());
            return;
        }

        // Also try class::method from the name itself
        let (parts, leaf) = split_cpp_qualified(&normalized_name);
        if !parts.is_empty() {
            let class = parts.join("::");
            if let Some(fref) =
                try_class_method_lookup(&class, leaf, declaration_file, index)
            {
                decl.host_function = Some(fref.clone());
                return;
            }
        }
    }

    // Strategy 3: Class::method lookup from declaration metadata
    if let Some(ref class) = decl.class_name {
        if let Some(fref) =
            try_class_method_lookup(class, &normalized_name, declaration_file, index)
        {
            decl.host_function = Some(fref.clone());
            return;
        }
    }

    // Strategy 4: Same-file lookup
    if let Some(fref) = try_same_file_lookup(&normalized_name, declaration_file, index) {
        decl.host_function = Some(fref.clone());
        return;
    }

    // Strategy 5: Simple name lookup with proximity-based disambiguation
    let candidates = index.lookup(&normalized_name);
    if candidates.len() == 1 {
        decl.host_function = Some(candidates[0].clone());
        return;
    }
    if candidates.len() > 1 {
        if let Some(best) = pick_best_candidate(&candidates, declaration_file) {
            decl.host_function = Some(best.clone());
            return;
        }
    }

    // Strategy 6: If normalized name differs from raw name, try raw name too
    if normalized_name != raw_name {
        let candidates = index.lookup(&raw_name);
        if candidates.len() == 1 {
            decl.host_function = Some(candidates[0].clone());
            return;
        }
        if candidates.len() > 1 {
            if let Some(best) = pick_best_candidate(&candidates, declaration_file) {
                decl.host_function = Some(best.clone());
                return;
            }
        }
    }

    // Strategy 7: For names with "::", try just the leaf part
    if normalized_name.contains("::") {
        if let Some(leaf) = normalized_name.rsplit("::").next() {
            if leaf != normalized_name {
                if let Some(fref) = try_same_file_lookup(leaf, declaration_file, index) {
                    decl.host_function = Some(fref.clone());
                    return;
                }

                let candidates = index.lookup(leaf);
                if candidates.len() == 1 {
                    decl.host_function = Some(candidates[0].clone());
                    return;
                }
                if candidates.len() > 1 {
                    if let Some(best) = pick_best_candidate(&candidates, declaration_file) {
                        decl.host_function = Some(best.clone());
                        return;
                    }
                }
            }
        }
    }

    // Strategy 8: Try file stem as module prefix with the simple name
    if let Some(stem) = file_stem(declaration_file) {
        let with_stem = format!("{}::{}", stem, normalized_name);
        if let Some(fref) = index.lookup_qualified(&with_stem) {
            decl.host_function = Some(fref.clone());
            return;
        }
    }

    // Strategy 9: Suffix-based lookup for the simple name -- if the name is a
    // bare function name (no ::), try matching it as a suffix of qualified names
    // in the index, preferring candidates near the declaration file.
    {
        let suffix_matches = index.lookup_by_suffix(&normalized_name);
        if !suffix_matches.is_empty() {
            // Filter to same-file or same-directory first
            if let Some(fref) = try_same_file_lookup(&normalized_name, declaration_file, index) {
                decl.host_function = Some(fref.clone());
                return;
            }
            if suffix_matches.len() == 1 {
                decl.host_function = Some(suffix_matches[0].clone());
                return;
            }
            // For multiple matches, only pick if there's a clear same-dir winner
            let decl_dir = parent_dir(declaration_file);
            if let Some(dd) = decl_dir {
                let same_dir: Vec<_> = suffix_matches
                    .iter()
                    .filter(|c| parent_dir(&c.file) == Some(dd))
                    .collect();
                if same_dir.len() == 1 {
                    decl.host_function = Some((*same_dir[0]).clone());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Metadata-based host function synthesis
// ---------------------------------------------------------------------------

/// Check if a Python-style name is a dunder method (e.g., `__init__`, `__repr__`).
///
/// Dunder methods in pybind11 are almost always implemented as lambdas or
/// special wrappers, not direct C++ function references. Trying to resolve
/// them would produce false positives.
fn is_dunder(name: &str) -> bool {
    name.len() > 4 && name.starts_with("__") && name.ends_with("__")
}

/// Check if a name looks like a plausible C++ function name for metadata synthesis.
///
/// Rejects names that are clearly NOT function references:
/// - Empty or single-char names
/// - All-uppercase names (enum constants: "CUDA", "CPU", "MPS")
/// - Single-word capitalized names without camelCase or underscores (type names: "Metal", "Lazy")
/// - Operator overloads ("operator+")
///
/// Accepts:
/// - snake_case: "get_value", "forward"
/// - camelCase: "getValue", "ProcessGroup" (lowercase-to-uppercase transition)
/// - Qualified: "MyClass::method"
/// - With underscore: "SomeFunc_v2"
fn looks_like_cpp_function_name(name: &str) -> bool {
    if name.is_empty() || name.len() <= 1 {
        return false;
    }
    if name.starts_with("operator") {
        return false;
    }
    // All-uppercase with possible digits/underscores = enum constant
    if name
        .chars()
        .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
    {
        return false;
    }
    // Single-word starting with uppercase, no underscore, no camelCase transition,
    // no "::" = likely a type or enum value name (e.g., "Metal", "Lazy", "Stream")
    if name.starts_with(|c: char| c.is_ascii_uppercase()) {
        let has_underscore = name.contains('_');
        let has_colons = name.contains("::");
        let has_camel_transition = name
            .as_bytes()
            .windows(2)
            .any(|w| w[0].is_ascii_lowercase() && w[1].is_ascii_uppercase());
        if !has_underscore && !has_colons && !has_camel_transition {
            return false;
        }
    }
    true
}

/// Try to synthesize and resolve host_function from binding metadata when no
/// host_function reference was provided by the detector.
///
/// This handles common pybind11 patterns where the detector captures the Python
/// exposed name and class name but not the C++ implementation function. For
/// example, `.def("get_value", &MyClass::get_value)` might only capture
/// `exposed_name="get_value"` and `class_name="MyClass"`, without extracting
/// the `&MyClass::get_value` part as host_function.
///
/// Called AFTER resolve_host_function, so it only runs for declarations where
/// host_function is still None or has an empty file.
fn resolve_host_from_metadata(decl: &mut BindingDeclaration, index: &FunctionIndex) {
    // Only run when host_function is completely absent.
    if decl.host_function.is_some() {
        return;
    }

    // Only meaningful for Export-direction bindings (host exposes to target).
    if decl.direction != BindingDirection::Export {
        return;
    }

    let exposed = &decl.exposed_name;

    // Skip dunder methods -- they're almost always lambdas or wrappers.
    if is_dunder(exposed) {
        return;
    }

    // Skip names that don't look like C++ function identifiers.
    // This avoids false positives from enum values ("PrivateUse1"),
    // device names ("CUDA", "MPS"), and other string constants.
    if !looks_like_cpp_function_name(exposed) {
        return;
    }

    let declaration_file = decl.declaration_file.clone();

    // Determine if we should restrict to C/C++ files.
    // For pybind11 and cuda_dispatch bindings, the host language is C++, so we
    // only want to match C/C++ files to avoid cross-language false positives.
    let require_cpp = matches!(
        decl.system,
        BindingSystem::Pybind11 | BindingSystem::CudaDispatch | BindingSystem::TorchLibrary
    );

    // Strategy A: class_name + exposed_name -> class::method lookup
    //
    // We call index.lookup_method() directly (instead of try_class_method_lookup)
    // so we can filter candidates to C/C++ files BEFORE picking the best one.
    // This prevents .pyi stubs from being chosen as "best" by proximity when
    // valid C++ candidates exist in the same pool.
    if let Some(ref class_name) = decl.class_name {
        let norm_method = normalize_cpp_name(exposed);
        let norm_class = normalize_cpp_name(class_name);

        // Collect all class::method candidates from exact and leaf-only variants
        let mut cm_candidates: Vec<&FunctionRef> =
            index.lookup_method(&norm_class, &norm_method);
        if norm_class.contains("::") {
            if let Some(last_part) = norm_class.rsplit("::").next() {
                cm_candidates.extend(index.lookup_method(last_part, &norm_method));
            }
        }

        // Pre-filter to C/C++ files when required, then pick best
        if require_cpp {
            cm_candidates.retain(|c| is_cpp_file(&c.file));
        }
        if let Some(best) = pick_best_candidate(&cm_candidates, &declaration_file) {
            decl.host_function = Some(best.clone());
            return;
        }

        // Try qualified lookup: class_name::exposed_name
        // Filter result to C++ files.
        let qualified = format!("{}::{}", class_name, exposed);
        if let Some(fref) = try_qualified_lookup(&qualified, &declaration_file, index) {
            if !require_cpp || is_cpp_file(&fref.file) {
                decl.host_function = Some(fref.clone());
                return;
            }
        }

        // Try suffix lookup: maybe the index has a longer prefix.
        // Filter to C/C++ files to avoid cross-language false positives.
        let suffix_matches = index.lookup_by_suffix(&qualified);
        let suffix_filtered: Vec<_> = if require_cpp {
            suffix_matches
                .iter()
                .filter(|c| is_cpp_file(&c.file))
                .copied()
                .collect()
        } else {
            suffix_matches
        };
        if let Some(best) = pick_best_candidate(&suffix_filtered, &declaration_file) {
            decl.host_function = Some(best.clone());
            return;
        }
    }

    // Strategy B: same-file lookup for exposed_name as a standalone function.
    // The declaration file for pybind11 is always a C++ file, so same-file
    // lookup inherently returns C++ functions.
    if let Some(fref) = try_same_file_lookup(exposed, &declaration_file, index) {
        decl.host_function = Some(fref.clone());
        return;
    }

    // Strategy C: simple name lookup with proximity (conservative for synthesized lookups).
    // Filter to host language files to avoid cross-language false positives.
    let candidates = index.lookup(exposed);
    let cpp_candidates: Vec<&FunctionRef> = if require_cpp {
        candidates
            .iter()
            .filter(|c| is_cpp_file(&c.file))
            .copied()
            .collect()
    } else {
        candidates.iter().copied().collect()
    };

    if cpp_candidates.len() == 1 {
        decl.host_function = Some(cpp_candidates[0].clone());
        return;
    }
    if cpp_candidates.len() > 1 {
        // For synthesized lookups, only accept same-directory matches to avoid
        // false positives from unrelated functions with the same name.
        let decl_dir = parent_dir(&declaration_file);
        if let Some(dd) = decl_dir {
            let same_dir: Vec<_> = cpp_candidates
                .iter()
                .filter(|c| parent_dir(&c.file) == Some(dd))
                .copied()
                .collect();
            if same_dir.len() == 1 {
                decl.host_function = Some(same_dir[0].clone());
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Target function resolution
// ---------------------------------------------------------------------------

/// Try to resolve target_function for Import-direction bindings.
fn resolve_target_function(decl: &mut BindingDeclaration, index: &FunctionIndex) {
    if let Some(ref target) = decl.target_function {
        if !target.file.is_empty() {
            return;
        }

        let raw_name = target.name.clone();
        let normalized = normalize_cpp_name(&raw_name);
        let declaration_file = &decl.declaration_file;

        // Try qualified name if present
        if let Some(ref qname) = target.qualified_name {
            if let Some(fref) = try_qualified_lookup(qname, declaration_file, index) {
                decl.target_function = Some(fref.clone());
                return;
            }
        }

        // Try same-file lookup
        if let Some(fref) = try_same_file_lookup(&normalized, declaration_file, index) {
            decl.target_function = Some(fref.clone());
            return;
        }

        // Try simple name with disambiguation
        let candidates = index.lookup(&normalized);
        if candidates.len() == 1 {
            decl.target_function = Some(candidates[0].clone());
            return;
        }
        if candidates.len() > 1 {
            if let Some(best) = pick_best_candidate(&candidates, declaration_file) {
                decl.target_function = Some(best.clone());
                return;
            }
        }

        // Try raw name if different from normalized
        if normalized != raw_name {
            let candidates = index.lookup(&raw_name);
            if candidates.len() == 1 {
                decl.target_function = Some(candidates[0].clone());
            } else if candidates.len() > 1 {
                if let Some(best) = pick_best_candidate(&candidates, declaration_file) {
                    decl.target_function = Some(best.clone());
                }
            }
        }
        return;
    }

    // No target_function at all -- try to populate from exposed_name
    let declaration_file = decl.declaration_file.clone();

    if decl.direction == BindingDirection::Import {
        if let Some(fref) = try_same_file_lookup(&decl.exposed_name, &declaration_file, index) {
            decl.target_function = Some(fref.clone());
            return;
        }

        let candidates = index.lookup(&decl.exposed_name);
        if candidates.len() == 1 {
            decl.target_function = Some(candidates[0].clone());
        } else if candidates.len() > 1 {
            if let Some(best) = pick_best_candidate(&candidates, &declaration_file) {
                decl.target_function = Some(best.clone());
            }
        }
    }

    // For JNI: try Java_pkg_Class_method naming
    if decl.system == BindingSystem::Jni && decl.direction == BindingDirection::Import {
        if decl.target_function.is_some() {
            return;
        }
        if let Some(ref class) = decl.class_name {
            let jni_name = format!(
                "Java_{}_{}",
                class.replace('.', "_"),
                decl.exposed_name
            );

            if let Some(fref) = try_same_file_lookup(&jni_name, &declaration_file, index) {
                decl.target_function = Some(fref.clone());
                return;
            }

            let candidates = index.lookup(&jni_name);
            if candidates.len() == 1 {
                decl.target_function = Some(candidates[0].clone());
            } else if candidates.len() > 1 {
                if let Some(best) = pick_best_candidate(&candidates, &declaration_file) {
                    decl.target_function = Some(best.clone());
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normalize_cpp_name() {
        assert_eq!(normalize_cpp_name("&foo"), "foo");
        assert_eq!(normalize_cpp_name("  &Bar::baz  "), "Bar::baz");
        assert_eq!(normalize_cpp_name("&Cls<int>::method"), "Cls::method");
        assert_eq!(normalize_cpp_name("func<T, U>"), "func");
        assert_eq!(normalize_cpp_name("ns::Cls<A<B>>::m"), "ns::Cls::m");
        // Leading :: (global scope qualifier) should be stripped
        assert_eq!(normalize_cpp_name("::c10d::ReduceOp::op_"), "c10d::ReduceOp::op_");
        assert_eq!(normalize_cpp_name("::foo"), "foo");
    }

    #[test]
    fn test_is_dunder() {
        assert!(is_dunder("__init__"));
        assert!(is_dunder("__repr__"));
        assert!(is_dunder("__getitem__"));
        assert!(!is_dunder("__"));     // too short
        assert!(!is_dunder("___"));    // too short
        assert!(!is_dunder("____"));   // exactly 4 chars, need > 4
        assert!(!is_dunder("_init_")); // doesn't start with __
        assert!(!is_dunder("normal_name"));
    }

    #[test]
    fn test_shared_path_depth() {
        assert_eq!(shared_path_depth("/a/b/c/d.cpp", "/a/b/c/e.cpp"), 4); // /, a, b, c
        assert_eq!(shared_path_depth("/a/b/c.cpp", "/x/y/z.cpp"), 1);     // just /
        assert_eq!(shared_path_depth("/a/b/c.cpp", "/a/b/d.cpp"), 3);     // /, a, b
        assert_eq!(shared_path_depth("a/b/c.cpp", "a/b/d.cpp"), 2);       // a, b
    }

    #[test]
    fn test_strip_template_params() {
        assert_eq!(strip_template_params("foo<int>"), "foo");
        assert_eq!(strip_template_params("A<B<C>>"), "A");
        assert_eq!(strip_template_params("no_template"), "no_template");
        assert_eq!(strip_template_params("X<T>::Y<U>"), "X::Y");
    }

    #[test]
    fn test_split_cpp_qualified() {
        let (parts, leaf) = split_cpp_qualified("at::native::add");
        assert_eq!(parts, vec!["at", "native"]);
        assert_eq!(leaf, "add");

        let (parts, leaf) = split_cpp_qualified("add");
        assert!(parts.is_empty());
        assert_eq!(leaf, "add");

        let (parts, leaf) = split_cpp_qualified("Class::method");
        assert_eq!(parts, vec!["Class"]);
        assert_eq!(leaf, "method");
    }

    #[test]
    fn test_pick_best_candidate_same_file() {
        let a = FunctionRef {
            file: "/project/src/foo.cpp".to_string(),
            name: "func".to_string(),
            qualified_name: None,
        };
        let b = FunctionRef {
            file: "/project/src/bar.cpp".to_string(),
            name: "func".to_string(),
            qualified_name: None,
        };
        let candidates = vec![&a, &b];
        let best = pick_best_candidate(&candidates, "/project/src/foo.cpp");
        assert_eq!(best.unwrap().file, "/project/src/foo.cpp");
    }

    #[test]
    fn test_pick_best_candidate_same_dir() {
        let a = FunctionRef {
            file: "/project/src/dir1/foo.cpp".to_string(),
            name: "func".to_string(),
            qualified_name: None,
        };
        let b = FunctionRef {
            file: "/project/src/dir2/bar.cpp".to_string(),
            name: "func".to_string(),
            qualified_name: None,
        };
        let candidates = vec![&a, &b];
        let best = pick_best_candidate(&candidates, "/project/src/dir1/other.cpp");
        assert_eq!(best.unwrap().file, "/project/src/dir1/foo.cpp");
    }

    #[test]
    fn test_pick_best_candidate_shortest() {
        let a = FunctionRef {
            file: "/very/long/path/to/deeply/nested/foo.cpp".to_string(),
            name: "func".to_string(),
            qualified_name: None,
        };
        let b = FunctionRef {
            file: "/short/bar.cpp".to_string(),
            name: "func".to_string(),
            qualified_name: None,
        };
        let candidates = vec![&a, &b];
        let best = pick_best_candidate(&candidates, "/other/dir/baz.cpp");
        assert_eq!(best.unwrap().file, "/short/bar.cpp");
    }

    #[test]
    fn test_pick_best_candidate_empty() {
        let candidates: Vec<&FunctionRef> = vec![];
        assert!(pick_best_candidate(&candidates, "/any.cpp").is_none());
    }

    #[test]
    fn test_pick_best_candidate_single() {
        let a = FunctionRef {
            file: "/a.cpp".to_string(),
            name: "f".to_string(),
            qualified_name: None,
        };
        let candidates = vec![&a];
        assert!(pick_best_candidate(&candidates, "/other.cpp").is_some());
    }

    #[test]
    fn test_looks_like_cpp_function_name() {
        // Valid function names
        assert!(looks_like_cpp_function_name("get_value"));
        assert!(looks_like_cpp_function_name("prepare_for_backward"));
        assert!(looks_like_cpp_function_name("torchVitalEnabled")); // camelCase
        assert!(looks_like_cpp_function_name("MyClass::method")); // qualified
        assert!(looks_like_cpp_function_name("SomeFunc_v2")); // uppercase start but has underscore

        // Rejected: enum-like uppercase constants
        assert!(!looks_like_cpp_function_name("CUDA"));
        assert!(!looks_like_cpp_function_name("MPS"));
        assert!(!looks_like_cpp_function_name("IPU"));
        assert!(!looks_like_cpp_function_name("CPU"));

        // Rejected: type-like names (uppercase start, no underscore, no camelCase)
        assert!(!looks_like_cpp_function_name("Metal"));
        assert!(!looks_like_cpp_function_name("Lazy"));

        // Rejected: operators and empty
        assert!(!looks_like_cpp_function_name(""));
        assert!(!looks_like_cpp_function_name("x"));
        assert!(!looks_like_cpp_function_name("operator+"));

        // Edge: CamelCase with lowercase transition should pass
        assert!(looks_like_cpp_function_name("getValue"));
        assert!(looks_like_cpp_function_name("ProcessGroup"));
    }
}
