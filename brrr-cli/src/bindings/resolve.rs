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

use std::path::Path;

use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::indexer::FunctionIndex;
use crate::callgraph::types::FunctionRef;

/// Resolve cross-file binding references using the function index.
pub fn resolve_bindings(declarations: &mut [BindingDeclaration], index: &FunctionIndex) {
    for decl in declarations.iter_mut() {
        resolve_host_function(decl, index);
        resolve_target_function(decl, index);
    }
}

// ---------------------------------------------------------------------------
// Name normalization
// ---------------------------------------------------------------------------

/// Normalize a C++ function reference name for lookup.
///
/// Strips leading `&`, template parameters `<...>`, and surrounding whitespace.
fn normalize_cpp_name(name: &str) -> String {
    let s = name.trim().trim_start_matches('&').trim();
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

// ---------------------------------------------------------------------------
// Disambiguation: pick the best match from multiple candidates
// ---------------------------------------------------------------------------

/// Pick the best candidate from multiple matches, using file proximity.
///
/// Preference order:
/// 1. Same file as declaration_file
/// 2. Same directory as declaration_file
/// 3. Shortest file path (heuristic: closer to project root = more likely)
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
            return same_dir.into_iter().min_by_key(|c| c.file.len());
        }
    }

    // 3. Shortest file path as tiebreaker
    candidates.iter().min_by_key(|c| c.file.len()).copied()
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
}
