//! Cross-file resolution for binding declarations.
//!
//! After per-file detection, each BindingDeclaration may have partial function
//! references (name only, no file). The resolver uses the FunctionIndex to
//! populate full FunctionRef values.

use crate::bindings::types::{BindingDeclaration, BindingDirection, BindingSystem};
use crate::callgraph::indexer::FunctionIndex;

/// Resolve cross-file binding references using the function index.
pub fn resolve_bindings(declarations: &mut [BindingDeclaration], index: &FunctionIndex) {
    for decl in declarations.iter_mut() {
        resolve_host_function(decl, index);
        resolve_target_function(decl, index);
    }
}

/// Try to resolve a partial host_function (name-only) to a full FunctionRef.
fn resolve_host_function(decl: &mut BindingDeclaration, index: &FunctionIndex) {
    let host = match decl.host_function.as_ref() {
        Some(h) if h.file.is_empty() => h,
        _ => return,
    };

    let name = host.name.clone();

    // Try qualified name first
    if let Some(ref qname) = host.qualified_name.clone() {
        if let Some(fref) = index.lookup_qualified(qname) {
            decl.host_function = Some(fref.clone());
            return;
        }
    }

    // Try class::method lookup
    if let Some(ref class) = decl.class_name {
        let candidates = index.lookup_method(class, &name);
        if candidates.len() == 1 {
            decl.host_function = Some(candidates[0].clone());
            return;
        }
    }

    // Try simple name lookup (unique match only)
    let candidates = index.lookup(&name);
    if candidates.len() == 1 {
        decl.host_function = Some(candidates[0].clone());
    }
}

/// Try to resolve target_function for Import-direction bindings.
fn resolve_target_function(decl: &mut BindingDeclaration, index: &FunctionIndex) {
    if decl.target_function.is_some() {
        let target = decl.target_function.as_ref().unwrap();
        if !target.file.is_empty() {
            return;
        }

        let name = target.name.clone();
        let candidates = index.lookup(&name);
        if candidates.len() == 1 {
            decl.target_function = Some(candidates[0].clone());
        }
        return;
    }

    // For Import direction with no target yet, try to find by exposed_name
    if decl.direction == BindingDirection::Import {
        let candidates = index.lookup(&decl.exposed_name);
        if candidates.len() == 1 {
            decl.target_function = Some(candidates[0].clone());
        }
    }

    // For JNI: try Java_pkg_Class_method naming
    if decl.system == BindingSystem::Jni && decl.direction == BindingDirection::Import {
        if let Some(ref class) = decl.class_name {
            let jni_name = format!("Java_{}_{}", class.replace('.', "_"), decl.exposed_name);
            let candidates = index.lookup(&jni_name);
            if candidates.len() == 1 {
                decl.target_function = Some(candidates[0].clone());
            }
        }
    }
}
