//! Synthetic CallEdge generation for callgraph integration.
//!
//! Converts resolved BindingDeclarations into CallEdge entries that can be
//! injected into the existing call graph.

use crate::bindings::types::{BindingDirection, BindingReport};
use crate::callgraph::types::{CallEdge, CallGraph, FunctionRef};

/// Generate synthetic CallEdges from binding declarations.
pub fn synthetic_edges(report: &BindingReport) -> Vec<CallEdge> {
    let mut edges = Vec::new();

    for decl in &report.declarations {
        match decl.direction {
            BindingDirection::Export => {
                // C++ exposes function to Python via pybind11 etc.
                // Edge: synthetic target-side ref → host implementation.
                // This makes the host function appear "called" so dead code
                // analysis doesn't flag it as unused.
                if let Some(ref host) = decl.host_function {
                    let caller = decl.target_function.clone().unwrap_or_else(|| FunctionRef {
                        file: String::new(),
                        name: decl.exposed_name.clone(),
                        qualified_name: Some(format!(
                            "<binding:{}>::{}",
                            decl.system,
                            decl.exposed_name
                        )),
                    });
                    edges.push(CallEdge {
                        caller,
                        callee: host.clone(),
                        call_line: decl.declaration_line,
                    });
                }
            }
            BindingDirection::Import => {
                // Python calls C via ctypes, Go calls C via CGo, etc.
                // Edge: synthetic caller at declaration site → target C function.
                if let Some(ref target) = decl.target_function {
                    let caller = FunctionRef {
                        file: decl.declaration_file.clone(),
                        name: format!("<{}:import>", decl.system),
                        qualified_name: None,
                    };
                    edges.push(CallEdge {
                        caller,
                        callee: target.clone(),
                        call_line: decl.declaration_line,
                    });
                }
            }
            BindingDirection::Dispatch => {
                // REGISTER_DISPATCH: stub → kernel implementation.
                if let Some(ref host) = decl.host_function {
                    let stub = FunctionRef {
                        file: decl.declaration_file.clone(),
                        name: decl.exposed_name.clone(),
                        qualified_name: Some(decl.exposed_name.clone()),
                    };
                    edges.push(CallEdge {
                        caller: stub,
                        callee: host.clone(),
                        call_line: decl.declaration_line,
                    });
                }
            }
        }
    }

    edges
}

/// Inject binding edges into an existing call graph.
///
/// Appends synthetic edges and rebuilds caller/callee indexes.
pub fn inject_into_graph(graph: &mut CallGraph, report: &BindingReport) {
    let mut new_edges = synthetic_edges(report);
    if new_edges.is_empty() {
        return;
    }
    graph.edges.append(&mut new_edges);
    graph.build_indexes();
}
