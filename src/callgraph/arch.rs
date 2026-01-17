//! Architecture layer detection from call graph patterns.
//!
//! Analyzes function call relationships to identify architectural layers:
//! - Entry points: Functions that initiate call chains (callers but no callees)
//! - Leaf functions: Functions at the bottom of call chains (callees but no callers)
//! - Middle functions: Functions in between (both callers and callees)
//!
//! Also detects circular dependencies which indicate potential architectural issues.

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use super::types::{CallGraph, FunctionRef};

/// Result of architecture analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArchAnalysis {
    /// Functions that call others but are not called (entry points).
    pub entry_functions: Vec<FunctionInfo>,
    /// Functions that are called but don't call others (leaf/utility functions).
    pub leaf_functions: Vec<FunctionInfo>,
    /// Functions that both call and are called (middle layer).
    pub middle_functions: Vec<FunctionInfo>,
    /// Orphan functions that neither call nor are called.
    pub orphan_functions: Vec<FunctionInfo>,
    /// Layered view of the architecture (topological ordering).
    pub layers: Vec<Vec<FunctionInfo>>,
    /// Detected circular dependencies (cycles in call graph).
    pub circular_dependencies: Vec<CycleDependency>,
    /// Statistics about the architecture.
    pub stats: ArchStats,
}

/// Information about a function in the architecture.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionInfo {
    /// File containing the function.
    pub file: String,
    /// Function name.
    pub name: String,
    /// Fully qualified name if available.
    pub qualified_name: Option<String>,
    /// Number of functions this calls.
    pub outgoing_calls: usize,
    /// Number of functions that call this.
    pub incoming_calls: usize,
}

impl From<&FunctionRef> for FunctionInfo {
    fn from(func: &FunctionRef) -> Self {
        FunctionInfo {
            file: func.file.clone(),
            name: func.name.clone(),
            qualified_name: func.qualified_name.clone(),
            outgoing_calls: 0,
            incoming_calls: 0,
        }
    }
}

/// A circular dependency in the call graph.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CycleDependency {
    /// Functions involved in the cycle, in call order.
    pub cycle: Vec<String>,
    /// Files involved in this cycle.
    pub files: Vec<String>,
}

/// Statistics about the architecture.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ArchStats {
    /// Total number of functions analyzed.
    pub total_functions: usize,
    /// Number of entry points.
    pub entry_count: usize,
    /// Number of leaf functions.
    pub leaf_count: usize,
    /// Number of middle layer functions.
    pub middle_count: usize,
    /// Number of orphan functions.
    pub orphan_count: usize,
    /// Number of distinct cycles detected.
    pub cycle_count: usize,
    /// Number of layers in the architecture.
    pub layer_count: usize,
    /// Maximum depth (longest call chain).
    pub max_depth: usize,
}

/// Analyze architecture from a call graph.
///
/// Categorizes functions by their role in the call hierarchy and detects
/// circular dependencies that may indicate architectural problems.
///
/// # Arguments
///
/// * `graph` - The call graph to analyze. Must have indexes built via `build_indexes()`.
///
/// # Returns
///
/// An `ArchAnalysis` containing categorized functions, layers, and cycles.
pub fn analyze_architecture(graph: &CallGraph) -> ArchAnalysis {
    // Collect all unique functions
    let all_functions: HashSet<_> = graph
        .edges
        .iter()
        .flat_map(|e| [e.caller.clone(), e.callee.clone()])
        .collect();

    let mut entry_functions = Vec::new();
    let mut leaf_functions = Vec::new();
    let mut middle_functions = Vec::new();
    let mut orphan_functions = Vec::new();

    // Categorize each function by its call relationships
    for func in &all_functions {
        let has_callers = graph.callers.get(func).map_or(false, |c| !c.is_empty());
        let has_callees = graph.callees.get(func).map_or(false, |c| !c.is_empty());

        let incoming = graph.callers.get(func).map_or(0, |c| c.len());
        let outgoing = graph.callees.get(func).map_or(0, |c| c.len());

        let mut info = FunctionInfo::from(func);
        info.incoming_calls = incoming;
        info.outgoing_calls = outgoing;

        match (has_callers, has_callees) {
            (false, true) => entry_functions.push(info),  // Entry point: calls others, not called
            (true, false) => leaf_functions.push(info),   // Leaf: called, doesn't call others
            (true, true) => middle_functions.push(info),  // Middle: both
            (false, false) => orphan_functions.push(info), // Orphan: neither (shouldn't happen often)
        }
    }

    // Sort by name for consistent output
    entry_functions.sort_by(|a, b| a.name.cmp(&b.name));
    leaf_functions.sort_by(|a, b| a.name.cmp(&b.name));
    middle_functions.sort_by(|a, b| a.name.cmp(&b.name));
    orphan_functions.sort_by(|a, b| a.name.cmp(&b.name));

    // Detect cycles using Tarjan's algorithm
    let circular_dependencies = detect_cycles(graph, &all_functions);

    // Build topological layers (ignoring cycles for layering)
    let layers = build_layers(graph, &all_functions, &circular_dependencies);

    let max_depth = layers.len();

    let stats = ArchStats {
        total_functions: all_functions.len(),
        entry_count: entry_functions.len(),
        leaf_count: leaf_functions.len(),
        middle_count: middle_functions.len(),
        orphan_count: orphan_functions.len(),
        cycle_count: circular_dependencies.len(),
        layer_count: layers.len(),
        max_depth,
    };

    ArchAnalysis {
        entry_functions,
        leaf_functions,
        middle_functions,
        orphan_functions,
        layers,
        circular_dependencies,
        stats,
    }
}

/// Detect cycles in the call graph using iterative DFS with cycle detection.
fn detect_cycles(graph: &CallGraph, all_functions: &HashSet<FunctionRef>) -> Vec<CycleDependency> {
    let mut cycles = Vec::new();
    let mut visited_global = HashSet::new();

    // Create a name-based lookup for simplicity
    let mut name_to_func: HashMap<String, &FunctionRef> = HashMap::new();
    for func in all_functions {
        let key = func.qualified_name.as_deref().unwrap_or(&func.name).to_string();
        name_to_func.insert(key, func);
    }

    // For each unvisited function, do DFS to find cycles
    for start_func in all_functions {
        if visited_global.contains(start_func) {
            continue;
        }

        let mut stack: Vec<(&FunctionRef, Vec<&FunctionRef>)> = vec![(start_func, vec![start_func])];
        let mut in_current_path: HashSet<&FunctionRef> = HashSet::new();
        in_current_path.insert(start_func);

        while let Some((current, path)) = stack.pop() {
            visited_global.insert(current.clone());

            if let Some(callees) = graph.callees.get(current) {
                for callee in callees {
                    // Check if callee is in current path (cycle detected)
                    if path.iter().any(|f| f.name == callee.name) {
                        // Found a cycle - extract the cycle portion
                        let cycle_start_idx = path.iter().position(|f| f.name == callee.name).unwrap();
                        let cycle_funcs: Vec<&FunctionRef> = path[cycle_start_idx..].to_vec();

                        // Only add if we haven't seen this cycle before
                        let cycle_names: Vec<String> = cycle_funcs
                            .iter()
                            .map(|f| f.qualified_name.as_deref().unwrap_or(&f.name).to_string())
                            .collect();

                        let cycle_files: Vec<String> = cycle_funcs
                            .iter()
                            .map(|f| f.file.clone())
                            .collect::<HashSet<_>>()
                            .into_iter()
                            .collect();

                        // Check if we already recorded this cycle (cycles can be found multiple times)
                        let normalized = normalize_cycle(&cycle_names);
                        let already_exists = cycles.iter().any(|c: &CycleDependency| {
                            normalize_cycle(&c.cycle) == normalized
                        });

                        if !already_exists && cycle_names.len() > 1 {
                            cycles.push(CycleDependency {
                                cycle: cycle_names,
                                files: cycle_files,
                            });
                        }
                    } else if !visited_global.contains(callee) {
                        // Continue DFS
                        let mut new_path = path.clone();
                        new_path.push(callee);
                        stack.push((callee, new_path));
                    }
                }
            }
        }
    }

    // Sort cycles by length (shorter cycles are often more problematic)
    cycles.sort_by_key(|c| c.cycle.len());
    cycles
}

/// Normalize a cycle for comparison (rotate to start with lexicographically smallest element).
fn normalize_cycle(cycle: &[String]) -> Vec<String> {
    if cycle.is_empty() {
        return Vec::new();
    }

    // Find the lexicographically smallest element
    let min_idx = cycle
        .iter()
        .enumerate()
        .min_by_key(|(_, name)| *name)
        .map(|(idx, _)| idx)
        .unwrap_or(0);

    // Rotate to start with that element
    let mut normalized = cycle[min_idx..].to_vec();
    normalized.extend_from_slice(&cycle[..min_idx]);
    normalized
}

/// Build topological layers using Kahn's algorithm (BFS-based topological sort).
/// Functions with no incoming edges (entry points) are in layer 0,
/// functions that only depend on layer 0 are in layer 1, etc.
fn build_layers(
    graph: &CallGraph,
    all_functions: &HashSet<FunctionRef>,
    cycles: &[CycleDependency],
) -> Vec<Vec<FunctionInfo>> {
    if all_functions.is_empty() {
        return Vec::new();
    }

    // Collect functions involved in cycles (we'll handle them specially)
    let cycle_functions: HashSet<String> = cycles
        .iter()
        .flat_map(|c| c.cycle.iter().cloned())
        .collect();

    // Build in-degree map (count of incoming edges, excluding cycle edges)
    let mut in_degree: HashMap<&FunctionRef, usize> = HashMap::new();
    let mut func_to_callees: HashMap<&FunctionRef, Vec<&FunctionRef>> = HashMap::new();

    for func in all_functions {
        in_degree.insert(func, 0);
    }

    // Count in-degrees (number of callers for each function)
    for func in all_functions {
        if let Some(callers) = graph.callers.get(func) {
            let count = callers
                .iter()
                .filter(|caller| {
                    // Skip edges that are part of cycles for layering purposes
                    let caller_name = caller.qualified_name.as_deref().unwrap_or(&caller.name);
                    let callee_name = func.qualified_name.as_deref().unwrap_or(&func.name);
                    !(cycle_functions.contains(caller_name) && cycle_functions.contains(callee_name))
                })
                .count();
            in_degree.insert(func, count);
        }

        // Build adjacency list for callees
        if let Some(callees) = graph.callees.get(func) {
            func_to_callees.insert(
                func,
                callees.iter().collect(),
            );
        }
    }

    let mut layers: Vec<Vec<FunctionInfo>> = Vec::new();
    let mut remaining: HashSet<&FunctionRef> = all_functions.iter().collect();

    // BFS-style layering
    while !remaining.is_empty() {
        // Find all functions with in-degree 0 among remaining
        let current_layer: Vec<&FunctionRef> = remaining
            .iter()
            .filter(|f| in_degree.get(*f).copied().unwrap_or(0) == 0)
            .copied()
            .collect();

        if current_layer.is_empty() {
            // All remaining functions have dependencies - they're in cycles
            // Put them all in the last layer
            let cycle_layer: Vec<FunctionInfo> = remaining
                .iter()
                .map(|f| {
                    let incoming = graph.callers.get(*f).map_or(0, |c| c.len());
                    let outgoing = graph.callees.get(*f).map_or(0, |c| c.len());
                    let mut info = FunctionInfo::from(*f);
                    info.incoming_calls = incoming;
                    info.outgoing_calls = outgoing;
                    info
                })
                .collect();

            if !cycle_layer.is_empty() {
                layers.push(cycle_layer);
            }
            break;
        }

        // Add current layer
        let mut layer_info: Vec<FunctionInfo> = current_layer
            .iter()
            .map(|f| {
                let incoming = graph.callers.get(*f).map_or(0, |c| c.len());
                let outgoing = graph.callees.get(*f).map_or(0, |c| c.len());
                let mut info = FunctionInfo::from(*f);
                info.incoming_calls = incoming;
                info.outgoing_calls = outgoing;
                info
            })
            .collect();
        layer_info.sort_by(|a, b| a.name.cmp(&b.name));
        layers.push(layer_info);

        // Remove current layer from remaining and update in-degrees
        for func in &current_layer {
            remaining.remove(func);

            // Decrease in-degree of all functions this one calls
            if let Some(callees) = func_to_callees.get(func) {
                for callee in callees {
                    if let Some(degree) = in_degree.get_mut(callee) {
                        *degree = degree.saturating_sub(1);
                    }
                }
            }
        }
    }

    layers
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::callgraph::types::CallEdge;

    fn make_func(file: &str, name: &str) -> FunctionRef {
        FunctionRef {
            file: file.to_string(),
            name: name.to_string(),
            qualified_name: None,
        }
    }

    fn make_graph(edges: Vec<(&str, &str, &str, &str)>) -> CallGraph {
        let call_edges: Vec<CallEdge> = edges
            .into_iter()
            .map(|(cf, cn, ef, en)| CallEdge {
                caller: make_func(cf, cn),
                callee: make_func(ef, en),
                call_line: 0,
            })
            .collect();
        let mut graph = CallGraph::from_edges(call_edges);
        graph.build_indexes();
        graph
    }

    #[test]
    fn test_categorization() {
        // main -> process -> helper
        let graph = make_graph(vec![
            ("main.rs", "main", "proc.rs", "process"),
            ("proc.rs", "process", "util.rs", "helper"),
        ]);

        let analysis = analyze_architecture(&graph);

        assert_eq!(analysis.entry_functions.len(), 1);
        assert_eq!(analysis.entry_functions[0].name, "main");

        assert_eq!(analysis.leaf_functions.len(), 1);
        assert_eq!(analysis.leaf_functions[0].name, "helper");

        assert_eq!(analysis.middle_functions.len(), 1);
        assert_eq!(analysis.middle_functions[0].name, "process");
    }

    #[test]
    fn test_cycle_detection() {
        // a -> b -> c -> a (cycle)
        let graph = make_graph(vec![
            ("a.rs", "a", "b.rs", "b"),
            ("b.rs", "b", "c.rs", "c"),
            ("c.rs", "c", "a.rs", "a"),
        ]);

        let analysis = analyze_architecture(&graph);

        assert!(!analysis.circular_dependencies.is_empty());
        let cycle = &analysis.circular_dependencies[0];
        assert_eq!(cycle.cycle.len(), 3);
    }

    #[test]
    fn test_layering() {
        // Layer 0: main
        // Layer 1: process
        // Layer 2: helper
        let graph = make_graph(vec![
            ("main.rs", "main", "proc.rs", "process"),
            ("proc.rs", "process", "util.rs", "helper"),
        ]);

        let analysis = analyze_architecture(&graph);

        assert_eq!(analysis.layers.len(), 3);
        assert_eq!(analysis.layers[0][0].name, "main");
        assert_eq!(analysis.layers[1][0].name, "process");
        assert_eq!(analysis.layers[2][0].name, "helper");
    }

    #[test]
    fn test_empty_graph() {
        let graph = CallGraph::default();
        let analysis = analyze_architecture(&graph);

        assert!(analysis.entry_functions.is_empty());
        assert!(analysis.leaf_functions.is_empty());
        assert!(analysis.circular_dependencies.is_empty());
        assert!(analysis.layers.is_empty());
    }
}
