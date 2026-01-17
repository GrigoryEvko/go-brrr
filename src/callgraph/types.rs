//! Call graph type definitions.

use serde::{Deserialize, Serialize};
use std::cell::OnceCell;
use std::collections::{HashMap, HashSet, VecDeque};

/// Reference to a function.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FunctionRef {
    /// File containing the function
    pub file: String,
    /// Function name
    pub name: String,
    /// Fully qualified name (e.g., "module.Class.method")
    pub qualified_name: Option<String>,
}

impl FunctionRef {
    /// Check if this ref matches another (by name, ignoring file if empty).
    pub fn matches(&self, other: &FunctionRef) -> bool {
        if !self.file.is_empty() && !other.file.is_empty() && self.file != other.file {
            return false;
        }
        self.name == other.name
    }
}

/// A call edge in the graph.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallEdge {
    /// Calling function
    pub caller: FunctionRef,
    /// Called function
    pub callee: FunctionRef,
    /// Line number of the call
    pub call_line: usize,
}

/// Complete call graph for a project.
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct CallGraph {
    /// All call edges
    pub edges: Vec<CallEdge>,

    /// Index: callee -> callers (who calls this?)
    #[serde(skip)]
    pub callers: HashMap<FunctionRef, HashSet<FunctionRef>>,

    /// Index: caller -> callees (what does this call?)
    #[serde(skip)]
    pub callees: HashMap<FunctionRef, HashSet<FunctionRef>>,

    /// Cached set of all functions (lazily computed on first access)
    #[serde(skip)]
    all_functions_cache: OnceCell<HashSet<FunctionRef>>,
}

impl Clone for CallGraph {
    fn clone(&self) -> Self {
        Self {
            edges: self.edges.clone(),
            callers: self.callers.clone(),
            callees: self.callees.clone(),
            // Clone the cache content if present, otherwise leave empty
            all_functions_cache: self
                .all_functions_cache
                .get()
                .cloned()
                .map(|v| {
                    let cell = OnceCell::new();
                    let _ = cell.set(v);
                    cell
                })
                .unwrap_or_default(),
        }
    }
}

impl CallGraph {
    /// Create a new CallGraph from edges.
    ///
    /// Indexes are not built automatically. Call `build_indexes()` after creation.
    #[must_use]
    pub fn from_edges(edges: Vec<CallEdge>) -> Self {
        Self {
            edges,
            callers: HashMap::new(),
            callees: HashMap::new(),
            all_functions_cache: OnceCell::new(),
        }
    }

    /// Build indexes from edges (call after deserialization).
    pub fn build_indexes(&mut self) {
        self.invalidate_caches();
        self.callers.clear();
        self.callees.clear();

        for edge in &self.edges {
            self.callers
                .entry(edge.callee.clone())
                .or_default()
                .insert(edge.caller.clone());
            self.callees
                .entry(edge.caller.clone())
                .or_default()
                .insert(edge.callee.clone());
        }
    }

    /// Invalidate all caches (call after modifying edges).
    pub fn invalidate_caches(&mut self) {
        self.all_functions_cache.take();
    }

    /// Forward call graph: what does function X call?
    ///
    /// Uses partial matching via `FunctionRef::matches()` to find the source function,
    /// then performs BFS traversal up to the specified depth.
    pub fn get_callees(&self, source: &FunctionRef, depth: usize) -> HashSet<FunctionRef> {
        if depth == 0 {
            return HashSet::new();
        }

        let mut visited: HashSet<FunctionRef> = HashSet::new();
        let mut queue: VecDeque<(FunctionRef, usize)> = VecDeque::new();

        // Find all matching source functions and seed the queue with their direct callees
        for (k, callees) in &self.callees {
            if k.matches(source) {
                for callee in callees {
                    if !visited.contains(callee) {
                        queue.push_back((callee.clone(), 1));
                    }
                }
            }
        }

        while let Some((current, current_depth)) = queue.pop_front() {
            if !visited.insert(current.clone()) {
                continue;
            }

            // Only expand if we haven't reached max depth
            if current_depth < depth {
                if let Some(callees) = self.callees.get(&current) {
                    for callee in callees {
                        if !visited.contains(callee) {
                            queue.push_back((callee.clone(), current_depth + 1));
                        }
                    }
                }
            }
        }

        visited
    }

    /// Get all unique functions in the graph (cached).
    ///
    /// The result is lazily computed on first access and cached for subsequent calls.
    /// The cache is automatically invalidated when `build_indexes()` or
    /// `invalidate_caches()` is called.
    pub fn all_functions(&self) -> &HashSet<FunctionRef> {
        self.all_functions_cache.get_or_init(|| {
            self.edges
                .iter()
                .flat_map(|e| [e.caller.clone(), e.callee.clone()])
                .collect()
        })
    }
}
