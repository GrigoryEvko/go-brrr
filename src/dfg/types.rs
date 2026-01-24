//! DFG type definitions.

use nohash_hasher::IntMap;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use std::sync::OnceLock;

/// Kind of data flow.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DataflowKind {
    /// Variable is defined
    Definition,
    /// Variable is read
    Use,
    /// Variable is mutated
    Mutation,
    /// Value is returned
    Return,
    /// Function parameter
    Param,
    /// Value is yielded from generator
    Yield,
    /// Comprehension-scoped variable (does not leak to outer scope in Python 3)
    ComprehensionVar,
    /// Lambda parameter (scoped to lambda body)
    LambdaParam,
    /// BUG-017 FIX: Variable declared as global (references module-level scope)
    Global,
    /// BUG-017 FIX: Variable declared as nonlocal (references enclosing function scope)
    Nonlocal,
    /// Nested function parameter (scoped to nested function body, used for closure analysis)
    NestedParam,
    /// Closure capture: use of outer variable from within nested function
    ClosureCapture,
    /// Go: Variable captured/used in goroutine (go func() {...})
    Goroutine,
    /// Go: Channel send operation (ch <- val)
    ChannelSend,
    /// Go: Channel receive operation (val := <-ch)
    ChannelReceive,
    /// Go: Deferred call (defer f())
    Defer,
    /// Go: Type assertion (x.(Type))
    TypeAssertion,
    // =========================================================================
    // Go: Panic/Recover/Error handling flow
    // =========================================================================
    /// Go: Panic call (panic(err))
    Panic,
    /// Go: Recover call in deferred function (recover())
    Recover,
    /// Go: Error value assigned (err := ...)
    ErrorAssign,
    /// Go: Error check (if err != nil)
    ErrorCheck,
    /// Go: Named return value modified in defer
    NamedReturnModify,
    // =========================================================================
    // Go: Channel and sync primitive operations
    // =========================================================================
    /// Go: Channel creation (make(chan T) or make(chan T, size))
    ChannelMake,
    /// Go: Channel close operation (close(ch))
    ChannelCloseDfg,
    /// Go: Select statement receive (case val := <-ch:)
    SelectReceive,
    /// Go: Select statement send (case ch <- val:)
    SelectSend,
    /// Go: Mutex lock (mu.Lock() or mu.RLock())
    MutexLock,
    /// Go: Mutex unlock (mu.Unlock() or mu.RUnlock())
    MutexUnlock,
    /// Go: WaitGroup.Add() operation
    WaitGroupAdd,
    /// Go: WaitGroup.Done() operation
    WaitGroupDone,
    /// Go: WaitGroup.Wait() synchronization point
    WaitGroupWait,
    /// Go: sync.Once.Do() call
    OnceDo,
    /// Go: Context.Done() check for cancellation
    ContextDone,
    /// Go: Context.Err() check for cancellation reason
    ContextErr,
    /// Go: Context.Value() retrieval
    ContextValue,
    /// Go: sync.Pool.Get()
    PoolGet,
    /// Go: sync.Pool.Put()
    PoolPut,
}

/// A single data flow edge.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataflowEdge {
    /// Variable name
    pub variable: String,
    /// Source line (where data comes from)
    pub from_line: usize,
    /// Target line (where data flows to)
    pub to_line: usize,
    /// Kind of data flow
    pub kind: DataflowKind,
}

/// Cached adjacency lists for efficient graph traversal.
///
/// Pre-computed once on first access, then reused for all subsequent
/// slice operations. This avoids O(E) rebuild per slice call.
///
/// This is an internal implementation detail. Users interact with it through
/// the `DFGInfo::get_adjacency_cache()` method.
#[derive(Debug)]
pub struct AdjacencyCache {
    /// Incoming edges: to_line -> [from_lines]
    /// Used for backward slicing.
    /// Uses `IntMap` for zero-cost hashing on usize keys.
    pub incoming: IntMap<usize, Vec<usize>>,
    /// Outgoing edges: from_line -> [to_lines]
    /// Used for forward slicing.
    /// Uses `IntMap` for zero-cost hashing on usize keys.
    pub outgoing: IntMap<usize, Vec<usize>>,
}

/// Per-variable adjacency cache for variable-filtered slicing.
///
/// Pre-computed once on first variable-filtered slice, then reused.
/// This eliminates O(E) string comparisons per variable-filtered slice call.
///
/// This is an internal implementation detail. Users interact with it through
/// the `DFGInfo::get_variable_adjacency_cache()` method.
#[derive(Debug)]
pub struct VariableAdjacencyCache {
    /// Per-variable incoming edges: variable -> (to_line -> [from_lines])
    /// Used for variable-specific backward slicing.
    /// Uses `FxHashMap` for string keys, `IntMap` for line number keys.
    pub var_incoming: FxHashMap<String, IntMap<usize, Vec<usize>>>,
    /// Per-variable outgoing edges: variable -> (from_line -> [to_lines])
    /// Used for variable-specific forward slicing.
    /// Uses `FxHashMap` for string keys, `IntMap` for line number keys.
    pub var_outgoing: FxHashMap<String, IntMap<usize, Vec<usize>>>,
}

/// Complete data flow graph for a function.
///
/// The DFG tracks variable definitions, uses, and the data flow edges between them.
/// It provides efficient slicing operations through cached adjacency lists that are
/// computed lazily on first access using interior mutability (OnceLock).
///
/// # Performance
///
/// The adjacency cache is built once on first slice operation and reused for all
/// subsequent operations. This amortizes the O(E) cost of building adjacency lists
/// across multiple slice calls, providing up to 15900x speedup for repeated queries.
///
/// Uses `FxHashMap` for string-keyed maps (2-3x faster than std HashMap).
#[derive(Debug, Serialize, Deserialize)]
pub struct DFGInfo {
    /// Function name
    pub function_name: String,
    /// All data flow edges
    pub edges: Vec<DataflowEdge>,
    /// Where each variable is defined
    pub definitions: FxHashMap<String, Vec<usize>>,
    /// Where each variable is used
    pub uses: FxHashMap<String, Vec<usize>>,
    /// Cached adjacency lists for O(1) edge lookups during slicing.
    /// Lazily initialized on first access via `get_adjacency_cache()`.
    #[serde(skip)]
    adjacency_cache: OnceLock<AdjacencyCache>,
    /// Per-variable adjacency cache for variable-filtered slicing.
    /// Lazily initialized on first variable-filtered slice via `get_variable_adjacency_cache()`.
    #[serde(skip)]
    variable_adjacency_cache: OnceLock<VariableAdjacencyCache>,
}

impl Clone for DFGInfo {
    fn clone(&self) -> Self {
        Self {
            function_name: self.function_name.clone(),
            edges: self.edges.clone(),
            definitions: self.definitions.clone(),
            uses: self.uses.clone(),
            // Fresh caches for clone - will be rebuilt on first access if needed
            adjacency_cache: OnceLock::new(),
            variable_adjacency_cache: OnceLock::new(),
        }
    }
}

// Public API methods - used by library consumers for advanced DFG queries
#[allow(dead_code)]
impl DFGInfo {
    /// Create a new DFGInfo with the given data.
    ///
    /// Both adjacency caches are initialized empty and will be lazily built
    /// on first slice operation.
    pub fn new(
        function_name: String,
        edges: Vec<DataflowEdge>,
        definitions: FxHashMap<String, Vec<usize>>,
        uses: FxHashMap<String, Vec<usize>>,
    ) -> Self {
        Self {
            function_name,
            edges,
            definitions,
            uses,
            adjacency_cache: OnceLock::new(),
            variable_adjacency_cache: OnceLock::new(),
        }
    }

    /// Get or lazily build the adjacency cache.
    ///
    /// This method uses interior mutability (OnceLock) to build the cache
    /// exactly once, even when called from multiple threads. The cache is
    /// then reused for all subsequent slice operations.
    ///
    /// # Performance
    ///
    /// - First call: O(E) to build both incoming and outgoing adjacency maps
    /// - Subsequent calls: O(1) to return cached reference
    ///
    /// This provides up to 15900x speedup for repeated slice operations
    /// compared to rebuilding adjacency maps on every call.
    #[inline]
    pub fn get_adjacency_cache(&self) -> &AdjacencyCache {
        self.adjacency_cache.get_or_init(|| {
            let edge_count = self.edges.len();
            let mut incoming: IntMap<usize, Vec<usize>> =
                IntMap::with_capacity_and_hasher(edge_count, nohash_hasher::BuildNoHashHasher::default());
            let mut outgoing: IntMap<usize, Vec<usize>> =
                IntMap::with_capacity_and_hasher(edge_count, nohash_hasher::BuildNoHashHasher::default());

            for edge in &self.edges {
                incoming
                    .entry(edge.to_line)
                    .or_default()
                    .push(edge.from_line);
                outgoing
                    .entry(edge.from_line)
                    .or_default()
                    .push(edge.to_line);
            }

            AdjacencyCache { incoming, outgoing }
        })
    }

    /// Get incoming edges for a line (sources that flow TO this line).
    ///
    /// Returns `None` if no edges flow to this line.
    /// Uses the cached adjacency list for O(1) lookup.
    #[inline]
    pub fn get_incoming(&self, line: usize) -> Option<&Vec<usize>> {
        self.get_adjacency_cache().incoming.get(&line)
    }

    /// Get outgoing edges for a line (targets that this line flows TO).
    ///
    /// Returns `None` if no edges flow from this line.
    /// Uses the cached adjacency list for O(1) lookup.
    #[inline]
    pub fn get_outgoing(&self, line: usize) -> Option<&Vec<usize>> {
        self.get_adjacency_cache().outgoing.get(&line)
    }

    /// Check if the adjacency cache has been built.
    ///
    /// Returns true if `get_adjacency_cache()` has been called at least once.
    #[inline]
    pub fn has_adjacency_cache(&self) -> bool {
        self.adjacency_cache.get().is_some()
    }

    /// Get or lazily build the per-variable adjacency cache.
    ///
    /// This method uses interior mutability (OnceLock) to build the cache
    /// exactly once, even when called from multiple threads. The cache is
    /// then reused for all subsequent variable-filtered slice operations.
    ///
    /// # Performance
    ///
    /// - First call: O(E) to build both incoming and outgoing per-variable adjacency maps
    /// - Subsequent calls: O(1) to return cached reference
    ///
    /// This eliminates repeated O(E) string comparisons when performing
    /// multiple variable-filtered slices on the same DFG.
    #[inline]
    pub fn get_variable_adjacency_cache(&self) -> &VariableAdjacencyCache {
        self.variable_adjacency_cache.get_or_init(|| {
            let mut var_incoming: FxHashMap<String, IntMap<usize, Vec<usize>>> = FxHashMap::default();
            let mut var_outgoing: FxHashMap<String, IntMap<usize, Vec<usize>>> = FxHashMap::default();

            for edge in &self.edges {
                var_incoming
                    .entry(edge.variable.clone())
                    .or_default()
                    .entry(edge.to_line)
                    .or_default()
                    .push(edge.from_line);

                var_outgoing
                    .entry(edge.variable.clone())
                    .or_default()
                    .entry(edge.from_line)
                    .or_default()
                    .push(edge.to_line);
            }

            VariableAdjacencyCache {
                var_incoming,
                var_outgoing,
            }
        })
    }

    /// Get incoming edges for a specific variable at a line.
    ///
    /// Returns the list of source lines that flow data for `variable` TO `line`.
    /// Returns `None` if no edges for this variable flow to this line.
    /// Uses the cached per-variable adjacency list for O(1) lookup.
    ///
    /// # Performance
    /// First call builds the variable cache O(E), subsequent calls are O(1).
    #[inline]
    pub fn get_var_incoming(&self, variable: &str, line: usize) -> Option<&Vec<usize>> {
        self.get_variable_adjacency_cache()
            .var_incoming
            .get(variable)?
            .get(&line)
    }

    /// Get outgoing edges for a specific variable from a line.
    ///
    /// Returns the list of target lines that receive data for `variable` FROM `line`.
    /// Returns `None` if no edges for this variable flow from this line.
    /// Uses the cached per-variable adjacency list for O(1) lookup.
    ///
    /// # Performance
    /// First call builds the variable cache O(E), subsequent calls are O(1).
    #[inline]
    pub fn get_var_outgoing(&self, variable: &str, line: usize) -> Option<&Vec<usize>> {
        self.get_variable_adjacency_cache()
            .var_outgoing
            .get(variable)?
            .get(&line)
    }

    /// Get all lines where a specific variable has incoming edges.
    ///
    /// Returns `None` if the variable has no incoming edges in the DFG.
    #[inline]
    pub fn get_var_incoming_lines(&self, variable: &str) -> Option<&IntMap<usize, Vec<usize>>> {
        self.get_variable_adjacency_cache()
            .var_incoming
            .get(variable)
    }

    /// Get all lines where a specific variable has outgoing edges.
    ///
    /// Returns `None` if the variable has no outgoing edges in the DFG.
    #[inline]
    pub fn get_var_outgoing_lines(&self, variable: &str) -> Option<&IntMap<usize, Vec<usize>>> {
        self.get_variable_adjacency_cache()
            .var_outgoing
            .get(variable)
    }

    /// Check if the per-variable adjacency cache has been built.
    ///
    /// Returns true if `get_variable_adjacency_cache()` has been called at least once.
    #[inline]
    pub fn has_variable_adjacency_cache(&self) -> bool {
        self.variable_adjacency_cache.get().is_some()
    }

    /// Backward slice: find all lines that affect the target line.
    ///
    /// Delegates to the optimized O(V + E) implementation in slice module.
    /// Uses cached adjacency list for efficient BFS traversal.
    #[inline]
    pub fn backward_slice(&self, target_line: usize) -> Vec<usize> {
        crate::dfg::slice::backward_slice_all(self, target_line)
    }

    /// Forward slice: find all lines affected by the source line.
    ///
    /// Delegates to the optimized O(V + E) implementation in slice module.
    /// Uses cached adjacency list for efficient BFS traversal.
    #[inline]
    pub fn forward_slice(&self, source_line: usize) -> Vec<usize> {
        crate::dfg::slice::forward_slice_all(self, source_line)
    }

    /// Get all variables used in the function.
    pub fn variables(&self) -> Vec<&str> {
        let mut vars: Vec<_> = self.definitions.keys().map(|s| s.as_str()).collect();
        vars.sort();
        vars.dedup();
        vars
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Create a test DFG with multiple variables.
    fn create_test_dfg() -> DFGInfo {
        DFGInfo::new(
            "test_func".to_string(),
            vec![
                // x flows: 1 -> 2, 1 -> 4
                DataflowEdge {
                    variable: "x".to_string(),
                    from_line: 1,
                    to_line: 2,
                    kind: DataflowKind::Definition,
                },
                DataflowEdge {
                    variable: "x".to_string(),
                    from_line: 1,
                    to_line: 4,
                    kind: DataflowKind::Use,
                },
                // y flows: 2 -> 3
                DataflowEdge {
                    variable: "y".to_string(),
                    from_line: 2,
                    to_line: 3,
                    kind: DataflowKind::Definition,
                },
                // z flows: 3 -> 4
                DataflowEdge {
                    variable: "z".to_string(),
                    from_line: 3,
                    to_line: 4,
                    kind: DataflowKind::Definition,
                },
            ],
            [
                ("x".to_string(), vec![1]),
                ("y".to_string(), vec![2]),
                ("z".to_string(), vec![3]),
            ]
            .into_iter()
            .collect(),
            [
                ("x".to_string(), vec![2, 4]),
                ("y".to_string(), vec![3]),
                ("z".to_string(), vec![4]),
            ]
            .into_iter()
            .collect(),
        )
    }

    #[test]
    fn test_variable_adjacency_cache_lazy_init() {
        let dfg = create_test_dfg();

        // Cache should not be built initially
        assert!(!dfg.has_variable_adjacency_cache());

        // Trigger cache build
        let _ = dfg.get_variable_adjacency_cache();

        // Cache should now be built
        assert!(dfg.has_variable_adjacency_cache());
    }

    #[test]
    fn test_get_var_incoming() {
        let dfg = create_test_dfg();

        // x at line 2 has incoming from line 1
        let incoming = dfg.get_var_incoming("x", 2);
        assert!(incoming.is_some());
        assert!(incoming.unwrap().contains(&1));

        // x at line 4 has incoming from line 1
        let incoming = dfg.get_var_incoming("x", 4);
        assert!(incoming.is_some());
        assert!(incoming.unwrap().contains(&1));

        // y at line 3 has incoming from line 2
        let incoming = dfg.get_var_incoming("y", 3);
        assert!(incoming.is_some());
        assert!(incoming.unwrap().contains(&2));

        // No x incoming at line 3
        let incoming = dfg.get_var_incoming("x", 3);
        assert!(incoming.is_none());

        // Nonexistent variable
        let incoming = dfg.get_var_incoming("nonexistent", 1);
        assert!(incoming.is_none());
    }

    #[test]
    fn test_get_var_outgoing() {
        let dfg = create_test_dfg();

        // x at line 1 flows to lines 2 and 4
        let outgoing = dfg.get_var_outgoing("x", 1);
        assert!(outgoing.is_some());
        let outgoing = outgoing.unwrap();
        assert!(outgoing.contains(&2));
        assert!(outgoing.contains(&4));

        // y at line 2 flows to line 3
        let outgoing = dfg.get_var_outgoing("y", 2);
        assert!(outgoing.is_some());
        assert!(outgoing.unwrap().contains(&3));

        // No x outgoing from line 3
        let outgoing = dfg.get_var_outgoing("x", 3);
        assert!(outgoing.is_none());

        // Nonexistent variable
        let outgoing = dfg.get_var_outgoing("nonexistent", 1);
        assert!(outgoing.is_none());
    }

    #[test]
    fn test_get_var_incoming_lines() {
        let dfg = create_test_dfg();

        // All incoming edges for x
        let x_incoming = dfg.get_var_incoming_lines("x");
        assert!(x_incoming.is_some());
        let x_incoming = x_incoming.unwrap();

        // x has incoming edges at lines 2 and 4
        assert!(x_incoming.contains_key(&2));
        assert!(x_incoming.contains_key(&4));
        assert!(!x_incoming.contains_key(&1)); // No incoming to line 1

        // Nonexistent variable
        assert!(dfg.get_var_incoming_lines("nonexistent").is_none());
    }

    #[test]
    fn test_get_var_outgoing_lines() {
        let dfg = create_test_dfg();

        // All outgoing edges for x
        let x_outgoing = dfg.get_var_outgoing_lines("x");
        assert!(x_outgoing.is_some());
        let x_outgoing = x_outgoing.unwrap();

        // x has outgoing edge from line 1 only
        assert!(x_outgoing.contains_key(&1));
        assert!(!x_outgoing.contains_key(&2)); // No outgoing from line 2

        // Nonexistent variable
        assert!(dfg.get_var_outgoing_lines("nonexistent").is_none());
    }

    #[test]
    fn test_variable_cache_clone_independent() {
        let dfg = create_test_dfg();

        // Build cache on original
        let _ = dfg.get_variable_adjacency_cache();
        assert!(dfg.has_variable_adjacency_cache());

        // Clone should have fresh cache
        let cloned = dfg.clone();
        assert!(!cloned.has_variable_adjacency_cache());

        // Building cache on clone should work independently
        let _ = cloned.get_variable_adjacency_cache();
        assert!(cloned.has_variable_adjacency_cache());
    }

    #[test]
    fn test_empty_dfg_variable_cache() {
        let dfg = DFGInfo::new("empty".to_string(), vec![], FxHashMap::default(), FxHashMap::default());

        // Should not panic on empty DFG
        let cache = dfg.get_variable_adjacency_cache();
        assert!(cache.var_incoming.is_empty());
        assert!(cache.var_outgoing.is_empty());

        // All lookups should return None
        assert!(dfg.get_var_incoming("x", 1).is_none());
        assert!(dfg.get_var_outgoing("x", 1).is_none());
        assert!(dfg.get_var_incoming_lines("x").is_none());
        assert!(dfg.get_var_outgoing_lines("x").is_none());
    }
}
