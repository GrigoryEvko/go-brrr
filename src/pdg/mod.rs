//! Program Dependence Graph (PDG) extraction and slicing.
//!
//! A PDG combines control flow (CFG) and data flow (DFG) into a unified graph
//! that enables accurate program slicing. This module provides:
//!
//! - **PDG construction**: Combines CFG and DFG with computed control dependencies
//! - **Accurate slicing**: Follows both control and data dependencies
//!
//! # Why PDG vs DFG-only slicing?
//!
//! Consider this code:
//! ```python
//! def example(x):
//!     if x > 0:        # Line 2 - condition
//!         result = x * 2  # Line 3
//!     return result    # Line 4
//! ```
//!
//! A backward slice from line 4 should include line 2 (the condition) because
//! whether `result` is assigned depends on the condition's outcome.
//!
//! - **DFG-only slice** misses line 2: There's no DATA edge from the condition
//! - **PDG slice** includes line 2: Line 3 is CONTROL-dependent on line 2
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::pdg::{build_pdg, backward_slice, SliceCriteria};
//!
//! let pdg = build_pdg("./src/main.py", "process")?;
//! let criteria = SliceCriteria::at_line(42);
//! let result = backward_slice(&pdg, &criteria);
//! println!("Lines affecting line 42: {:?}", result.lines);
//! ```

pub mod builder;
pub mod types;

// Re-export types
pub use builder::{build_pdg, build_pdg_from_graphs, build_pdg_with_language, PDGBuilder};
pub use types::{BranchType, ControlDependence, PDGInfo};

use std::collections::{HashMap, HashSet, VecDeque};

use crate::error::{Result, BrrrError};

/// Criteria for slicing operations.
#[derive(Debug, Clone)]
pub struct SliceCriteria {
    /// Target line number (1-indexed, matching source code)
    pub line: usize,
    /// Optional: specific variable to track.
    /// When None, all dependencies are followed.
    /// When Some(var), only data edges for that variable are followed
    /// (but all control edges are still followed).
    pub variable: Option<String>,
}

impl SliceCriteria {
    /// Create criteria for a specific line.
    #[inline]
    pub fn at_line(line: usize) -> Self {
        Self {
            line,
            variable: None,
        }
    }

    /// Create criteria for a specific line and variable.
    #[inline]
    pub fn at_line_variable(line: usize, variable: impl Into<String>) -> Self {
        Self {
            line,
            variable: Some(variable.into()),
        }
    }
}

/// Result of a program slice computation.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SliceResult {
    /// Function name where slicing was performed.
    pub function_name: String,

    /// Target/source line of the slice criterion.
    pub target_line: usize,

    /// Direction of the slice ("backward" or "forward").
    pub direction: String,

    /// Lines in the slice (sorted ascending).
    pub lines: Vec<usize>,

    /// Variables involved in the slice.
    pub variables: Vec<String>,

    /// If slicing was restricted to a specific variable.
    pub variable_filter: Option<String>,

    /// Metrics about the slice computation.
    pub metrics: SliceMetrics,
}

/// Metrics about a computed slice.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SliceMetrics {
    /// Total number of lines in the slice.
    pub slice_size: usize,

    /// Number of data flow edges traversed.
    pub data_edges_traversed: usize,

    /// Number of control dependencies traversed.
    pub control_deps_traversed: usize,

    /// Slice ratio: slice_size / total_function_lines.
    pub slice_ratio: f64,

    /// Number of unique variables in the slice.
    pub variable_count: usize,
}

impl SliceResult {
    /// Check if a specific line is in the slice.
    #[inline]
    pub fn contains_line(&self, line: usize) -> bool {
        self.lines.binary_search(&line).is_ok()
    }

    /// Get the line range covered by the slice.
    pub fn line_range(&self) -> Option<(usize, usize)> {
        if self.lines.is_empty() {
            None
        } else {
            Some((self.lines[0], *self.lines.last().unwrap()))
        }
    }

    /// Check if the slice is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.lines.is_empty()
    }
}

/// Compute a backward slice using both control AND data dependencies.
///
/// Starting from the slicing criterion (target line), traces backward through:
/// 1. Data flow edges (def-use chains)
/// 2. Control dependencies (condition -> dependent statements)
///
/// This is the key difference from DFG-only slicing: control dependencies ensure
/// that conditions affecting whether a statement executes are included.
///
/// # Arguments
/// * `pdg` - Program dependence graph to slice
/// * `criteria` - Slicing criteria (line and optional variable filter)
///
/// # Returns
/// `SliceResult` containing affected lines and metadata.
pub fn backward_slice(pdg: &PDGInfo, criteria: &SliceCriteria) -> SliceResult {
    let (lines, data_edges, control_deps) = if let Some(ref var) = criteria.variable {
        backward_slice_variable_impl(pdg, criteria.line, var)
    } else {
        backward_slice_all_impl(pdg, criteria.line)
    };

    // Collect variables involved in the slice
    let variables = collect_slice_variables(pdg, &lines);

    // Compute function line range for ratio
    let total_lines = compute_function_line_range(pdg).map(|(min, max)| max.saturating_sub(min).saturating_add(1)).unwrap_or(1);

    let metrics = SliceMetrics {
        slice_size: lines.len(),
        data_edges_traversed: data_edges,
        control_deps_traversed: control_deps,
        slice_ratio: lines.len() as f64 / total_lines as f64,
        variable_count: variables.len(),
    };

    SliceResult {
        function_name: pdg.function_name.clone(),
        target_line: criteria.line,
        direction: "backward".to_string(),
        lines,
        variables,
        variable_filter: criteria.variable.clone(),
        metrics,
    }
}

/// Compute a forward slice using both control AND data dependencies.
///
/// Starting from the slicing criterion (source line), traces forward through:
/// 1. Data flow edges (use-def chains)
/// 2. Control dependencies (for conditions: what statements they control)
///
/// # Arguments
/// * `pdg` - Program dependence graph to slice
/// * `criteria` - Slicing criteria (line and optional variable filter)
///
/// # Returns
/// `SliceResult` containing affected lines and metadata.
pub fn forward_slice(pdg: &PDGInfo, criteria: &SliceCriteria) -> SliceResult {
    let (lines, data_edges, control_deps) = if let Some(ref var) = criteria.variable {
        forward_slice_variable_impl(pdg, criteria.line, var)
    } else {
        forward_slice_all_impl(pdg, criteria.line)
    };

    // Collect variables involved in the slice
    let variables = collect_slice_variables(pdg, &lines);

    // Compute function line range for ratio
    let total_lines = compute_function_line_range(pdg).map(|(min, max)| max.saturating_sub(min).saturating_add(1)).unwrap_or(1);

    let metrics = SliceMetrics {
        slice_size: lines.len(),
        data_edges_traversed: data_edges,
        control_deps_traversed: control_deps,
        slice_ratio: lines.len() as f64 / total_lines as f64,
        variable_count: variables.len(),
    };

    SliceResult {
        function_name: pdg.function_name.clone(),
        target_line: criteria.line,
        direction: "forward".to_string(),
        lines,
        variables,
        variable_filter: criteria.variable.clone(),
        metrics,
    }
}

/// Compute bidirectional slice (both backward and forward from a line).
pub fn bidirectional_slice(pdg: &PDGInfo, criteria: &SliceCriteria) -> (SliceResult, SliceResult) {
    let backward = backward_slice(pdg, criteria);
    let forward = forward_slice(pdg, criteria);
    (backward, forward)
}

/// Compute the chop between two lines.
///
/// A chop(source, target) contains all statements that can be
/// on a path from source to target.
///
/// # Algorithm
/// Chop = Forward_slice(source) INTERSECT Backward_slice(target)
pub fn chop(pdg: &PDGInfo, source_line: usize, target_line: usize) -> Vec<usize> {
    let (forward_lines, _, _) = forward_slice_all_impl(pdg, source_line);
    let forward_set: HashSet<usize> = forward_lines.into_iter().collect();

    let (backward_lines, _, _) = backward_slice_all_impl(pdg, target_line);
    let backward_set: HashSet<usize> = backward_lines.into_iter().collect();

    let mut result: Vec<usize> = forward_set.intersection(&backward_set).copied().collect();
    result.sort_unstable();
    result
}

// =============================================================================
// Internal Implementation Functions
// =============================================================================

/// Backward slice without variable filtering.
/// Returns (lines, data_edges_traversed, control_deps_traversed)
fn backward_slice_all_impl(pdg: &PDGInfo, target_line: usize) -> (Vec<usize>, usize, usize) {
    // Build reverse adjacency for data flow: to_line -> [from_line]
    let mut data_incoming: HashMap<usize, Vec<usize>> = HashMap::new();
    for edge in &pdg.dfg.edges {
        data_incoming
            .entry(edge.to_line)
            .or_default()
            .push(edge.from_line);
    }

    // Build reverse adjacency for control deps: dependent_line -> [condition_line]
    let mut control_incoming: HashMap<usize, Vec<usize>> = HashMap::new();
    for dep in &pdg.control_deps {
        control_incoming
            .entry(dep.dependent_line)
            .or_default()
            .push(dep.condition_line);
    }

    // BFS backward through both data and control dependencies
    let mut result = HashSet::new();
    let mut frontier = VecDeque::new();
    frontier.push_back(target_line);

    let mut data_edges_traversed = 0;
    let mut control_deps_traversed = 0;

    while let Some(line) = frontier.pop_front() {
        if result.insert(line) {
            // Follow data flow edges backward
            if let Some(sources) = data_incoming.get(&line) {
                for &source in sources {
                    if !result.contains(&source) {
                        frontier.push_back(source);
                        data_edges_traversed += 1;
                    }
                }
            }

            // Follow control dependencies backward
            if let Some(conditions) = control_incoming.get(&line) {
                for &condition in conditions {
                    if !result.contains(&condition) {
                        frontier.push_back(condition);
                        control_deps_traversed += 1;
                    }
                }
            }
        }
    }

    let mut lines: Vec<_> = result.into_iter().collect();
    lines.sort_unstable();
    (lines, data_edges_traversed, control_deps_traversed)
}

/// Backward slice for a specific variable.
/// Still follows all control dependencies (they're not variable-specific).
fn backward_slice_variable_impl(
    pdg: &PDGInfo,
    target_line: usize,
    variable: &str,
) -> (Vec<usize>, usize, usize) {
    // Build reverse adjacency for data flow (filtered by variable)
    let mut data_incoming: HashMap<usize, Vec<usize>> = HashMap::new();
    for edge in &pdg.dfg.edges {
        if edge.variable == variable {
            data_incoming
                .entry(edge.to_line)
                .or_default()
                .push(edge.from_line);
        }
    }

    // Build reverse adjacency for control deps (not filtered - control deps are universal)
    let mut control_incoming: HashMap<usize, Vec<usize>> = HashMap::new();
    for dep in &pdg.control_deps {
        control_incoming
            .entry(dep.dependent_line)
            .or_default()
            .push(dep.condition_line);
    }

    // BFS backward
    let mut result = HashSet::new();
    let mut frontier = VecDeque::new();
    frontier.push_back(target_line);

    let mut data_edges_traversed = 0;
    let mut control_deps_traversed = 0;

    while let Some(line) = frontier.pop_front() {
        if result.insert(line) {
            // Follow variable-specific data flow edges
            if let Some(sources) = data_incoming.get(&line) {
                for &source in sources {
                    if !result.contains(&source) {
                        frontier.push_back(source);
                        data_edges_traversed += 1;
                    }
                }
            }

            // Follow all control dependencies
            if let Some(conditions) = control_incoming.get(&line) {
                for &condition in conditions {
                    if !result.contains(&condition) {
                        frontier.push_back(condition);
                        control_deps_traversed += 1;
                    }
                }
            }
        }
    }

    let mut lines: Vec<_> = result.into_iter().collect();
    lines.sort_unstable();
    (lines, data_edges_traversed, control_deps_traversed)
}

/// Forward slice without variable filtering.
fn forward_slice_all_impl(pdg: &PDGInfo, source_line: usize) -> (Vec<usize>, usize, usize) {
    // Build forward adjacency for data flow: from_line -> [to_line]
    let mut data_outgoing: HashMap<usize, Vec<usize>> = HashMap::new();
    for edge in &pdg.dfg.edges {
        data_outgoing
            .entry(edge.from_line)
            .or_default()
            .push(edge.to_line);
    }

    // Build forward adjacency for control deps: condition_line -> [dependent_line]
    let mut control_outgoing: HashMap<usize, Vec<usize>> = HashMap::new();
    for dep in &pdg.control_deps {
        control_outgoing
            .entry(dep.condition_line)
            .or_default()
            .push(dep.dependent_line);
    }

    // BFS forward
    let mut result = HashSet::new();
    let mut frontier = VecDeque::new();
    frontier.push_back(source_line);

    let mut data_edges_traversed = 0;
    let mut control_deps_traversed = 0;

    while let Some(line) = frontier.pop_front() {
        if result.insert(line) {
            // Follow data flow edges forward
            if let Some(targets) = data_outgoing.get(&line) {
                for &target in targets {
                    if !result.contains(&target) {
                        frontier.push_back(target);
                        data_edges_traversed += 1;
                    }
                }
            }

            // Follow control dependencies forward
            if let Some(dependents) = control_outgoing.get(&line) {
                for &dependent in dependents {
                    if !result.contains(&dependent) {
                        frontier.push_back(dependent);
                        control_deps_traversed += 1;
                    }
                }
            }
        }
    }

    let mut lines: Vec<_> = result.into_iter().collect();
    lines.sort_unstable();
    (lines, data_edges_traversed, control_deps_traversed)
}

/// Forward slice for a specific variable.
fn forward_slice_variable_impl(
    pdg: &PDGInfo,
    source_line: usize,
    variable: &str,
) -> (Vec<usize>, usize, usize) {
    // Build forward adjacency for data flow (filtered by variable)
    let mut data_outgoing: HashMap<usize, Vec<usize>> = HashMap::new();
    for edge in &pdg.dfg.edges {
        if edge.variable == variable {
            data_outgoing
                .entry(edge.from_line)
                .or_default()
                .push(edge.to_line);
        }
    }

    // Build forward adjacency for control deps (not filtered)
    let mut control_outgoing: HashMap<usize, Vec<usize>> = HashMap::new();
    for dep in &pdg.control_deps {
        control_outgoing
            .entry(dep.condition_line)
            .or_default()
            .push(dep.dependent_line);
    }

    // BFS forward
    let mut result = HashSet::new();
    let mut frontier = VecDeque::new();
    frontier.push_back(source_line);

    let mut data_edges_traversed = 0;
    let mut control_deps_traversed = 0;

    while let Some(line) = frontier.pop_front() {
        if result.insert(line) {
            // Follow variable-specific data flow edges
            if let Some(targets) = data_outgoing.get(&line) {
                for &target in targets {
                    if !result.contains(&target) {
                        frontier.push_back(target);
                        data_edges_traversed += 1;
                    }
                }
            }

            // Follow all control dependencies
            if let Some(dependents) = control_outgoing.get(&line) {
                for &dependent in dependents {
                    if !result.contains(&dependent) {
                        frontier.push_back(dependent);
                        control_deps_traversed += 1;
                    }
                }
            }
        }
    }

    let mut lines: Vec<_> = result.into_iter().collect();
    lines.sort_unstable();
    (lines, data_edges_traversed, control_deps_traversed)
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Collect all variables involved in edges touching the given lines.
fn collect_slice_variables(pdg: &PDGInfo, lines: &[usize]) -> Vec<String> {
    let line_set: HashSet<usize> = lines.iter().copied().collect();

    let mut variables: HashSet<&str> = HashSet::new();
    for edge in &pdg.dfg.edges {
        if line_set.contains(&edge.from_line) || line_set.contains(&edge.to_line) {
            variables.insert(&edge.variable);
        }
    }

    let mut result: Vec<String> = variables.into_iter().map(String::from).collect();
    result.sort_unstable();
    result
}

/// Compute the line range covered by the PDG.
fn compute_function_line_range(pdg: &PDGInfo) -> Option<(usize, usize)> {
    let mut min_line = usize::MAX;
    let mut max_line = 0;

    // Check CFG blocks
    for block in pdg.cfg.blocks.values() {
        min_line = min_line.min(block.start_line);
        max_line = max_line.max(block.end_line);
    }

    // Check DFG edges
    for edge in &pdg.dfg.edges {
        min_line = min_line.min(edge.from_line).min(edge.to_line);
        max_line = max_line.max(edge.from_line).max(edge.to_line);
    }

    if min_line <= max_line {
        Some((min_line, max_line))
    } else {
        None
    }
}

// =============================================================================
// High-Level API Functions
// =============================================================================

/// Extract PDG and compute backward slice for a file/function/line.
///
/// This is the recommended function for accurate slicing that includes
/// control dependencies.
///
/// # Arguments
/// * `file` - Path to the source file
/// * `function` - Name of the function containing the line
/// * `line` - Target line number (1-indexed)
///
/// # Returns
/// Sorted vector of line numbers that affect the target line.
///
/// # Errors
/// Returns [`BrrrError::InvalidArgument`] if line is 0 (lines are 1-indexed).
pub fn get_slice(file: &str, function: &str, line: usize) -> Result<Vec<usize>> {
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }
    get_slice_with_language(file, function, line, None)
}

/// Extract PDG and compute backward slice with explicit language specification.
///
/// # Errors
/// Returns [`BrrrError::InvalidArgument`] if line is 0 (lines are 1-indexed).
pub fn get_slice_with_language(
    file: &str,
    function: &str,
    line: usize,
    language: Option<&str>,
) -> Result<Vec<usize>> {
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }
    let pdg = build_pdg_with_language(file, function, language)?;
    let (lines, _, _) = backward_slice_all_impl(&pdg, line);
    Ok(lines)
}

/// Get backward slice with full result metadata.
///
/// # Errors
/// Returns [`BrrrError::InvalidArgument`] if line is 0 (lines are 1-indexed).
pub fn get_slice_result(file: &str, function: &str, line: usize) -> Result<SliceResult> {
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }
    let pdg = build_pdg(file, function)?;
    let criteria = SliceCriteria::at_line(line);
    Ok(backward_slice(&pdg, &criteria))
}

/// Get forward slice: what does the given line affect?
///
/// # Errors
/// Returns [`BrrrError::InvalidArgument`] if line is 0 (lines are 1-indexed).
pub fn get_forward_slice(file: &str, function: &str, line: usize) -> Result<Vec<usize>> {
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }
    get_forward_slice_with_language(file, function, line, None)
}

/// Get forward slice with explicit language specification.
///
/// # Errors
/// Returns [`BrrrError::InvalidArgument`] if line is 0 (lines are 1-indexed).
pub fn get_forward_slice_with_language(
    file: &str,
    function: &str,
    line: usize,
    language: Option<&str>,
) -> Result<Vec<usize>> {
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }
    let pdg = build_pdg_with_language(file, function, language)?;
    let (lines, _, _) = forward_slice_all_impl(&pdg, line);
    Ok(lines)
}

/// Get forward slice with full result metadata.
///
/// # Errors
/// Returns [`BrrrError::InvalidArgument`] if line is 0 (lines are 1-indexed).
pub fn get_forward_slice_result(file: &str, function: &str, line: usize) -> Result<SliceResult> {
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }
    let pdg = build_pdg(file, function)?;
    let criteria = SliceCriteria::at_line(line);
    Ok(forward_slice(&pdg, &criteria))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::types::{BlockId, BlockType, CFGBlock, CFGEdge, CFGInfo, EdgeType};
    use crate::dfg::types::{DataflowEdge, DataflowKind, DFGInfo};
    use std::collections::HashMap;

    /// Create a test scenario representing:
    /// ```python
    /// def example(x):       # Line 1
    ///     if x > 0:         # Line 2 - CONDITION
    ///         result = x * 2  # Line 3 - TRUE BRANCH
    ///     else:
    ///         result = 0    # Line 5 - FALSE BRANCH
    ///     return result     # Line 6
    /// ```
    fn create_test_pdg() -> PDGInfo {
        // Create CFG
        let mut blocks = HashMap::new();

        blocks.insert(BlockId(0), CFGBlock {
            id: BlockId(0),
            label: "entry".to_string(),
            block_type: BlockType::Entry,
            statements: vec!["def example(x):".to_string()],
            func_calls: vec![],
            start_line: 1,
            end_line: 1,
        });

        blocks.insert(BlockId(1), CFGBlock {
            id: BlockId(1),
            label: "if x > 0".to_string(),
            block_type: BlockType::Branch,
            statements: vec!["if x > 0:".to_string()],
            func_calls: vec![],
            start_line: 2,
            end_line: 2,
        });

        blocks.insert(BlockId(2), CFGBlock {
            id: BlockId(2),
            label: "true branch".to_string(),
            block_type: BlockType::Body,
            statements: vec!["result = x * 2".to_string()],
            func_calls: vec![],
            start_line: 3,
            end_line: 3,
        });

        blocks.insert(BlockId(3), CFGBlock {
            id: BlockId(3),
            label: "false branch".to_string(),
            block_type: BlockType::Body,
            statements: vec!["result = 0".to_string()],
            func_calls: vec![],
            start_line: 5,
            end_line: 5,
        });

        blocks.insert(BlockId(4), CFGBlock {
            id: BlockId(4),
            label: "return".to_string(),
            block_type: BlockType::Return,
            statements: vec!["return result".to_string()],
            func_calls: vec![],
            start_line: 6,
            end_line: 6,
        });

        let cfg = CFGInfo {
            function_name: "example".to_string(),
            blocks,
            edges: vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::new(BlockId(1), BlockId(2), EdgeType::True),
                CFGEdge::new(BlockId(1), BlockId(3), EdgeType::False),
                CFGEdge::unconditional(BlockId(2), BlockId(4)),
                CFGEdge::unconditional(BlockId(3), BlockId(4)),
            ],
            entry: BlockId(0),
            exits: vec![BlockId(4)],
            decision_points: 1,
            comprehension_decision_points: 0,
            nested_cfgs: HashMap::new(),
            is_async: false,
            await_points: 0,
            blocking_calls: Vec::new(),
            ..Default::default()
        };

        // Create DFG
        let dfg = DFGInfo::new(
            "example".to_string(),
            vec![
                // x flows from param (line 1) to use in condition (line 2)
                DataflowEdge {
                    variable: "x".to_string(),
                    from_line: 1,
                    to_line: 2,
                    kind: DataflowKind::Use,
                },
                // x flows from param to true branch
                DataflowEdge {
                    variable: "x".to_string(),
                    from_line: 1,
                    to_line: 3,
                    kind: DataflowKind::Use,
                },
                // result defined at line 3, used at line 6
                DataflowEdge {
                    variable: "result".to_string(),
                    from_line: 3,
                    to_line: 6,
                    kind: DataflowKind::Definition,
                },
                // result defined at line 5, used at line 6
                DataflowEdge {
                    variable: "result".to_string(),
                    from_line: 5,
                    to_line: 6,
                    kind: DataflowKind::Definition,
                },
            ],
            [
                ("x".to_string(), vec![1]),
                ("result".to_string(), vec![3, 5]),
            ]
            .into_iter()
            .collect(),
            [
                ("x".to_string(), vec![2, 3]),
                ("result".to_string(), vec![6]),
            ]
            .into_iter()
            .collect(),
        );

        // Build PDG with control dependencies
        build_pdg_from_graphs(cfg, dfg)
    }

    #[test]
    fn test_backward_slice_includes_condition() {
        let pdg = create_test_pdg();
        let criteria = SliceCriteria::at_line(6); // return result

        let result = backward_slice(&pdg, &criteria);

        // The slice should include:
        // - Line 6 (return result) - the target
        // - Line 3 (result = x * 2) - data dependency (result defined)
        // - Line 5 (result = 0) - data dependency (result defined)
        // - Line 2 (if x > 0) - CONTROL dependency on lines 3 and 5!
        // - Line 1 (param x) - data dependency through x

        assert!(
            result.lines.contains(&6),
            "Slice should contain target line 6"
        );
        assert!(
            result.lines.contains(&3),
            "Slice should contain data dep line 3"
        );
        assert!(
            result.lines.contains(&5),
            "Slice should contain data dep line 5"
        );
        assert!(
            result.lines.contains(&2),
            "BUG FIX: Slice MUST contain condition line 2 (control dependency)!"
        );
        assert!(
            result.lines.contains(&1),
            "Slice should contain param line 1"
        );
    }

    #[test]
    fn test_backward_slice_from_true_branch() {
        let pdg = create_test_pdg();
        let criteria = SliceCriteria::at_line(3); // result = x * 2

        let result = backward_slice(&pdg, &criteria);

        // From line 3, we should get:
        // - Line 3 itself
        // - Line 2 (condition that controls line 3)
        // - Line 1 (x parameter used in line 3)

        assert!(result.lines.contains(&3));
        assert!(
            result.lines.contains(&2),
            "Slice from true branch should include condition line"
        );
        assert!(result.lines.contains(&1));
    }

    #[test]
    fn test_forward_slice_from_condition() {
        let pdg = create_test_pdg();
        let criteria = SliceCriteria::at_line(2); // if x > 0

        let result = forward_slice(&pdg, &criteria);

        // Forward from condition should include:
        // - Line 2 itself
        // - Line 3 (true branch, control-dependent)
        // - Line 5 (false branch, control-dependent)
        // - Line 6 (return, through data dependencies from 3 and 5)

        assert!(result.lines.contains(&2));
        assert!(
            result.lines.contains(&3),
            "Forward slice should include true branch"
        );
        assert!(
            result.lines.contains(&5),
            "Forward slice should include false branch"
        );
    }

    #[test]
    fn test_control_deps_computed() {
        let pdg = create_test_pdg();

        // Line 3 should be control-dependent on line 2
        assert!(
            pdg.is_control_dependent(3, 2),
            "Line 3 should be control-dependent on line 2"
        );

        // Line 5 should be control-dependent on line 2
        assert!(
            pdg.is_control_dependent(5, 2),
            "Line 5 should be control-dependent on line 2"
        );
    }

    #[test]
    fn test_slice_metrics_track_both_types() {
        let pdg = create_test_pdg();
        let criteria = SliceCriteria::at_line(6);

        let result = backward_slice(&pdg, &criteria);

        // Should have traversed both data edges and control deps
        assert!(
            result.metrics.data_edges_traversed > 0 || result.metrics.control_deps_traversed > 0,
            "Slice should have traversed some edges"
        );
    }

    #[test]
    fn test_chop_includes_control_deps() {
        let pdg = create_test_pdg();

        // Chop from param (line 1) to return (line 6) should include condition
        let result = chop(&pdg, 1, 6);

        assert!(result.contains(&2), "Chop should include condition line");
    }

    #[test]
    fn test_dfg_only_slice_would_miss_condition() {
        // This test demonstrates the bug we're fixing:
        // A DFG-only slice from line 6 would NOT include line 2

        let pdg = create_test_pdg();

        // Simulate DFG-only slice by only following data edges
        let mut data_incoming: HashMap<usize, Vec<usize>> = HashMap::new();
        for edge in &pdg.dfg.edges {
            data_incoming
                .entry(edge.to_line)
                .or_default()
                .push(edge.from_line);
        }

        let mut dfg_only_result = HashSet::new();
        let mut frontier = VecDeque::new();
        frontier.push_back(6usize);

        while let Some(line) = frontier.pop_front() {
            if dfg_only_result.insert(line) {
                if let Some(sources) = data_incoming.get(&line) {
                    for &source in sources {
                        if !dfg_only_result.contains(&source) {
                            frontier.push_back(source);
                        }
                    }
                }
            }
        }

        // DFG-only slice misses the condition!
        assert!(
            !dfg_only_result.contains(&2),
            "DFG-only slice correctly does NOT include condition (demonstrating the bug)"
        );

        // But PDG slice includes it
        let criteria = SliceCriteria::at_line(6);
        let pdg_result = backward_slice(&pdg, &criteria);

        assert!(
            pdg_result.lines.contains(&2),
            "PDG slice correctly DOES include condition (the fix)"
        );
    }
}
