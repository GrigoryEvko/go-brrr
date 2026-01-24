//! PDG (Program Dependence Graph) construction.
//!
//! Builds a PDG by combining CFG and DFG, computing control dependencies
//! from the CFG structure.
//!
//! # Control Dependency Computation
//!
//! A statement S is control-dependent on a predicate P if:
//! 1. There exists a path from P to S where S executes
//! 2. There exists another path from P where S does not execute
//!
//! In practice, we compute this from CFG edges:
//! - For True/False edges: target block lines are control-dependent on source condition
//! - For Loop edges: body lines are control-dependent on loop header
//! - For Exception edges: handler lines are control-dependent on try block

use fixedbitset::FixedBitSet;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::cfg::types::{BlockId, CFGInfo, EdgeType};
use crate::dfg::types::DFGInfo;
use crate::pdg::types::{BranchType, ControlDependence, PDGInfo};

/// Builder for constructing Program Dependence Graphs.
///
/// Combines CFG (control flow) and DFG (data flow) into a unified PDG
/// with computed control dependencies.
pub struct PDGBuilder {
    cfg: CFGInfo,
    dfg: DFGInfo,
    control_deps: Vec<ControlDependence>,

    /// Cache: block ID -> (start_line, end_line)
    block_line_ranges: FxHashMap<BlockId, (usize, usize)>,
}

impl PDGBuilder {
    /// Create a new PDGBuilder from CFG and DFG.
    pub fn new(cfg: CFGInfo, dfg: DFGInfo) -> Self {
        // Pre-compute block line ranges for efficient lookup
        let block_line_ranges: FxHashMap<BlockId, (usize, usize)> = cfg
            .blocks
            .iter()
            .map(|(id, block)| (*id, (block.start_line, block.end_line)))
            .collect();

        Self {
            cfg,
            dfg,
            control_deps: Vec::new(),
            block_line_ranges,
        }
    }

    /// Build the PDG with computed control dependencies.
    pub fn build(mut self) -> PDGInfo {
        self.compute_control_dependencies();
        PDGInfo::new(self.cfg, self.dfg, self.control_deps)
    }

    /// Compute control dependencies from CFG structure.
    ///
    /// For each conditional edge (True/False/Loop/Exception), the target block's
    /// lines are control-dependent on the source block's condition line.
    fn compute_control_dependencies(&mut self) {
        // Track which blocks are in each branch to compute proper control dependencies
        // For now, use the simpler approach: direct edge targets are control-dependent

        // Collect transitive dependency computation requests to avoid borrow conflict
        let mut transitive_deps: Vec<(BlockId, BlockId, usize, BranchType)> = Vec::new();

        for edge in &self.cfg.edges {
            // Skip unconditional edges - they don't create control dependencies
            let branch_type = match edge.edge_type {
                EdgeType::True => BranchType::True,
                EdgeType::False | EdgeType::Else => BranchType::False,
                EdgeType::BackEdge | EdgeType::Loop | EdgeType::Iterate => BranchType::Loop,
                EdgeType::Exception | EdgeType::ExceptionGroup => BranchType::Exception,
                // These edge types also create control dependencies
                EdgeType::Enter | EdgeType::Case | EdgeType::PatternMatch | EdgeType::Match => {
                    BranchType::True // Treat as conditional
                }
                EdgeType::OkSome | EdgeType::ErrNone => BranchType::True, // Rust Result/Option
                EdgeType::Pass | EdgeType::Fail => BranchType::True,      // Assert
                _ => continue, // Skip unconditional/sequential edges
            };

            // Get source block's condition line (usually the block's start line)
            let condition_line = self.get_condition_line(edge.from);

            // Get all lines in the target block and add control dependencies
            let (target_start, target_end) = match self.block_line_ranges.get(&edge.to) {
                Some(&range) => range,
                None => continue,
            };

            // For each line in the target block, it's control-dependent on the condition
            for line in target_start..=target_end {
                // Don't create self-dependencies
                if line != condition_line {
                    self.control_deps.push(ControlDependence {
                        condition_line,
                        dependent_line: line,
                        branch_type,
                    });
                }
            }

            // For branches, also add control dependencies for all blocks reachable
            // only through this branch (until they reconverge)
            if matches!(branch_type, BranchType::True | BranchType::False) {
                transitive_deps.push((edge.from, edge.to, condition_line, branch_type));
            }
        }

        // Process transitive control dependencies after releasing the immutable borrow
        for (source_block, start_block, condition_line, branch_type) in transitive_deps {
            self.add_transitive_control_deps(
                source_block,
                start_block,
                condition_line,
                branch_type,
            );
        }

        // Deduplicate control dependencies
        self.deduplicate_control_deps();
    }

    /// Add transitive control dependencies for blocks only reachable through a branch.
    ///
    /// This handles nested statements inside if/else blocks, loops, etc.
    fn add_transitive_control_deps(
        &mut self,
        source_block: BlockId,
        start_block: BlockId,
        condition_line: usize,
        branch_type: BranchType,
    ) {
        // Find all blocks reachable from start_block
        // Use FixedBitSet for O(1) visited checks with minimal memory
        let capacity = self.cfg.blocks.len();
        let mut visited = FixedBitSet::with_capacity(capacity);
        let mut to_visit: Vec<BlockId> = vec![start_block];

        // Find the reconvergence point (where branches merge)
        // For simplicity, we limit depth and avoid loops
        let mut depth = 0;
        const MAX_DEPTH: usize = 50;

        while let Some(block_id) = to_visit.pop() {
            if visited.contains(block_id.0) || depth > MAX_DEPTH {
                continue;
            }

            // Don't go back to the source block (would create cycles)
            if block_id == source_block {
                continue;
            }

            visited.insert(block_id.0);
            depth += 1;

            // Get successors of this block
            for &succ in self.cfg.successors(block_id) {
                // Skip back edges to avoid infinite loops
                if let Some(edge) = self
                    .cfg
                    .edges
                    .iter()
                    .find(|e| e.from == block_id && e.to == succ)
                {
                    if edge.edge_type == EdgeType::BackEdge {
                        continue;
                    }
                }
                to_visit.push(succ);
            }
        }

        // For all visited blocks (except start_block which we already handled),
        // add control dependencies for their lines
        for block_idx in visited.ones() {
            let block_id = BlockId(block_idx);
            if block_id == start_block {
                continue;
            }

            let (start_line, end_line) = match self.block_line_ranges.get(&block_id) {
                Some(&range) => range,
                None => continue,
            };

            for line in start_line..=end_line {
                if line != condition_line {
                    self.control_deps.push(ControlDependence {
                        condition_line,
                        dependent_line: line,
                        branch_type,
                    });
                }
            }
        }
    }

    /// Get the condition line for a block (typically the block's start line).
    fn get_condition_line(&self, block_id: BlockId) -> usize {
        self.cfg
            .blocks
            .get(&block_id)
            .map(|b| b.start_line)
            .unwrap_or(1)
    }

    /// Remove duplicate control dependencies.
    fn deduplicate_control_deps(&mut self) {
        let mut seen: FxHashSet<(usize, usize)> = FxHashSet::default();
        self.control_deps.retain(|dep| {
            let key = (dep.condition_line, dep.dependent_line);
            seen.insert(key)
        });
    }
}

/// Build a PDG from file and function name.
///
/// # Arguments
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
/// PDGInfo containing combined CFG, DFG, and control dependencies.
pub fn build_pdg(file: &str, function: &str) -> crate::error::Result<PDGInfo> {
    build_pdg_with_language(file, function, None)
}

/// Build a PDG from file and function name with explicit language specification.
///
/// This function allows overriding the language auto-detection, which is useful
/// for files without extensions or with non-standard extensions.
///
/// # Arguments
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
/// * `language` - Optional language override (e.g., "python", "typescript", "rust").
///   If `None`, language is auto-detected from file extension.
///
/// # Returns
/// PDGInfo containing combined CFG, DFG, and control dependencies.
///
/// # Example
/// ```ignore
/// use go_brrr::pdg::build_pdg_with_language;
///
/// // Auto-detect language from file extension
/// let pdg = build_pdg_with_language("main.py", "process", None)?;
///
/// // Force Python language for extensionless file
/// let pdg = build_pdg_with_language("Makefile.inc", "target", Some("python"))?;
/// ```
pub fn build_pdg_with_language(
    file: &str,
    function: &str,
    language: Option<&str>,
) -> crate::error::Result<PDGInfo> {
    let cfg = crate::cfg::extract_with_language(file, function, language)?;
    let dfg = crate::dfg::extract_with_language(file, function, language)?;
    Ok(PDGBuilder::new(cfg, dfg).build())
}

/// Build a PDG from existing CFG and DFG.
pub fn build_pdg_from_graphs(cfg: CFGInfo, dfg: DFGInfo) -> PDGInfo {
    PDGBuilder::new(cfg, dfg).build()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::types::{BlockType, CFGBlock, CFGEdge};
    use crate::dfg::types::{DataflowEdge, DataflowKind};

    /// Create a test CFG representing:
    /// ```text
    /// def test(x):        # Block 0, line 1 (entry)
    ///     if x > 0:       # Block 1, line 2 (branch)
    ///         result = x  # Block 2, line 3 (true branch)
    ///     else:
    ///         result = 0  # Block 3, line 5 (false branch)
    ///     return result   # Block 4, line 6 (exit)
    /// ```
    fn create_test_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def test(x):".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "if x > 0".to_string(),
                block_type: BlockType::Branch,
                statements: vec!["if x > 0:".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 2,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "true branch".to_string(),
                block_type: BlockType::Body,
                statements: vec!["result = x".to_string()],
                func_calls: vec![],
                start_line: 3,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "false branch".to_string(),
                block_type: BlockType::Body,
                statements: vec!["result = 0".to_string()],
                func_calls: vec![],
                start_line: 5,
                end_line: 5,
            },
        );

        blocks.insert(
            BlockId(4),
            CFGBlock {
                id: BlockId(4),
                label: "exit".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return result".to_string()],
                func_calls: vec![],
                start_line: 6,
                end_line: 6,
            },
        );

        let edges = vec![
            CFGEdge::unconditional(BlockId(0), BlockId(1)),
            CFGEdge::new(BlockId(1), BlockId(2), EdgeType::True),
            CFGEdge::new(BlockId(1), BlockId(3), EdgeType::False),
            CFGEdge::unconditional(BlockId(2), BlockId(4)),
            CFGEdge::unconditional(BlockId(3), BlockId(4)),
        ];

        CFGInfo {
            function_name: "test".to_string(),
            blocks,
            edges,
            entry: BlockId(0),
            exits: vec![BlockId(4)],
            decision_points: 1,
            comprehension_decision_points: 0,
            nested_cfgs: FxHashMap::default(),
            is_async: false,
            await_points: 0,
            blocking_calls: Vec::new(),
            ..Default::default()
        }
    }

    /// Create a test DFG for the same function.
    fn create_test_dfg() -> DFGInfo {
        DFGInfo::new(
            "test".to_string(),
            vec![
                // x flows from parameter to line 3 (true branch)
                DataflowEdge {
                    variable: "x".to_string(),
                    from_line: 1,
                    to_line: 3,
                    kind: DataflowKind::Use,
                },
                // result flows from line 3 to return (line 6)
                DataflowEdge {
                    variable: "result".to_string(),
                    from_line: 3,
                    to_line: 6,
                    kind: DataflowKind::Definition,
                },
                // result flows from line 5 to return (line 6)
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
            [("x".to_string(), vec![3]), ("result".to_string(), vec![6])]
                .into_iter()
                .collect(),
        )
    }

    #[test]
    fn test_pdg_builder_creates_control_deps() {
        let cfg = create_test_cfg();
        let dfg = create_test_dfg();

        let pdg = PDGBuilder::new(cfg, dfg).build();

        // Line 3 (true branch) should be control-dependent on line 2 (condition)
        assert!(
            pdg.is_control_dependent(3, 2),
            "Line 3 should be control-dependent on line 2 (true branch)"
        );

        // Line 5 (false branch) should be control-dependent on line 2 (condition)
        assert!(
            pdg.is_control_dependent(5, 2),
            "Line 5 should be control-dependent on line 2 (false branch)"
        );
    }

    #[test]
    fn test_pdg_has_both_control_and_data_edges() {
        let cfg = create_test_cfg();
        let dfg = create_test_dfg();

        let pdg = PDGBuilder::new(cfg, dfg).build();

        // Should have control dependencies
        assert!(
            pdg.control_dep_count() > 0,
            "PDG should have control dependencies"
        );

        // Should have data flow edges
        assert!(pdg.data_edge_count() > 0, "PDG should have data flow edges");
    }

    #[test]
    fn test_control_deps_for_line() {
        let cfg = create_test_cfg();
        let dfg = create_test_dfg();

        let pdg = PDGBuilder::new(cfg, dfg).build();

        // Line 3 should have line 2 as its control dependency
        let deps = pdg.control_deps_for(3);
        assert!(
            deps.contains(&2),
            "Line 3's control deps should include line 2"
        );
    }

    #[test]
    fn test_lines_controlled_by() {
        let cfg = create_test_cfg();
        let dfg = create_test_dfg();

        let pdg = PDGBuilder::new(cfg, dfg).build();

        // Line 2 should control lines 3 and 5
        let controlled = pdg.lines_controlled_by(2);
        assert!(controlled.contains(&3), "Line 2 should control line 3");
        assert!(controlled.contains(&5), "Line 2 should control line 5");
    }
}
