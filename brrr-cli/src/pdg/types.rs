//! PDG (Program Dependence Graph) type definitions.
//!
//! A PDG combines control flow (CFG) and data flow (DFG) into a unified graph
//! where slicing operations can follow both types of dependencies.
//!
//! Control dependency: "this statement executes only if that condition is true"
//! Data dependency: "this statement uses a value computed by that statement"

use serde::{Deserialize, Serialize};

use crate::cfg::types::{BlockId, CFGInfo, EdgeType};
use crate::dfg::types::DFGInfo;

/// A control dependence between two lines.
///
/// Represents that `dependent_line` only executes based on the outcome
/// of the condition at `condition_line`.
///
/// For example, in:
/// ```text
/// if x > 0:        # Line 2 - condition_line
///     result = x   # Line 3 - dependent_line
/// ```
/// Line 3 is control-dependent on line 2.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ControlDependence {
    /// Line number of the controlling condition (e.g., if/while condition)
    pub condition_line: usize,
    /// Line number that depends on the condition
    pub dependent_line: usize,
    /// Type of control dependence (true branch, false branch, etc.)
    pub branch_type: BranchType,
}

/// Type of control dependence branch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BranchType {
    /// Dependent on true branch of condition
    True,
    /// Dependent on false branch of condition
    False,
    /// Loop body depends on loop condition
    Loop,
    /// Exception handler depends on try block
    Exception,
    /// Unconditional flow (sequential)
    Unconditional,
}

impl From<EdgeType> for BranchType {
    fn from(edge_type: EdgeType) -> Self {
        match edge_type {
            EdgeType::True => BranchType::True,
            EdgeType::False | EdgeType::Else => BranchType::False,
            EdgeType::BackEdge | EdgeType::Loop | EdgeType::Iterate | EdgeType::Next => {
                BranchType::Loop
            }
            EdgeType::Exception | EdgeType::ExceptionGroup => BranchType::Exception,
            _ => BranchType::Unconditional,
        }
    }
}

/// Complete Program Dependence Graph combining CFG and DFG.
///
/// Provides access to:
/// - The underlying CFG for control flow analysis
/// - The underlying DFG for data flow analysis
/// - Computed control dependencies for slicing operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PDGInfo {
    /// Function name
    pub function_name: String,

    /// Control flow graph (provides control structure)
    pub cfg: CFGInfo,

    /// Data flow graph (provides data dependencies)
    pub dfg: DFGInfo,

    /// Computed control dependencies.
    ///
    /// Maps from dependent line -> condition line.
    /// These are derived from the CFG structure:
    /// - Lines in the true branch of an if are control-dependent on the condition
    /// - Lines in the false branch of an if are control-dependent on the condition
    /// - Loop body lines are control-dependent on the loop condition
    pub control_deps: Vec<ControlDependence>,
}

impl PDGInfo {
    /// Create a new PDGInfo from CFG and DFG with computed control dependencies.
    pub fn new(cfg: CFGInfo, dfg: DFGInfo, control_deps: Vec<ControlDependence>) -> Self {
        let function_name = cfg.function_name.clone();
        Self {
            function_name,
            cfg,
            dfg,
            control_deps,
        }
    }

    /// Get all control dependency source lines for a given line.
    ///
    /// Returns lines that control whether `line` executes.
    pub fn control_deps_for(&self, line: usize) -> Vec<usize> {
        self.control_deps
            .iter()
            .filter(|dep| dep.dependent_line == line)
            .map(|dep| dep.condition_line)
            .collect()
    }

    /// Get all lines that are control-dependent on a given condition line.
    ///
    /// Returns lines whose execution depends on the condition at `condition_line`.
    pub fn lines_controlled_by(&self, condition_line: usize) -> Vec<usize> {
        self.control_deps
            .iter()
            .filter(|dep| dep.condition_line == condition_line)
            .map(|dep| dep.dependent_line)
            .collect()
    }

    /// Check if line_a is control-dependent on line_b.
    pub fn is_control_dependent(&self, line_a: usize, line_b: usize) -> bool {
        self.control_deps
            .iter()
            .any(|dep| dep.dependent_line == line_a && dep.condition_line == line_b)
    }

    /// Get total number of control dependencies.
    pub fn control_dep_count(&self) -> usize {
        self.control_deps.len()
    }

    /// Get total number of data flow edges.
    pub fn data_edge_count(&self) -> usize {
        self.dfg.edges.len()
    }

    /// Get all unique variables in the PDG.
    pub fn variables(&self) -> Vec<&str> {
        self.dfg.variables()
    }

    /// Get the block containing a specific line number.
    pub fn block_for_line(&self, line: usize) -> Option<BlockId> {
        self.cfg.block_for_line(line)
    }

    /// Convert to dictionary for JSON serialization.
    pub fn to_dict(&self) -> serde_json::Value {
        serde_json::json!({
            "function_name": self.function_name,
            "control_deps": self.control_deps.len(),
            "data_edges": self.dfg.edges.len(),
            "cfg_blocks": self.cfg.blocks.len(),
            "cfg_edges": self.cfg.edges.len(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_control_dep() -> ControlDependence {
        ControlDependence {
            condition_line: 2,
            dependent_line: 3,
            branch_type: BranchType::True,
        }
    }

    #[test]
    fn test_branch_type_from_edge_type() {
        assert_eq!(BranchType::from(EdgeType::True), BranchType::True);
        assert_eq!(BranchType::from(EdgeType::False), BranchType::False);
        assert_eq!(BranchType::from(EdgeType::Else), BranchType::False);
        assert_eq!(BranchType::from(EdgeType::BackEdge), BranchType::Loop);
        assert_eq!(BranchType::from(EdgeType::Loop), BranchType::Loop);
        assert_eq!(BranchType::from(EdgeType::Exception), BranchType::Exception);
        assert_eq!(
            BranchType::from(EdgeType::Unconditional),
            BranchType::Unconditional
        );
    }

    #[test]
    fn test_control_dependence_equality() {
        let dep1 = create_test_control_dep();
        let dep2 = create_test_control_dep();
        assert_eq!(dep1, dep2);

        let dep3 = ControlDependence {
            condition_line: 2,
            dependent_line: 4, // Different line
            branch_type: BranchType::True,
        };
        assert_ne!(dep1, dep3);
    }
}
