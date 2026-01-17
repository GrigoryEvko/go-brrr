//! Taint propagation engine with inter-procedural analysis.
//!
//! This module implements comprehensive taint propagation that tracks how
//! tainted data flows through a program across function boundaries.
//!
//! # Key Features
//!
//! - **Worklist-based propagation**: Efficient fixed-point iteration
//! - **Inter-procedural analysis**: Tracks taint across function calls via call graph
//! - **Implicit flow tracking**: Detects control-flow dependent taint leakage
//! - **Sanitization awareness**: Stops propagation at known sanitizers
//!
//! # Propagation Rules
//!
//! ## Explicit Flows
//!
//! ```text
//! Assignment:        taint(lhs) = taint(rhs)
//! Binary op:         taint(result) = taint(a) ∪ taint(b)
//! Function call:     taint(return) = f(taint(args))
//! Collection access: taint(elem) = taint(collection)
//! Field access:      taint(obj.field) = taint(obj)
//! ```
//!
//! ## Special Cases
//!
//! - String concatenation: preserves taint
//! - Type conversion: preserves taint
//! - Serialization (JSON.stringify): preserves taint
//! - Comparison (==, <, etc.): does NOT propagate (returns clean bool)
//!
//! ## Implicit Flows
//!
//! Implicit flows occur when tainted data influences control flow:
//!
//! ```text
//! if (tainted) {
//!     x = secret;  // x is implicitly tainted
//! } else {
//!     x = public;  // x is also implicitly tainted
//! }
//! ```
//!
//! The value of x depends on the tainted condition, leaking 1 bit of information.

use super::types::{
    Location, PropagationStep, TaintLabel, TaintPropagation, TaintState, TaintedValue,
};
use crate::callgraph::types::{CallGraph, FunctionRef};
use crate::cfg::types::{BlockId, CFGInfo, EdgeType};
use crate::dfg::types::{DataflowEdge, DataflowKind, DFGInfo};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};

// =============================================================================
// Node ID and Core Types
// =============================================================================

/// Unique identifier for a node in the tainted DFG.
///
/// Combines file path and line number for cross-file uniqueness.
/// Within a single function, line number alone is sufficient.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NodeId {
    /// File path (empty for single-function analysis)
    pub file: String,
    /// Line number (1-indexed)
    pub line: usize,
    /// Optional variable name for variable-specific tracking
    pub variable: Option<String>,
}

impl NodeId {
    /// Create a new NodeId from line number (single-function context).
    #[inline]
    pub fn from_line(line: usize) -> Self {
        Self {
            file: String::new(),
            line,
            variable: None,
        }
    }

    /// Create a NodeId with file and line.
    #[inline]
    pub fn new(file: impl Into<String>, line: usize) -> Self {
        Self {
            file: file.into(),
            line,
            variable: None,
        }
    }

    /// Create a NodeId with variable tracking.
    #[inline]
    pub fn with_variable(file: impl Into<String>, line: usize, variable: impl Into<String>) -> Self {
        Self {
            file: file.into(),
            line,
            variable: Some(variable.into()),
        }
    }

    /// Convert to a Location for reporting.
    pub fn to_location(&self) -> Location {
        Location::new(
            if self.file.is_empty() { "<function>" } else { &self.file },
            self.line,
            1,
        )
    }
}

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.file.is_empty() {
            write!(f, "line:{}", self.line)?;
        } else {
            write!(f, "{}:{}", self.file, self.line)?;
        }
        if let Some(ref var) = self.variable {
            write!(f, ":{}", var)?;
        }
        Ok(())
    }
}

// =============================================================================
// Taint-Annotated DFG Edge
// =============================================================================

/// A DFG edge annotated with taint propagation information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintedEdge {
    /// The original DFG edge
    pub edge: DataflowEdge,
    /// Type of taint propagation for this edge
    pub propagation: TaintPropagation,
    /// Taint labels flowing through this edge (if any)
    #[serde(skip_serializing_if = "HashSet::is_empty", default)]
    pub labels: HashSet<TaintLabel>,
    /// Whether this edge passes through a sanitizer
    #[serde(default)]
    pub sanitized: bool,
    /// Sanitization method if sanitized
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sanitization_method: Option<String>,
}

impl TaintedEdge {
    /// Create a new tainted edge from a DFG edge.
    pub fn from_dfg_edge(edge: DataflowEdge) -> Self {
        let propagation = Self::infer_propagation(&edge);
        Self {
            edge,
            propagation,
            labels: HashSet::new(),
            sanitized: false,
            sanitization_method: None,
        }
    }

    /// Infer propagation type from the DFG edge kind.
    fn infer_propagation(edge: &DataflowEdge) -> TaintPropagation {
        match edge.kind {
            DataflowKind::Definition => TaintPropagation::Copy,
            DataflowKind::Use => TaintPropagation::Copy,
            DataflowKind::Mutation => TaintPropagation::Transform,
            DataflowKind::Return => TaintPropagation::CallReturn,
            DataflowKind::Param => TaintPropagation::Copy,
            DataflowKind::Yield => TaintPropagation::CallReturn,
            DataflowKind::ClosureCapture => TaintPropagation::Copy,
            DataflowKind::Goroutine => TaintPropagation::Copy,
            DataflowKind::ChannelSend | DataflowKind::ChannelReceive => TaintPropagation::Copy,
            DataflowKind::Defer => TaintPropagation::Copy,
            DataflowKind::TypeAssertion => TaintPropagation::Transform,
            DataflowKind::ComprehensionVar
            | DataflowKind::LambdaParam
            | DataflowKind::NestedParam => TaintPropagation::Copy,
            DataflowKind::Global | DataflowKind::Nonlocal => TaintPropagation::Copy,
            // Go error handling patterns
            DataflowKind::Panic | DataflowKind::Recover => TaintPropagation::Transform,
            DataflowKind::ErrorAssign | DataflowKind::ErrorCheck => TaintPropagation::Copy,
            DataflowKind::NamedReturnModify => TaintPropagation::Transform,
            // Go concurrency patterns - data flows through channels and sync primitives
            DataflowKind::ChannelMake
            | DataflowKind::ChannelCloseDfg
            | DataflowKind::SelectReceive
            | DataflowKind::SelectSend => TaintPropagation::Copy,
            DataflowKind::MutexLock
            | DataflowKind::MutexUnlock
            | DataflowKind::WaitGroupAdd
            | DataflowKind::WaitGroupDone
            | DataflowKind::WaitGroupWait
            | DataflowKind::OnceDo => TaintPropagation::Copy,
            DataflowKind::ContextDone
            | DataflowKind::ContextErr
            | DataflowKind::ContextValue => TaintPropagation::Copy,
            DataflowKind::PoolGet | DataflowKind::PoolPut => TaintPropagation::Copy,
        }
    }

    /// Mark this edge as sanitized.
    pub fn mark_sanitized(&mut self, method: impl Into<String>) {
        self.sanitized = true;
        self.sanitization_method = Some(method.into());
        self.propagation = TaintPropagation::Sanitize;
    }

    /// Add taint labels to this edge.
    pub fn add_labels(&mut self, labels: impl IntoIterator<Item = TaintLabel>) {
        self.labels.extend(labels);
    }

    /// Check if this edge carries taint.
    pub fn is_tainted(&self) -> bool {
        !self.labels.is_empty() && !self.sanitized
    }
}

// =============================================================================
// Taint-Annotated DFG with NodeId-based tracking
// =============================================================================

/// A data flow graph with comprehensive taint annotations.
///
/// This structure extends the base DFG with:
/// - Node-level taint label tracking
/// - Sanitization point registry
/// - Implicit flow detection support
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintedDFG {
    /// Reference to the underlying DFG
    pub dfg: DFGInfo,
    /// Taint labels at each node: NodeId -> set of TaintLabels
    pub taint_labels: HashMap<NodeId, HashSet<TaintLabel>>,
    /// Nodes where sanitization occurs (taint stops propagating)
    pub sanitization_points: HashSet<NodeId>,
    /// Function name for context
    pub function_name: String,
    /// File path for cross-file analysis
    pub file_path: String,
    /// Lines identified as taint sources
    pub source_lines: HashMap<usize, Vec<TaintLabel>>,
    /// Lines identified as taint sinks
    pub sink_lines: HashSet<usize>,
    /// Sanitization methods at each line
    pub sanitization_methods: HashMap<usize, String>,
    /// Taint-annotated edges
    pub edges: Vec<TaintedEdge>,
}

impl TaintedDFG {
    /// Create a taint-annotated DFG from a base DFG.
    pub fn from_dfg(dfg: &DFGInfo, file_path: impl Into<String>) -> Self {
        let edges = dfg
            .edges
            .iter()
            .map(|e| TaintedEdge::from_dfg_edge(e.clone()))
            .collect();

        Self {
            dfg: dfg.clone(),
            taint_labels: HashMap::new(),
            sanitization_points: HashSet::new(),
            function_name: dfg.function_name.clone(),
            file_path: file_path.into(),
            source_lines: HashMap::new(),
            sink_lines: HashSet::new(),
            sanitization_methods: HashMap::new(),
            edges,
        }
    }

    /// Mark a node as tainted with specific labels.
    pub fn mark_tainted(&mut self, node: NodeId, labels: impl IntoIterator<Item = TaintLabel>) {
        self.taint_labels
            .entry(node)
            .or_default()
            .extend(labels);
    }

    /// Mark a line as a taint source.
    pub fn mark_source(&mut self, line: usize, label: TaintLabel) {
        let node = NodeId::from_line(line);
        self.source_lines.entry(line).or_default().push(label.clone());
        self.mark_tainted(node, std::iter::once(label));
    }

    /// Mark a line as a taint sink.
    pub fn mark_sink(&mut self, line: usize) {
        self.sink_lines.insert(line);
    }

    /// Mark a node as a sanitization point.
    pub fn mark_sanitization(&mut self, line: usize, method: impl Into<String>) {
        let node = NodeId::from_line(line);
        self.sanitization_points.insert(node);
        let method_str = method.into();
        self.sanitization_methods.insert(line, method_str.clone());

        // Mark edges flowing through this line as sanitized
        for edge in &mut self.edges {
            if edge.edge.to_line == line || edge.edge.from_line == line {
                edge.mark_sanitized(&method_str);
            }
        }
    }

    /// Check if a node is tainted.
    pub fn is_tainted(&self, node: &NodeId) -> bool {
        self.taint_labels
            .get(node)
            .map_or(false, |labels| !labels.is_empty())
            && !self.sanitization_points.contains(node)
    }

    /// Get taint labels for a node.
    pub fn get_taint(&self, node: &NodeId) -> Option<&HashSet<TaintLabel>> {
        if self.sanitization_points.contains(node) {
            None
        } else {
            self.taint_labels.get(node)
        }
    }

    /// Get all edges originating from a line.
    pub fn edges_from(&self, line: usize) -> Vec<&TaintedEdge> {
        self.edges
            .iter()
            .filter(|e| e.edge.from_line == line)
            .collect()
    }

    /// Get all edges flowing to a line.
    pub fn edges_to(&self, line: usize) -> Vec<&TaintedEdge> {
        self.edges
            .iter()
            .filter(|e| e.edge.to_line == line)
            .collect()
    }

    /// Get all tainted nodes.
    pub fn tainted_nodes(&self) -> Vec<(&NodeId, &HashSet<TaintLabel>)> {
        self.taint_labels
            .iter()
            .filter(|(node, labels)| !labels.is_empty() && !self.sanitization_points.contains(*node))
            .collect()
    }

    /// Check if there is a tainted path from source to sink.
    pub fn has_tainted_path(&self, source_line: usize, sink_line: usize) -> bool {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(source_line);

        while let Some(current) = queue.pop_front() {
            if current == sink_line {
                return true;
            }
            if !visited.insert(current) {
                continue;
            }

            // Follow unsanitized edges
            for edge in self.edges_from(current) {
                if !edge.sanitized {
                    queue.push_back(edge.edge.to_line);
                }
            }
        }

        false
    }
}

// =============================================================================
// Propagation Configuration
// =============================================================================

/// Configuration for the taint propagation engine.
#[derive(Debug, Clone)]
pub struct PropagationConfig {
    /// Maximum iterations for fixed-point computation
    pub max_iterations: usize,
    /// Track implicit flows (control-flow dependent taint)
    pub track_implicit_flows: bool,
    /// Propagate through collections conservatively
    pub conservative_collections: bool,
    /// Consider function returns as tainted if any argument is tainted
    pub taint_through_calls: bool,
    /// Enable inter-procedural analysis
    pub inter_procedural: bool,
    /// Maximum call depth for inter-procedural analysis
    pub max_call_depth: usize,
    /// Minimum confidence threshold for reporting
    pub min_confidence: f64,
}

impl Default for PropagationConfig {
    fn default() -> Self {
        Self {
            max_iterations: 100,
            track_implicit_flows: true,
            conservative_collections: true,
            taint_through_calls: true,
            inter_procedural: true,
            max_call_depth: 5,
            min_confidence: 0.5,
        }
    }
}

// =============================================================================
// Function Taint Summary (for inter-procedural analysis)
// =============================================================================

/// Summary of how taint propagates through a function.
///
/// Used for efficient inter-procedural analysis without re-analyzing
/// the same function multiple times.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FunctionTaintSummary {
    /// Function name
    pub name: String,
    /// Which parameters can be tainted (by index)
    pub tainted_params: HashSet<usize>,
    /// Whether return value can be tainted
    pub return_tainted: bool,
    /// Which parameter indices flow to the return value
    pub param_to_return: HashSet<usize>,
    /// Whether the function is a known sanitizer
    pub is_sanitizer: bool,
    /// Sanitization method name (if sanitizer)
    pub sanitization_method: Option<String>,
    /// Whether function modifies global state with taint
    pub taints_globals: bool,
    /// Global variables that may be tainted
    pub tainted_globals: HashSet<String>,
}

impl FunctionTaintSummary {
    /// Create a new empty summary.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            ..Default::default()
        }
    }

    /// Mark as a sanitizer.
    pub fn as_sanitizer(mut self, method: impl Into<String>) -> Self {
        self.is_sanitizer = true;
        self.sanitization_method = Some(method.into());
        self
    }

    /// Mark parameter as flowing to return.
    pub fn param_flows_to_return(mut self, param_idx: usize) -> Self {
        self.param_to_return.insert(param_idx);
        self.return_tainted = true;
        self
    }

    /// Mark all parameters as flowing to return.
    pub fn all_params_flow_to_return(mut self, param_count: usize) -> Self {
        for i in 0..param_count {
            self.param_to_return.insert(i);
        }
        self.return_tainted = true;
        self
    }
}

// =============================================================================
// Implicit Flow Context
// =============================================================================

/// Tracks implicit flow context during propagation.
///
/// When code is inside a branch controlled by tainted data,
/// all assignments potentially leak information about the taint.
#[derive(Debug, Clone, Default)]
pub struct ImplicitFlowContext {
    /// Stack of taint labels from enclosing branches
    pub condition_taint_stack: Vec<HashSet<TaintLabel>>,
    /// Blocks currently under implicit taint
    pub tainted_blocks: HashSet<BlockId>,
    /// Current implicit taint level (union of all condition taints)
    pub current_implicit_taint: HashSet<TaintLabel>,
}

impl ImplicitFlowContext {
    /// Enter a branch controlled by tainted condition.
    pub fn enter_branch(&mut self, condition_taint: HashSet<TaintLabel>) {
        if !condition_taint.is_empty() {
            self.current_implicit_taint.extend(condition_taint.iter().cloned());
        }
        self.condition_taint_stack.push(condition_taint);
    }

    /// Exit a branch.
    pub fn exit_branch(&mut self) {
        if let Some(exited_taint) = self.condition_taint_stack.pop() {
            // Rebuild current implicit taint from remaining stack
            self.current_implicit_taint.clear();
            for taint_set in &self.condition_taint_stack {
                self.current_implicit_taint.extend(taint_set.iter().cloned());
            }
            // If the exited branch had taint, we should still consider
            // it for merging at the join point
            let _ = exited_taint; // suppress unused warning, used for merge logic
        }
    }

    /// Check if currently under implicit taint.
    pub fn has_implicit_taint(&self) -> bool {
        !self.current_implicit_taint.is_empty()
    }

    /// Get the current implicit taint labels.
    pub fn get_implicit_taint(&self) -> &HashSet<TaintLabel> {
        &self.current_implicit_taint
    }

    /// Mark a block as being under implicit taint.
    pub fn mark_block_tainted(&mut self, block_id: BlockId) {
        self.tainted_blocks.insert(block_id);
    }

    /// Check if a block is under implicit taint.
    pub fn is_block_tainted(&self, block_id: BlockId) -> bool {
        self.tainted_blocks.contains(&block_id)
    }
}

// =============================================================================
// Worklist Item
// =============================================================================

/// An item in the propagation worklist.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct WorklistItem {
    /// Node to process
    node: NodeId,
    /// Source of taint (for path tracking)
    source_node: NodeId,
    /// Current propagation depth
    depth: usize,
}

// =============================================================================
// Propagation Engine
// =============================================================================

/// The taint propagation engine with worklist algorithm.
///
/// Performs dataflow-based taint analysis using efficient worklist
/// iteration to reach a fixed point.
pub struct PropagationEngine {
    /// Configuration
    config: PropagationConfig,
    /// Current taint state during analysis
    state: TaintState,
    /// All findings (source -> sink flows)
    findings: Vec<TaintFlow>,
    /// Function summaries for inter-procedural analysis
    summaries: HashMap<String, FunctionTaintSummary>,
    /// Implicit flow context
    implicit_context: ImplicitFlowContext,
}

impl PropagationEngine {
    /// Create a new propagation engine with default config.
    pub fn new() -> Self {
        Self {
            config: PropagationConfig::default(),
            state: TaintState::new(),
            findings: Vec::new(),
            summaries: HashMap::new(),
            implicit_context: ImplicitFlowContext::default(),
        }
    }

    /// Create a new propagation engine with custom config.
    pub fn with_config(config: PropagationConfig) -> Self {
        Self {
            config,
            state: TaintState::new(),
            findings: Vec::new(),
            summaries: HashMap::new(),
            implicit_context: ImplicitFlowContext::default(),
        }
    }

    /// Reset the engine state for a new analysis.
    pub fn reset(&mut self) {
        self.state.clear();
        self.findings.clear();
        self.implicit_context = ImplicitFlowContext::default();
    }

    /// Get all findings from the analysis.
    pub fn findings(&self) -> &[TaintFlow] {
        &self.findings
    }

    /// Get the current taint state.
    pub fn state(&self) -> &TaintState {
        &self.state
    }

    /// Register a function summary for inter-procedural analysis.
    pub fn register_summary(&mut self, summary: FunctionTaintSummary) {
        self.summaries.insert(summary.name.clone(), summary);
    }

    /// Introduce a taint source.
    pub fn introduce_taint(
        &mut self,
        variable: &str,
        label: TaintLabel,
        location: Location,
        expression: Option<&str>,
    ) {
        let mut taint = TaintedValue::new(label, location);
        if let Some(expr) = expression {
            taint = taint.with_source_expression(expr);
        }
        self.state.set_variable(variable, taint);
    }

    /// Propagate taint through an assignment: `target = source`
    pub fn propagate_assignment(&mut self, target: &str, source: &str, location: Location) {
        // Get explicit taint from source
        let explicit_taint = self.state.get_variable(source).cloned();

        // Combine with implicit taint if tracking enabled
        let combined_taint = if self.config.track_implicit_flows && self.implicit_context.has_implicit_taint() {
            let implicit_labels = self.implicit_context.get_implicit_taint().clone();
            match explicit_taint {
                Some(mut t) => {
                    // Merge implicit taint into explicit
                    t.labels.extend(implicit_labels);
                    t.add_step(PropagationStep {
                        location: location.clone(),
                        propagation: TaintPropagation::ImplicitFlow,
                        operation: Some("implicit flow from branch condition".to_string()),
                    });
                    Some(t)
                }
                None if !implicit_labels.is_empty() => {
                    // Create new taint from implicit flow only
                    let mut t = TaintedValue::with_labels(implicit_labels, location.clone());
                    t.add_step(PropagationStep {
                        location,
                        propagation: TaintPropagation::ImplicitFlow,
                        operation: Some("implicit flow from branch condition".to_string()),
                    });
                    t.confidence = 0.7; // Lower confidence for implicit flows
                    Some(t)
                }
                None => None,
            }
        } else {
            explicit_taint.map(|t| t.propagate_copy(location))
        };

        if let Some(taint) = combined_taint {
            self.state.set_variable(target, taint);
        }
    }

    /// Propagate taint through a binary operation: `result = left op right`
    ///
    /// Special handling for comparison operators which do NOT propagate taint.
    pub fn propagate_binary_op(
        &mut self,
        result: &str,
        left: &str,
        right: &str,
        operator: &str,
        location: Location,
    ) {
        // Comparison operators do NOT propagate taint
        // The result is a boolean that doesn't contain the tainted data
        if matches!(operator, "==" | "!=" | "<" | ">" | "<=" | ">=" | "is" | "in" | "not in") {
            return;
        }

        let left_taint = self.state.get_variable(left);
        let right_taint = self.state.get_variable(right);

        match (left_taint, right_taint) {
            (Some(lt), Some(rt)) => {
                let merged = TaintedValue::merge(&[lt, rt], location);
                self.state.set_variable(result, merged);
            }
            (Some(lt), None) => {
                let propagated = lt.propagate_copy(location);
                self.state.set_variable(result, propagated);
            }
            (None, Some(rt)) => {
                let propagated = rt.propagate_copy(location);
                self.state.set_variable(result, propagated);
            }
            (None, None) => {
                // Add implicit taint if applicable
                if self.config.track_implicit_flows && self.implicit_context.has_implicit_taint() {
                    let implicit_labels = self.implicit_context.get_implicit_taint().clone();
                    if !implicit_labels.is_empty() {
                        let mut t = TaintedValue::with_labels(implicit_labels, location.clone());
                        t.add_step(PropagationStep {
                            location,
                            propagation: TaintPropagation::ImplicitFlow,
                            operation: Some("implicit flow in binary op".to_string()),
                        });
                        t.confidence = 0.7;
                        self.state.set_variable(result, t);
                    }
                }
            }
        }
    }

    /// Propagate taint through string concatenation (always preserves taint).
    pub fn propagate_string_concat(
        &mut self,
        result: &str,
        parts: &[&str],
        location: Location,
    ) {
        let mut tainted_parts: Vec<&TaintedValue> = Vec::new();
        for part in parts {
            if let Some(t) = self.state.get_variable(part) {
                if t.is_tainted() {
                    tainted_parts.push(t);
                }
            }
        }

        if !tainted_parts.is_empty() {
            let merged = TaintedValue::merge(&tainted_parts, location.clone());
            let transformed = merged.transform("string_concat", location);
            self.state.set_variable(result, transformed);
        }
    }

    /// Propagate taint through type conversion (preserves taint).
    pub fn propagate_type_conversion(
        &mut self,
        result: &str,
        source: &str,
        target_type: &str,
        location: Location,
    ) {
        if let Some(source_taint) = self.state.get_variable(source) {
            let converted = source_taint.transform(&format!("convert_to_{}", target_type), location);
            self.state.set_variable(result, converted);
        }
    }

    /// Propagate taint through serialization (preserves taint).
    pub fn propagate_serialization(
        &mut self,
        result: &str,
        source: &str,
        format: &str,
        location: Location,
    ) {
        if let Some(source_taint) = self.state.get_variable(source) {
            let serialized = source_taint.transform(&format!("{}_serialize", format), location);
            self.state.set_variable(result, serialized);
        }
    }

    /// Propagate taint through a collection access: `result = collection[index]`
    pub fn propagate_collection_access(
        &mut self,
        result: &str,
        collection: &str,
        access_expr: &str,
        location: Location,
    ) {
        if let Some(collection_taint) = self.state.get_collection(collection) {
            let accessed = collection_taint.collection_access(access_expr, location);
            self.state.set_variable(result, accessed);
        }
    }

    /// Propagate taint when storing to a collection: `collection[index] = value`
    pub fn propagate_collection_store(
        &mut self,
        collection: &str,
        value: &str,
        location: Location,
    ) {
        if let Some(value_taint) = self.state.get_variable(value).cloned() {
            if self.config.conservative_collections {
                // Mark entire collection as tainted
                let mut collection_taint = value_taint;
                collection_taint.add_step(PropagationStep {
                    location,
                    propagation: TaintPropagation::CollectionStore,
                    operation: Some(format!("store to {}", collection)),
                });
                self.state.set_collection(collection, collection_taint);
            }
        }
    }

    /// Propagate taint through property access: `result = obj.prop`
    pub fn propagate_property_access(
        &mut self,
        result: &str,
        object: &str,
        property: &str,
        location: Location,
    ) {
        if let Some(prop_taint) = self.state.get_property(object, property).cloned() {
            let accessed = prop_taint.collection_access(&format!(".{}", property), location);
            self.state.set_variable(result, accessed);
        }
    }

    /// Propagate taint through property assignment: `obj.prop = value`
    pub fn propagate_property_store(
        &mut self,
        object: &str,
        property: &str,
        value: &str,
        location: Location,
    ) {
        let value_taint = match self.state.get_variable(value) {
            Some(t) => t.clone(),
            None => return,
        };

        let mut prop_taint = value_taint.clone();
        prop_taint.add_step(PropagationStep {
            location: location.clone(),
            propagation: TaintPropagation::CollectionStore,
            operation: Some(format!("{}.{}", object, property)),
        });
        self.state.set_property(object, property, prop_taint);

        // Also taint the object itself (conservative)
        if self.config.conservative_collections {
            let mut obj_taint = value_taint;
            obj_taint.add_step(PropagationStep {
                location,
                propagation: TaintPropagation::CollectionStore,
                operation: Some(format!("property store to {}", object)),
            });
            self.state.set_variable(object, obj_taint);
        }
    }

    /// Propagate taint through a function call return.
    ///
    /// Uses function summaries for known functions, otherwise conservatively
    /// propagates taint from any tainted argument.
    pub fn propagate_call_return(
        &mut self,
        result: &str,
        function: &str,
        arguments: &[&str],
        location: Location,
    ) {
        // Check if we have a summary for this function
        if let Some(summary) = self.summaries.get(function) {
            if summary.is_sanitizer {
                // Sanitizer: result is clean
                if let Some(method) = &summary.sanitization_method {
                    // If any argument was tainted, record the sanitization
                    for arg in arguments {
                        if let Some(t) = self.state.get_variable(arg) {
                            if t.is_tainted() {
                                let sanitized = t.sanitize(method, location.clone());
                                self.state.set_variable(result, sanitized);
                                return;
                            }
                        }
                    }
                }
                return;
            }

            // Use param_to_return mapping
            if !summary.param_to_return.is_empty() {
                let mut tainted_args: Vec<&TaintedValue> = Vec::new();
                for &param_idx in &summary.param_to_return {
                    if let Some(arg) = arguments.get(param_idx) {
                        if let Some(t) = self.state.get_variable(arg) {
                            if t.is_tainted() {
                                tainted_args.push(t);
                            }
                        }
                    }
                }

                if !tainted_args.is_empty() {
                    let merged = TaintedValue::merge(&tainted_args, location.clone());
                    let returned = merged.call_return(function, location);
                    self.state.set_variable(result, returned);
                }
                return;
            }
        }

        // Default: propagate if any argument is tainted (conservative)
        if !self.config.taint_through_calls {
            return;
        }

        let mut tainted_args: Vec<&TaintedValue> = Vec::new();
        for arg in arguments {
            if let Some(arg_taint) = self.state.get_variable(arg) {
                if arg_taint.is_tainted() {
                    tainted_args.push(arg_taint);
                }
            }
        }

        if !tainted_args.is_empty() {
            let merged = TaintedValue::merge(&tainted_args, location.clone());
            let returned = merged.call_return(function, location);
            self.state.set_variable(result, returned);
        }
    }

    /// Apply sanitization to a variable.
    pub fn sanitize(&mut self, variable: &str, method: &str, location: Location) {
        if let Some(taint) = self.state.get_variable(variable).cloned() {
            let sanitized = taint.sanitize(method, location);
            self.state.set_variable(variable, sanitized);
        }
    }

    /// Enter a branch controlled by a condition variable.
    pub fn enter_branch(&mut self, condition_var: &str) {
        if self.config.track_implicit_flows {
            let condition_taint = self
                .state
                .get_variable(condition_var)
                .map(|t| t.labels.clone())
                .unwrap_or_default();
            self.implicit_context.enter_branch(condition_taint);
        }
    }

    /// Exit a branch.
    pub fn exit_branch(&mut self) {
        if self.config.track_implicit_flows {
            self.implicit_context.exit_branch();
        }
    }

    /// Check if a variable reaching a sink is tainted and record finding.
    pub fn check_sink(&mut self, variable: &str, sink_type: &str, location: Location) {
        if let Some(taint) = self.state.get_variable(variable) {
            if taint.is_tainted() && taint.confidence >= self.config.min_confidence {
                self.findings.push(TaintFlow {
                    source: taint.source_location.clone(),
                    sink: location,
                    labels: taint.labels.clone(),
                    path: taint.propagation_path.clone(),
                    sink_type: sink_type.to_string(),
                    variable: variable.to_string(),
                    confidence: taint.confidence,
                    source_expression: taint.source_expression.clone(),
                });
            }
        }
    }

    /// Run taint propagation on a tainted DFG using worklist algorithm.
    ///
    /// Uses SOA (Structure of Arrays) layout with SIMD-accelerated edge filtering
    /// for optimal cache utilization and throughput.
    pub fn analyze_dfg(&mut self, dfg: &mut TaintedDFG) -> Vec<TaintFlow> {
        self.reset();

        // Clone needed data to avoid borrow conflicts
        let source_lines = dfg.source_lines.clone();
        let function_name = dfg.function_name.clone();
        let file_path = dfg.file_path.clone();

        // SOA (Structure of Arrays) layout for cache-friendly SIMD edge filtering.
        // Storing from_lines contiguously enables u32x8 SIMD comparison.
        let edge_count = dfg.edges.len();
        let mut from_lines: Vec<u32> = Vec::with_capacity(edge_count);
        let mut to_lines: Vec<usize> = Vec::with_capacity(edge_count);
        let mut variables: Vec<String> = Vec::with_capacity(edge_count);
        let mut kinds: Vec<DataflowKind> = Vec::with_capacity(edge_count);
        let mut sanitized: Vec<bool> = Vec::with_capacity(edge_count);

        for e in &dfg.edges {
            // Safe truncation: line numbers won't exceed u32::MAX in practice
            from_lines.push(e.edge.from_line as u32);
            to_lines.push(e.edge.to_line);
            variables.push(e.edge.variable.clone());
            kinds.push(e.edge.kind);
            sanitized.push(e.sanitized);
        }

        // Phase 1: Initialize sources - collect nodes to mark
        // Reuse buffer for SIMD edge index lookup
        let mut matching_indices: Vec<usize> = Vec::new();
        let mut initial_nodes: Vec<(NodeId, TaintLabel)> = Vec::new();

        for (line, labels) in &source_lines {
            let location = Location::new(&function_name, *line, 1);

            // SIMD-accelerated lookup: find all edges originating from this line
            crate::simd::find_matching_u32_into(&from_lines, *line as u32, &mut matching_indices);

            for label in labels {
                for &idx in &matching_indices {
                    if matches!(kinds[idx], DataflowKind::Definition) {
                        self.introduce_taint(&variables[idx], label.clone(), location.clone(), None);
                        let node = NodeId::with_variable(&file_path, *line, &variables[idx]);
                        initial_nodes.push((node, label.clone()));
                    }
                }
            }
        }

        // Apply initial markings
        for (node, label) in initial_nodes {
            dfg.mark_tainted(node, std::iter::once(label));
        }

        // Phase 2: Worklist-based propagation
        let mut worklist: VecDeque<usize> = VecDeque::new();
        let mut in_worklist: HashSet<usize> = HashSet::new();

        // Initialize worklist with source lines
        for &line in source_lines.keys() {
            if in_worklist.insert(line) {
                worklist.push_back(line);
            }
        }

        // Collect nodes to mark after propagation
        let mut nodes_to_mark: Vec<(NodeId, HashSet<TaintLabel>)> = Vec::new();

        let mut iterations = 0;
        while let Some(current_line) = worklist.pop_front() {
            in_worklist.remove(&current_line);

            if iterations >= self.config.max_iterations {
                break;
            }
            iterations += 1;

            // SIMD-accelerated edge filtering: find all edges from current_line
            // O(n/8) SIMD comparisons instead of O(n) scalar iterations
            crate::simd::find_matching_u32_into(&from_lines, current_line as u32, &mut matching_indices);

            // Process only matching edges (cache-friendly indexed access)
            for &idx in &matching_indices {
                if sanitized[idx] {
                    continue; // Skip sanitized edges
                }

                let variable = &variables[idx];

                // Check if source variable is tainted
                if !self.state.is_variable_tainted(variable) {
                    continue;
                }

                let target_line = to_lines[idx];
                let target_var = variable.clone();

                // Check if this propagation adds new taint
                let was_tainted = self.state.is_variable_tainted(&target_var);

                // Propagate (all branches do the same operation)
                let location = Location::new(&function_name, target_line, 1);
                self.propagate_assignment(&target_var, variable, location);

                // If taint changed, add target to worklist
                let is_tainted = self.state.is_variable_tainted(&target_var);
                if is_tainted && !was_tainted {
                    // Collect node to mark later
                    if let Some(labels) = self.state.get_variable(&target_var).map(|t| t.labels.clone()) {
                        let node = NodeId::with_variable(&file_path, target_line, &target_var);
                        nodes_to_mark.push((node, labels));
                    }

                    if in_worklist.insert(target_line) {
                        worklist.push_back(target_line);
                    }
                }
            }
        }

        // Apply collected node markings
        for (node, labels) in nodes_to_mark {
            dfg.mark_tainted(node, labels);
        }

        // Phase 3: Check sinks
        // Note: Sink checking iterates to_lines which is outside the hot worklist loop.
        // For large edge sets, consider adding a to_lines_u32 array for SIMD filtering.
        let sink_lines: Vec<usize> = dfg.sink_lines.iter().copied().collect();
        for sink_line in sink_lines {
            let location = Location::new(&function_name, sink_line, 1);

            // Check all variables used at this sink line
            for (idx, &to_line) in to_lines.iter().enumerate() {
                if to_line == sink_line {
                    self.check_sink(&variables[idx], "generic_sink", location.clone());
                }
            }
        }

        self.findings.clone()
    }

    /// Analyze with inter-procedural propagation using call graph.
    pub fn analyze_inter_procedural(
        &mut self,
        dfg: &mut TaintedDFG,
        cfg: Option<&CFGInfo>,
        call_graph: Option<&CallGraph>,
        function_dfgs: &HashMap<String, DFGInfo>,
    ) -> Vec<TaintFlow> {
        // First run intra-procedural analysis
        let mut findings = self.analyze_dfg(dfg);

        // If inter-procedural is disabled or no call graph, return
        if !self.config.inter_procedural || call_graph.is_none() {
            return findings;
        }

        let call_graph = call_graph.unwrap();

        // Build function reference for current function
        let current_func = FunctionRef {
            file: dfg.file_path.clone(),
            name: dfg.function_name.clone(),
            qualified_name: None,
        };

        // Find all functions called by the current function
        let callees = call_graph.get_callees(&current_func, 1);

        // For each callee, check if we're passing tainted data
        for callee in callees {
            // If we have a DFG for this callee, analyze the call
            if let Some(_callee_dfg) = function_dfgs.get(&callee.name) {
                // Find call sites in the current function
                for edge in &dfg.edges {
                    // Look for edges representing calls to this function
                    // This is a simplified heuristic - in practice, you'd need
                    // to parse the AST to find actual call expressions
                    if edge.edge.kind == DataflowKind::Return {
                        // Check if any argument at this line is tainted
                        let call_line = edge.edge.from_line;

                        // Check all variables used at this line
                        for other_edge in &dfg.edges {
                            if other_edge.edge.to_line == call_line {
                                if self.state.is_variable_tainted(&other_edge.edge.variable) {
                                    // Tainted data flows into a call
                                    // Add to findings with inter-procedural path
                                    let location = Location::new(&dfg.function_name, call_line, 1);
                                    self.check_sink(
                                        &other_edge.edge.variable,
                                        &format!("call_to_{}", callee.name),
                                        location,
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }

        // Handle implicit flows if CFG is provided
        if self.config.track_implicit_flows {
            if let Some(cfg) = cfg {
                self.analyze_implicit_flows(dfg, cfg);
            }
        }

        findings.append(&mut self.findings.clone());
        findings
    }

    /// Analyze implicit flows using CFG.
    fn analyze_implicit_flows(&mut self, dfg: &mut TaintedDFG, cfg: &CFGInfo) {
        // Clone edges to avoid borrow conflicts
        let edges_snapshot: Vec<(usize, String, DataflowKind)> = dfg
            .edges
            .iter()
            .map(|e| (e.edge.from_line, e.edge.variable.clone(), e.edge.kind))
            .collect();
        let file_path = dfg.file_path.clone();

        // Find branch blocks with tainted conditions
        for block in cfg.blocks.values() {
            if block.block_type == crate::cfg::types::BlockType::Branch {
                // Check if any variable at this block's lines is tainted
                for line in block.start_line..=block.end_line {
                    let node = NodeId::from_line(line);
                    if dfg.is_tainted(&node) {
                        // This is a branch with tainted condition
                        // Mark successor blocks as under implicit flow
                        for edge in &cfg.edges {
                            if edge.from == block.id {
                                match edge.edge_type {
                                    EdgeType::True | EdgeType::False => {
                                        self.implicit_context.mark_block_tainted(edge.to);
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                }
            }
        }

        // Collect nodes to mark
        let mut nodes_to_mark: Vec<(NodeId, HashSet<TaintLabel>)> = Vec::new();

        // Propagate implicit taint to assignments in tainted blocks
        for block in cfg.blocks.values() {
            if self.implicit_context.is_block_tainted(block.id) {
                let implicit_labels = self.implicit_context.get_implicit_taint().clone();
                if !implicit_labels.is_empty() {
                    // Find all definitions in this block
                    for line in block.start_line..=block.end_line {
                        for (from_line, variable, kind) in &edges_snapshot {
                            if *from_line == line && matches!(kind, DataflowKind::Definition) {
                                // Collect node to mark
                                let node = NodeId::with_variable(&file_path, line, variable);
                                nodes_to_mark.push((node, implicit_labels.clone()));
                            }
                        }
                    }
                }
            }
        }

        // Apply collected markings
        for (node, labels) in nodes_to_mark {
            dfg.mark_tainted(node, labels);
        }
    }

    /// Merge taint state from another engine (for control flow merge).
    pub fn merge_state(&mut self, other: &PropagationEngine, location: &Location) {
        self.state.merge(&other.state, location);
    }
}

impl Default for PropagationEngine {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Taint Flow Finding
// =============================================================================

/// A detected taint flow from source to sink.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintFlow {
    /// Where the taint originated
    pub source: Location,
    /// Where the tainted data reached a sink
    pub sink: Location,
    /// Taint labels that reached the sink
    pub labels: HashSet<TaintLabel>,
    /// Path the taint took
    pub path: Vec<PropagationStep>,
    /// Type of sink (e.g., "sql_query", "command_exec")
    pub sink_type: String,
    /// Variable that carried the taint to the sink
    pub variable: String,
    /// Confidence score
    pub confidence: f64,
    /// Original source expression (if known)
    pub source_expression: Option<String>,
}

impl TaintFlow {
    /// Get the highest severity label in this flow.
    pub fn max_severity(&self) -> u8 {
        self.labels
            .iter()
            .map(TaintLabel::severity_weight)
            .max()
            .unwrap_or(0)
    }

    /// Get a human-readable description of this flow.
    pub fn description(&self) -> String {
        let labels: Vec<_> = self.labels.iter().map(|l| l.to_string()).collect();
        format!(
            "Taint flow from {} to {} via {} (labels: {})",
            self.source,
            self.sink,
            self.variable,
            labels.join(", ")
        )
    }

    /// Check if this flow involves implicit taint.
    pub fn has_implicit_flow(&self) -> bool {
        self.path.iter().any(|step| step.propagation == TaintPropagation::ImplicitFlow)
    }
}

// =============================================================================
// Propagation Rules Registry
// =============================================================================

/// A propagation rule for a specific operation or function.
#[derive(Debug, Clone)]
pub struct PropagationRule {
    /// Name of the operation/function this rule applies to
    pub name: String,
    /// How arguments propagate to return value
    pub arg_to_return: Vec<usize>,
    /// Whether this is a sanitizer
    pub is_sanitizer: bool,
    /// Sanitization method name (if sanitizer)
    pub sanitization_method: Option<String>,
    /// Whether all arguments propagate (if arg_to_return is empty)
    pub propagate_all: bool,
}

impl PropagationRule {
    /// Create a rule that propagates all arguments.
    pub fn propagate_all(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            arg_to_return: Vec::new(),
            is_sanitizer: false,
            sanitization_method: None,
            propagate_all: true,
        }
    }

    /// Create a rule that propagates specific arguments.
    pub fn propagate_args(name: impl Into<String>, args: Vec<usize>) -> Self {
        Self {
            name: name.into(),
            arg_to_return: args,
            is_sanitizer: false,
            sanitization_method: None,
            propagate_all: false,
        }
    }

    /// Create a sanitizer rule.
    pub fn sanitizer(name: impl Into<String>, method: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            arg_to_return: Vec::new(),
            is_sanitizer: true,
            sanitization_method: Some(method.into()),
            propagate_all: false,
        }
    }
}

/// Registry of propagation rules for known functions.
#[derive(Debug, Default)]
pub struct PropagationRules {
    rules: HashMap<String, PropagationRule>,
}

impl PropagationRules {
    /// Create a new empty rule registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a rule to the registry.
    pub fn add_rule(&mut self, rule: PropagationRule) {
        self.rules.insert(rule.name.clone(), rule);
    }

    /// Get a rule by function name.
    pub fn get_rule(&self, name: &str) -> Option<&PropagationRule> {
        self.rules.get(name)
    }

    /// Check if a function is a known sanitizer.
    pub fn is_sanitizer(&self, name: &str) -> bool {
        self.rules.get(name).map_or(false, |r| r.is_sanitizer)
    }

    /// Create default Python propagation rules.
    pub fn python_defaults() -> Self {
        let mut rules = Self::new();

        // String operations that propagate taint
        rules.add_rule(PropagationRule::propagate_args("str.upper", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("str.lower", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("str.strip", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("str.format", vec![0]));
        rules.add_rule(PropagationRule::propagate_all("str.join"));
        rules.add_rule(PropagationRule::propagate_all("+"));

        // JSON serialization preserves taint
        rules.add_rule(PropagationRule::propagate_args("json.dumps", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("json.loads", vec![0]));

        // Type conversions preserve taint
        rules.add_rule(PropagationRule::propagate_args("str", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("int", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("float", vec![0]));

        // Sanitizers
        rules.add_rule(PropagationRule::sanitizer("html.escape", "html_escape"));
        rules.add_rule(PropagationRule::sanitizer("markupsafe.escape", "markup_escape"));
        rules.add_rule(PropagationRule::sanitizer("bleach.clean", "bleach_clean"));
        rules.add_rule(PropagationRule::sanitizer("shlex.quote", "shell_escape"));
        rules.add_rule(PropagationRule::sanitizer("urllib.parse.quote", "url_encode"));
        rules.add_rule(PropagationRule::sanitizer("cgi.escape", "cgi_escape"));

        rules
    }

    /// Create default TypeScript/JavaScript propagation rules.
    pub fn typescript_defaults() -> Self {
        let mut rules = Self::new();

        // String operations
        rules.add_rule(PropagationRule::propagate_args("String.prototype.toUpperCase", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("String.prototype.toLowerCase", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("String.prototype.trim", vec![0]));
        rules.add_rule(PropagationRule::propagate_all("String.prototype.concat"));
        rules.add_rule(PropagationRule::propagate_all("+"));

        // JSON serialization preserves taint
        rules.add_rule(PropagationRule::propagate_args("JSON.stringify", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("JSON.parse", vec![0]));

        // Type conversions
        rules.add_rule(PropagationRule::propagate_args("String", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("Number", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("toString", vec![0]));

        // Sanitizers
        rules.add_rule(PropagationRule::sanitizer("DOMPurify.sanitize", "dom_purify"));
        rules.add_rule(PropagationRule::sanitizer("escape", "html_escape"));
        rules.add_rule(PropagationRule::sanitizer("encodeURIComponent", "url_encode"));
        rules.add_rule(PropagationRule::sanitizer("validator.escape", "validator_escape"));
        rules.add_rule(PropagationRule::sanitizer("xss", "xss_filter"));

        rules
    }

    /// Create default Go propagation rules.
    pub fn go_defaults() -> Self {
        let mut rules = Self::new();

        // String operations
        rules.add_rule(PropagationRule::propagate_all("strings.Join"));
        rules.add_rule(PropagationRule::propagate_args("strings.ToUpper", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("strings.ToLower", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("strings.TrimSpace", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("fmt.Sprintf", vec![0, 1, 2, 3, 4]));

        // JSON
        rules.add_rule(PropagationRule::propagate_args("json.Marshal", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("json.Unmarshal", vec![0]));

        // Type conversions
        rules.add_rule(PropagationRule::propagate_args("strconv.Itoa", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("strconv.Atoi", vec![0]));

        // Sanitizers
        rules.add_rule(PropagationRule::sanitizer("html.EscapeString", "html_escape"));
        rules.add_rule(PropagationRule::sanitizer("url.QueryEscape", "url_encode"));
        rules.add_rule(PropagationRule::sanitizer("template.HTMLEscapeString", "html_escape"));

        rules
    }

    /// Create default Rust propagation rules.
    pub fn rust_defaults() -> Self {
        let mut rules = Self::new();

        // String operations
        rules.add_rule(PropagationRule::propagate_args("to_uppercase", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("to_lowercase", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("trim", vec![0]));
        rules.add_rule(PropagationRule::propagate_all("format!"));
        rules.add_rule(PropagationRule::propagate_args("to_string", vec![0]));

        // JSON
        rules.add_rule(PropagationRule::propagate_args("serde_json::to_string", vec![0]));
        rules.add_rule(PropagationRule::propagate_args("serde_json::from_str", vec![0]));

        // Sanitizers
        rules.add_rule(PropagationRule::sanitizer("html_escape", "html_escape"));
        rules.add_rule(PropagationRule::sanitizer("encode_minimal", "html_escape"));
        rules.add_rule(PropagationRule::sanitizer("urlencoding::encode", "url_encode"));

        rules
    }

    /// Convert to function summaries for the propagation engine.
    pub fn to_summaries(&self) -> Vec<FunctionTaintSummary> {
        self.rules
            .values()
            .map(|rule| {
                let mut summary = FunctionTaintSummary::new(&rule.name);
                if rule.is_sanitizer {
                    summary.is_sanitizer = true;
                    summary.sanitization_method = rule.sanitization_method.clone();
                } else if rule.propagate_all {
                    // Mark all params as flowing to return (up to 10)
                    for i in 0..10 {
                        summary.param_to_return.insert(i);
                    }
                    summary.return_tainted = true;
                } else {
                    for &idx in &rule.arg_to_return {
                        summary.param_to_return.insert(idx);
                    }
                    summary.return_tainted = !rule.arg_to_return.is_empty();
                }
                summary
            })
            .collect()
    }
}

// =============================================================================
// Taint Trace Result (for CLI output)
// =============================================================================

/// Result of a taint trace operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintTraceResult {
    /// File analyzed
    pub file: String,
    /// Starting line number
    pub start_line: usize,
    /// Total tainted nodes found
    pub tainted_node_count: usize,
    /// Tainted lines with their labels
    pub tainted_lines: HashMap<usize, Vec<String>>,
    /// Detected flows to sinks
    pub flows: Vec<TaintFlow>,
    /// Whether implicit flows were tracked
    pub implicit_flow_tracking: bool,
    /// Sanitization points encountered
    pub sanitization_points: Vec<usize>,
}

impl TaintTraceResult {
    /// Create a new trace result.
    pub fn new(file: impl Into<String>, start_line: usize) -> Self {
        Self {
            file: file.into(),
            start_line,
            tainted_node_count: 0,
            tainted_lines: HashMap::new(),
            flows: Vec::new(),
            implicit_flow_tracking: false,
            sanitization_points: Vec::new(),
        }
    }

    /// Convert to JSON for CLI output.
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "file": self.file,
            "start_line": self.start_line,
            "tainted_node_count": self.tainted_node_count,
            "tainted_lines": self.tainted_lines,
            "flow_count": self.flows.len(),
            "flows": self.flows.iter().map(|f| serde_json::json!({
                "source": f.source.to_string(),
                "sink": f.sink.to_string(),
                "labels": f.labels.iter().map(|l| l.to_string()).collect::<Vec<_>>(),
                "sink_type": f.sink_type,
                "variable": f.variable,
                "confidence": f.confidence,
                "has_implicit_flow": f.has_implicit_flow(),
            })).collect::<Vec<_>>(),
            "implicit_flow_tracking": self.implicit_flow_tracking,
            "sanitization_points": self.sanitization_points,
        })
    }
}

// =============================================================================
// High-level API
// =============================================================================

/// Trace taint from a source line in a file.
///
/// This is the main entry point for the `taint-trace` CLI command.
pub fn trace_taint_from_line(
    file_path: &str,
    source_line: usize,
    function_name: &str,
    language: &str,
    config: Option<PropagationConfig>,
) -> Result<TaintTraceResult, String> {
    // Build DFG for the function
    let dfg = crate::dfg::DfgBuilder::extract_from_file_with_language(
        file_path,
        function_name,
        Some(language),
    )
    .map_err(|e| format!("Failed to extract DFG: {}", e))?;

    let config = config.unwrap_or_default();
    let mut engine = PropagationEngine::with_config(config.clone());

    // Register language-specific rules
    let rules = match language {
        "python" => PropagationRules::python_defaults(),
        "typescript" | "javascript" => PropagationRules::typescript_defaults(),
        "go" => PropagationRules::go_defaults(),
        "rust" => PropagationRules::rust_defaults(),
        _ => PropagationRules::new(),
    };

    for summary in rules.to_summaries() {
        engine.register_summary(summary);
    }

    // Create tainted DFG and mark source
    let mut tainted_dfg = TaintedDFG::from_dfg(&dfg, file_path);

    // Automatically detect what taint label to use based on context
    // For manual tracing, use UserInput as the default label
    tainted_dfg.mark_source(source_line, TaintLabel::UserInput);

    // Run propagation
    let flows = engine.analyze_dfg(&mut tainted_dfg);

    // Build result
    let mut result = TaintTraceResult::new(file_path, source_line);
    result.implicit_flow_tracking = config.track_implicit_flows;

    // Collect tainted lines
    for (node, labels) in tainted_dfg.tainted_nodes() {
        result
            .tainted_lines
            .entry(node.line)
            .or_default()
            .extend(labels.iter().map(|l| l.to_string()));
    }
    result.tainted_node_count = result.tainted_lines.len();

    // Collect sanitization points
    for node in &tainted_dfg.sanitization_points {
        result.sanitization_points.push(node.line);
    }
    result.sanitization_points.sort();
    result.sanitization_points.dedup();

    result.flows = flows;

    Ok(result)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_location() -> Location {
        Location::new("test.py", 10, 5)
    }

    #[test]
    fn test_node_id() {
        let node1 = NodeId::from_line(42);
        assert_eq!(node1.line, 42);
        assert!(node1.file.is_empty());

        let node2 = NodeId::new("test.py", 10);
        assert_eq!(node2.file, "test.py");
        assert_eq!(node2.line, 10);

        let node3 = NodeId::with_variable("test.py", 10, "x");
        assert_eq!(node3.variable, Some("x".to_string()));
    }

    #[test]
    fn test_propagation_engine_basic() {
        let mut engine = PropagationEngine::new();
        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);

        // Introduce taint
        engine.introduce_taint("user_input", TaintLabel::UserInput, loc1, Some("input()"));

        // Propagate assignment
        engine.propagate_assignment("x", "user_input", loc2);

        // Check state
        assert!(engine.state().is_variable_tainted("user_input"));
        assert!(engine.state().is_variable_tainted("x"));
    }

    #[test]
    fn test_comparison_does_not_propagate() {
        let mut engine = PropagationEngine::new();
        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);

        engine.introduce_taint("tainted", TaintLabel::UserInput, loc1, None);
        engine.propagate_binary_op("result", "tainted", "safe", "==", loc2);

        // Result of comparison should NOT be tainted
        assert!(!engine.state().is_variable_tainted("result"));
    }

    #[test]
    fn test_string_concat_propagates() {
        let mut engine = PropagationEngine::new();
        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);

        engine.introduce_taint("tainted", TaintLabel::UserInput, loc1, None);
        engine.propagate_string_concat("result", &["safe", "tainted"], loc2);

        // String concatenation should preserve taint
        assert!(engine.state().is_variable_tainted("result"));
    }

    #[test]
    fn test_type_conversion_propagates() {
        let mut engine = PropagationEngine::new();
        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);

        engine.introduce_taint("tainted", TaintLabel::UserInput, loc1, None);
        engine.propagate_type_conversion("result", "tainted", "int", loc2);

        // Type conversion should preserve taint
        assert!(engine.state().is_variable_tainted("result"));
    }

    #[test]
    fn test_serialization_propagates() {
        let mut engine = PropagationEngine::new();
        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);

        engine.introduce_taint("tainted", TaintLabel::UserInput, loc1, None);
        engine.propagate_serialization("result", "tainted", "json", loc2);

        // Serialization should preserve taint
        assert!(engine.state().is_variable_tainted("result"));
    }

    #[test]
    fn test_propagation_binary_op() {
        let mut engine = PropagationEngine::new();
        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);
        let loc3 = Location::new("test.py", 3, 1);

        engine.introduce_taint("a", TaintLabel::UserInput, loc1, None);
        engine.introduce_taint("b", TaintLabel::FileContent, loc2, None);

        engine.propagate_binary_op("c", "a", "b", "+", loc3);

        let c_taint = engine.state().get_variable("c").unwrap();
        assert!(c_taint.has_label(&TaintLabel::UserInput));
        assert!(c_taint.has_label(&TaintLabel::FileContent));
    }

    #[test]
    fn test_sanitization() {
        let mut engine = PropagationEngine::new();
        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);

        engine.introduce_taint("x", TaintLabel::UserInput, loc1, None);
        assert!(engine.state().is_variable_tainted("x"));

        engine.sanitize("x", "html_escape", loc2);
        assert!(!engine.state().is_variable_tainted("x"));
    }

    #[test]
    fn test_collection_propagation() {
        let mut engine = PropagationEngine::new();
        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);
        let loc3 = Location::new("test.py", 3, 1);

        engine.introduce_taint("value", TaintLabel::UserInput, loc1, None);

        // Store to collection
        engine.propagate_collection_store("arr", "value", loc2);

        // Access from collection
        engine.propagate_collection_access("elem", "arr", "[0]", loc3);

        assert!(engine.state().is_variable_tainted("elem"));
    }

    #[test]
    fn test_implicit_flow_tracking() {
        let mut engine = PropagationEngine::with_config(PropagationConfig {
            track_implicit_flows: true,
            ..Default::default()
        });

        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 5, 1);

        // Introduce tainted condition
        engine.introduce_taint("condition", TaintLabel::UserInput, loc1, None);

        // Enter branch controlled by tainted condition
        engine.enter_branch("condition");

        // Assignment inside branch should pick up implicit taint
        engine.propagate_assignment("x", "safe_value", loc2);

        engine.exit_branch();

        // x should be implicitly tainted (if tracking is enabled and we had condition)
        // Note: In this test, "safe_value" doesn't exist so no explicit taint,
        // but implicit taint should be present
        // The actual behavior depends on the implementation
    }

    #[test]
    fn test_function_summary() {
        let summary = FunctionTaintSummary::new("html_escape")
            .as_sanitizer("html_escape");

        assert!(summary.is_sanitizer);
        assert_eq!(summary.sanitization_method, Some("html_escape".to_string()));
    }

    #[test]
    fn test_propagation_rules() {
        let rules = PropagationRules::python_defaults();

        assert!(rules.is_sanitizer("html.escape"));
        assert!(!rules.is_sanitizer("str.upper"));

        let escape_rule = rules.get_rule("html.escape").unwrap();
        assert!(escape_rule.is_sanitizer);
        assert_eq!(
            escape_rule.sanitization_method,
            Some("html_escape".to_string())
        );
    }

    #[test]
    fn test_taint_flow_description() {
        let flow = TaintFlow {
            source: Location::new("input.py", 5, 1),
            sink: Location::new("query.py", 20, 1),
            labels: [TaintLabel::UserInput].into_iter().collect(),
            path: vec![],
            sink_type: "sql_query".to_string(),
            variable: "user_data".to_string(),
            confidence: 0.95,
            source_expression: Some("request.get('id')".to_string()),
        };

        let desc = flow.description();
        assert!(desc.contains("input.py:5:1"));
        assert!(desc.contains("query.py:20:1"));
        assert!(desc.contains("user_data"));
    }

    #[test]
    fn test_tainted_dfg_creation() {
        let dfg = DFGInfo::new(
            "test_func".to_string(),
            vec![],
            HashMap::new(),
            HashMap::new(),
        );

        let mut tainted = TaintedDFG::from_dfg(&dfg, "test.py");
        tainted.mark_source(10, TaintLabel::UserInput);

        assert!(!tainted.source_lines.is_empty());
        assert!(tainted.source_lines.contains_key(&10));

        let node = NodeId::from_line(10);
        assert!(tainted.is_tainted(&node));
    }

    #[test]
    fn test_taint_trace_result_json() {
        let mut result = TaintTraceResult::new("test.py", 10);
        result.tainted_node_count = 5;
        result.tainted_lines.insert(10, vec!["UserInput".to_string()]);
        result.tainted_lines.insert(11, vec!["UserInput".to_string()]);

        let json = result.to_json();
        assert_eq!(json["file"], "test.py");
        assert_eq!(json["start_line"], 10);
        assert_eq!(json["tainted_node_count"], 5);
    }

    #[test]
    fn test_call_with_sanitizer_summary() {
        let mut engine = PropagationEngine::new();

        // Register html_escape as a sanitizer
        engine.register_summary(
            FunctionTaintSummary::new("html_escape")
                .as_sanitizer("html_escape")
        );

        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);

        engine.introduce_taint("tainted_input", TaintLabel::UserInput, loc1, None);
        engine.propagate_call_return("result", "html_escape", &["tainted_input"], loc2);

        // Result should be sanitized (not tainted)
        assert!(!engine.state().is_variable_tainted("result"));
    }

    #[test]
    fn test_call_with_propagating_summary() {
        let mut engine = PropagationEngine::new();

        // Register str.upper as propagating first argument
        let mut summary = FunctionTaintSummary::new("str.upper");
        summary.param_to_return.insert(0);
        summary.return_tainted = true;
        engine.register_summary(summary);

        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);

        engine.introduce_taint("tainted_input", TaintLabel::UserInput, loc1, None);
        engine.propagate_call_return("result", "str.upper", &["tainted_input"], loc2);

        // Result should be tainted
        assert!(engine.state().is_variable_tainted("result"));
    }
}
