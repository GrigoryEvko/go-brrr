//! Very Busy Expressions (Anticipable Expressions) Data Flow Analysis.
//!
//! An expression is "very busy" (anticipable) at a program point if it will
//! definitely be computed on ALL paths from that point before any variable
//! in the expression is redefined.
//!
//! # Data Flow Equations (Backward Analysis with Intersection)
//!
//! - USE[B] = expressions computed in B before any operand is redefined
//! - KILL[B] = expressions containing variables defined in B
//! - OUT[B] = INTERSECTION(IN[S]) for all successors S
//! - IN[B] = USE[B] UNION (OUT[B] - KILL[B])
//!
//! # Key Difference from Live Variables
//!
//! - Live Variables: UNION at join points (may be used on some path)
//! - Very Busy: INTERSECTION at join points (must be used on all paths)
//!
//! # Applications
//!
//! - **Code Hoisting**: If expression is very busy at point P, compute it at P
//!   instead of at multiple points downstream. This reduces code size and
//!   can improve performance by computing once instead of multiple times.
//!
//! - **Partial Redundancy Elimination (PRE)**: Combined with available expressions:
//!   - Available: computed on all paths TO a point
//!   - Very Busy: computed on all paths FROM a point
//!   Together they enable optimal expression placement.
//!
//! - **Speculative Computation**: Identify expressions that can be safely
//!   computed early even if not needed on all paths.
//!
//! # Example
//!
//! ```ignore
//! if cond:
//!     x = a + b  # a + b very busy before if
//!     ...
//! else:
//!     y = a + b  # same expression
//!     ...
//! # Can hoist: t = a + b; if cond: x = t else: y = t
//! ```
//!
//! # Caveats
//!
//! - **Side Effects**: Cannot hoist expressions with side effects (function calls
//!   that modify state, I/O operations, etc.)
//! - **Exceptions**: Cannot hoist expressions that may raise exceptions unless
//!   they would be raised on all paths anyway
//! - **Short-Circuit**: Boolean operators with short-circuit evaluation need
//!   special handling

use std::collections::{HashSet, VecDeque};

use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

use crate::cfg::{extract_with_language, BlockId, CFGInfo};
use crate::dataflow::common::is_valid_identifier;
use crate::error::Result;

// =============================================================================
// Types
// =============================================================================

/// Unique identifier for an expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ExprId(pub usize);

/// Location in source code.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Location {
    /// Line number (1-indexed).
    pub line: usize,
    /// Column number (0-indexed, optional).
    pub column: Option<usize>,
    /// Block ID in CFG.
    pub block_id: BlockId,
}

impl Location {
    /// Create a new location.
    #[inline]
    pub fn new(line: usize, block_id: BlockId) -> Self {
        Self {
            line,
            column: None,
            block_id,
        }
    }

    /// Create a new location with column.
    #[inline]
    pub fn with_column(line: usize, column: usize, block_id: BlockId) -> Self {
        Self {
            line,
            column: Some(column),
            block_id,
        }
    }
}

/// Binary operators for expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl BinaryOp {
    /// Parse operator from string representation.
    #[must_use]
    pub fn from_str(s: &str) -> Option<Self> {
        match s.trim() {
            "+" => Some(BinaryOp::Add),
            "-" => Some(BinaryOp::Sub),
            "*" => Some(BinaryOp::Mul),
            "/" => Some(BinaryOp::Div),
            "%" | "mod" => Some(BinaryOp::Mod),
            "&" => Some(BinaryOp::BitAnd),
            "|" => Some(BinaryOp::BitOr),
            "^" => Some(BinaryOp::BitXor),
            "<<" => Some(BinaryOp::Shl),
            ">>" => Some(BinaryOp::Shr),
            "==" => Some(BinaryOp::Eq),
            "!=" | "<>" => Some(BinaryOp::Ne),
            "<" => Some(BinaryOp::Lt),
            "<=" => Some(BinaryOp::Le),
            ">" => Some(BinaryOp::Gt),
            ">=" => Some(BinaryOp::Ge),
            "&&" | "and" => Some(BinaryOp::And),
            "||" | "or" => Some(BinaryOp::Or),
            _ => None,
        }
    }

    /// Check if this operator has short-circuit semantics.
    ///
    /// Short-circuit operators may not evaluate their right operand,
    /// so we cannot hoist them freely.
    #[must_use]
    pub fn is_short_circuit(&self) -> bool {
        matches!(self, BinaryOp::And | BinaryOp::Or)
    }

    /// Check if this operator can raise exceptions (e.g., division by zero).
    #[must_use]
    pub fn can_raise(&self) -> bool {
        matches!(self, BinaryOp::Div | BinaryOp::Mod)
    }
}

impl std::fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinaryOp::Add => "+",
            BinaryOp::Sub => "-",
            BinaryOp::Mul => "*",
            BinaryOp::Div => "/",
            BinaryOp::Mod => "%",
            BinaryOp::BitAnd => "&",
            BinaryOp::BitOr => "|",
            BinaryOp::BitXor => "^",
            BinaryOp::Shl => "<<",
            BinaryOp::Shr => ">>",
            BinaryOp::Eq => "==",
            BinaryOp::Ne => "!=",
            BinaryOp::Lt => "<",
            BinaryOp::Le => "<=",
            BinaryOp::Gt => ">",
            BinaryOp::Ge => ">=",
            BinaryOp::And => "and",
            BinaryOp::Or => "or",
        };
        write!(f, "{}", s)
    }
}

/// Unary operators for expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UnaryOp {
    Neg,
    Not,
    BitNot,
}

impl UnaryOp {
    /// Parse operator from string representation.
    #[must_use]
    pub fn from_str(s: &str) -> Option<Self> {
        match s.trim() {
            "-" => Some(UnaryOp::Neg),
            "!" | "not" => Some(UnaryOp::Not),
            "~" => Some(UnaryOp::BitNot),
            _ => None,
        }
    }
}

impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            UnaryOp::Neg => "-",
            UnaryOp::Not => "not",
            UnaryOp::BitNot => "~",
        };
        write!(f, "{}", s)
    }
}

/// An expression that can be tracked for very busy analysis.
///
/// We track binary and unary expressions because:
/// 1. They are the primary targets for code hoisting
/// 2. They have well-defined operands for kill analysis
/// 3. They are pure (no side effects) unlike function calls
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Expression {
    /// Binary operation: left op right
    Binary {
        left: Box<Operand>,
        op: BinaryOp,
        right: Box<Operand>,
    },
    /// Unary operation: op operand
    Unary { op: UnaryOp, operand: Box<Operand> },
    /// Array/subscript access: base[index]
    Subscript {
        base: Box<Operand>,
        index: Box<Operand>,
    },
    /// Field/attribute access: base.field
    Field { base: Box<Operand>, field: String },
}

impl Expression {
    /// Get all variables referenced in this expression.
    pub fn variables(&self) -> Vec<String> {
        let mut vars = Vec::new();
        self.collect_variables(&mut vars);
        vars
    }

    /// Collect variables into the provided vector.
    fn collect_variables(&self, vars: &mut Vec<String>) {
        match self {
            Expression::Binary { left, right, .. } => {
                left.collect_variables(vars);
                right.collect_variables(vars);
            }
            Expression::Unary { operand, .. } => {
                operand.collect_variables(vars);
            }
            Expression::Subscript { base, index } => {
                base.collect_variables(vars);
                index.collect_variables(vars);
            }
            Expression::Field { base, .. } => {
                base.collect_variables(vars);
            }
        }
    }

    /// Check if this expression has potential side effects.
    ///
    /// Expressions with side effects cannot be safely hoisted.
    pub fn has_side_effects(&self) -> bool {
        // Pure expressions (arithmetic, comparisons, field access) are side-effect free
        // Function calls would have side effects but we don't track them as expressions
        false
    }

    /// Check if this expression may raise an exception.
    ///
    /// Expressions that may raise exceptions need careful hoisting consideration.
    pub fn may_raise(&self) -> bool {
        match self {
            Expression::Binary { op, .. } => op.can_raise(),
            Expression::Subscript { .. } => true, // IndexError possible
            _ => false,
        }
    }

    /// Check if this expression uses short-circuit evaluation.
    pub fn is_short_circuit(&self) -> bool {
        match self {
            Expression::Binary { op, .. } => op.is_short_circuit(),
            _ => false,
        }
    }

    /// Get a canonical string representation for display.
    pub fn to_string_repr(&self) -> String {
        match self {
            Expression::Binary { left, op, right } => {
                format!(
                    "{} {} {}",
                    left.to_string_repr(),
                    op,
                    right.to_string_repr()
                )
            }
            Expression::Unary { op, operand } => {
                format!("{}{}", op, operand.to_string_repr())
            }
            Expression::Subscript { base, index } => {
                format!("{}[{}]", base.to_string_repr(), index.to_string_repr())
            }
            Expression::Field { base, field } => {
                format!("{}.{}", base.to_string_repr(), field)
            }
        }
    }
}

impl std::fmt::Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string_repr())
    }
}

/// An operand in an expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Operand {
    /// Variable reference
    Variable(String),
    /// Integer literal
    IntLiteral(i64),
    /// Float literal (stored as bits for hashing)
    FloatLiteral(u64),
    /// String literal
    StringLiteral(String),
    /// Boolean literal
    BoolLiteral(bool),
    /// Nested expression
    Expr(Expression),
}

impl Operand {
    /// Collect variables from this operand.
    fn collect_variables(&self, vars: &mut Vec<String>) {
        match self {
            Operand::Variable(name) => vars.push(name.clone()),
            Operand::Expr(expr) => expr.collect_variables(vars),
            _ => {}
        }
    }

    /// Get string representation.
    pub fn to_string_repr(&self) -> String {
        match self {
            Operand::Variable(name) => name.clone(),
            Operand::IntLiteral(i) => i.to_string(),
            Operand::FloatLiteral(bits) => f64::from_bits(*bits).to_string(),
            Operand::StringLiteral(s) => format!("\"{}\"", s),
            Operand::BoolLiteral(b) => b.to_string(),
            Operand::Expr(e) => format!("({})", e.to_string_repr()),
        }
    }
}

/// Information about an expression occurrence in the code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExpressionInfo {
    /// Unique expression ID.
    pub expr_id: ExprId,
    /// The expression itself.
    pub expression: Expression,
    /// All locations where this expression is computed.
    pub locations: Vec<Location>,
    /// Variables used in this expression.
    pub variables: Vec<String>,
    /// Whether the expression has side effects.
    pub has_side_effects: bool,
    /// Whether the expression may raise exceptions.
    pub may_raise: bool,
    /// Whether the expression uses short-circuit evaluation.
    pub is_short_circuit: bool,
}

/// Benefit type for hoisting an expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HoistingBenefit {
    /// Expression computed in multiple branches can be factored out.
    ReduceCodeSize,
    /// Expression can be moved out of a loop.
    ReduceLatency,
    /// Expression is independent and can be computed in parallel.
    EnableParallelism,
    /// Expression can be computed speculatively.
    SpeculativeComputation,
}

impl std::fmt::Display for HoistingBenefit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HoistingBenefit::ReduceCodeSize => write!(f, "reduce_code_size"),
            HoistingBenefit::ReduceLatency => write!(f, "reduce_latency"),
            HoistingBenefit::EnableParallelism => write!(f, "enable_parallelism"),
            HoistingBenefit::SpeculativeComputation => write!(f, "speculative_computation"),
        }
    }
}

/// A hoisting opportunity detected by the analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HoistingOpportunity {
    /// The expression that can be hoisted.
    pub expression: Expression,
    /// Current locations where the expression is computed.
    pub current_locations: Vec<Location>,
    /// Location to hoist to.
    pub hoist_to: Location,
    /// Type of benefit from hoisting.
    pub benefit: HoistingBenefit,
    /// Estimated code size reduction (in expression occurrences).
    pub occurrences_saved: usize,
    /// Safety notes (e.g., exception handling considerations).
    pub safety_notes: Vec<String>,
}

// =============================================================================
// BitSet - Efficient set operations for data flow analysis
// =============================================================================

/// A simple bit set for efficient set operations.
///
/// Uses a Vec<u64> as backing storage. Each bit represents membership
/// of an element in the set. Operations are O(n/64) where n is the
/// maximum element value.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitSet {
    /// Backing storage: each u64 holds 64 bits.
    bits: Vec<u64>,
    /// Number of elements that can be stored.
    capacity: usize,
}

impl BitSet {
    /// Create a new empty BitSet with given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        let num_words = (capacity + 63) / 64;
        Self {
            bits: vec![0; num_words],
            capacity,
        }
    }

    /// Create a BitSet with all bits set (universe).
    pub fn full(capacity: usize) -> Self {
        let num_words = (capacity + 63) / 64;
        let mut bits = vec![u64::MAX; num_words];
        // Clear bits beyond capacity in the last word
        if capacity % 64 != 0 {
            let last_word_bits = capacity % 64;
            bits[num_words - 1] = (1u64 << last_word_bits) - 1;
        }
        Self { bits, capacity }
    }

    /// Insert an element. Returns true if the element was not already present.
    #[inline]
    pub fn insert(&mut self, elem: usize) -> bool {
        if elem >= self.capacity {
            return false;
        }
        let word_idx = elem / 64;
        let bit_idx = elem % 64;
        let mask = 1u64 << bit_idx;
        let was_present = (self.bits[word_idx] & mask) != 0;
        self.bits[word_idx] |= mask;
        !was_present
    }

    /// Remove an element. Returns true if the element was present.
    #[inline]
    pub fn remove(&mut self, elem: usize) -> bool {
        if elem >= self.capacity {
            return false;
        }
        let word_idx = elem / 64;
        let bit_idx = elem % 64;
        let mask = 1u64 << bit_idx;
        let was_present = (self.bits[word_idx] & mask) != 0;
        self.bits[word_idx] &= !mask;
        was_present
    }

    /// Check if an element is in the set.
    #[inline]
    pub fn contains(&self, elem: usize) -> bool {
        if elem >= self.capacity {
            return false;
        }
        let word_idx = elem / 64;
        let bit_idx = elem % 64;
        (self.bits[word_idx] & (1u64 << bit_idx)) != 0
    }

    /// Union: self = self | other
    #[inline]
    pub fn union_with(&mut self, other: &BitSet) {
        for (a, b) in self.bits.iter_mut().zip(other.bits.iter()) {
            *a |= *b;
        }
    }

    /// Intersection: self = self & other
    #[inline]
    pub fn intersect_with(&mut self, other: &BitSet) {
        for (a, b) in self.bits.iter_mut().zip(other.bits.iter()) {
            *a &= *b;
        }
    }

    /// Difference: self = self - other
    #[inline]
    pub fn difference_with(&mut self, other: &BitSet) {
        for (a, b) in self.bits.iter_mut().zip(other.bits.iter()) {
            *a &= !*b;
        }
    }

    /// Check if the set is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.bits.iter().all(|&w| w == 0)
    }

    /// Count the number of elements.
    #[inline]
    pub fn len(&self) -> usize {
        self.bits.iter().map(|w| w.count_ones() as usize).sum()
    }

    /// Clear all elements.
    #[inline]
    pub fn clear(&mut self) {
        for w in &mut self.bits {
            *w = 0;
        }
    }

    /// Set all elements (make universe).
    #[inline]
    pub fn fill(&mut self) {
        for w in &mut self.bits {
            *w = u64::MAX;
        }
        // Clear bits beyond capacity in the last word
        if self.capacity % 64 != 0 {
            let last_word_bits = self.capacity % 64;
            if let Some(last) = self.bits.last_mut() {
                *last = (1u64 << last_word_bits) - 1;
            }
        }
    }

    /// Copy contents from another BitSet.
    #[inline]
    pub fn copy_from(&mut self, other: &BitSet) {
        for (a, b) in self.bits.iter_mut().zip(other.bits.iter()) {
            *a = *b;
        }
    }

    /// Iterate over all elements in the set.
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        let capacity = self.capacity;
        self.bits
            .iter()
            .enumerate()
            .flat_map(move |(word_idx, &word)| {
                (0..64).filter_map(move |bit_idx| {
                    if (word & (1u64 << bit_idx)) != 0 {
                        let elem = word_idx * 64 + bit_idx;
                        if elem < capacity {
                            Some(elem)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
            })
    }
}

impl Default for BitSet {
    fn default() -> Self {
        Self::with_capacity(0)
    }
}

// =============================================================================
// Very Busy Expressions Result
// =============================================================================

/// Result of very busy expressions analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VeryBusyExpressionsResult {
    /// Function name analyzed.
    pub function_name: String,
    /// All expressions found in the function.
    pub expressions: Vec<ExpressionInfo>,
    /// Expressions busy at block entry (expression IDs).
    pub busy_in: FxHashMap<BlockId, BitSet>,
    /// Expressions busy at block exit (expression IDs).
    pub busy_out: FxHashMap<BlockId, BitSet>,
    /// Detected hoisting opportunities.
    pub hoisting_opportunities: Vec<HoistingOpportunity>,
    /// USE sets per block (expressions computed before kill).
    pub use_sets: FxHashMap<BlockId, BitSet>,
    /// KILL sets per block (expressions killed by definitions).
    pub kill_sets: FxHashMap<BlockId, BitSet>,
    /// Number of iterations to reach fixpoint.
    pub iterations: usize,
    /// Analysis time in microseconds.
    pub analysis_time_us: u64,
}

impl VeryBusyExpressionsResult {
    /// Get expressions that are busy at a specific block's entry.
    pub fn busy_at_entry(&self, block_id: BlockId) -> Vec<&Expression> {
        self.busy_in
            .get(&block_id)
            .map(|bits| {
                bits.iter()
                    .filter_map(|idx| self.expressions.get(idx).map(|info| &info.expression))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Get expressions that are busy at a specific block's exit.
    pub fn busy_at_exit(&self, block_id: BlockId) -> Vec<&Expression> {
        self.busy_out
            .get(&block_id)
            .map(|bits| {
                bits.iter()
                    .filter_map(|idx| self.expressions.get(idx).map(|info| &info.expression))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Check if an expression is very busy at a point (block entry).
    pub fn is_busy_at(&self, expr: &Expression, block_id: BlockId) -> bool {
        // Find the expression index
        if let Some(idx) = self
            .expressions
            .iter()
            .position(|info| &info.expression == expr)
        {
            self.busy_in
                .get(&block_id)
                .map(|bits| bits.contains(idx))
                .unwrap_or(false)
        } else {
            false
        }
    }

    /// Get hoisting opportunities filtered by benefit type.
    pub fn opportunities_by_benefit(&self, benefit: HoistingBenefit) -> Vec<&HoistingOpportunity> {
        self.hoisting_opportunities
            .iter()
            .filter(|opp| opp.benefit == benefit)
            .collect()
    }

    /// Convert to JSON value for output.
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "function_name": self.function_name,
            "expressions": self.expressions.iter().map(|info| {
                serde_json::json!({
                    "id": info.expr_id.0,
                    "expression": info.expression.to_string_repr(),
                    "locations": info.locations.iter().map(|loc| {
                        serde_json::json!({
                            "line": loc.line,
                            "block": loc.block_id.0,
                        })
                    }).collect::<Vec<_>>(),
                    "variables": info.variables,
                    "has_side_effects": info.has_side_effects,
                    "may_raise": info.may_raise,
                    "is_short_circuit": info.is_short_circuit,
                })
            }).collect::<Vec<_>>(),
            "busy_in": self.busy_in.iter().map(|(block_id, bits)| {
                (block_id.0.to_string(), bits.iter().collect::<Vec<_>>())
            }).collect::<FxHashMap<_, _>>(),
            "busy_out": self.busy_out.iter().map(|(block_id, bits)| {
                (block_id.0.to_string(), bits.iter().collect::<Vec<_>>())
            }).collect::<FxHashMap<_, _>>(),
            "hoisting_opportunities": self.hoisting_opportunities.iter().map(|opp| {
                serde_json::json!({
                    "expression": opp.expression.to_string_repr(),
                    "current_locations": opp.current_locations.iter().map(|loc| {
                        serde_json::json!({
                            "line": loc.line,
                            "block": loc.block_id.0,
                        })
                    }).collect::<Vec<_>>(),
                    "hoist_to": {
                        "line": opp.hoist_to.line,
                        "block": opp.hoist_to.block_id.0,
                    },
                    "benefit": opp.benefit.to_string(),
                    "occurrences_saved": opp.occurrences_saved,
                    "safety_notes": opp.safety_notes,
                })
            }).collect::<Vec<_>>(),
            "metrics": {
                "expression_count": self.expressions.len(),
                "hoisting_count": self.hoisting_opportunities.len(),
                "iterations": self.iterations,
                "analysis_time_us": self.analysis_time_us,
            }
        })
    }

    /// Convert to compact text format for CLI output.
    pub fn to_text(&self) -> String {
        let mut output = String::new();

        output.push_str(&format!("Very Busy Expressions: {}\n", self.function_name));
        output.push_str(&"=".repeat(50));
        output.push('\n');

        // Expressions
        output.push_str(&format!("\nExpressions ({}):\n", self.expressions.len()));
        for info in &self.expressions {
            let locations: Vec<_> = info.locations.iter().map(|l| l.line).collect();
            let mut flags = Vec::new();
            if info.may_raise {
                flags.push("may_raise");
            }
            if info.is_short_circuit {
                flags.push("short_circuit");
            }
            let flag_str = if flags.is_empty() {
                String::new()
            } else {
                format!(" [{}]", flags.join(", "))
            };
            output.push_str(&format!(
                "  [{}] {} at lines {:?}{}\n",
                info.expr_id.0,
                info.expression.to_string_repr(),
                locations,
                flag_str
            ));
        }

        // Hoisting opportunities
        if !self.hoisting_opportunities.is_empty() {
            output.push_str(&format!(
                "\nHoisting Opportunities ({}):\n",
                self.hoisting_opportunities.len()
            ));
            for opp in &self.hoisting_opportunities {
                let current_lines: Vec<_> = opp.current_locations.iter().map(|l| l.line).collect();
                output.push_str(&format!(
                    "  {} (lines {:?} -> line {}, benefit: {}, saves {} occurrences)\n",
                    opp.expression.to_string_repr(),
                    current_lines,
                    opp.hoist_to.line,
                    opp.benefit,
                    opp.occurrences_saved
                ));
                for note in &opp.safety_notes {
                    output.push_str(&format!("    Note: {}\n", note));
                }
            }
        }

        // Busy sets per block
        output.push_str("\nBusy Expressions per Block:\n");
        let mut block_ids: Vec<_> = self.busy_in.keys().collect();
        block_ids.sort_by_key(|b| b.0);

        for block_id in block_ids {
            let busy_in: Vec<_> = self
                .busy_in
                .get(block_id)
                .map(|bits| {
                    bits.iter()
                        .filter_map(|idx| self.expressions.get(idx))
                        .map(|info| info.expression.to_string_repr())
                        .collect()
                })
                .unwrap_or_default();
            let busy_out: Vec<_> = self
                .busy_out
                .get(block_id)
                .map(|bits| {
                    bits.iter()
                        .filter_map(|idx| self.expressions.get(idx))
                        .map(|info| info.expression.to_string_repr())
                        .collect()
                })
                .unwrap_or_default();

            output.push_str(&format!(
                "  Block {}: IN={:?}, OUT={:?}\n",
                block_id.0, busy_in, busy_out
            ));
        }

        // Metrics
        output.push_str(&format!(
            "\nMetrics: {} expressions, {} hoisting opportunities, {} iterations, {}us\n",
            self.expressions.len(),
            self.hoisting_opportunities.len(),
            self.iterations,
            self.analysis_time_us
        ));

        output
    }
}

// =============================================================================
// Expression Extraction
// =============================================================================

/// Extract expressions from code statements.
struct ExpressionExtractor;

impl ExpressionExtractor {
    /// Extract expressions from a statement.
    ///
    /// Identifies binary and unary expressions that are candidates for
    /// very busy analysis.
    fn extract_from_statement(
        stmt: &str,
        line: usize,
        block_id: BlockId,
        expressions: &mut Vec<(Expression, Location)>,
    ) {
        let stmt = stmt.trim();

        // Skip empty or comment-only lines
        if stmt.is_empty() || stmt.starts_with('#') || stmt.starts_with("//") {
            return;
        }

        // Look for binary expressions
        // This is a simplified parser - a real implementation would use proper AST
        Self::extract_binary_expressions(stmt, line, block_id, expressions);
    }

    /// Extract binary expressions from a statement.
    fn extract_binary_expressions(
        stmt: &str,
        line: usize,
        block_id: BlockId,
        expressions: &mut Vec<(Expression, Location)>,
    ) {
        // Common binary operators to look for
        let operators = [
            ("+", BinaryOp::Add),
            ("-", BinaryOp::Sub),
            ("*", BinaryOp::Mul),
            ("/", BinaryOp::Div),
            ("%", BinaryOp::Mod),
            ("==", BinaryOp::Eq),
            ("!=", BinaryOp::Ne),
            ("<=", BinaryOp::Le),
            (">=", BinaryOp::Ge),
            ("<", BinaryOp::Lt),
            (">", BinaryOp::Gt),
        ];

        // First check for multi-char operators
        for (op_str, op) in &operators {
            if op_str.len() > 1 {
                if let Some(idx) = stmt.find(op_str) {
                    let left = stmt[..idx].trim();
                    let right = stmt[idx + op_str.len()..].trim();

                    // Don't process if this is part of an assignment
                    if left.contains('=') && !left.contains("==") && !left.contains("!=") {
                        // This is likely "x = a + b", extract the RHS expression
                        if let Some(eq_idx) = left.rfind('=') {
                            let actual_left = left[eq_idx + 1..].trim();
                            if let (Some(left_op), Some(right_op)) =
                                (Self::parse_operand(actual_left), Self::parse_operand(right))
                            {
                                expressions.push((
                                    Expression::Binary {
                                        left: Box::new(left_op),
                                        op: *op,
                                        right: Box::new(right_op),
                                    },
                                    Location::new(line, block_id),
                                ));
                            }
                        }
                        continue;
                    }

                    // Parse operands
                    if let (Some(left_op), Some(right_op)) =
                        (Self::parse_operand(left), Self::parse_operand(right))
                    {
                        expressions.push((
                            Expression::Binary {
                                left: Box::new(left_op),
                                op: *op,
                                right: Box::new(right_op),
                            },
                            Location::new(line, block_id),
                        ));
                    }
                }
            }
        }

        // Then single-char operators (avoiding conflicts with multi-char)
        for (op_str, op) in &operators {
            if op_str.len() == 1 {
                // Skip if we already matched a multi-char operator at this position
                for (idx, _) in stmt.match_indices(op_str) {
                    // Check it's not part of ==, !=, <=, >=
                    let prev_char = if idx > 0 {
                        stmt.chars().nth(idx - 1)
                    } else {
                        None
                    };
                    let next_char = stmt.chars().nth(idx + 1);

                    if matches!(prev_char, Some('=') | Some('!') | Some('<') | Some('>')) {
                        continue;
                    }
                    if matches!(next_char, Some('=')) {
                        continue;
                    }

                    let left = stmt[..idx].trim();
                    let right = stmt[idx + 1..].trim();

                    // Handle assignment context
                    let actual_left =
                        if left.contains('=') && !left.contains("==") && !left.contains("!=") {
                            if let Some(eq_idx) = left.rfind('=') {
                                left[eq_idx + 1..].trim()
                            } else {
                                left
                            }
                        } else {
                            left
                        };

                    // Clean up right side (remove trailing parts like ';', ')', etc.)
                    let right_clean = right
                        .split(|c: char| c == ')' || c == ';' || c == ':' || c == ']')
                        .next()
                        .unwrap_or(right)
                        .trim();

                    if let (Some(left_op), Some(right_op)) = (
                        Self::parse_operand(actual_left),
                        Self::parse_operand(right_clean),
                    ) {
                        expressions.push((
                            Expression::Binary {
                                left: Box::new(left_op),
                                op: *op,
                                right: Box::new(right_op),
                            },
                            Location::new(line, block_id),
                        ));
                        break; // Only extract one expression per operator type per line
                    }
                }
            }
        }
    }

    /// Parse an operand from a string.
    fn parse_operand(s: &str) -> Option<Operand> {
        let s = s.trim();
        if s.is_empty() {
            return None;
        }

        // Remove parentheses
        let s = s.trim_start_matches('(').trim_end_matches(')').trim();

        // Try to parse as integer
        if let Ok(i) = s.parse::<i64>() {
            return Some(Operand::IntLiteral(i));
        }

        // Try to parse as float
        if let Ok(f) = s.parse::<f64>() {
            return Some(Operand::FloatLiteral(f.to_bits()));
        }

        // Try to parse as boolean
        if s == "true" || s == "True" {
            return Some(Operand::BoolLiteral(true));
        }
        if s == "false" || s == "False" {
            return Some(Operand::BoolLiteral(false));
        }

        // Check for string literal
        if (s.starts_with('"') && s.ends_with('"')) || (s.starts_with('\'') && s.ends_with('\'')) {
            return Some(Operand::StringLiteral(s[1..s.len() - 1].to_string()));
        }

        // Must be a variable - validate it's a valid identifier
        if is_valid_identifier(s) {
            return Some(Operand::Variable(s.to_string()));
        }

        // Could be a more complex expression (function call, array access, etc.)
        // For now, skip these
        None
    }

}

// =============================================================================
// Definition Extraction (for KILL set computation)
// =============================================================================

/// Extract variable definitions from statements.
fn extract_definitions_from_statement(stmt: &str) -> HashSet<String> {
    let mut defs = HashSet::new();
    let stmt = stmt.trim();

    // Skip empty or comment-only lines
    if stmt.is_empty() || stmt.starts_with('#') || stmt.starts_with("//") {
        return defs;
    }

    // Look for assignment patterns
    // x = ...
    // x, y = ...
    // x += ...
    // etc.

    // Simple assignment: x = expr
    if let Some(eq_idx) = stmt.find('=') {
        // Check it's not ==, !=, <=, >=
        let prev_char = if eq_idx > 0 {
            stmt.chars().nth(eq_idx - 1)
        } else {
            None
        };
        let next_char = stmt.chars().nth(eq_idx + 1);

        if !matches!(prev_char, Some('=') | Some('!') | Some('<') | Some('>'))
            && !matches!(next_char, Some('='))
        {
            let lhs = stmt[..eq_idx].trim();

            // Handle augmented assignment (+=, -=, etc.)
            let lhs = lhs
                .strip_suffix('+')
                .or_else(|| lhs.strip_suffix('-'))
                .or_else(|| lhs.strip_suffix('*'))
                .or_else(|| lhs.strip_suffix('/'))
                .or_else(|| lhs.strip_suffix('%'))
                .or_else(|| lhs.strip_suffix('&'))
                .or_else(|| lhs.strip_suffix('|'))
                .or_else(|| lhs.strip_suffix('^'))
                .unwrap_or(lhs)
                .trim();

            // Handle tuple unpacking
            for var in lhs.split(',') {
                let var = var.trim();
                if is_valid_identifier(var) {
                    defs.insert(var.to_string());
                }
            }
        }
    }

    // For loop variable
    if stmt.starts_with("for ") || stmt.starts_with("async for ") {
        let stmt = stmt.strip_prefix("async ").unwrap_or(stmt);
        if let Some(in_idx) = stmt.find(" in ") {
            let var_part = stmt[4..in_idx].trim();
            for var in var_part.split(',') {
                let var = var.trim();
                if is_valid_identifier(var) {
                    defs.insert(var.to_string());
                }
            }
        }
    }

    defs
}

// =============================================================================
// Very Busy Expressions Analysis
// =============================================================================

/// Compute USE and KILL sets for very busy expressions.
///
/// - USE[B] = expressions computed in B before any operand is redefined
/// - KILL[B] = expressions containing variables defined in B
fn compute_use_kill_sets(
    cfg: &CFGInfo,
    expressions: &[ExpressionInfo],
) -> (FxHashMap<BlockId, BitSet>, FxHashMap<BlockId, BitSet>) {
    let expr_count = expressions.len();
    let mut use_sets: FxHashMap<BlockId, BitSet> = FxHashMap::default();
    let mut kill_sets: FxHashMap<BlockId, BitSet> = FxHashMap::default();

    // Build a map from variable to expressions containing it
    let mut var_to_exprs: FxHashMap<String, Vec<usize>> = FxHashMap::default();
    for (idx, info) in expressions.iter().enumerate() {
        for var in &info.variables {
            var_to_exprs.entry(var.clone()).or_default().push(idx);
        }
    }

    // Build a map from expression string to index for quick lookup
    let expr_str_to_idx: FxHashMap<String, usize> = expressions
        .iter()
        .enumerate()
        .map(|(idx, info)| (info.expression.to_string_repr(), idx))
        .collect();

    for (&block_id, block) in &cfg.blocks {
        let mut use_set = BitSet::with_capacity(expr_count);
        let mut kill_set = BitSet::with_capacity(expr_count);

        // Track which variables have been defined in this block so far
        let mut defined_vars: HashSet<String> = HashSet::new();

        // Process statements in order
        for stmt in &block.statements {
            // First, check for expressions used before any operand is redefined
            let mut stmt_exprs: Vec<(Expression, Location)> = Vec::new();
            ExpressionExtractor::extract_from_statement(
                stmt,
                block.start_line,
                block_id,
                &mut stmt_exprs,
            );

            for (expr, _) in &stmt_exprs {
                let expr_str = expr.to_string_repr();
                if let Some(&idx) = expr_str_to_idx.get(&expr_str) {
                    // Check if any operand has been defined in this block
                    let operand_killed = expr.variables().iter().any(|v| defined_vars.contains(v));
                    if !operand_killed {
                        use_set.insert(idx);
                    }
                }
            }

            // Then, track definitions in this statement
            let defs = extract_definitions_from_statement(stmt);
            for def in &defs {
                defined_vars.insert(def.clone());
                // Kill all expressions containing this variable
                if let Some(expr_indices) = var_to_exprs.get(def) {
                    for &idx in expr_indices {
                        kill_set.insert(idx);
                    }
                }
            }
        }

        use_sets.insert(block_id, use_set);
        kill_sets.insert(block_id, kill_set);
    }

    (use_sets, kill_sets)
}

/// Run backward data flow analysis with INTERSECTION at join points.
///
/// This is the core algorithm for very busy expressions:
/// - Initialize OUT[exit] = empty (no expression is busy after exit)
/// - Initialize OUT[B] = universe for all other blocks (optimistic)
/// - Iterate until fixpoint:
///   - OUT[B] = INTERSECTION(IN[S]) for all successors S
///   - IN[B] = USE[B] UNION (OUT[B] - KILL[B])
fn compute_very_busy(
    cfg: &CFGInfo,
    use_sets: &FxHashMap<BlockId, BitSet>,
    kill_sets: &FxHashMap<BlockId, BitSet>,
    expr_count: usize,
) -> (FxHashMap<BlockId, BitSet>, FxHashMap<BlockId, BitSet>, usize) {
    let mut busy_in: FxHashMap<BlockId, BitSet> = FxHashMap::default();
    let mut busy_out: FxHashMap<BlockId, BitSet> = FxHashMap::default();

    // Initialize: all sets to universe except exit blocks
    for &block_id in cfg.blocks.keys() {
        if cfg.exits.contains(&block_id) {
            // Exit blocks: OUT = empty (nothing is busy after exit)
            busy_out.insert(block_id, BitSet::with_capacity(expr_count));
        } else {
            // Other blocks: OUT = universe (optimistic initialization)
            busy_out.insert(block_id, BitSet::full(expr_count));
        }
        busy_in.insert(block_id, BitSet::with_capacity(expr_count));
    }

    // Build successor map
    let mut successors: FxHashMap<BlockId, Vec<BlockId>> = FxHashMap::default();
    let mut predecessors: FxHashMap<BlockId, Vec<BlockId>> = FxHashMap::default();
    for edge in &cfg.edges {
        successors.entry(edge.from).or_default().push(edge.to);
        predecessors.entry(edge.to).or_default().push(edge.from);
    }

    // Get blocks in reverse postorder for backward analysis
    let order = cfg.topological_order();
    let reverse_order: Vec<BlockId> = order.into_iter().rev().collect();

    // Worklist-based fixpoint iteration
    let mut worklist: VecDeque<BlockId> = reverse_order.iter().copied().collect();
    let mut in_worklist: HashSet<BlockId> = worklist.iter().copied().collect();
    let mut iterations = 0;

    while let Some(block_id) = worklist.pop_front() {
        in_worklist.remove(&block_id);
        iterations += 1;

        // Compute OUT[B] = INTERSECTION(IN[S]) for all successors S
        let new_out = if cfg.exits.contains(&block_id) {
            BitSet::with_capacity(expr_count)
        } else {
            match successors.get(&block_id) {
                Some(succs) if !succs.is_empty() => {
                    // Start with the first successor's IN
                    let mut result = busy_in
                        .get(&succs[0])
                        .cloned()
                        .unwrap_or_else(|| BitSet::with_capacity(expr_count));
                    // Intersect with remaining successors
                    for &succ_id in &succs[1..] {
                        if let Some(succ_in) = busy_in.get(&succ_id) {
                            result.intersect_with(succ_in);
                        } else {
                            // No IN for successor yet means empty
                            result.clear();
                            break;
                        }
                    }
                    result
                }
                _ => BitSet::with_capacity(expr_count),
            }
        };

        // Compute IN[B] = USE[B] UNION (OUT[B] - KILL[B])
        let use_b = use_sets
            .get(&block_id)
            .cloned()
            .unwrap_or_else(|| BitSet::with_capacity(expr_count));
        let kill_b = kill_sets
            .get(&block_id)
            .cloned()
            .unwrap_or_else(|| BitSet::with_capacity(expr_count));

        let mut new_in = new_out.clone();
        new_in.difference_with(&kill_b);
        new_in.union_with(&use_b);

        // Check if IN changed
        let old_in = busy_in.get(&block_id);
        let changed = old_in.map_or(true, |old| *old != new_in);

        if changed {
            busy_in.insert(block_id, new_in);
            busy_out.insert(block_id, new_out);

            // Add predecessors to worklist
            if let Some(preds) = predecessors.get(&block_id) {
                for &pred_id in preds {
                    if !in_worklist.contains(&pred_id) {
                        worklist.push_back(pred_id);
                        in_worklist.insert(pred_id);
                    }
                }
            }
        } else {
            busy_out.insert(block_id, new_out);
        }
    }

    (busy_in, busy_out, iterations)
}

/// Detect hoisting opportunities from very busy expressions.
fn detect_hoisting_opportunities(
    cfg: &CFGInfo,
    expressions: &[ExpressionInfo],
    busy_in: &FxHashMap<BlockId, BitSet>,
) -> Vec<HoistingOpportunity> {
    let mut opportunities = Vec::new();

    // For each expression that is very busy at some point,
    // check if it can be hoisted
    for (idx, info) in expressions.iter().enumerate() {
        // Skip expressions with side effects
        if info.has_side_effects {
            continue;
        }

        // Find blocks where this expression is very busy at entry
        let busy_blocks: Vec<BlockId> = busy_in
            .iter()
            .filter(|(_, bits)| bits.contains(idx))
            .map(|(&block_id, _)| block_id)
            .collect();

        if busy_blocks.is_empty() {
            continue;
        }

        // Check if expression is computed in multiple branches after a common point
        // This is a hoisting opportunity
        if info.locations.len() > 1 {
            // Find the dominator block (common ancestor)
            // For now, use the entry block if the expression is busy there
            if busy_in
                .get(&cfg.entry)
                .map_or(false, |bits| bits.contains(idx))
            {
                let mut safety_notes = Vec::new();
                if info.may_raise {
                    safety_notes.push(
                        "Expression may raise exception; ensure exception would occur on all paths"
                            .to_string(),
                    );
                }
                if info.is_short_circuit {
                    safety_notes.push(
                        "Short-circuit expression; operands may not all be evaluated".to_string(),
                    );
                }

                let entry_block = cfg.blocks.get(&cfg.entry);
                let hoist_line = entry_block.map_or(1, |b| b.start_line);

                opportunities.push(HoistingOpportunity {
                    expression: info.expression.clone(),
                    current_locations: info.locations.clone(),
                    hoist_to: Location::new(hoist_line, cfg.entry),
                    benefit: HoistingBenefit::ReduceCodeSize,
                    occurrences_saved: info.locations.len() - 1,
                    safety_notes,
                });
            }
        }
    }

    opportunities
}

/// Main entry point: analyze very busy expressions in a function.
pub fn analyze_very_busy_expressions(cfg: &CFGInfo) -> VeryBusyExpressionsResult {
    let start = std::time::Instant::now();

    // Step 1: Extract all expressions from the CFG
    let mut raw_expressions: Vec<(Expression, Location)> = Vec::new();
    for (&block_id, block) in &cfg.blocks {
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            let line = block.start_line + stmt_idx;
            ExpressionExtractor::extract_from_statement(stmt, line, block_id, &mut raw_expressions);
        }
    }

    // Step 2: Deduplicate expressions and collect locations
    let mut expr_map: FxHashMap<String, (Expression, Vec<Location>)> = FxHashMap::default();
    for (expr, loc) in raw_expressions {
        let key = expr.to_string_repr();
        expr_map
            .entry(key)
            .or_insert_with(|| (expr.clone(), Vec::new()))
            .1
            .push(loc);
    }

    // Build expression info list
    let expressions: Vec<ExpressionInfo> = expr_map
        .into_iter()
        .enumerate()
        .map(|(idx, (_, (expr, locations)))| {
            let variables = expr.variables();
            let has_side_effects = expr.has_side_effects();
            let may_raise = expr.may_raise();
            let is_short_circuit = expr.is_short_circuit();

            ExpressionInfo {
                expr_id: ExprId(idx),
                expression: expr,
                locations,
                variables,
                has_side_effects,
                may_raise,
                is_short_circuit,
            }
        })
        .collect();

    if expressions.is_empty() {
        let elapsed = start.elapsed();
        return VeryBusyExpressionsResult {
            function_name: cfg.function_name.clone(),
            expressions: Vec::new(),
            busy_in: FxHashMap::default(),
            busy_out: FxHashMap::default(),
            hoisting_opportunities: Vec::new(),
            use_sets: FxHashMap::default(),
            kill_sets: FxHashMap::default(),
            iterations: 0,
            analysis_time_us: elapsed.as_micros() as u64,
        };
    }

    // Step 3: Compute USE and KILL sets
    let (use_sets, kill_sets) = compute_use_kill_sets(cfg, &expressions);

    // Step 4: Run the data flow analysis
    let (busy_in, busy_out, iterations) =
        compute_very_busy(cfg, &use_sets, &kill_sets, expressions.len());

    // Step 5: Detect hoisting opportunities
    let hoisting_opportunities = detect_hoisting_opportunities(cfg, &expressions, &busy_in);

    let elapsed = start.elapsed();

    VeryBusyExpressionsResult {
        function_name: cfg.function_name.clone(),
        expressions,
        busy_in,
        busy_out,
        hoisting_opportunities,
        use_sets,
        kill_sets,
        iterations,
        analysis_time_us: elapsed.as_micros() as u64,
    }
}

/// Analyze very busy expressions from a file.
pub fn analyze_very_busy_expressions_file(
    file: &str,
    function: &str,
) -> Result<VeryBusyExpressionsResult> {
    analyze_very_busy_expressions_with_language(file, function, None)
}

/// Analyze very busy expressions with explicit language specification.
pub fn analyze_very_busy_expressions_with_language(
    file: &str,
    function: &str,
    language: Option<&str>,
) -> Result<VeryBusyExpressionsResult> {
    // Extract CFG from file
    let cfg = extract_with_language(file, function, language)?;

    Ok(analyze_very_busy_expressions(&cfg))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashMap;

    use super::*;
    use crate::cfg::types::{BlockType, CFGBlock, CFGEdge, EdgeType};

    /// Create a CFG for testing very busy expressions in conditionals.
    ///
    /// ```text
    /// def f(a, b, cond):
    ///     if cond:
    ///         x = a + b
    ///     else:
    ///         y = a + b
    ///     return x or y
    /// ```
    fn create_conditional_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        // Entry block
        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def f(a, b, cond):".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        // Condition block
        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "if cond".to_string(),
                block_type: BlockType::Branch,
                statements: vec!["if cond:".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 2,
            },
        );

        // True branch: x = a + b
        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "x = a + b".to_string(),
                block_type: BlockType::Body,
                statements: vec!["x = a + b".to_string()],
                func_calls: vec![],
                start_line: 3,
                end_line: 3,
            },
        );

        // False branch: y = a + b
        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "y = a + b".to_string(),
                block_type: BlockType::Body,
                statements: vec!["y = a + b".to_string()],
                func_calls: vec![],
                start_line: 5,
                end_line: 5,
            },
        );

        // Return block
        blocks.insert(
            BlockId(4),
            CFGBlock {
                id: BlockId(4),
                label: "return".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return x or y".to_string()],
                func_calls: vec![],
                start_line: 6,
                end_line: 6,
            },
        );

        CFGInfo::new(
            "f".to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::new(BlockId(1), BlockId(2), EdgeType::True),
                CFGEdge::new(BlockId(1), BlockId(3), EdgeType::False),
                CFGEdge::unconditional(BlockId(2), BlockId(4)),
                CFGEdge::unconditional(BlockId(3), BlockId(4)),
            ],
            BlockId(0),
            vec![BlockId(4)],
        )
    }

    /// Create a CFG where expression is killed before use.
    ///
    /// ```text
    /// def g(a, b):
    ///     a = 10  # kills a + b
    ///     x = a + b
    ///     return x
    /// ```
    fn create_killed_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec![
                    "def g(a, b):".to_string(),
                    "a = 10".to_string(),
                    "x = a + b".to_string(),
                ],
                func_calls: vec![],
                start_line: 1,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "return".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return x".to_string()],
                func_calls: vec![],
                start_line: 4,
                end_line: 4,
            },
        );

        CFGInfo::new(
            "g".to_string(),
            blocks,
            vec![CFGEdge::unconditional(BlockId(0), BlockId(1))],
            BlockId(0),
            vec![BlockId(1)],
        )
    }

    /// Create a CFG with different expressions in branches (not very busy).
    ///
    /// ```text
    /// def h(a, b, c, cond):
    ///     if cond:
    ///         x = a + b
    ///     else:
    ///         y = a + c  # Different expression
    ///     return x or y
    /// ```
    fn create_different_expressions_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def h(a, b, c, cond):".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "if cond".to_string(),
                block_type: BlockType::Branch,
                statements: vec!["if cond:".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 2,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "x = a + b".to_string(),
                block_type: BlockType::Body,
                statements: vec!["x = a + b".to_string()],
                func_calls: vec![],
                start_line: 3,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "y = a + c".to_string(),
                block_type: BlockType::Body,
                statements: vec!["y = a + c".to_string()],
                func_calls: vec![],
                start_line: 5,
                end_line: 5,
            },
        );

        blocks.insert(
            BlockId(4),
            CFGBlock {
                id: BlockId(4),
                label: "return".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return x or y".to_string()],
                func_calls: vec![],
                start_line: 6,
                end_line: 6,
            },
        );

        CFGInfo::new(
            "h".to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::new(BlockId(1), BlockId(2), EdgeType::True),
                CFGEdge::new(BlockId(1), BlockId(3), EdgeType::False),
                CFGEdge::unconditional(BlockId(2), BlockId(4)),
                CFGEdge::unconditional(BlockId(3), BlockId(4)),
            ],
            BlockId(0),
            vec![BlockId(4)],
        )
    }

    /// Create a CFG with a loop.
    ///
    /// ```text
    /// def loop_test(a, b, n):
    ///     i = 0
    ///     while i < n:
    ///         x = a + b
    ///         i = i + 1
    ///     return x
    /// ```
    fn create_loop_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def loop_test(a, b, n):".to_string(), "i = 0".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 2,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "while i < n".to_string(),
                block_type: BlockType::LoopHeader,
                statements: vec!["while i < n:".to_string()],
                func_calls: vec![],
                start_line: 3,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "loop body".to_string(),
                block_type: BlockType::LoopBody,
                statements: vec!["x = a + b".to_string(), "i = i + 1".to_string()],
                func_calls: vec![],
                start_line: 4,
                end_line: 5,
            },
        );

        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "return".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return x".to_string()],
                func_calls: vec![],
                start_line: 6,
                end_line: 6,
            },
        );

        CFGInfo::new(
            "loop_test".to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::new(BlockId(1), BlockId(2), EdgeType::True),
                CFGEdge::new(BlockId(1), BlockId(3), EdgeType::False),
                CFGEdge::new(BlockId(2), BlockId(1), EdgeType::BackEdge),
            ],
            BlockId(0),
            vec![BlockId(3)],
        )
    }

    #[test]
    fn test_very_busy_conditional() {
        let cfg = create_conditional_cfg();
        let result = analyze_very_busy_expressions(&cfg);

        // The expression "a + b" should be found
        assert!(!result.expressions.is_empty(), "Should find expressions");

        // Check that a + b is in the expressions list
        let ab_expr = result
            .expressions
            .iter()
            .find(|info| info.expression.to_string_repr() == "a + b");
        assert!(ab_expr.is_some(), "Should find expression a + b");

        // The expression should appear in both branches
        let ab_info = ab_expr.unwrap();
        assert_eq!(ab_info.locations.len(), 2, "a + b should appear twice");

        // Check for hoisting opportunity
        assert!(
            !result.hoisting_opportunities.is_empty(),
            "Should detect hoisting opportunity for a + b"
        );
    }

    #[test]
    fn test_expression_killed() {
        let cfg = create_killed_cfg();
        let result = analyze_very_busy_expressions(&cfg);

        // a + b is computed, but a is redefined first
        // The expression should still be found but not very busy at entry

        // Check that use/kill sets are computed correctly
        // The kill set for block 0 should include a + b because a is defined
        if let Some(kill_set) = result.kill_sets.get(&BlockId(0)) {
            // Find the index of a + b expression
            let ab_idx = result
                .expressions
                .iter()
                .position(|info| info.expression.to_string_repr() == "a + b");
            if let Some(idx) = ab_idx {
                assert!(
                    kill_set.contains(idx),
                    "a + b should be killed in block 0 where a is redefined"
                );
            }
        }
    }

    #[test]
    fn test_different_expressions_not_busy() {
        let cfg = create_different_expressions_cfg();
        let result = analyze_very_busy_expressions(&cfg);

        // Both a + b and a + c should be found
        let ab_expr = result
            .expressions
            .iter()
            .find(|info| info.expression.to_string_repr() == "a + b");
        let ac_expr = result
            .expressions
            .iter()
            .find(|info| info.expression.to_string_repr() == "a + c");

        assert!(ab_expr.is_some(), "Should find a + b");
        assert!(ac_expr.is_some(), "Should find a + c");

        // Neither should be very busy at the branch point (block 1)
        // because they are not computed on all paths
        if let Some(busy_in) = result.busy_in.get(&BlockId(1)) {
            // Find indices
            let ab_idx = result
                .expressions
                .iter()
                .position(|info| info.expression.to_string_repr() == "a + b");
            let ac_idx = result
                .expressions
                .iter()
                .position(|info| info.expression.to_string_repr() == "a + c");

            if let Some(idx) = ab_idx {
                // a + b should not be very busy at the condition because
                // it's only computed on one branch
                assert!(
                    !busy_in.contains(idx),
                    "a + b should not be very busy at condition block"
                );
            }
            if let Some(idx) = ac_idx {
                assert!(
                    !busy_in.contains(idx),
                    "a + c should not be very busy at condition block"
                );
            }
        }
    }

    #[test]
    fn test_loop_very_busy() {
        let cfg = create_loop_cfg();
        let result = analyze_very_busy_expressions(&cfg);

        // a + b should be found in the loop body
        let ab_expr = result
            .expressions
            .iter()
            .find(|info| info.expression.to_string_repr() == "a + b");
        assert!(ab_expr.is_some(), "Should find a + b in loop");
    }

    #[test]
    fn test_bitset_operations() {
        let mut set1 = BitSet::with_capacity(100);
        let mut set2 = BitSet::with_capacity(100);

        set1.insert(1);
        set1.insert(5);
        set1.insert(10);

        set2.insert(5);
        set2.insert(10);
        set2.insert(20);

        // Test intersection
        let mut intersection = set1.clone();
        intersection.intersect_with(&set2);
        assert!(intersection.contains(5));
        assert!(intersection.contains(10));
        assert!(!intersection.contains(1));
        assert!(!intersection.contains(20));

        // Test full set
        let full = BitSet::full(10);
        assert_eq!(full.len(), 10);
        assert!(full.contains(0));
        assert!(full.contains(9));
        assert!(!full.contains(10));
    }

    #[test]
    fn test_expression_parsing() {
        let mut exprs = Vec::new();
        ExpressionExtractor::extract_from_statement("x = a + b", 1, BlockId(0), &mut exprs);

        assert_eq!(exprs.len(), 1, "Should extract one expression");
        assert_eq!(exprs[0].0.to_string_repr(), "a + b", "Should extract a + b");
    }

    #[test]
    fn test_json_output() {
        let cfg = create_conditional_cfg();
        let result = analyze_very_busy_expressions(&cfg);
        let json = result.to_json();

        assert!(json.get("function_name").is_some());
        assert!(json.get("expressions").is_some());
        assert!(json.get("hoisting_opportunities").is_some());
        assert!(json.get("metrics").is_some());
    }

    #[test]
    fn test_text_output() {
        let cfg = create_conditional_cfg();
        let result = analyze_very_busy_expressions(&cfg);
        let text = result.to_text();

        assert!(text.contains("Very Busy Expressions"));
        assert!(text.contains("Expressions"));
        assert!(text.contains("Metrics"));
    }

    #[test]
    fn test_definition_extraction() {
        let defs = extract_definitions_from_statement("x = a + b");
        assert!(defs.contains("x"));
        assert!(!defs.contains("a"));
        assert!(!defs.contains("b"));

        let defs2 = extract_definitions_from_statement("x, y = values");
        assert!(defs2.contains("x"));
        assert!(defs2.contains("y"));

        let defs3 = extract_definitions_from_statement("x += 1");
        assert!(defs3.contains("x"));
    }
}
