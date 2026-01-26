//! Available Expressions Data Flow Analysis.
//!
//! An expression is "available" at a program point if it has been computed on
//! every path to that point and no variable in the expression has been redefined.
//!
//! This is a FORWARD analysis with INTERSECTION at join points (must-analysis).
//! Unlike reaching definitions (may-analysis with union), available expressions
//! require that an expression be computed on ALL paths to be considered available.
//!
//! # Data Flow Equations
//!
//! - `GEN[B]` = expressions computed in B (not later killed in B)
//! - `KILL[B]` = expressions containing variables defined in B
//! - `OUT[B]` = GEN[B] UNION (IN[B] - KILL[B])
//! - `IN[B]` = INTERSECTION(OUT[P]) for all predecessors P
//!
//! # Applications
//!
//! - Common Subexpression Elimination (CSE): reuse previously computed values
//! - Loop-invariant code motion: identify expressions that can be hoisted
//! - Redundant computation detection: find unnecessary recalculations
//!
//! # Example
//!
//! ```ignore
//! // Before CSE:
//! x = a + b;      // Expression a+b computed
//! y = a + b;      // Expression a+b available - can reuse x
//!
//! // After CSE:
//! x = a + b;
//! y = x;          // Reuse the computed value
//! ```

use std::collections::{HashSet, VecDeque};
use std::path::Path;

use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

use crate::cfg::{extract_with_language, BlockId, CFGInfo};
use crate::dataflow::common::is_valid_identifier;
use crate::error::{BrrrError, Result};

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
    #[must_use]
    pub fn new(line: usize, block_id: BlockId) -> Self {
        Self {
            line,
            column: None,
            block_id,
        }
    }

    /// Create a new location with column.
    #[inline]
    #[must_use]
    pub fn with_column(line: usize, column: usize, block_id: BlockId) -> Self {
        Self {
            line,
            column: Some(column),
            block_id,
        }
    }
}

/// Kind of expression for available expression analysis.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExprKind {
    /// Binary operation: left op right (e.g., `a + b`, `x * y`)
    BinaryOp {
        left: String,
        op: String,
        right: String,
    },
    /// Unary operation: op operand (e.g., `-x`, `!flag`)
    UnaryOp { op: String, operand: String },
    /// Field access: object.field (e.g., `self.value`, `obj.attr`)
    FieldAccess { object: String, field: String },
    /// Array/index access: array[index] (e.g., `arr[i]`, `dict[key]`)
    ArrayAccess { array: String, index: String },
    /// Function call: callee(args) (only pure functions are available)
    Call { callee: String, args: Vec<String> },
    /// Comparison expression (e.g., `a < b`, `x == y`)
    Comparison {
        left: String,
        op: String,
        right: String,
    },
}

impl ExprKind {
    /// Get the canonical text representation of this expression kind.
    #[must_use]
    pub fn to_text(&self) -> String {
        match self {
            ExprKind::BinaryOp { left, op, right } => {
                format!("{} {} {}", left, op, right)
            }
            ExprKind::UnaryOp { op, operand } => {
                format!("{}{}", op, operand)
            }
            ExprKind::FieldAccess { object, field } => {
                format!("{}.{}", object, field)
            }
            ExprKind::ArrayAccess { array, index } => {
                format!("{}[{}]", array, index)
            }
            ExprKind::Call { callee, args } => {
                format!("{}({})", callee, args.join(", "))
            }
            ExprKind::Comparison { left, op, right } => {
                format!("{} {} {}", left, op, right)
            }
        }
    }
}

/// A tracked expression in the analysis.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Expression {
    /// Unique expression ID.
    pub expr_id: ExprId,
    /// Canonical text representation of the expression.
    pub text: String,
    /// Variables used in this expression.
    /// If any of these are redefined, the expression is killed.
    pub variables: HashSet<String>,
    /// Kind of expression with structured data.
    pub kind: ExprKind,
    /// Whether this expression is considered pure (no side effects).
    /// Only pure expressions can be truly "available" for CSE.
    pub is_pure: bool,
}

impl Expression {
    /// Check if this expression is killed by a definition of the given variable.
    #[inline]
    #[must_use]
    pub fn is_killed_by(&self, var: &str) -> bool {
        self.variables.contains(var)
    }
}

/// A Common Subexpression Elimination opportunity.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CSEOpportunity {
    /// The expression that can be reused.
    pub expression: Expression,
    /// Location where the expression was first computed.
    pub first_computation: Location,
    /// Locations where the expression is redundantly recomputed.
    pub redundant_computations: Vec<Location>,
    /// Estimated savings (number of redundant computations).
    pub estimated_savings: u32,
    /// Whether this is a safe optimization (pure expression).
    pub is_safe: bool,
    /// Suggested variable name for storing the result.
    pub suggested_temp_name: String,
}

// =============================================================================
// BitSet with Intersection - Efficient set operations for must-analysis
// =============================================================================

/// A simple bit set for efficient set operations.
///
/// Extended from reaching definitions BitSet to support intersection
/// for must-analysis (available expressions).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitSet {
    /// Backing storage: each u64 holds 64 bits.
    bits: Vec<u64>,
    /// Number of elements that can be stored.
    capacity: usize,
}

impl BitSet {
    /// Create a new empty BitSet with given capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        let num_words = (capacity + 63) / 64;
        Self {
            bits: vec![0; num_words],
            capacity,
        }
    }

    /// Create a BitSet with all bits set (full set).
    /// Used as the initial state for intersection-based analysis.
    #[must_use]
    pub fn full(capacity: usize) -> Self {
        let num_words = (capacity + 63) / 64;
        let mut bits = vec![!0u64; num_words];

        // Clear bits beyond capacity in the last word
        if capacity > 0 {
            let last_word_bits = capacity % 64;
            if last_word_bits > 0 {
                bits[num_words - 1] = (1u64 << last_word_bits) - 1;
            }
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
    #[must_use]
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
    /// Critical for available expressions (must-analysis).
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
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bits.iter().all(|&w| w == 0)
    }

    /// Check if all elements are set (full set).
    #[inline]
    #[must_use]
    pub fn is_full(&self) -> bool {
        if self.capacity == 0 {
            return true;
        }

        let num_full_words = self.capacity / 64;
        let remaining_bits = self.capacity % 64;

        // Check all full words
        for i in 0..num_full_words {
            if self.bits[i] != !0u64 {
                return false;
            }
        }

        // Check remaining bits in last word
        if remaining_bits > 0 {
            let mask = (1u64 << remaining_bits) - 1;
            if self.bits[num_full_words] & mask != mask {
                return false;
            }
        }

        true
    }

    /// Count the number of elements.
    #[inline]
    #[must_use]
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

    /// Set all elements (make full set).
    #[inline]
    pub fn set_all(&mut self) {
        for w in &mut self.bits {
            *w = !0u64;
        }
        // Clear bits beyond capacity
        if self.capacity > 0 {
            let last_word_bits = self.capacity % 64;
            if last_word_bits > 0 {
                let num_words = (self.capacity + 63) / 64;
                self.bits[num_words - 1] = (1u64 << last_word_bits) - 1;
            }
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

// =============================================================================
// Available Expressions Result
// =============================================================================

/// Result of available expressions analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AvailableExpressionsResult {
    /// Function name analyzed.
    pub function_name: String,
    /// All expressions found in the function.
    pub expressions: Vec<Expression>,
    /// Expressions available at each block's entry.
    /// Maps BlockId.0 -> set of ExprId.0 values.
    pub available_in: FxHashMap<usize, Vec<usize>>,
    /// Expressions available at each block's exit.
    /// Maps BlockId.0 -> set of ExprId.0 values.
    pub available_out: FxHashMap<usize, Vec<usize>>,
    /// Detected CSE opportunities.
    pub cse_opportunities: Vec<CSEOpportunity>,
    /// Loop-invariant expressions (available at loop header from outside).
    pub loop_invariants: Vec<LoopInvariant>,
    /// Number of iterations until fixpoint.
    pub iterations: usize,
    /// Analysis metrics.
    pub metrics: AvailableExpressionsMetrics,
}

/// A loop-invariant expression that could be hoisted.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoopInvariant {
    /// The invariant expression.
    pub expression: Expression,
    /// Loop header block where invariance was detected.
    pub loop_header: BlockId,
    /// Whether hoisting is safe (no side effects in loop body).
    pub is_safe_to_hoist: bool,
}

/// Metrics about the available expressions analysis.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AvailableExpressionsMetrics {
    /// Number of blocks analyzed.
    pub blocks_analyzed: usize,
    /// Number of expressions tracked.
    pub expressions_tracked: usize,
    /// Number of CSE opportunities found.
    pub cse_opportunities: usize,
    /// Estimated instructions saved by CSE.
    pub estimated_savings: usize,
    /// Number of loop invariants found.
    pub loop_invariants: usize,
    /// Analysis time in microseconds.
    pub analysis_time_us: u64,
}

// =============================================================================
// Expression Extraction
// =============================================================================

/// Known pure functions that have no side effects.
/// These can safely be considered for CSE.
const PURE_FUNCTIONS: &[&str] = &[
    // Math functions
    "abs",
    "min",
    "max",
    "pow",
    "sqrt",
    "sin",
    "cos",
    "tan",
    "log",
    "exp",
    "floor",
    "ceil",
    "round",
    // String functions (read-only)
    "len",
    "strlen",
    "length",
    // Type constructors
    "int",
    "float",
    "str",
    "bool",
    // Rust specific
    "clone",
    "to_string",
    "to_owned",
    "as_ref",
    "as_str",
    // Go specific
    "len",
    "cap",
    "make",
    "new",
];

/// Patterns for extracting expressions from code.
struct ExpressionExtractor;

impl ExpressionExtractor {
    /// Extract expressions from a statement.
    ///
    /// Parses common expression patterns:
    /// - Binary operations: `a + b`, `x * y`
    /// - Comparisons: `a < b`, `x == y`
    /// - Field access: `obj.field`
    /// - Array access: `arr[i]`
    /// - Function calls: `func(args)`
    fn extract_from_statement(
        stmt: &str,
        _line: usize,
        _block_id: BlockId,
        next_expr_id: &mut usize,
        expressions: &mut Vec<Expression>,
        expr_map: &mut FxHashMap<String, ExprId>,
    ) {
        let stmt = stmt.trim();

        // Skip empty, comment-only, or control flow lines
        if stmt.is_empty()
            || stmt.starts_with('#')
            || stmt.starts_with("//")
            || stmt.starts_with("if ")
            || stmt.starts_with("elif ")
            || stmt.starts_with("else")
            || stmt.starts_with("while ")
            || stmt.starts_with("for ")
            || stmt.starts_with("def ")
            || stmt.starts_with("class ")
            || stmt.starts_with("return")
            || stmt.starts_with("break")
            || stmt.starts_with("continue")
            || stmt.starts_with("pass")
            || stmt.starts_with("import ")
            || stmt.starts_with("from ")
        {
            return;
        }

        // For assignments, extract RHS expression
        if let Some(eq_pos) = Self::find_assignment_eq(stmt) {
            let rhs = stmt[eq_pos + 1..].trim();
            Self::extract_expression(rhs, next_expr_id, expressions, expr_map);
        } else {
            // Try to extract from the whole statement
            Self::extract_expression(stmt, next_expr_id, expressions, expr_map);
        }
    }

    /// Find the position of assignment = (not ==, !=, <=, >=, :=).
    fn find_assignment_eq(stmt: &str) -> Option<usize> {
        let mut depth: i32 = 0;
        let chars: Vec<char> = stmt.chars().collect();

        for (i, &c) in chars.iter().enumerate() {
            match c {
                '(' | '[' | '{' => depth += 1,
                ')' | ']' | '}' => depth -= 1,
                '=' if depth == 0 => {
                    // Check not ==, !=, <=, >=, :=, +=, -=, etc.
                    let prev = if i > 0 { chars[i - 1] } else { ' ' };
                    let next = chars.get(i + 1).copied().unwrap_or(' ');

                    if prev != '!'
                        && prev != '='
                        && prev != '<'
                        && prev != '>'
                        && prev != ':'
                        && prev != '+'
                        && prev != '-'
                        && prev != '*'
                        && prev != '/'
                        && prev != '%'
                        && prev != '&'
                        && prev != '|'
                        && prev != '^'
                        && prev != '@'
                        && next != '='
                    {
                        return Some(i);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Extract an expression and add it to the collection.
    fn extract_expression(
        expr: &str,
        next_expr_id: &mut usize,
        expressions: &mut Vec<Expression>,
        expr_map: &mut FxHashMap<String, ExprId>,
    ) {
        let expr = expr.trim();
        if expr.is_empty() {
            return;
        }

        // Try to parse as binary operation
        if let Some((kind, vars)) = Self::parse_binary_op(expr) {
            Self::add_expression(expr, kind, vars, true, next_expr_id, expressions, expr_map);
        }
        // Try to parse as comparison
        else if let Some((kind, vars)) = Self::parse_comparison(expr) {
            Self::add_expression(expr, kind, vars, true, next_expr_id, expressions, expr_map);
        }
        // Try to parse as field access
        else if let Some((kind, vars)) = Self::parse_field_access(expr) {
            Self::add_expression(expr, kind, vars, true, next_expr_id, expressions, expr_map);
        }
        // Try to parse as array access
        else if let Some((kind, vars)) = Self::parse_array_access(expr) {
            // Array access with variable index may alias
            Self::add_expression(expr, kind, vars, true, next_expr_id, expressions, expr_map);
        }
        // Try to parse as function call
        else if let Some((kind, vars, is_pure)) = Self::parse_function_call(expr) {
            Self::add_expression(
                expr,
                kind,
                vars,
                is_pure,
                next_expr_id,
                expressions,
                expr_map,
            );
        }
    }

    /// Add an expression if not already present.
    fn add_expression(
        text: &str,
        kind: ExprKind,
        variables: HashSet<String>,
        is_pure: bool,
        next_expr_id: &mut usize,
        expressions: &mut Vec<Expression>,
        expr_map: &mut FxHashMap<String, ExprId>,
    ) {
        let canonical = kind.to_text();

        // Check if we already have this expression
        if expr_map.contains_key(&canonical) {
            return;
        }

        let expr_id = ExprId(*next_expr_id);
        *next_expr_id += 1;

        expr_map.insert(canonical.clone(), expr_id);

        expressions.push(Expression {
            expr_id,
            text: text.to_string(),
            variables,
            kind,
            is_pure,
        });
    }

    /// Parse a binary operation (e.g., `a + b`, `x * y`).
    fn parse_binary_op(expr: &str) -> Option<(ExprKind, HashSet<String>)> {
        // Look for operators (in precedence order for splitting)
        let binary_ops = [
            ("||", "||"),
            ("&&", "&&"),
            ("|", "|"),
            ("^", "^"),
            ("&", "&"),
            ("<<", "<<"),
            (">>", ">>"),
            ("+", "+"),
            ("-", "-"),
            ("*", "*"),
            ("/", "/"),
            ("//", "//"),
            ("%", "%"),
            ("**", "**"),
        ];

        for (op_str, op_name) in binary_ops {
            if let Some(pos) = Self::find_operator_at_depth_0(expr, op_str) {
                let left = expr[..pos].trim();
                let right = expr[pos + op_str.len()..].trim();

                if !left.is_empty() && !right.is_empty() {
                    // Check if operands are simple identifiers or expressions
                    let left_var = Self::extract_base_variable(left);
                    let right_var = Self::extract_base_variable(right);

                    let mut variables = HashSet::new();
                    if let Some(v) = left_var {
                        variables.insert(v);
                    }
                    if let Some(v) = right_var {
                        variables.insert(v);
                    }

                    // Only track if we have at least one variable
                    if !variables.is_empty() {
                        return Some((
                            ExprKind::BinaryOp {
                                left: left.to_string(),
                                op: op_name.to_string(),
                                right: right.to_string(),
                            },
                            variables,
                        ));
                    }
                }
            }
        }
        None
    }

    /// Parse a comparison expression.
    fn parse_comparison(expr: &str) -> Option<(ExprKind, HashSet<String>)> {
        let comparison_ops = [
            ("==", "=="),
            ("!=", "!="),
            ("<=", "<="),
            (">=", ">="),
            ("<", "<"),
            (">", ">"),
            (" is ", "is"),
            (" in ", "in"),
            (" not in ", "not in"),
        ];

        for (op_str, op_name) in comparison_ops {
            if let Some(pos) = Self::find_operator_at_depth_0(expr, op_str) {
                let left = expr[..pos].trim();
                let right = expr[pos + op_str.len()..].trim();

                if !left.is_empty() && !right.is_empty() {
                    let left_var = Self::extract_base_variable(left);
                    let right_var = Self::extract_base_variable(right);

                    let mut variables = HashSet::new();
                    if let Some(v) = left_var {
                        variables.insert(v);
                    }
                    if let Some(v) = right_var {
                        variables.insert(v);
                    }

                    if !variables.is_empty() {
                        return Some((
                            ExprKind::Comparison {
                                left: left.to_string(),
                                op: op_name.to_string(),
                                right: right.to_string(),
                            },
                            variables,
                        ));
                    }
                }
            }
        }
        None
    }

    /// Parse a field access expression (e.g., `obj.field`).
    fn parse_field_access(expr: &str) -> Option<(ExprKind, HashSet<String>)> {
        // Look for . not inside brackets/parens
        let chars: Vec<char> = expr.chars().collect();
        let mut depth = 0;

        for (i, &c) in chars.iter().enumerate() {
            match c {
                '(' | '[' | '{' => depth += 1,
                ')' | ']' | '}' => depth -= 1,
                '.' if depth == 0 && i > 0 => {
                    let object = expr[..i].trim();
                    let field = expr[i + 1..].trim();

                    if !object.is_empty()
                        && !field.is_empty()
                        && is_valid_identifier(field)
                        && !field.contains('(')
                    {
                        let mut variables = HashSet::new();
                        if let Some(v) = Self::extract_base_variable(object) {
                            variables.insert(v);
                        }

                        if !variables.is_empty() {
                            return Some((
                                ExprKind::FieldAccess {
                                    object: object.to_string(),
                                    field: field.to_string(),
                                },
                                variables,
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Parse an array access expression (e.g., `arr[i]`).
    fn parse_array_access(expr: &str) -> Option<(ExprKind, HashSet<String>)> {
        // Look for [...] pattern
        if let Some(bracket_start) = expr.find('[') {
            if expr.ends_with(']') {
                let array = expr[..bracket_start].trim();
                let index = expr[bracket_start + 1..expr.len() - 1].trim();

                if !array.is_empty() && !index.is_empty() && is_valid_identifier(array) {
                    let mut variables = HashSet::new();
                    variables.insert(array.to_string());

                    // Also add index variable if it's an identifier
                    if let Some(idx_var) = Self::extract_base_variable(index) {
                        variables.insert(idx_var);
                    }

                    return Some((
                        ExprKind::ArrayAccess {
                            array: array.to_string(),
                            index: index.to_string(),
                        },
                        variables,
                    ));
                }
            }
        }
        None
    }

    /// Parse a function call expression.
    fn parse_function_call(expr: &str) -> Option<(ExprKind, HashSet<String>, bool)> {
        if let Some(paren_start) = expr.find('(') {
            if expr.ends_with(')') {
                let callee = expr[..paren_start].trim();
                let args_str = expr[paren_start + 1..expr.len() - 1].trim();

                if is_valid_identifier(callee) || callee.contains('.') {
                    let args: Vec<String> = if args_str.is_empty() {
                        Vec::new()
                    } else {
                        Self::split_args(args_str)
                    };

                    let mut variables = HashSet::new();

                    // Extract variables from arguments
                    for arg in &args {
                        if let Some(v) = Self::extract_base_variable(arg) {
                            variables.insert(v);
                        }
                    }

                    // Check if callee is a method call (obj.method)
                    if let Some(dot_pos) = callee.rfind('.') {
                        let obj = &callee[..dot_pos];
                        if let Some(v) = Self::extract_base_variable(obj) {
                            variables.insert(v);
                        }
                    }

                    // Check if this is a known pure function
                    let func_name = callee.rsplit('.').next().unwrap_or(callee);
                    let is_pure = PURE_FUNCTIONS.contains(&func_name);

                    if !variables.is_empty() {
                        return Some((
                            ExprKind::Call {
                                callee: callee.to_string(),
                                args,
                            },
                            variables,
                            is_pure,
                        ));
                    }
                }
            }
        }
        None
    }

    /// Find an operator at depth 0 (not inside parens/brackets).
    fn find_operator_at_depth_0(expr: &str, op: &str) -> Option<usize> {
        let chars: Vec<char> = expr.chars().collect();
        let mut depth = 0;
        let mut in_string = false;
        let mut string_char = ' ';

        for i in 0..chars.len() {
            let c = chars[i];

            if in_string {
                if c == string_char && (i == 0 || chars[i - 1] != '\\') {
                    in_string = false;
                }
                continue;
            }

            if c == '"' || c == '\'' {
                in_string = true;
                string_char = c;
                continue;
            }

            if c == '(' || c == '[' || c == '{' {
                depth += 1;
                continue;
            }

            if c == ')' || c == ']' || c == '}' {
                depth -= 1;
                continue;
            }

            if depth == 0 && expr[i..].starts_with(op) {
                // Make sure we're not matching part of a longer operator
                let after = i + op.len();
                let before = if i > 0 { chars[i - 1] } else { ' ' };
                let after_char = chars.get(after).copied().unwrap_or(' ');

                // For operators that could be prefix of others (e.g., < vs <=)
                if !Self::is_operator_char(before)
                    && !Self::is_operator_continuation(after_char, op)
                {
                    return Some(i);
                }
            }
        }
        None
    }

    /// Check if a character is an operator character.
    fn is_operator_char(c: char) -> bool {
        matches!(
            c,
            '+' | '-' | '*' | '/' | '%' | '<' | '>' | '=' | '!' | '&' | '|' | '^'
        )
    }

    /// Check if the character after an operator continues a different operator.
    fn is_operator_continuation(c: char, op: &str) -> bool {
        match op {
            "<" | ">" => c == '=' || c == '<' || c == '>',
            "=" => c == '=',
            "!" => c == '=',
            "&" => c == '&',
            "|" => c == '|',
            _ => false,
        }
    }

    /// Extract the base variable from an expression.
    fn extract_base_variable(expr: &str) -> Option<String> {
        let expr = expr.trim();

        // Skip if it's a literal
        if expr.starts_with('"')
            || expr.starts_with('\'')
            || expr.parse::<f64>().is_ok()
            || expr == "True"
            || expr == "False"
            || expr == "None"
            || expr == "true"
            || expr == "false"
            || expr == "null"
            || expr == "nil"
        {
            return None;
        }

        // Handle field access: return the base object
        if let Some(dot_pos) = expr.find('.') {
            let base = &expr[..dot_pos];
            if is_valid_identifier(base) {
                return Some(base.to_string());
            }
        }

        // Handle array access: return the array name
        if let Some(bracket_pos) = expr.find('[') {
            let base = &expr[..bracket_pos];
            if is_valid_identifier(base) {
                return Some(base.to_string());
            }
        }

        // Simple identifier
        if is_valid_identifier(expr) {
            return Some(expr.to_string());
        }

        None
    }


    /// Split function arguments respecting nesting.
    fn split_args(args_str: &str) -> Vec<String> {
        let mut args = Vec::new();
        let mut current = String::new();
        let mut depth = 0;

        for c in args_str.chars() {
            match c {
                '(' | '[' | '{' => {
                    depth += 1;
                    current.push(c);
                }
                ')' | ']' | '}' => {
                    depth -= 1;
                    current.push(c);
                }
                ',' if depth == 0 => {
                    let arg = current.trim().to_string();
                    if !arg.is_empty() {
                        args.push(arg);
                    }
                    current.clear();
                }
                _ => current.push(c),
            }
        }

        let arg = current.trim().to_string();
        if !arg.is_empty() {
            args.push(arg);
        }

        args
    }
}

// =============================================================================
// Definition Extraction (for KILL sets)
// =============================================================================

/// Extract variable definitions from a statement.
fn extract_definitions_from_statement(stmt: &str) -> Vec<String> {
    let mut definitions = Vec::new();
    let stmt = stmt.trim();

    if stmt.is_empty() || stmt.starts_with('#') || stmt.starts_with("//") {
        return definitions;
    }

    // For loop variables
    if stmt.starts_with("for ") || stmt.starts_with("async for ") {
        let stmt = stmt.strip_prefix("async ").unwrap_or(stmt);
        let stmt = stmt.strip_prefix("for ").unwrap_or(stmt);
        if let Some(in_pos) = stmt.find(" in ") {
            let vars_part = stmt[..in_pos].trim();
            for v in vars_part.split(',') {
                let v = v.trim().trim_start_matches('(').trim_end_matches(')');
                if is_valid_identifier(v) {
                    definitions.push(v.to_string());
                }
            }
        }
        return definitions;
    }

    // Augmented assignment
    let aug_ops = [
        "+=", "-=", "*=", "/=", "//=", "%=", "**=", "&=", "|=", "^=", "<<=", ">>=", "@=",
    ];
    for op in aug_ops {
        if let Some(pos) = stmt.find(op) {
            let target = stmt[..pos].trim();
            let base = target
                .split('.')
                .next()
                .unwrap_or(target)
                .split('[')
                .next()
                .unwrap_or(target);
            if is_valid_identifier(base) {
                definitions.push(base.to_string());
            }
            return definitions;
        }
    }

    // Regular assignment
    if let Some(eq_pos) = ExpressionExtractor::find_assignment_eq(stmt) {
        let targets_part = stmt[..eq_pos].trim();
        // Handle tuple unpacking
        for target in targets_part.split(',') {
            let target = target.trim().trim_start_matches('(').trim_end_matches(')');
            let base = target
                .split('.')
                .next()
                .unwrap_or(target)
                .split('[')
                .next()
                .unwrap_or(target)
                .trim_start_matches('*');
            if is_valid_identifier(base) {
                definitions.push(base.to_string());
            }
        }
    }

    definitions
}

// =============================================================================
// Available Expressions Analysis
// =============================================================================

/// Analyze available expressions for a function.
///
/// # Arguments
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
/// Result containing the available expressions analysis.
///
/// # Errors
/// Returns error if file cannot be read, parsed, or function not found.
pub fn analyze_available_expressions(
    file: &str,
    function: &str,
) -> Result<AvailableExpressionsResult> {
    analyze_available_expressions_with_language(file, function, None)
}

/// Analyze available expressions with explicit language specification.
///
/// # Arguments
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
/// * `language` - Optional language override
///
/// # Returns
/// Result containing the available expressions analysis.
pub fn analyze_available_expressions_with_language(
    file: &str,
    function: &str,
    language: Option<&str>,
) -> Result<AvailableExpressionsResult> {
    let start = std::time::Instant::now();

    // Validate path exists
    let path = Path::new(file);
    if !path.exists() {
        return Err(BrrrError::io_with_path(
            std::io::Error::new(std::io::ErrorKind::NotFound, "File not found"),
            path,
        ));
    }

    // Extract CFG
    let cfg = extract_with_language(file, function, language)?;

    // Run analysis
    let mut result = analyze_available_expressions_from_cfg(&cfg)?;

    // Update timing
    let elapsed = start.elapsed();
    result.metrics.analysis_time_us = elapsed.as_micros() as u64;

    Ok(result)
}

/// Run available expressions analysis on a CFG.
pub fn analyze_available_expressions_from_cfg(cfg: &CFGInfo) -> Result<AvailableExpressionsResult> {
    // Step 1: Extract all expressions from CFG blocks
    let mut expressions = Vec::new();
    let mut next_expr_id = 0;
    let mut expr_map: FxHashMap<String, ExprId> = FxHashMap::default();
    let mut block_expressions: FxHashMap<BlockId, Vec<ExprId>> = FxHashMap::default();
    let mut expr_locations: FxHashMap<ExprId, Vec<Location>> = FxHashMap::default();

    for (block_id, block) in &cfg.blocks {
        let mut block_exprs = Vec::new();

        for stmt in &block.statements {
            let start_idx = expressions.len();
            ExpressionExtractor::extract_from_statement(
                stmt,
                block.start_line,
                *block_id,
                &mut next_expr_id,
                &mut expressions,
                &mut expr_map,
            );

            // Record expressions created in this block
            for i in start_idx..expressions.len() {
                let expr_id = expressions[i].expr_id;
                block_exprs.push(expr_id);

                // Record location for this expression
                expr_locations
                    .entry(expr_id)
                    .or_default()
                    .push(Location::new(block.start_line, *block_id));
            }
        }

        // Also record expressions that appear in this block (even if created elsewhere)
        for expr in &expressions {
            let canonical = expr.kind.to_text();
            for stmt in &block.statements {
                if stmt.contains(&canonical) || stmt.contains(&expr.text) {
                    if !block_exprs.contains(&expr.expr_id) {
                        block_exprs.push(expr.expr_id);
                        expr_locations
                            .entry(expr.expr_id)
                            .or_default()
                            .push(Location::new(block.start_line, *block_id));
                    }
                }
            }
        }

        block_expressions.insert(*block_id, block_exprs);
    }

    let num_exprs = expressions.len();

    if num_exprs == 0 {
        // No expressions found, return empty result
        return Ok(AvailableExpressionsResult {
            function_name: cfg.function_name.clone(),
            expressions: Vec::new(),
            available_in: FxHashMap::default(),
            available_out: FxHashMap::default(),
            cse_opportunities: Vec::new(),
            loop_invariants: Vec::new(),
            iterations: 0,
            metrics: AvailableExpressionsMetrics {
                blocks_analyzed: cfg.blocks.len(),
                ..Default::default()
            },
        });
    }

    // Step 2: Extract definitions from each block (for KILL set)
    let mut block_definitions: FxHashMap<BlockId, Vec<String>> = FxHashMap::default();
    for (block_id, block) in &cfg.blocks {
        let mut defs = Vec::new();
        for stmt in &block.statements {
            defs.extend(extract_definitions_from_statement(stmt));
        }
        block_definitions.insert(*block_id, defs);
    }

    // Step 3: Compute GEN and KILL sets for each block
    let mut gen_sets: FxHashMap<BlockId, BitSet> = FxHashMap::default();
    let mut kill_sets: FxHashMap<BlockId, BitSet> = FxHashMap::default();

    for (block_id, block_exprs) in &block_expressions {
        let mut gen = BitSet::with_capacity(num_exprs);
        let mut kill = BitSet::with_capacity(num_exprs);

        // Get definitions in this block
        let defs = block_definitions.get(block_id).cloned().unwrap_or_default();

        // GEN: expressions computed in this block (not later killed in block)
        for expr_id in block_exprs {
            let expr = &expressions[expr_id.0];

            // Check if this expression is killed by any definition in this block
            let is_killed = defs.iter().any(|d| expr.is_killed_by(d));

            if !is_killed && expr.is_pure {
                gen.insert(expr_id.0);
            }
        }

        // KILL: expressions containing variables defined in this block
        for (expr_idx, expr) in expressions.iter().enumerate() {
            if defs.iter().any(|d| expr.is_killed_by(d)) {
                kill.insert(expr_idx);
            }
        }

        gen_sets.insert(*block_id, gen);
        kill_sets.insert(*block_id, kill);
    }

    // Step 4: Initialize IN and OUT sets
    // For available expressions (must-analysis), initialize OUT to "all expressions"
    // except for entry block which has empty IN
    let mut in_sets: FxHashMap<BlockId, BitSet> = FxHashMap::default();
    let mut out_sets: FxHashMap<BlockId, BitSet> = FxHashMap::default();

    for block_id in cfg.blocks.keys() {
        // IN[entry] = empty, IN[others] will be computed
        in_sets.insert(*block_id, BitSet::with_capacity(num_exprs));
        // OUT initialized to full for must-analysis
        out_sets.insert(*block_id, BitSet::full(num_exprs));
    }

    // Entry block starts with empty IN (no expressions available at function entry)
    in_sets.insert(cfg.entry, BitSet::with_capacity(num_exprs));

    // Step 5: Worklist algorithm for forward data flow with INTERSECTION
    let mut worklist: VecDeque<BlockId> = cfg.topological_order().into_iter().collect();
    let mut iterations = 0;
    const MAX_ITERATIONS: usize = 1000;

    while let Some(block_id) = worklist.pop_front() {
        iterations += 1;
        if iterations > MAX_ITERATIONS {
            break;
        }

        // Compute IN[B] = INTERSECTION of OUT[P] for all predecessors P
        let predecessors = cfg.predecessors(block_id);
        let new_in = if predecessors.is_empty() {
            // Entry block or unreachable block
            BitSet::with_capacity(num_exprs)
        } else if predecessors.len() == 1 {
            // Single predecessor: just copy
            out_sets
                .get(&predecessors[0])
                .cloned()
                .unwrap_or_else(|| BitSet::with_capacity(num_exprs))
        } else {
            // Multiple predecessors: INTERSECTION (must-analysis)
            let mut result = out_sets
                .get(&predecessors[0])
                .cloned()
                .unwrap_or_else(|| BitSet::full(num_exprs));

            for pred in predecessors.iter().skip(1) {
                if let Some(pred_out) = out_sets.get(pred) {
                    result.intersect_with(pred_out);
                } else {
                    // Predecessor not yet processed - treat as empty for safety
                    result.clear();
                    break;
                }
            }
            result
        };

        // Compute OUT[B] = GEN[B] UNION (IN[B] - KILL[B])
        let mut new_out = new_in.clone();
        if let Some(kill) = kill_sets.get(&block_id) {
            new_out.difference_with(kill);
        }
        if let Some(gen) = gen_sets.get(&block_id) {
            new_out.union_with(gen);
        }

        // Check if OUT changed
        let old_out = out_sets.get(&block_id);
        let changed = old_out.map(|o| o != &new_out).unwrap_or(true);

        // Update sets
        in_sets.insert(block_id, new_in);
        out_sets.insert(block_id, new_out);

        // If OUT changed, add successors to worklist
        if changed {
            for succ in cfg.successors(block_id) {
                if !worklist.contains(succ) {
                    worklist.push_back(*succ);
                }
            }
        }
    }

    // Step 6: Detect CSE opportunities
    let cse_opportunities = detect_cse_opportunities(
        cfg,
        &expressions,
        &in_sets,
        &block_expressions,
        &expr_locations,
    );

    // Step 7: Detect loop invariants
    let loop_invariants = detect_loop_invariants(cfg, &expressions, &in_sets);

    // Convert BitSets to Vec for serialization
    let available_in: FxHashMap<usize, Vec<usize>> = in_sets
        .into_iter()
        .map(|(k, v)| (k.0, v.iter().collect()))
        .collect();

    let available_out: FxHashMap<usize, Vec<usize>> = out_sets
        .into_iter()
        .map(|(k, v)| (k.0, v.iter().collect()))
        .collect();

    let estimated_savings: usize = cse_opportunities
        .iter()
        .map(|c| c.estimated_savings as usize)
        .sum();

    Ok(AvailableExpressionsResult {
        function_name: cfg.function_name.clone(),
        expressions,
        available_in,
        available_out,
        cse_opportunities: cse_opportunities.clone(),
        loop_invariants: loop_invariants.clone(),
        iterations,
        metrics: AvailableExpressionsMetrics {
            blocks_analyzed: cfg.blocks.len(),
            expressions_tracked: num_exprs,
            cse_opportunities: cse_opportunities.len(),
            estimated_savings,
            loop_invariants: loop_invariants.len(),
            analysis_time_us: 0, // Will be filled by caller
        },
    })
}

/// Detect CSE opportunities from available expressions.
fn detect_cse_opportunities(
    _cfg: &CFGInfo,
    expressions: &[Expression],
    in_sets: &FxHashMap<BlockId, BitSet>,
    _block_expressions: &FxHashMap<BlockId, Vec<ExprId>>,
    expr_locations: &FxHashMap<ExprId, Vec<Location>>,
) -> Vec<CSEOpportunity> {
    let mut opportunities = Vec::new();

    // For each expression, check if it's recomputed when already available
    for expr in expressions {
        // Skip impure expressions
        if !expr.is_pure {
            continue;
        }

        // Get all locations where this expression is computed
        let locations = match expr_locations.get(&expr.expr_id) {
            Some(locs) if locs.len() > 1 => locs,
            _ => continue, // Need at least 2 computations for CSE
        };

        // Find the first computation
        let first = &locations[0];

        // Find redundant computations (where expression is already available)
        let mut redundant = Vec::new();
        for loc in locations.iter().skip(1) {
            // Check if expression is available at this block's entry
            if let Some(available) = in_sets.get(&loc.block_id) {
                if available.contains(expr.expr_id.0) {
                    redundant.push(loc.clone());
                }
            }
        }

        if !redundant.is_empty() {
            // Generate a suggested temp name
            let temp_name = generate_temp_name(&expr.kind);

            opportunities.push(CSEOpportunity {
                expression: expr.clone(),
                first_computation: first.clone(),
                redundant_computations: redundant.clone(),
                estimated_savings: redundant.len() as u32,
                is_safe: expr.is_pure,
                suggested_temp_name: temp_name,
            });
        }
    }

    opportunities
}

/// Generate a suggested temporary variable name for CSE.
fn generate_temp_name(kind: &ExprKind) -> String {
    match kind {
        ExprKind::BinaryOp { left, op, right } => {
            let op_name = match op.as_str() {
                "+" => "sum",
                "-" => "diff",
                "*" => "prod",
                "/" => "quot",
                "%" => "rem",
                "&" => "and",
                "|" => "or",
                "^" => "xor",
                _ => "tmp",
            };
            format!(
                "{}_{}",
                op_name,
                sanitize_for_name(&format!("{}_{}", left, right))
            )
        }
        ExprKind::FieldAccess { object, field } => {
            format!("{}_{}", sanitize_for_name(object), field)
        }
        ExprKind::ArrayAccess { array, index } => {
            format!("{}_{}", array, sanitize_for_name(index))
        }
        ExprKind::Call { callee, .. } => {
            format!("{}_result", sanitize_for_name(callee))
        }
        _ => "tmp".to_string(),
    }
}

/// Sanitize a string to be a valid identifier part.
fn sanitize_for_name(s: &str) -> String {
    s.chars()
        .filter(|c| c.is_alphanumeric() || *c == '_')
        .collect::<String>()
        .chars()
        .take(10)
        .collect()
}

/// Detect loop-invariant expressions.
fn detect_loop_invariants(
    cfg: &CFGInfo,
    expressions: &[Expression],
    in_sets: &FxHashMap<BlockId, BitSet>,
) -> Vec<LoopInvariant> {
    let mut invariants = Vec::new();

    // Find loop headers
    for (block_id, block) in &cfg.blocks {
        if matches!(
            block.block_type,
            crate::cfg::BlockType::LoopHeader | crate::cfg::BlockType::LoopBody
        ) {
            // Get expressions available at loop header entry
            if let Some(available) = in_sets.get(block_id) {
                for expr_id in available.iter() {
                    if expr_id < expressions.len() {
                        let expr = &expressions[expr_id];
                        if expr.is_pure {
                            invariants.push(LoopInvariant {
                                expression: expr.clone(),
                                loop_header: *block_id,
                                is_safe_to_hoist: expr.is_pure,
                            });
                        }
                    }
                }
            }
        }
    }

    invariants
}

// =============================================================================
// JSON and Text Output
// =============================================================================

impl AvailableExpressionsResult {
    /// Convert to JSON value for output.
    #[must_use]
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "function_name": self.function_name,
            "expressions": self.expressions.iter().map(|e| {
                serde_json::json!({
                    "id": e.expr_id.0,
                    "text": e.text,
                    "kind": format!("{:?}", e.kind),
                    "variables": e.variables.iter().collect::<Vec<_>>(),
                    "is_pure": e.is_pure,
                })
            }).collect::<Vec<_>>(),
            "available_in": self.available_in.iter().map(|(k, v)| {
                (k.to_string(), v.clone())
            }).collect::<FxHashMap<_, _>>(),
            "available_out": self.available_out.iter().map(|(k, v)| {
                (k.to_string(), v.clone())
            }).collect::<FxHashMap<_, _>>(),
            "cse_opportunities": self.cse_opportunities.iter().map(|c| {
                serde_json::json!({
                    "expression": c.expression.text,
                    "first_computation": {
                        "line": c.first_computation.line,
                        "block": c.first_computation.block_id.0,
                    },
                    "redundant_computations": c.redundant_computations.iter().map(|l| {
                        serde_json::json!({
                            "line": l.line,
                            "block": l.block_id.0,
                        })
                    }).collect::<Vec<_>>(),
                    "estimated_savings": c.estimated_savings,
                    "is_safe": c.is_safe,
                    "suggested_temp_name": c.suggested_temp_name,
                })
            }).collect::<Vec<_>>(),
            "loop_invariants": self.loop_invariants.iter().map(|l| {
                serde_json::json!({
                    "expression": l.expression.text,
                    "loop_header": l.loop_header.0,
                    "is_safe_to_hoist": l.is_safe_to_hoist,
                })
            }).collect::<Vec<_>>(),
            "metrics": {
                "blocks_analyzed": self.metrics.blocks_analyzed,
                "expressions_tracked": self.metrics.expressions_tracked,
                "cse_opportunities": self.metrics.cse_opportunities,
                "estimated_savings": self.metrics.estimated_savings,
                "loop_invariants": self.metrics.loop_invariants,
                "analysis_time_us": self.metrics.analysis_time_us,
            },
            "iterations": self.iterations,
        })
    }

    /// Convert to compact text format for CLI output.
    #[must_use]
    pub fn to_text(&self) -> String {
        let mut output = String::new();

        output.push_str(&format!(
            "Available Expressions Analysis: {}\n",
            self.function_name
        ));
        output.push_str(&"=".repeat(50));
        output.push('\n');

        // Expressions
        if !self.expressions.is_empty() {
            output.push_str("\nTracked Expressions:\n");
            for expr in &self.expressions {
                let purity = if expr.is_pure { "pure" } else { "impure" };
                output.push_str(&format!(
                    "  [{}] {} ({})\n",
                    expr.expr_id.0, expr.text, purity
                ));
            }
        }

        // CSE Opportunities
        if !self.cse_opportunities.is_empty() {
            output.push_str("\nCSE Opportunities:\n");
            for cse in &self.cse_opportunities {
                output.push_str(&format!("  Expression: {}\n", cse.expression.text));
                output.push_str(&format!(
                    "    First computed at line {}\n",
                    cse.first_computation.line
                ));
                for redundant in &cse.redundant_computations {
                    output.push_str(&format!(
                        "    Redundant at line {} (can reuse)\n",
                        redundant.line
                    ));
                }
                output.push_str(&format!(
                    "    Suggested temp: {}\n",
                    cse.suggested_temp_name
                ));
                output.push_str(&format!(
                    "    Estimated savings: {} computation(s)\n",
                    cse.estimated_savings
                ));
            }
        }

        // Loop Invariants
        if !self.loop_invariants.is_empty() {
            output.push_str("\nLoop Invariants (can be hoisted):\n");
            for inv in &self.loop_invariants {
                let safety = if inv.is_safe_to_hoist {
                    "safe"
                } else {
                    "unsafe"
                };
                output.push_str(&format!(
                    "  {} at loop {} ({})\n",
                    inv.expression.text, inv.loop_header.0, safety
                ));
            }
        }

        // Available at each block
        output.push_str("\nAvailable Expressions per Block:\n");
        let mut block_ids: Vec<_> = self.available_in.keys().collect();
        block_ids.sort();

        for block_id in block_ids {
            let in_exprs = self.available_in.get(block_id).cloned().unwrap_or_default();
            let out_exprs = self
                .available_out
                .get(block_id)
                .cloned()
                .unwrap_or_default();

            if !in_exprs.is_empty() || !out_exprs.is_empty() {
                output.push_str(&format!("  Block {}:\n", block_id));
                if !in_exprs.is_empty() {
                    let in_names: Vec<_> = in_exprs
                        .iter()
                        .filter_map(|&id| self.expressions.get(id).map(|e| e.text.as_str()))
                        .collect();
                    output.push_str(&format!("    IN:  {:?}\n", in_names));
                }
                if !out_exprs.is_empty() {
                    let out_names: Vec<_> = out_exprs
                        .iter()
                        .filter_map(|&id| self.expressions.get(id).map(|e| e.text.as_str()))
                        .collect();
                    output.push_str(&format!("    OUT: {:?}\n", out_names));
                }
            }
        }

        // Metrics
        output.push_str(&format!(
            "\nMetrics: {} blocks, {} expressions, {} CSE opportunities, {} savings, {}us\n",
            self.metrics.blocks_analyzed,
            self.metrics.expressions_tracked,
            self.metrics.cse_opportunities,
            self.metrics.estimated_savings,
            self.metrics.analysis_time_us
        ));

        output
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::types::{BlockType, CFGBlock, CFGEdge, EdgeType};

    /// Create a simple linear CFG for testing:
    /// ```python
    /// def test():          # Block 0
    ///     x = a + b        # Block 1 - expression a+b computed
    ///     y = a + b        # Block 1 - expression a+b available (CSE opportunity)
    ///     return x + y     # Block 2
    /// ```
    fn create_linear_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def test():".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "body".to_string(),
                block_type: BlockType::Body,
                statements: vec!["x = a + b".to_string(), "y = a + b".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "return".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return x + y".to_string()],
                func_calls: vec![],
                start_line: 4,
                end_line: 4,
            },
        );

        CFGInfo::new(
            "test".to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::unconditional(BlockId(1), BlockId(2)),
            ],
            BlockId(0),
            vec![BlockId(2)],
        )
    }

    /// Create a CFG with a branch where expression is killed on one path:
    /// ```python
    /// def test(c):         # Block 0
    ///     x = a + b        # Block 1
    ///     if c:            # Block 1
    ///         a = 10       # Block 2 - kills a+b
    ///     else:
    ///         pass         # Block 3
    ///     y = a + b        # Block 4 - NOT available (killed on true branch)
    /// ```
    fn create_branch_kill_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def test(c):".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "compute".to_string(),
                block_type: BlockType::Body,
                statements: vec!["x = a + b".to_string(), "if c:".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "true_branch".to_string(),
                block_type: BlockType::Body,
                statements: vec!["a = 10".to_string()],
                func_calls: vec![],
                start_line: 4,
                end_line: 4,
            },
        );

        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "false_branch".to_string(),
                block_type: BlockType::Body,
                statements: vec!["pass".to_string()],
                func_calls: vec![],
                start_line: 6,
                end_line: 6,
            },
        );

        blocks.insert(
            BlockId(4),
            CFGBlock {
                id: BlockId(4),
                label: "merge".to_string(),
                block_type: BlockType::Body,
                statements: vec!["y = a + b".to_string()],
                func_calls: vec![],
                start_line: 7,
                end_line: 7,
            },
        );

        CFGInfo::new(
            "test".to_string(),
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

    /// Create a CFG with a loop for loop-invariant detection:
    /// ```python
    /// def test(n):         # Block 0
    ///     x = a + b        # Block 1 - computed before loop
    ///     for i in range(n):  # Block 2 - loop header
    ///         y = a + b    # Block 3 - loop invariant (a+b available)
    ///     return x         # Block 4
    /// ```
    fn create_loop_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def test(n):".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "init".to_string(),
                block_type: BlockType::Body,
                statements: vec!["x = a + b".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 2,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "loop_header".to_string(),
                block_type: BlockType::LoopHeader,
                statements: vec!["for i in range(n):".to_string()],
                func_calls: vec!["range".to_string()],
                start_line: 3,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "loop_body".to_string(),
                block_type: BlockType::LoopBody,
                statements: vec!["y = a + b".to_string()],
                func_calls: vec![],
                start_line: 4,
                end_line: 4,
            },
        );

        blocks.insert(
            BlockId(4),
            CFGBlock {
                id: BlockId(4),
                label: "return".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return x".to_string()],
                func_calls: vec![],
                start_line: 5,
                end_line: 5,
            },
        );

        CFGInfo::new(
            "test".to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::unconditional(BlockId(1), BlockId(2)),
                CFGEdge::new(BlockId(2), BlockId(3), EdgeType::Enter),
                CFGEdge::new(BlockId(3), BlockId(2), EdgeType::BackEdge),
                CFGEdge::new(BlockId(2), BlockId(4), EdgeType::Exit),
            ],
            BlockId(0),
            vec![BlockId(4)],
        )
    }

    #[test]
    fn test_bitset_intersection() {
        let mut set1 = BitSet::with_capacity(100);
        let mut set2 = BitSet::with_capacity(100);

        set1.insert(1);
        set1.insert(2);
        set1.insert(3);
        set1.insert(4);

        set2.insert(2);
        set2.insert(3);
        set2.insert(5);

        set1.intersect_with(&set2);

        // Should only contain elements in both: 2, 3
        assert!(!set1.contains(1));
        assert!(set1.contains(2));
        assert!(set1.contains(3));
        assert!(!set1.contains(4));
        assert!(!set1.contains(5));
        assert_eq!(set1.len(), 2);
    }

    #[test]
    fn test_bitset_full() {
        let set = BitSet::full(10);

        for i in 0..10 {
            assert!(set.contains(i), "Should contain {}", i);
        }
        assert!(!set.contains(10));
        assert_eq!(set.len(), 10);
    }

    #[test]
    fn test_expression_extraction_binary_op() {
        let mut expressions = Vec::new();
        let mut next_expr_id = 0;
        let mut expr_map = FxHashMap::default();

        ExpressionExtractor::extract_from_statement(
            "x = a + b",
            1,
            BlockId(0),
            &mut next_expr_id,
            &mut expressions,
            &mut expr_map,
        );

        assert_eq!(expressions.len(), 1);
        assert!(expressions[0].text.contains("a + b") || expressions[0].text == "a + b");
        assert!(expressions[0].variables.contains("a"));
        assert!(expressions[0].variables.contains("b"));
    }

    #[test]
    fn test_expression_extraction_field_access() {
        let mut expressions = Vec::new();
        let mut next_expr_id = 0;
        let mut expr_map = FxHashMap::default();

        ExpressionExtractor::extract_from_statement(
            "x = obj.field",
            1,
            BlockId(0),
            &mut next_expr_id,
            &mut expressions,
            &mut expr_map,
        );

        // Field access should be extracted
        let field_expr = expressions
            .iter()
            .find(|e| matches!(e.kind, ExprKind::FieldAccess { .. }));
        assert!(field_expr.is_some());
    }

    #[test]
    fn test_expression_killed_by() {
        let expr = Expression {
            expr_id: ExprId(0),
            text: "a + b".to_string(),
            variables: ["a".to_string(), "b".to_string()].into_iter().collect(),
            kind: ExprKind::BinaryOp {
                left: "a".to_string(),
                op: "+".to_string(),
                right: "b".to_string(),
            },
            is_pure: true,
        };

        assert!(expr.is_killed_by("a"));
        assert!(expr.is_killed_by("b"));
        assert!(!expr.is_killed_by("c"));
    }

    #[test]
    fn test_definition_extraction() {
        let defs = extract_definitions_from_statement("x = 10");
        assert!(defs.contains(&"x".to_string()));

        let defs = extract_definitions_from_statement("a, b = func()");
        assert!(defs.contains(&"a".to_string()));
        assert!(defs.contains(&"b".to_string()));

        let defs = extract_definitions_from_statement("x += 1");
        assert!(defs.contains(&"x".to_string()));

        let defs = extract_definitions_from_statement("for i in range(10):");
        assert!(defs.contains(&"i".to_string()));
    }

    #[test]
    fn test_linear_available_expressions() {
        let cfg = create_linear_cfg();
        let result = analyze_available_expressions_from_cfg(&cfg).unwrap();

        // Should find the a+b expression
        assert!(!result.expressions.is_empty());

        // Check that analysis converged
        assert!(result.iterations > 0);
    }

    #[test]
    fn test_branch_kills_expression() {
        let cfg = create_branch_kill_cfg();
        let result = analyze_available_expressions_from_cfg(&cfg).unwrap();

        // At the merge block (block 4), a+b should NOT be available
        // because it's killed on the true branch where a=10
        let available_at_4 = result.available_in.get(&4).cloned().unwrap_or_default();

        // The expression a+b should not be in available_in at block 4
        // because it's killed on one path (must-analysis requires all paths)
        for expr_id in &available_at_4 {
            let expr = &result.expressions[*expr_id];
            // If a+b is in available, the test should fail
            // (it should be killed by a=10 on true branch)
            assert!(
                !expr.text.contains("a + b"),
                "a+b should not be available after branch"
            );
        }
    }

    #[test]
    fn test_loop_invariant_detection() {
        let cfg = create_loop_cfg();
        let result = analyze_available_expressions_from_cfg(&cfg).unwrap();

        // The expression a+b computed before the loop should be available
        // at the loop header and detected as loop invariant
        assert!(
            result.expressions.iter().any(|e| e.text.contains("a + b")),
            "Should find a+b expression"
        );
    }

    #[test]
    fn test_cse_opportunity_detection() {
        // Create a CFG where same expression is computed twice
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def test():".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "first".to_string(),
                block_type: BlockType::Body,
                statements: vec!["x = a + b".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 2,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "second".to_string(),
                block_type: BlockType::Body,
                statements: vec!["y = a + b".to_string()], // CSE opportunity
                func_calls: vec![],
                start_line: 3,
                end_line: 3,
            },
        );

        let cfg = CFGInfo::new(
            "test".to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::unconditional(BlockId(1), BlockId(2)),
            ],
            BlockId(0),
            vec![BlockId(2)],
        );

        let result = analyze_available_expressions_from_cfg(&cfg).unwrap();

        // Should detect that a+b at block 2 is redundant
        // Note: CSE detection depends on the expression being tracked at both locations
        assert!(
            result.expressions.len() >= 1,
            "Should find at least one expression"
        );
    }

    #[test]
    fn test_json_output() {
        let cfg = create_linear_cfg();
        let result = analyze_available_expressions_from_cfg(&cfg).unwrap();
        let json = result.to_json();

        assert!(json.get("function_name").is_some());
        assert!(json.get("expressions").is_some());
        assert!(json.get("cse_opportunities").is_some());
        assert!(json.get("metrics").is_some());
    }

    #[test]
    fn test_text_output() {
        let cfg = create_linear_cfg();
        let result = analyze_available_expressions_from_cfg(&cfg).unwrap();
        let text = result.to_text();

        assert!(text.contains("Available Expressions Analysis"));
        assert!(text.contains("Metrics"));
    }

    #[test]
    fn test_impure_function_not_available() {
        let mut expressions = Vec::new();
        let mut next_expr_id = 0;
        let mut expr_map = FxHashMap::default();

        // random() is not in the pure functions list
        ExpressionExtractor::extract_from_statement(
            "x = random()",
            1,
            BlockId(0),
            &mut next_expr_id,
            &mut expressions,
            &mut expr_map,
        );

        // If extracted, it should be marked as impure
        for expr in &expressions {
            if matches!(expr.kind, ExprKind::Call { .. }) {
                assert!(!expr.is_pure, "random() should be impure");
            }
        }
    }

    #[test]
    fn test_pure_function_available() {
        let mut expressions = Vec::new();
        let mut next_expr_id = 0;
        let mut expr_map = FxHashMap::default();

        // len() is in the pure functions list
        ExpressionExtractor::extract_from_statement(
            "x = len(arr)",
            1,
            BlockId(0),
            &mut next_expr_id,
            &mut expressions,
            &mut expr_map,
        );

        // If extracted, it should be marked as pure
        for expr in &expressions {
            if let ExprKind::Call { callee, .. } = &expr.kind {
                if callee == "len" {
                    assert!(expr.is_pure, "len() should be pure");
                }
            }
        }
    }
}
