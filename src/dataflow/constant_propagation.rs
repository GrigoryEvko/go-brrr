//! Constant Propagation Dataflow Analysis.
//!
//! This module implements forward dataflow analysis to track which variables
//! have known constant values at each program point. It detects:
//! - Constant folding opportunities (e.g., `x = 2 + 3` can be folded to `x = 5`)
//! - Dead branches (e.g., `if (true)` or `if (false)`)
//! - Unreachable code following dead branches
//!
//! # Lattice Structure
//!
//! The analysis uses a three-level lattice for each variable:
//! ```text
//!        Top (unknown/not constant)
//!       /   \
//!  Constant(v1) ... Constant(vn)
//!       \   /
//!       Bottom (undefined/unreachable)
//! ```
//!
//! The meet operation (at join points) is:
//! - `Constant(v) meet Constant(v) = Constant(v)`
//! - `Constant(v1) meet Constant(v2) = Top` (if v1 != v2)
//! - `Top meet anything = Top`
//! - `Bottom meet x = x`
//!
//! # Algorithm
//!
//! Uses worklist-based forward iteration:
//! 1. Initialize all variables to `Bottom` (undefined)
//! 2. Process entry block, setting parameters to `Top` (unknown from caller)
//! 3. For each statement, apply transfer function
//! 4. At control flow merge points, apply meet operation
//! 5. Repeat until fixpoint (no changes)
//!
//! # Limitations
//!
//! - Intraprocedural only (function calls set result to `Top`)
//! - Does not track array/object element constants
//! - String operations are not folded (only tracked as constants)

use crate::cfg::{BlockId, CFGInfo, EdgeType};
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;

// =============================================================================
// Core Types
// =============================================================================

/// Source code location for reporting.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Location {
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed, optional)
    pub column: Option<usize>,
    /// Block ID in CFG
    pub block_id: BlockId,
    /// Statement index within block
    pub stmt_index: usize,
}

impl Location {
    /// Create a new location.
    #[must_use]
    pub fn new(line: usize, block_id: BlockId, stmt_index: usize) -> Self {
        Self {
            line,
            column: None,
            block_id,
            stmt_index,
        }
    }

    /// Create a location with column information.
    #[must_use]
    pub fn with_column(line: usize, column: usize, block_id: BlockId, stmt_index: usize) -> Self {
        Self {
            line,
            column: Some(column),
            block_id,
            stmt_index,
        }
    }
}

/// Concrete constant value types.
///
/// Represents the actual runtime value for constants that can be tracked.
/// Used inside `ConstantValue::Constant` to hold the specific value.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Value {
    /// Integer constant (64-bit signed)
    Int(i64),
    /// Floating-point constant (64-bit)
    Float(f64),
    /// String constant
    String(String),
    /// Boolean constant
    Bool(bool),
    /// Null/None/nil constant
    Null,
}

impl Value {
    /// Check if this value is truthy (for branch analysis).
    ///
    /// Returns `Some(true)` for truthy values, `Some(false)` for falsy values.
    /// This follows Python/JavaScript semantics where:
    /// - `false`, `0`, `0.0`, `""`, `null` are falsy
    /// - Everything else is truthy
    #[must_use]
    pub fn is_truthy(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Int(i) => *i != 0,
            Value::Float(f) => *f != 0.0 && !f.is_nan(),
            Value::String(s) => !s.is_empty(),
            Value::Null => false,
        }
    }

    /// Try to perform binary arithmetic on two values.
    ///
    /// Returns `None` if the operation is not applicable (type mismatch, etc.)
    #[must_use]
    pub fn binary_op(&self, op: BinaryOp, rhs: &Value) -> Option<Value> {
        match (self, op, rhs) {
            // Integer arithmetic
            (Value::Int(a), BinaryOp::Add, Value::Int(b)) => Some(Value::Int(a.wrapping_add(*b))),
            (Value::Int(a), BinaryOp::Sub, Value::Int(b)) => Some(Value::Int(a.wrapping_sub(*b))),
            (Value::Int(a), BinaryOp::Mul, Value::Int(b)) => Some(Value::Int(a.wrapping_mul(*b))),
            (Value::Int(a), BinaryOp::Div, Value::Int(b)) if *b != 0 => {
                Some(Value::Int(a.wrapping_div(*b)))
            }
            (Value::Int(a), BinaryOp::Mod, Value::Int(b)) if *b != 0 => {
                Some(Value::Int(a.wrapping_rem(*b)))
            }
            (Value::Int(a), BinaryOp::BitAnd, Value::Int(b)) => Some(Value::Int(*a & *b)),
            (Value::Int(a), BinaryOp::BitOr, Value::Int(b)) => Some(Value::Int(*a | *b)),
            (Value::Int(a), BinaryOp::BitXor, Value::Int(b)) => Some(Value::Int(*a ^ *b)),
            (Value::Int(a), BinaryOp::Shl, Value::Int(b)) if *b >= 0 && *b < 64 => {
                Some(Value::Int(a.wrapping_shl(*b as u32)))
            }
            (Value::Int(a), BinaryOp::Shr, Value::Int(b)) if *b >= 0 && *b < 64 => {
                Some(Value::Int(a.wrapping_shr(*b as u32)))
            }

            // Float arithmetic
            (Value::Float(a), BinaryOp::Add, Value::Float(b)) => Some(Value::Float(*a + *b)),
            (Value::Float(a), BinaryOp::Sub, Value::Float(b)) => Some(Value::Float(*a - *b)),
            (Value::Float(a), BinaryOp::Mul, Value::Float(b)) => Some(Value::Float(*a * *b)),
            (Value::Float(a), BinaryOp::Div, Value::Float(b)) => Some(Value::Float(*a / *b)),

            // Mixed int/float (promote to float)
            (Value::Int(a), BinaryOp::Add, Value::Float(b)) => Some(Value::Float(*a as f64 + *b)),
            (Value::Float(a), BinaryOp::Add, Value::Int(b)) => Some(Value::Float(*a + *b as f64)),
            (Value::Int(a), BinaryOp::Sub, Value::Float(b)) => Some(Value::Float(*a as f64 - *b)),
            (Value::Float(a), BinaryOp::Sub, Value::Int(b)) => Some(Value::Float(*a - *b as f64)),
            (Value::Int(a), BinaryOp::Mul, Value::Float(b)) => Some(Value::Float(*a as f64 * *b)),
            (Value::Float(a), BinaryOp::Mul, Value::Int(b)) => Some(Value::Float(*a * *b as f64)),
            (Value::Int(a), BinaryOp::Div, Value::Float(b)) => Some(Value::Float(*a as f64 / *b)),
            (Value::Float(a), BinaryOp::Div, Value::Int(b)) => Some(Value::Float(*a / *b as f64)),

            // String concatenation
            (Value::String(a), BinaryOp::Add, Value::String(b)) => {
                Some(Value::String(format!("{}{}", a, b)))
            }

            // Comparison operations returning booleans
            (Value::Int(a), BinaryOp::Eq, Value::Int(b)) => Some(Value::Bool(*a == *b)),
            (Value::Int(a), BinaryOp::Ne, Value::Int(b)) => Some(Value::Bool(*a != *b)),
            (Value::Int(a), BinaryOp::Lt, Value::Int(b)) => Some(Value::Bool(*a < *b)),
            (Value::Int(a), BinaryOp::Le, Value::Int(b)) => Some(Value::Bool(*a <= *b)),
            (Value::Int(a), BinaryOp::Gt, Value::Int(b)) => Some(Value::Bool(*a > *b)),
            (Value::Int(a), BinaryOp::Ge, Value::Int(b)) => Some(Value::Bool(*a >= *b)),

            (Value::Float(a), BinaryOp::Eq, Value::Float(b)) => Some(Value::Bool(*a == *b)),
            (Value::Float(a), BinaryOp::Ne, Value::Float(b)) => Some(Value::Bool(*a != *b)),
            (Value::Float(a), BinaryOp::Lt, Value::Float(b)) => Some(Value::Bool(*a < *b)),
            (Value::Float(a), BinaryOp::Le, Value::Float(b)) => Some(Value::Bool(*a <= *b)),
            (Value::Float(a), BinaryOp::Gt, Value::Float(b)) => Some(Value::Bool(*a > *b)),
            (Value::Float(a), BinaryOp::Ge, Value::Float(b)) => Some(Value::Bool(*a >= *b)),

            (Value::Bool(a), BinaryOp::Eq, Value::Bool(b)) => Some(Value::Bool(*a == *b)),
            (Value::Bool(a), BinaryOp::Ne, Value::Bool(b)) => Some(Value::Bool(*a != *b)),
            (Value::Bool(a), BinaryOp::And, Value::Bool(b)) => Some(Value::Bool(*a && *b)),
            (Value::Bool(a), BinaryOp::Or, Value::Bool(b)) => Some(Value::Bool(*a || *b)),

            (Value::String(a), BinaryOp::Eq, Value::String(b)) => Some(Value::Bool(*a == *b)),
            (Value::String(a), BinaryOp::Ne, Value::String(b)) => Some(Value::Bool(*a != *b)),
            (Value::String(a), BinaryOp::Lt, Value::String(b)) => Some(Value::Bool(*a < *b)),
            (Value::String(a), BinaryOp::Le, Value::String(b)) => Some(Value::Bool(*a <= *b)),
            (Value::String(a), BinaryOp::Gt, Value::String(b)) => Some(Value::Bool(*a > *b)),
            (Value::String(a), BinaryOp::Ge, Value::String(b)) => Some(Value::Bool(*a >= *b)),

            // Null comparisons
            (Value::Null, BinaryOp::Eq, Value::Null) => Some(Value::Bool(true)),
            (Value::Null, BinaryOp::Ne, Value::Null) => Some(Value::Bool(false)),
            (Value::Null, BinaryOp::Eq, _) => Some(Value::Bool(false)),
            (_, BinaryOp::Eq, Value::Null) => Some(Value::Bool(false)),
            (Value::Null, BinaryOp::Ne, _) => Some(Value::Bool(true)),
            (_, BinaryOp::Ne, Value::Null) => Some(Value::Bool(true)),

            _ => None,
        }
    }

    /// Try to perform unary operation on a value.
    #[must_use]
    pub fn unary_op(&self, op: UnaryOp) -> Option<Value> {
        match (self, op) {
            (Value::Int(i), UnaryOp::Neg) => Some(Value::Int(i.wrapping_neg())),
            (Value::Float(f), UnaryOp::Neg) => Some(Value::Float(-*f)),
            (Value::Bool(b), UnaryOp::Not) => Some(Value::Bool(!*b)),
            (Value::Int(i), UnaryOp::BitNot) => Some(Value::Int(!*i)),
            _ => None,
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{}", i),
            Value::Float(fl) => write!(f, "{}", fl),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Null => write!(f, "null"),
        }
    }
}

/// Binary operators for constant folding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
}

/// Unary operators for constant folding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

/// Lattice value for constant propagation.
///
/// Represents the abstract value of a variable at a program point:
/// - `Bottom`: Undefined (unreachable code or uninitialized)
/// - `Constant(v)`: Known constant value `v`
/// - `Top`: Unknown (could be any value)
///
/// The lattice ordering is: `Bottom < Constant(v) < Top`
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ConstantValue {
    /// Bottom of lattice: undefined/unreachable.
    /// This is the initial state for all variables.
    Bottom,
    /// Known constant value.
    Constant(Value),
    /// Top of lattice: unknown/not constant.
    /// Variables that could have multiple values reach this state.
    Top,
}

impl Default for ConstantValue {
    fn default() -> Self {
        ConstantValue::Bottom
    }
}

impl ConstantValue {
    /// Meet operation for combining values at join points.
    ///
    /// This implements the lattice meet (greatest lower bound):
    /// - `Bottom meet x = x` (bottom is identity)
    /// - `x meet Bottom = x`
    /// - `Top meet x = Top` (top absorbs)
    /// - `x meet Top = Top`
    /// - `Constant(v) meet Constant(v) = Constant(v)` (same constant)
    /// - `Constant(v1) meet Constant(v2) = Top` (different constants)
    #[must_use]
    pub fn meet(&self, other: &ConstantValue) -> ConstantValue {
        match (self, other) {
            // Bottom is the identity element
            (ConstantValue::Bottom, x) | (x, ConstantValue::Bottom) => x.clone(),
            // Top absorbs everything
            (ConstantValue::Top, _) | (_, ConstantValue::Top) => ConstantValue::Top,
            // Same constant stays constant
            (ConstantValue::Constant(v1), ConstantValue::Constant(v2)) => {
                if v1 == v2 {
                    ConstantValue::Constant(v1.clone())
                } else {
                    // Different constants -> Top (unknown which one)
                    ConstantValue::Top
                }
            }
        }
    }

    /// Check if this is a known constant value.
    #[must_use]
    pub fn is_constant(&self) -> bool {
        matches!(self, ConstantValue::Constant(_))
    }

    /// Check if this is the top element (unknown).
    #[must_use]
    pub fn is_top(&self) -> bool {
        matches!(self, ConstantValue::Top)
    }

    /// Check if this is the bottom element (undefined).
    #[must_use]
    pub fn is_bottom(&self) -> bool {
        matches!(self, ConstantValue::Bottom)
    }

    /// Get the constant value if this is a Constant.
    #[must_use]
    pub fn as_constant(&self) -> Option<&Value> {
        match self {
            ConstantValue::Constant(v) => Some(v),
            _ => None,
        }
    }

    /// Try to determine if this value is truthy (for branch analysis).
    ///
    /// Returns `Some(true)` or `Some(false)` if the truthiness is known,
    /// `None` if the value is unknown (Top or Bottom).
    #[must_use]
    pub fn known_truthiness(&self) -> Option<bool> {
        match self {
            ConstantValue::Constant(v) => Some(v.is_truthy()),
            _ => None,
        }
    }
}

impl std::fmt::Display for ConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantValue::Bottom => write!(f, "bottom"),
            ConstantValue::Constant(v) => write!(f, "{}", v),
            ConstantValue::Top => write!(f, "top"),
        }
    }
}

// =============================================================================
// Analysis State
// =============================================================================

/// State mapping variables to their constant values.
pub type ConstantState = FxHashMap<String, ConstantValue>;

/// Meet two states by meeting each variable individually.
fn meet_states(state1: &ConstantState, state2: &ConstantState) -> ConstantState {
    let mut result = ConstantState::default();

    // Get all variables from both states
    let all_vars: FxHashSet<_> = state1.keys().chain(state2.keys()).collect();

    for var in all_vars {
        let v1 = state1.get(var).cloned().unwrap_or(ConstantValue::Bottom);
        let v2 = state2.get(var).cloned().unwrap_or(ConstantValue::Bottom);
        result.insert(var.clone(), v1.meet(&v2));
    }

    result
}

// =============================================================================
// Expression Parsing (Simplified)
// =============================================================================

/// Parsed expression for analysis.
#[derive(Debug, Clone)]
pub enum Expression {
    /// Literal constant value
    Literal(Value),
    /// Variable reference
    Variable(String),
    /// Binary operation
    Binary {
        left: Box<Expression>,
        op: BinaryOp,
        right: Box<Expression>,
    },
    /// Unary operation
    Unary {
        op: UnaryOp,
        operand: Box<Expression>,
    },
    /// Function call (result is unknown)
    Call { name: String, args: Vec<Expression> },
    /// Unknown/unparseable expression
    Unknown(String),
}

impl Expression {
    /// Evaluate expression given current constant state.
    ///
    /// Returns the constant value if computable, otherwise Top.
    pub fn evaluate(&self, state: &ConstantState) -> ConstantValue {
        match self {
            Expression::Literal(v) => ConstantValue::Constant(v.clone()),

            Expression::Variable(name) => state.get(name).cloned().unwrap_or(ConstantValue::Top),

            Expression::Binary { left, op, right } => {
                let left_val = left.evaluate(state);
                let right_val = right.evaluate(state);

                match (&left_val, &right_val) {
                    (ConstantValue::Constant(l), ConstantValue::Constant(r)) => {
                        if let Some(result) = l.binary_op(*op, r) {
                            ConstantValue::Constant(result)
                        } else {
                            ConstantValue::Top
                        }
                    }
                    (ConstantValue::Bottom, _) | (_, ConstantValue::Bottom) => {
                        ConstantValue::Bottom
                    }
                    _ => ConstantValue::Top,
                }
            }

            Expression::Unary { op, operand } => {
                let operand_val = operand.evaluate(state);
                match &operand_val {
                    ConstantValue::Constant(v) => {
                        if let Some(result) = v.unary_op(*op) {
                            ConstantValue::Constant(result)
                        } else {
                            ConstantValue::Top
                        }
                    }
                    ConstantValue::Bottom => ConstantValue::Bottom,
                    ConstantValue::Top => ConstantValue::Top,
                }
            }

            // Function calls invalidate constants (interprocedural unknown)
            Expression::Call { .. } => ConstantValue::Top,

            Expression::Unknown(_) => ConstantValue::Top,
        }
    }
}

/// Simple expression parser for common patterns.
///
/// This is a lightweight parser that handles common constant expression patterns.
/// For complex expressions, we fall back to Unknown.
pub struct ExpressionParser;

impl ExpressionParser {
    /// Parse an expression string into structured form.
    pub fn parse(expr: &str) -> Expression {
        let expr = expr.trim();

        // Try parsing as literal
        if let Some(lit) = Self::parse_literal(expr) {
            return Expression::Literal(lit);
        }

        // Try parsing as simple variable
        if Self::is_identifier(expr) {
            return Expression::Variable(expr.to_string());
        }

        // Try parsing as binary expression (simple: a op b)
        if let Some(binary) = Self::parse_binary(expr) {
            return binary;
        }

        // Try parsing as unary expression
        if let Some(unary) = Self::parse_unary(expr) {
            return unary;
        }

        // Try parsing as function call
        if let Some(call) = Self::parse_call(expr) {
            return call;
        }

        Expression::Unknown(expr.to_string())
    }

    fn parse_literal(s: &str) -> Option<Value> {
        let s = s.trim();

        // Boolean
        if s == "true" || s == "True" || s == "TRUE" {
            return Some(Value::Bool(true));
        }
        if s == "false" || s == "False" || s == "FALSE" {
            return Some(Value::Bool(false));
        }

        // Null
        if s == "null" || s == "None" || s == "nil" || s == "NULL" {
            return Some(Value::Null);
        }

        // Integer (handle negative numbers)
        if let Ok(i) = s.parse::<i64>() {
            return Some(Value::Int(i));
        }

        // Float
        if let Ok(f) = s.parse::<f64>() {
            return Some(Value::Float(f));
        }

        // String literal (quoted)
        if (s.starts_with('"') && s.ends_with('"')) || (s.starts_with('\'') && s.ends_with('\'')) {
            if s.len() >= 2 {
                return Some(Value::String(s[1..s.len() - 1].to_string()));
            }
        }

        None
    }

    fn is_identifier(s: &str) -> bool {
        if s.is_empty() {
            return false;
        }
        let mut chars = s.chars();
        let first = chars.next().unwrap();
        if !first.is_alphabetic() && first != '_' {
            return false;
        }
        chars.all(|c| c.is_alphanumeric() || c == '_')
    }

    fn parse_binary(s: &str) -> Option<Expression> {
        // Look for binary operators (in precedence order, lowest first)
        // This is a simplified parser that looks for the leftmost lowest-precedence operator
        let operators = [
            ("||", BinaryOp::Or),
            ("or", BinaryOp::Or),
            ("&&", BinaryOp::And),
            ("and", BinaryOp::And),
            ("==", BinaryOp::Eq),
            ("!=", BinaryOp::Ne),
            ("<>", BinaryOp::Ne),
            ("<=", BinaryOp::Le),
            (">=", BinaryOp::Ge),
            ("<", BinaryOp::Lt),
            (">", BinaryOp::Gt),
            ("|", BinaryOp::BitOr),
            ("^", BinaryOp::BitXor),
            ("&", BinaryOp::BitAnd),
            ("<<", BinaryOp::Shl),
            (">>", BinaryOp::Shr),
            ("+", BinaryOp::Add),
            ("-", BinaryOp::Sub),
            ("*", BinaryOp::Mul),
            ("/", BinaryOp::Div),
            ("%", BinaryOp::Mod),
        ];

        for (op_str, op) in operators.iter() {
            // Find the operator, avoiding matches inside strings or at the start (unary)
            if let Some(pos) = Self::find_operator(s, op_str) {
                if pos > 0 && pos + op_str.len() < s.len() {
                    let left = &s[..pos];
                    let right = &s[pos + op_str.len()..];
                    if !left.trim().is_empty() && !right.trim().is_empty() {
                        return Some(Expression::Binary {
                            left: Box::new(Self::parse(left)),
                            op: *op,
                            right: Box::new(Self::parse(right)),
                        });
                    }
                }
            }
        }

        None
    }

    fn find_operator(s: &str, op: &str) -> Option<usize> {
        let mut depth = 0;
        let mut in_string = false;
        let mut string_char = ' ';
        let chars: Vec<char> = s.chars().collect();

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

            // Only look for operators at depth 0
            if depth == 0 && s[i..].starts_with(op) {
                // Make sure we're not matching a longer operator
                // e.g., don't match "=" when looking for "<"
                let after = i + op.len();
                if after >= s.len()
                    || !matches!(s.chars().nth(after), Some('=') | Some('<') | Some('>'))
                {
                    return Some(i);
                }
            }
        }

        None
    }

    fn parse_unary(s: &str) -> Option<Expression> {
        let s = s.trim();

        // Unary minus
        if s.starts_with('-') && s.len() > 1 {
            let operand = &s[1..];
            if !operand.starts_with('-') {
                // Avoid double negative confusion
                return Some(Expression::Unary {
                    op: UnaryOp::Neg,
                    operand: Box::new(Self::parse(operand)),
                });
            }
        }

        // Logical not
        if s.starts_with('!') && s.len() > 1 {
            return Some(Expression::Unary {
                op: UnaryOp::Not,
                operand: Box::new(Self::parse(&s[1..])),
            });
        }

        if s.starts_with("not ") && s.len() > 4 {
            return Some(Expression::Unary {
                op: UnaryOp::Not,
                operand: Box::new(Self::parse(&s[4..])),
            });
        }

        // Bitwise not
        if s.starts_with('~') && s.len() > 1 {
            return Some(Expression::Unary {
                op: UnaryOp::BitNot,
                operand: Box::new(Self::parse(&s[1..])),
            });
        }

        None
    }

    fn parse_call(s: &str) -> Option<Expression> {
        let s = s.trim();

        // Look for function call pattern: name(args)
        if let Some(paren_pos) = s.find('(') {
            if s.ends_with(')') {
                let name = s[..paren_pos].trim();
                if Self::is_identifier(name) {
                    let args_str = &s[paren_pos + 1..s.len() - 1];
                    let args = Self::parse_args(args_str);
                    return Some(Expression::Call {
                        name: name.to_string(),
                        args,
                    });
                }
            }
        }

        None
    }

    fn parse_args(s: &str) -> Vec<Expression> {
        if s.trim().is_empty() {
            return vec![];
        }

        // Simple comma-split (doesn't handle nested commas properly)
        let mut args = vec![];
        let mut depth = 0;
        let mut current = String::new();

        for c in s.chars() {
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
                    if !current.trim().is_empty() {
                        args.push(Self::parse(&current));
                    }
                    current.clear();
                }
                _ => current.push(c),
            }
        }

        if !current.trim().is_empty() {
            args.push(Self::parse(&current));
        }

        args
    }
}

// =============================================================================
// Statement Parsing
// =============================================================================

/// Parsed statement for transfer function application.
#[derive(Debug, Clone)]
pub enum Statement {
    /// Assignment: variable = expression
    Assignment { target: String, value: Expression },
    /// Augmented assignment: variable op= expression
    AugAssignment {
        target: String,
        op: BinaryOp,
        value: Expression,
    },
    /// Return statement
    Return { value: Option<Expression> },
    /// Expression statement (side effects only)
    Expression(Expression),
    /// Branch condition
    Branch { condition: Expression },
    /// Unknown/unparseable statement
    Unknown(String),
}

impl Statement {
    /// Parse a statement string.
    pub fn parse(stmt: &str) -> Self {
        let stmt = stmt.trim();

        // Check for return statement
        if stmt.starts_with("return ") || stmt == "return" {
            let value = if stmt.len() > 7 {
                Some(ExpressionParser::parse(&stmt[7..]))
            } else {
                None
            };
            return Statement::Return { value };
        }

        // Check for augmented assignment (+=, -=, etc.)
        let aug_ops = [
            ("+=", BinaryOp::Add),
            ("-=", BinaryOp::Sub),
            ("*=", BinaryOp::Mul),
            ("/=", BinaryOp::Div),
            ("%=", BinaryOp::Mod),
            ("&=", BinaryOp::BitAnd),
            ("|=", BinaryOp::BitOr),
            ("^=", BinaryOp::BitXor),
            ("<<=", BinaryOp::Shl),
            (">>=", BinaryOp::Shr),
        ];

        for (op_str, op) in aug_ops.iter() {
            if let Some(pos) = stmt.find(op_str) {
                let target = stmt[..pos].trim();
                let value = &stmt[pos + op_str.len()..];
                if ExpressionParser::is_identifier(target) {
                    return Statement::AugAssignment {
                        target: target.to_string(),
                        op: *op,
                        value: ExpressionParser::parse(value),
                    };
                }
            }
        }

        // Check for regular assignment
        if let Some(pos) = stmt.find('=') {
            // Make sure it's not ==, !=, <=, >=
            let before = if pos > 0 {
                stmt.chars().nth(pos - 1)
            } else {
                None
            };
            let after = stmt.chars().nth(pos + 1);

            if !matches!(before, Some('!') | Some('<') | Some('>') | Some('='))
                && !matches!(after, Some('='))
            {
                let target = stmt[..pos].trim();
                let value = &stmt[pos + 1..];
                if ExpressionParser::is_identifier(target) {
                    return Statement::Assignment {
                        target: target.to_string(),
                        value: ExpressionParser::parse(value),
                    };
                }
            }
        }

        // Otherwise treat as expression statement
        Statement::Expression(ExpressionParser::parse(stmt))
    }
}

// =============================================================================
// Results
// =============================================================================

/// A constant folding opportunity detected by the analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FoldedExpression {
    /// Location in source
    pub location: Location,
    /// Original expression text
    pub original: String,
    /// Value it can be folded to
    pub folded_value: Value,
}

/// A dead branch detected by the analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadBranch {
    /// Location in source
    pub location: Location,
    /// Condition expression text
    pub condition: String,
    /// Whether condition is always true or false
    pub always_value: bool,
    /// Lines that are unreachable as a result
    pub unreachable_lines: Vec<usize>,
}

/// Complete result of constant propagation analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstantPropagationResult {
    /// Function name analyzed
    pub function_name: String,
    /// Constants known at each program point.
    /// Key is (block_id, stmt_index), value is variable -> constant map.
    pub constants_at_point: FxHashMap<(usize, usize), FxHashMap<String, ConstantValue>>,
    /// Expressions that can be constant-folded
    pub folded_expressions: Vec<FoldedExpression>,
    /// Branches with constant conditions (dead code)
    pub dead_branches: Vec<DeadBranch>,
    /// Total number of iterations until fixpoint
    pub iterations: usize,
    /// Whether analysis reached fixpoint (always true unless max iterations hit)
    pub converged: bool,
}

impl ConstantPropagationResult {
    /// Get constants at a specific program point.
    pub fn constants_at(
        &self,
        block_id: BlockId,
        stmt_index: usize,
    ) -> Option<&FxHashMap<String, ConstantValue>> {
        self.constants_at_point.get(&(block_id.0, stmt_index))
    }

    /// Get the constant value of a variable at a program point.
    pub fn get_constant(
        &self,
        block_id: BlockId,
        stmt_index: usize,
        var: &str,
    ) -> Option<&ConstantValue> {
        self.constants_at_point
            .get(&(block_id.0, stmt_index))
            .and_then(|state| state.get(var))
    }

    /// Check if a variable is constant at a program point.
    pub fn is_constant_at(&self, block_id: BlockId, stmt_index: usize, var: &str) -> bool {
        self.get_constant(block_id, stmt_index, var)
            .map(|v| v.is_constant())
            .unwrap_or(false)
    }

    /// Get all variables that are constant at any point.
    pub fn constant_variables(&self) -> FxHashSet<String> {
        let mut vars = FxHashSet::default();
        for state in self.constants_at_point.values() {
            for (var, val) in state {
                if val.is_constant() {
                    vars.insert(var.clone());
                }
            }
        }
        vars
    }
}

// =============================================================================
// Main Analysis Engine
// =============================================================================

/// Constant propagation analysis engine.
///
/// Performs forward dataflow analysis on a CFG to determine which variables
/// have known constant values at each program point.
pub struct ConstantPropagation<'a> {
    cfg: &'a CFGInfo,
    /// Maximum iterations before giving up (prevents infinite loops)
    max_iterations: usize,
}

impl<'a> ConstantPropagation<'a> {
    /// Create new analysis for a CFG.
    pub fn new(cfg: &'a CFGInfo) -> Self {
        Self {
            cfg,
            max_iterations: 1000,
        }
    }

    /// Set maximum iterations.
    pub fn with_max_iterations(mut self, max: usize) -> Self {
        self.max_iterations = max;
        self
    }

    /// Run the analysis.
    pub fn analyze(&self) -> ConstantPropagationResult {
        let mut result = ConstantPropagationResult {
            function_name: self.cfg.function_name.clone(),
            constants_at_point: FxHashMap::default(),
            folded_expressions: Vec::new(),
            dead_branches: Vec::new(),
            iterations: 0,
            converged: false,
        };

        // State at entry of each block
        let mut block_in_states: FxHashMap<BlockId, ConstantState> = FxHashMap::default();
        // State at exit of each block
        let mut block_out_states: FxHashMap<BlockId, ConstantState> = FxHashMap::default();

        // Initialize entry block with empty state (all variables undefined = Bottom)
        block_in_states.insert(self.cfg.entry, ConstantState::default());

        // Worklist of blocks to process
        let mut worklist: VecDeque<BlockId> = VecDeque::new();
        worklist.push_back(self.cfg.entry);

        let mut iterations = 0;

        while let Some(block_id) = worklist.pop_front() {
            iterations += 1;
            if iterations > self.max_iterations {
                result.iterations = iterations;
                return result;
            }

            // Get the block
            let block = match self.cfg.blocks.get(&block_id) {
                Some(b) => b,
                None => continue,
            };

            // Get incoming state (meet of all predecessors)
            let in_state = if block_id == self.cfg.entry {
                block_in_states.get(&block_id).cloned().unwrap_or_default()
            } else {
                let preds = self.cfg.predecessors(block_id);
                if preds.is_empty() {
                    ConstantState::default()
                } else {
                    let mut combined = block_out_states.get(&preds[0]).cloned().unwrap_or_default();
                    for pred in preds.iter().skip(1) {
                        if let Some(pred_state) = block_out_states.get(pred) {
                            combined = meet_states(&combined, pred_state);
                        }
                    }
                    combined
                }
            };

            // Process statements in the block
            let mut state = in_state.clone();
            for (stmt_idx, stmt_text) in block.statements.iter().enumerate() {
                // Record state before this statement
                result
                    .constants_at_point
                    .insert((block_id.0, stmt_idx), state.clone());

                // Apply transfer function
                let stmt = Statement::parse(stmt_text);
                self.apply_transfer(
                    &mut state,
                    &stmt,
                    block_id,
                    stmt_idx,
                    stmt_text,
                    &mut result,
                );
            }

            // Check if output state changed
            let old_out = block_out_states.get(&block_id);
            let changed = old_out.map(|old| old != &state).unwrap_or(true);

            if changed {
                block_out_states.insert(block_id, state.clone());
                block_in_states.insert(block_id, in_state);

                // Add successors to worklist
                for succ in self.cfg.successors(block_id) {
                    if !worklist.contains(succ) {
                        worklist.push_back(*succ);
                    }
                }
            }
        }

        // Record final state at end of each block
        for (block_id, state) in &block_out_states {
            if let Some(block) = self.cfg.blocks.get(block_id) {
                let last_idx = block.statements.len();
                result
                    .constants_at_point
                    .insert((block_id.0, last_idx), state.clone());
            }
        }

        // Detect dead branches
        self.detect_dead_branches(&block_out_states, &mut result);

        result.iterations = iterations;
        result.converged = true;
        result
    }

    /// Apply transfer function for a statement.
    fn apply_transfer(
        &self,
        state: &mut ConstantState,
        stmt: &Statement,
        block_id: BlockId,
        stmt_idx: usize,
        original_text: &str,
        result: &mut ConstantPropagationResult,
    ) {
        match stmt {
            Statement::Assignment { target, value } => {
                let eval_result = value.evaluate(state);

                // Check if this is a constant folding opportunity
                if let ConstantValue::Constant(v) = &eval_result {
                    // Only record if the original expression was not already a literal
                    if !matches!(value, Expression::Literal(_)) {
                        let location = self.location_for_block(block_id, stmt_idx);
                        result.folded_expressions.push(FoldedExpression {
                            location,
                            original: original_text.to_string(),
                            folded_value: v.clone(),
                        });
                    }
                }

                state.insert(target.clone(), eval_result);
            }

            Statement::AugAssignment { target, op, value } => {
                let current = state.get(target).cloned().unwrap_or(ConstantValue::Top);
                let rhs = value.evaluate(state);

                let new_val = match (&current, &rhs) {
                    (ConstantValue::Constant(l), ConstantValue::Constant(r)) => {
                        if let Some(result_val) = l.binary_op(*op, r) {
                            // Record folding opportunity
                            let location = self.location_for_block(block_id, stmt_idx);
                            result.folded_expressions.push(FoldedExpression {
                                location,
                                original: original_text.to_string(),
                                folded_value: result_val.clone(),
                            });
                            ConstantValue::Constant(result_val)
                        } else {
                            ConstantValue::Top
                        }
                    }
                    (ConstantValue::Bottom, _) | (_, ConstantValue::Bottom) => {
                        ConstantValue::Bottom
                    }
                    _ => ConstantValue::Top,
                };

                state.insert(target.clone(), new_val);
            }

            Statement::Return { value } => {
                // Return doesn't modify variable state, but we could track return value
                if let Some(expr) = value {
                    let _ = expr.evaluate(state);
                }
            }

            Statement::Expression(expr) => {
                // Side-effect expressions might modify global state
                // For now, we're conservative and don't modify local state
                if let Expression::Call { name, .. } = expr {
                    // Function calls might modify any variable via closure/global
                    // In a more sophisticated analysis, we'd track this
                    // For now, be conservative: function calls don't change local state
                    // unless they're known pure functions
                    let _ = name;
                }
            }

            Statement::Branch { condition } => {
                // Evaluate condition to check for dead branch
                let cond_val = condition.evaluate(state);
                if let ConstantValue::Constant(v) = &cond_val {
                    // Record dead branch opportunity (actual dead branch detection
                    // happens in detect_dead_branches after analysis completes)
                    let _ = v.is_truthy();
                }
            }

            Statement::Unknown(_) => {
                // Unknown statements: be conservative, don't modify state
            }
        }
    }

    /// Detect dead branches based on final analysis state.
    fn detect_dead_branches(
        &self,
        block_out_states: &FxHashMap<BlockId, ConstantState>,
        result: &mut ConstantPropagationResult,
    ) {
        for (block_id, block) in &self.cfg.blocks {
            // Check if this block is a branch point
            let succs = self.cfg.successors(*block_id);
            if succs.len() < 2 {
                continue;
            }

            // Get the outgoing edges to check for True/False branch types
            let edges: Vec<_> = self
                .cfg
                .edges
                .iter()
                .filter(|e| e.from == *block_id)
                .collect();

            // Check if we have True/False branches
            let has_conditional_edges = edges
                .iter()
                .any(|e| e.edge_type == EdgeType::True || e.edge_type == EdgeType::False);

            if !has_conditional_edges {
                continue;
            }

            // Get state at end of this block
            let state = match block_out_states.get(block_id) {
                Some(s) => s,
                None => continue,
            };

            // Try to find the condition in the last statement
            if let Some(last_stmt) = block.statements.last() {
                // Extract condition from if/while/etc statement
                let condition = self.extract_condition(last_stmt);
                if let Some(cond_expr) = condition {
                    let expr = ExpressionParser::parse(&cond_expr);
                    let cond_val = expr.evaluate(state);

                    if let Some(is_true) = cond_val.known_truthiness() {
                        // Find unreachable lines in the dead branch
                        let unreachable = self.find_unreachable_lines(&edges, is_true);

                        let location =
                            self.location_for_block(*block_id, block.statements.len() - 1);
                        result.dead_branches.push(DeadBranch {
                            location,
                            condition: cond_expr,
                            always_value: is_true,
                            unreachable_lines: unreachable,
                        });
                    }
                }
            }
        }
    }

    /// Extract condition from a branch statement.
    fn extract_condition(&self, stmt: &str) -> Option<String> {
        let stmt = stmt.trim();

        // Python/JS: if condition:
        if stmt.starts_with("if ") {
            let rest = &stmt[3..];
            // Remove trailing colon
            let cond = rest.trim_end_matches(':').trim();
            if !cond.is_empty() {
                return Some(cond.to_string());
            }
        }

        // while condition:
        if stmt.starts_with("while ") {
            let rest = &stmt[6..];
            let cond = rest.trim_end_matches(':').trim();
            if !cond.is_empty() {
                return Some(cond.to_string());
            }
        }

        // C/Java/Rust style: if (condition)
        if stmt.starts_with("if (") || stmt.starts_with("if(") {
            if let Some(close) = stmt.rfind(')') {
                let start = if stmt.starts_with("if (") { 4 } else { 3 };
                let cond = &stmt[start..close];
                if !cond.is_empty() {
                    return Some(cond.to_string());
                }
            }
        }

        None
    }

    /// Find lines that become unreachable due to dead branch.
    fn find_unreachable_lines(
        &self,
        edges: &[&crate::cfg::CFGEdge],
        condition_is_true: bool,
    ) -> Vec<usize> {
        let mut unreachable = Vec::new();

        // Find the dead edge (false if always true, true if always false)
        let dead_edge_type = if condition_is_true {
            EdgeType::False
        } else {
            EdgeType::True
        };

        for edge in edges {
            if edge.edge_type == dead_edge_type {
                // Collect all lines reachable from this dead edge
                if let Some(target_block) = self.cfg.blocks.get(&edge.to) {
                    unreachable.push(target_block.start_line);
                    // Could recursively collect all lines in dominated blocks
                }
            }
        }

        unreachable
    }

    /// Create location for a statement in a block.
    fn location_for_block(&self, block_id: BlockId, stmt_idx: usize) -> Location {
        let line = self
            .cfg
            .blocks
            .get(&block_id)
            .map(|b| b.start_line + stmt_idx)
            .unwrap_or(0);
        Location::new(line, block_id, stmt_idx)
    }
}

// =============================================================================
// Public API
// =============================================================================

/// Analyze a function for constant propagation.
///
/// This is the main entry point for constant propagation analysis.
///
/// # Arguments
///
/// * `cfg` - The control flow graph to analyze
///
/// # Returns
///
/// Analysis result with constant values at each point and optimization opportunities.
///
/// # Example
///
/// ```ignore
/// use go_brrr::cfg;
/// use go_brrr::dataflow::analyze_constants;
///
/// let cfg = cfg::extract("src/main.py", "compute")?;
/// let result = analyze_constants(&cfg);
///
/// for folded in &result.folded_expressions {
///     println!("Can fold: {}", folded.original);
/// }
/// ```
pub fn analyze_constants(cfg: &CFGInfo) -> ConstantPropagationResult {
    ConstantPropagation::new(cfg).analyze()
}

/// Analyze a function file for constant propagation.
///
/// Convenience function that extracts CFG and runs analysis.
///
/// # Arguments
///
/// * `file` - Path to source file
/// * `function` - Function name to analyze
///
/// # Returns
///
/// Analysis result or error if CFG extraction fails.
pub fn analyze_constants_in_file(
    file: &str,
    function: &str,
) -> crate::error::Result<ConstantPropagationResult> {
    let cfg = crate::cfg::extract(file, function)?;
    Ok(analyze_constants(&cfg))
}

/// Analyze with explicit language specification.
pub fn analyze_constants_with_language(
    file: &str,
    function: &str,
    language: Option<&str>,
) -> crate::error::Result<ConstantPropagationResult> {
    let cfg = crate::cfg::extract_with_language(file, function, language)?;
    Ok(analyze_constants(&cfg))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::{BlockType, CFGBlock};
    use crate::dataflow::common::test_utils::create_loop_cfg;
    use rustc_hash::FxHashMap;

    /// Create a simple test CFG with linear flow.
    fn simple_linear_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        // Entry block with two assignments
        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["x = 5".to_string(), "y = x + 3".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 2,
            },
        );

        // Exit block with return
        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "exit".to_string(),
                block_type: BlockType::Exit,
                statements: vec!["return y".to_string()],
                func_calls: vec![],
                start_line: 3,
                end_line: 3,
            },
        );

        let edges = vec![crate::cfg::CFGEdge::unconditional(BlockId(0), BlockId(1))];

        CFGInfo::new(
            "test_func".to_string(),
            blocks,
            edges,
            BlockId(0),
            vec![BlockId(1)],
        )
    }

    /// Create a CFG with a branch.
    fn branching_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["x = 10".to_string(), "if x > 5".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 2,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "then".to_string(),
                block_type: BlockType::Branch,
                statements: vec!["y = x + 1".to_string()],
                func_calls: vec![],
                start_line: 3,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "else".to_string(),
                block_type: BlockType::Branch,
                statements: vec!["y = x - 1".to_string()],
                func_calls: vec![],
                start_line: 5,
                end_line: 5,
            },
        );

        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "exit".to_string(),
                block_type: BlockType::Exit,
                statements: vec!["return y".to_string()],
                func_calls: vec![],
                start_line: 7,
                end_line: 7,
            },
        );

        let edges = vec![
            crate::cfg::CFGEdge::new(BlockId(0), BlockId(1), EdgeType::True),
            crate::cfg::CFGEdge::new(BlockId(0), BlockId(2), EdgeType::False),
            crate::cfg::CFGEdge::unconditional(BlockId(1), BlockId(3)),
            crate::cfg::CFGEdge::unconditional(BlockId(2), BlockId(3)),
        ];

        CFGInfo::new(
            "branching_func".to_string(),
            blocks,
            edges,
            BlockId(0),
            vec![BlockId(3)],
        )
    }

    #[test]
    fn test_value_arithmetic() {
        let a = Value::Int(10);
        let b = Value::Int(3);

        assert_eq!(a.binary_op(BinaryOp::Add, &b), Some(Value::Int(13)));
        assert_eq!(a.binary_op(BinaryOp::Sub, &b), Some(Value::Int(7)));
        assert_eq!(a.binary_op(BinaryOp::Mul, &b), Some(Value::Int(30)));
        assert_eq!(a.binary_op(BinaryOp::Div, &b), Some(Value::Int(3)));
        assert_eq!(a.binary_op(BinaryOp::Mod, &b), Some(Value::Int(1)));
    }

    #[test]
    fn test_value_comparison() {
        let a = Value::Int(5);
        let b = Value::Int(3);

        assert_eq!(a.binary_op(BinaryOp::Lt, &b), Some(Value::Bool(false)));
        assert_eq!(a.binary_op(BinaryOp::Gt, &b), Some(Value::Bool(true)));
        assert_eq!(a.binary_op(BinaryOp::Eq, &b), Some(Value::Bool(false)));
        assert_eq!(a.binary_op(BinaryOp::Ne, &b), Some(Value::Bool(true)));
    }

    #[test]
    fn test_value_truthiness() {
        assert!(Value::Bool(true).is_truthy());
        assert!(!Value::Bool(false).is_truthy());
        assert!(Value::Int(1).is_truthy());
        assert!(!Value::Int(0).is_truthy());
        assert!(Value::String("hello".to_string()).is_truthy());
        assert!(!Value::String("".to_string()).is_truthy());
        assert!(!Value::Null.is_truthy());
    }

    #[test]
    fn test_constant_value_meet() {
        let c5 = ConstantValue::Constant(Value::Int(5));
        let c10 = ConstantValue::Constant(Value::Int(10));
        let top = ConstantValue::Top;
        let bottom = ConstantValue::Bottom;

        // Same constant
        assert_eq!(c5.meet(&c5), c5);

        // Different constants -> Top
        assert_eq!(c5.meet(&c10), ConstantValue::Top);

        // Top absorbs
        assert_eq!(top.meet(&c5), ConstantValue::Top);
        assert_eq!(c5.meet(&top), ConstantValue::Top);

        // Bottom is identity
        assert_eq!(bottom.meet(&c5), c5);
        assert_eq!(c5.meet(&bottom), c5);
    }

    #[test]
    fn test_expression_parser_literals() {
        // Integers
        assert!(matches!(
            ExpressionParser::parse("42"),
            Expression::Literal(Value::Int(42))
        ));
        // Negative numbers are parsed as literals (more efficient than unary)
        assert!(matches!(
            ExpressionParser::parse("-5"),
            Expression::Literal(Value::Int(-5))
        ));

        // Floats
        assert!(matches!(
            ExpressionParser::parse("3.14"),
            Expression::Literal(Value::Float(f)) if (f - 3.14).abs() < 0.001
        ));

        // Booleans
        assert!(matches!(
            ExpressionParser::parse("true"),
            Expression::Literal(Value::Bool(true))
        ));
        assert!(matches!(
            ExpressionParser::parse("false"),
            Expression::Literal(Value::Bool(false))
        ));

        // Strings
        assert!(matches!(
            ExpressionParser::parse("\"hello\""),
            Expression::Literal(Value::String(s)) if s == "hello"
        ));

        // Null
        assert!(matches!(
            ExpressionParser::parse("null"),
            Expression::Literal(Value::Null)
        ));
    }

    #[test]
    fn test_expression_parser_binary() {
        let expr = ExpressionParser::parse("2 + 3");
        if let Expression::Binary { left, op, right } = expr {
            assert!(matches!(*left, Expression::Literal(Value::Int(2))));
            assert_eq!(op, BinaryOp::Add);
            assert!(matches!(*right, Expression::Literal(Value::Int(3))));
        } else {
            panic!("Expected binary expression");
        }
    }

    #[test]
    fn test_expression_evaluation() {
        let state = ConstantState::default();

        // Literal evaluation
        let expr = ExpressionParser::parse("5");
        assert_eq!(
            expr.evaluate(&state),
            ConstantValue::Constant(Value::Int(5))
        );

        // Binary evaluation
        let expr = ExpressionParser::parse("2 + 3");
        assert_eq!(
            expr.evaluate(&state),
            ConstantValue::Constant(Value::Int(5))
        );

        // Variable evaluation (unknown variable)
        let expr = ExpressionParser::parse("x");
        assert_eq!(expr.evaluate(&state), ConstantValue::Top);

        // Variable evaluation (known variable)
        let mut state_with_x = ConstantState::default();
        state_with_x.insert("x".to_string(), ConstantValue::Constant(Value::Int(10)));
        let expr = ExpressionParser::parse("x + 5");
        assert_eq!(
            expr.evaluate(&state_with_x),
            ConstantValue::Constant(Value::Int(15))
        );
    }

    #[test]
    fn test_simple_constant_propagation() {
        let cfg = simple_linear_cfg();
        let result = analyze_constants(&cfg);

        assert!(result.converged);
        assert!(result.iterations > 0);

        // Should detect that y = x + 3 = 5 + 3 = 8 can be folded
        assert!(!result.folded_expressions.is_empty());
    }

    #[test]
    fn test_branching_constant_propagation() {
        let cfg = branching_cfg();
        let result = analyze_constants(&cfg);

        assert!(result.converged);

        // x is constant (10) throughout
        // y depends on branch, should be 11 in then, 9 in else
        // After merge, y should be Top
    }

    #[test]
    fn test_loop_constant_propagation() {
        let cfg = create_loop_cfg("loop_func");
        let result = analyze_constants(&cfg);

        assert!(result.converged);

        // In a loop, i and sum change each iteration
        // After fixpoint, they should become Top in the loop body
    }

    #[test]
    fn test_statement_parse_assignment() {
        if let Statement::Assignment { target, value } = Statement::parse("x = 5") {
            assert_eq!(target, "x");
            assert!(matches!(value, Expression::Literal(Value::Int(5))));
        } else {
            panic!("Expected assignment");
        }
    }

    #[test]
    fn test_statement_parse_aug_assignment() {
        if let Statement::AugAssignment { target, op, value } = Statement::parse("x += 1") {
            assert_eq!(target, "x");
            assert_eq!(op, BinaryOp::Add);
            assert!(matches!(value, Expression::Literal(Value::Int(1))));
        } else {
            panic!("Expected augmented assignment");
        }
    }

    #[test]
    fn test_constant_propagation_result_api() {
        let cfg = simple_linear_cfg();
        let result = analyze_constants(&cfg);

        // Test the result API
        let constants = result.constant_variables();
        assert!(!constants.is_empty());
    }

    #[test]
    fn test_string_concatenation() {
        let a = Value::String("hello ".to_string());
        let b = Value::String("world".to_string());

        assert_eq!(
            a.binary_op(BinaryOp::Add, &b),
            Some(Value::String("hello world".to_string()))
        );
    }

    #[test]
    fn test_null_comparisons() {
        let null = Value::Null;
        let five = Value::Int(5);

        assert_eq!(null.binary_op(BinaryOp::Eq, &null), Some(Value::Bool(true)));
        assert_eq!(
            null.binary_op(BinaryOp::Eq, &five),
            Some(Value::Bool(false))
        );
        assert_eq!(five.binary_op(BinaryOp::Ne, &null), Some(Value::Bool(true)));
    }

    #[test]
    fn test_unary_operations() {
        assert_eq!(Value::Int(5).unary_op(UnaryOp::Neg), Some(Value::Int(-5)));
        assert_eq!(
            Value::Bool(true).unary_op(UnaryOp::Not),
            Some(Value::Bool(false))
        );
        assert_eq!(
            Value::Int(0).unary_op(UnaryOp::BitNot),
            Some(Value::Int(-1))
        );
    }

    #[test]
    fn test_function_call_invalidates() {
        let expr = ExpressionParser::parse("foo(x)");
        let state = ConstantState::default();

        // Function calls always return Top
        assert_eq!(expr.evaluate(&state), ConstantValue::Top);
    }

    #[test]
    fn test_conditional_constant_propagation() {
        // Test case: x = 5; if (cond) x = 5 else x = 5
        // x should still be constant 5 after the join
        let c5 = ConstantValue::Constant(Value::Int(5));

        // Meet of same constant should still be that constant
        assert_eq!(c5.meet(&c5), ConstantValue::Constant(Value::Int(5)));
    }

    #[test]
    fn test_float_operations() {
        let a = Value::Float(3.5);
        let b = Value::Float(2.0);

        assert_eq!(a.binary_op(BinaryOp::Add, &b), Some(Value::Float(5.5)));
        assert_eq!(a.binary_op(BinaryOp::Mul, &b), Some(Value::Float(7.0)));
        assert_eq!(a.binary_op(BinaryOp::Div, &b), Some(Value::Float(1.75)));
    }

    #[test]
    fn test_mixed_int_float() {
        let i = Value::Int(5);
        let f = Value::Float(2.5);

        assert_eq!(i.binary_op(BinaryOp::Add, &f), Some(Value::Float(7.5)));
        assert_eq!(f.binary_op(BinaryOp::Mul, &i), Some(Value::Float(12.5)));
    }

    #[test]
    fn test_division_by_zero() {
        let a = Value::Int(10);
        let zero = Value::Int(0);

        // Division by zero should return None
        assert_eq!(a.binary_op(BinaryOp::Div, &zero), None);
        assert_eq!(a.binary_op(BinaryOp::Mod, &zero), None);
    }

    #[test]
    fn test_bitwise_operations() {
        let a = Value::Int(0b1010);
        let b = Value::Int(0b1100);

        assert_eq!(a.binary_op(BinaryOp::BitAnd, &b), Some(Value::Int(0b1000)));
        assert_eq!(a.binary_op(BinaryOp::BitOr, &b), Some(Value::Int(0b1110)));
        assert_eq!(a.binary_op(BinaryOp::BitXor, &b), Some(Value::Int(0b0110)));
    }

    #[test]
    fn test_shift_operations() {
        let a = Value::Int(4);
        let b = Value::Int(2);

        assert_eq!(a.binary_op(BinaryOp::Shl, &b), Some(Value::Int(16)));
        assert_eq!(a.binary_op(BinaryOp::Shr, &b), Some(Value::Int(1)));
    }
}
