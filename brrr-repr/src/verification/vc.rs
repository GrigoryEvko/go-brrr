//! Verification conditions and weakest precondition computation
//!
//! Mirrors F* Contracts.fst vc type (lines 487-520) and wp_compute (lines 382-428).
//!
//! Verification conditions (VCs) are logical formulas that must be proven to verify
//! program correctness. They are generated via weakest precondition computation
//! from contracts (pre/post conditions, invariants, assertions).

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::formula::{formula_and, formula_implies, formula_not, Formula};
use crate::expr::{Expr, Expr_, WithLoc};
use crate::types::BrrrType;

/// Variable identifier (interned string)
pub type VarId = Spur;

/// Verification Condition
///
/// Maps to F* Contracts.fst (lines 487-520):
/// ```fstar
/// noeq type vc =
///   | VCTrue   : vc
///   | VCFalse  : vc
///   | VCImpl   : vc -> vc -> vc
///   | VCAnd    : vc -> vc -> vc
///   | VCOr     : vc -> vc -> vc
///   | VCNot    : vc -> vc
///   | VCForall : var_id -> brrr_type -> vc -> vc
///   | VCExists : var_id -> brrr_type -> vc -> vc
///   | VCFormula : formula -> vc
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum VC {
    /// Trivially true: always satisfied
    True,

    /// Trivially false: never satisfied (indicates unreachable or bug)
    False,

    /// Implication: `antecedent => consequent`
    Impl(Box<VC>, Box<VC>),

    /// Conjunction: `lhs /\ rhs`
    And(Box<VC>, Box<VC>),

    /// Disjunction: `lhs \/ rhs`
    Or(Box<VC>, Box<VC>),

    /// Negation: `not vc`
    Not(Box<VC>),

    /// Universal quantification: `forall (x: ty). body`
    Forall {
        var: VarId,
        ty: BrrrType,
        body: Box<VC>,
    },

    /// Existential quantification: `exists (x: ty). body`
    Exists {
        var: VarId,
        ty: BrrrType,
        body: Box<VC>,
    },

    /// Atomic formula (leaf predicate)
    Formula(Formula),
}

impl VC {
    /// Create conjunction: `self /\ other`
    ///
    /// Applies simplification rules:
    /// - `True /\ x = x`
    /// - `x /\ True = x`
    /// - `False /\ x = False`
    /// - `x /\ False = False`
    #[must_use]
    pub fn and(self, other: Self) -> Self {
        vc_and(self, other)
    }

    /// Create disjunction: `self \/ other`
    ///
    /// Applies simplification rules:
    /// - `True \/ x = True`
    /// - `x \/ True = True`
    /// - `False \/ x = x`
    /// - `x \/ False = x`
    #[must_use]
    pub fn or(self, other: Self) -> Self {
        vc_or(self, other)
    }

    /// Create negation: `not self`
    ///
    /// Applies simplification rules:
    /// - `not True = False`
    /// - `not False = True`
    /// - `not (not x) = x`
    #[must_use]
    pub fn not(self) -> Self {
        vc_not(self)
    }

    /// Create implication: `self => other`
    ///
    /// Applies simplification rules:
    /// - `True => x = x`
    /// - `False => x = True`
    /// - `x => True = True`
    /// - `x => False = not x`
    #[must_use]
    pub fn implies(self, other: Self) -> Self {
        vc_impl(self, other)
    }

    /// Check if this VC is trivially true
    ///
    /// Returns true for:
    /// - `VC::True`
    /// - `VC::Formula(Formula::True)`
    /// - `VC::Impl(VC::False, _)`
    /// - `VC::Impl(_, VC::True)`
    #[must_use]
    pub fn is_trivially_true(&self) -> bool {
        is_trivially_true(self)
    }

    /// Check if this VC is trivially false
    ///
    /// Returns true for:
    /// - `VC::False`
    /// - `VC::Formula(Formula::False)`
    /// - `VC::And(x, y)` where x or y is trivially false
    #[must_use]
    pub fn is_trivially_false(&self) -> bool {
        is_trivially_false(self)
    }

    /// Simplify the verification condition
    ///
    /// Applies rewrite rules to reduce VC complexity.
    /// Does not perform deep logical reasoning, only syntactic simplification.
    #[must_use]
    pub fn simplify(self) -> Self {
        vc_simplify(self)
    }

    /// Create a VC from a boolean literal
    #[must_use]
    pub fn from_bool(b: bool) -> Self {
        if b { Self::True } else { Self::False }
    }

    /// Create a VC from a formula
    #[must_use]
    pub fn from_formula(f: Formula) -> Self {
        vc_from_formula(f)
    }
}

impl Default for VC {
    fn default() -> Self {
        Self::True
    }
}

/// Create conjunction with simplification
///
/// Simplification rules applied:
/// - `True /\ x = x`
/// - `x /\ True = x`
/// - `False /\ x = False`
/// - `x /\ False = False`
/// - `x /\ x = x` (idempotence)
#[must_use]
pub fn vc_and(lhs: VC, rhs: VC) -> VC {
    match (&lhs, &rhs) {
        (VC::True, _) => rhs,
        (_, VC::True) => lhs,
        (VC::False, _) | (_, VC::False) => VC::False,
        _ if lhs == rhs => lhs,
        _ => VC::And(Box::new(lhs), Box::new(rhs)),
    }
}

/// Create disjunction with simplification
///
/// Simplification rules applied:
/// - `True \/ x = True`
/// - `x \/ True = True`
/// - `False \/ x = x`
/// - `x \/ False = x`
/// - `x \/ x = x` (idempotence)
#[must_use]
pub fn vc_or(lhs: VC, rhs: VC) -> VC {
    match (&lhs, &rhs) {
        (VC::True, _) | (_, VC::True) => VC::True,
        (VC::False, _) => rhs,
        (_, VC::False) => lhs,
        _ if lhs == rhs => lhs,
        _ => VC::Or(Box::new(lhs), Box::new(rhs)),
    }
}

/// Create negation with simplification
///
/// Simplification rules applied:
/// - `not True = False`
/// - `not False = True`
/// - `not (not x) = x` (double negation elimination)
#[must_use]
pub fn vc_not(vc: VC) -> VC {
    match vc {
        VC::True => VC::False,
        VC::False => VC::True,
        VC::Not(inner) => *inner,
        _ => VC::Not(Box::new(vc)),
    }
}

/// Create implication with simplification
///
/// Simplification rules applied:
/// - `True => x = x`
/// - `False => x = True` (ex falso quodlibet)
/// - `x => True = True`
/// - `x => False = not x`
/// - `x => x = True` (reflexivity)
#[must_use]
pub fn vc_impl(antecedent: VC, consequent: VC) -> VC {
    match (&antecedent, &consequent) {
        (VC::True, _) => consequent,
        (VC::False, _) => VC::True,
        (_, VC::True) => VC::True,
        (_, VC::False) => vc_not(antecedent),
        _ if antecedent == consequent => VC::True,
        _ => VC::Impl(Box::new(antecedent), Box::new(consequent)),
    }
}

/// Convert a formula to a verification condition
///
/// Handles special formula cases:
/// - `Formula::True` becomes `VC::True`
/// - `Formula::False` becomes `VC::False`
/// - Quantified formulas become quantified VCs
#[must_use]
pub fn vc_from_formula(f: Formula) -> VC {
    match f {
        Formula::True => VC::True,
        Formula::False => VC::False,
        Formula::Not(inner) => vc_not(vc_from_formula(*inner)),
        Formula::And(lhs, rhs) => vc_and(vc_from_formula(*lhs), vc_from_formula(*rhs)),
        Formula::Or(lhs, rhs) => vc_or(vc_from_formula(*lhs), vc_from_formula(*rhs)),
        Formula::Impl(lhs, rhs) => vc_impl(vc_from_formula(*lhs), vc_from_formula(*rhs)),
        Formula::Forall(var, ty, body) => VC::Forall {
            var: var.0,
            ty,
            body: Box::new(vc_from_formula(*body)),
        },
        Formula::Exists(var, ty, body) => VC::Exists {
            var: var.0,
            ty,
            body: Box::new(vc_from_formula(*body)),
        },
        _ => VC::Formula(f),
    }
}

/// Simplify a verification condition
///
/// Recursively applies simplification rules to reduce VC size.
/// This is a syntactic simplifier - it does not use SMT solving.
///
/// Rules applied:
/// - Propagate True/False through logical connectives
/// - Double negation elimination
/// - Idempotence (x /\ x = x, x \/ x = x)
/// - Absorption (x /\ True = x, x \/ False = x)
/// - Identity implications (x => x = True)
/// - Trivial quantifiers over True/False
#[must_use]
pub fn vc_simplify(vc: VC) -> VC {
    match vc {
        VC::True | VC::False => vc,

        VC::Not(inner) => {
            let simplified = vc_simplify(*inner);
            vc_not(simplified)
        }

        VC::And(lhs, rhs) => {
            let lhs = vc_simplify(*lhs);
            let rhs = vc_simplify(*rhs);
            vc_and(lhs, rhs)
        }

        VC::Or(lhs, rhs) => {
            let lhs = vc_simplify(*lhs);
            let rhs = vc_simplify(*rhs);
            vc_or(lhs, rhs)
        }

        VC::Impl(ante, cons) => {
            let ante = vc_simplify(*ante);
            let cons = vc_simplify(*cons);
            vc_impl(ante, cons)
        }

        VC::Forall { var, ty, body } => {
            let body = vc_simplify(*body);
            match body {
                VC::True => VC::True,
                VC::False => VC::False,
                _ => VC::Forall {
                    var,
                    ty,
                    body: Box::new(body),
                },
            }
        }

        VC::Exists { var, ty, body } => {
            let body = vc_simplify(*body);
            match body {
                VC::True => VC::True,
                VC::False => VC::False,
                _ => VC::Exists {
                    var,
                    ty,
                    body: Box::new(body),
                },
            }
        }

        VC::Formula(f) => {
            // Try to simplify the formula itself
            match f {
                Formula::True => VC::True,
                Formula::False => VC::False,
                _ => VC::Formula(f),
            }
        }
    }
}

/// Check if a VC is trivially true
///
/// Returns true when the VC can be determined true without SMT solving.
/// Conservative: may return false for complex but valid VCs.
#[must_use]
pub fn is_trivially_true(vc: &VC) -> bool {
    match vc {
        VC::True => true,
        VC::False => false,
        VC::Formula(f) => f.is_true(),
        VC::Impl(ante, _) if is_trivially_false(ante) => true,
        VC::Impl(_, cons) if is_trivially_true(cons) => true,
        VC::And(lhs, rhs) => is_trivially_true(lhs) && is_trivially_true(rhs),
        VC::Or(lhs, rhs) => is_trivially_true(lhs) || is_trivially_true(rhs),
        VC::Not(inner) => is_trivially_false(inner),
        VC::Forall { body, .. } => is_trivially_true(body),
        VC::Exists { body, .. } => is_trivially_true(body),
        _ => false,
    }
}

/// Check if a VC is trivially false
///
/// Returns true when the VC can be determined false without SMT solving.
/// Conservative: may return false for complex but unsatisfiable VCs.
#[must_use]
pub fn is_trivially_false(vc: &VC) -> bool {
    match vc {
        VC::True => false,
        VC::False => true,
        VC::Formula(f) => f.is_false(),
        VC::And(lhs, rhs) => is_trivially_false(lhs) || is_trivially_false(rhs),
        VC::Or(lhs, rhs) => is_trivially_false(lhs) && is_trivially_false(rhs),
        VC::Not(inner) => is_trivially_true(inner),
        VC::Impl(ante, cons) => is_trivially_true(ante) && is_trivially_false(cons),
        VC::Forall { body, .. } => is_trivially_false(body),
        VC::Exists { body, .. } => is_trivially_false(body),
    }
}

/// Result of verification condition checking
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum VerificationResult {
    /// The VC is valid (always true)
    Valid,

    /// The VC is invalid with a counterexample
    Invalid(Counterexample),

    /// Verification timed out or solver gave up
    Unknown {
        /// Reason for unknown result
        reason: String,
    },
}

impl VerificationResult {
    /// Check if the result is valid
    #[must_use]
    pub const fn is_valid(&self) -> bool {
        matches!(self, Self::Valid)
    }

    /// Check if the result is invalid
    #[must_use]
    pub const fn is_invalid(&self) -> bool {
        matches!(self, Self::Invalid(_))
    }

    /// Check if the result is unknown
    #[must_use]
    pub const fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown { .. })
    }

    /// Get counterexample if invalid
    #[must_use]
    pub fn counterexample(&self) -> Option<&Counterexample> {
        match self {
            Self::Invalid(cex) => Some(cex),
            _ => None,
        }
    }
}

/// Counterexample demonstrating VC invalidity
///
/// Contains variable bindings that make the VC false.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Counterexample {
    /// Variable bindings that falsify the VC
    pub bindings: Vec<(VarId, Value)>,
}

impl Counterexample {
    /// Create an empty counterexample
    #[must_use]
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    /// Create a counterexample with bindings
    #[must_use]
    pub fn with_bindings(bindings: Vec<(VarId, Value)>) -> Self {
        Self { bindings }
    }

    /// Add a binding to the counterexample
    pub fn add_binding(&mut self, var: VarId, value: Value) {
        self.bindings.push((var, value));
    }

    /// Get binding for a variable
    #[must_use]
    pub fn get(&self, var: VarId) -> Option<&Value> {
        self.bindings
            .iter()
            .find(|(v, _)| *v == var)
            .map(|(_, val)| val)
    }
}

impl Default for Counterexample {
    fn default() -> Self {
        Self::new()
    }
}

/// Runtime value in a counterexample
///
/// Represents concrete values that variables can take.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Value {
    /// Unit value
    Unit,

    /// Boolean value
    Bool(bool),

    /// Integer value (signed, up to 128 bits)
    Int(i128),

    /// Floating point value
    Float(f64),

    /// String value
    String(String),

    /// Array/sequence of values
    Array(Vec<Value>),

    /// Tuple of values
    Tuple(Vec<Value>),

    /// Struct with named fields
    Struct {
        name: String,
        fields: Vec<(String, Value)>,
    },

    /// Reference (address as integer)
    Ref(u64),

    /// Null/undefined value
    Null,
}

impl Value {
    /// Check if this is a boolean value
    #[must_use]
    pub const fn is_bool(&self) -> bool {
        matches!(self, Self::Bool(_))
    }

    /// Try to get boolean value
    #[must_use]
    pub const fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Check if this is an integer value
    #[must_use]
    pub const fn is_int(&self) -> bool {
        matches!(self, Self::Int(_))
    }

    /// Try to get integer value
    #[must_use]
    pub const fn as_int(&self) -> Option<i128> {
        match self {
            Self::Int(n) => Some(*n),
            _ => None,
        }
    }
}

// ============================================================================
// FORMULA SUBSTITUTION FOR WP COMPUTATION
// ============================================================================

/// Substitute an expression for a variable in a formula
///
/// Computes `[replacement/var]formula` - replaces free occurrences of `var`
/// with `replacement`.
///
/// Note: This is a simplified substitution for verification::formula::Formula.
/// The more general subst_formula in subst.rs works with crate::types::Formula.
fn wp_subst_formula(var: VarId, replacement: &Expr, f: &Formula) -> Formula {
    match f {
        Formula::True => Formula::True,
        Formula::False => Formula::False,

        Formula::Cmp(op, lhs, rhs) => Formula::Cmp(
            *op,
            Box::new(wp_subst_expr(var, replacement, lhs)),
            Box::new(wp_subst_expr(var, replacement, rhs)),
        ),

        Formula::And(lhs, rhs) => formula_and(
            wp_subst_formula(var, replacement, lhs),
            wp_subst_formula(var, replacement, rhs),
        ),

        Formula::Or(lhs, rhs) => Formula::Or(
            Box::new(wp_subst_formula(var, replacement, lhs)),
            Box::new(wp_subst_formula(var, replacement, rhs)),
        ),

        Formula::Not(inner) => formula_not(wp_subst_formula(var, replacement, inner)),

        Formula::Impl(lhs, rhs) => formula_implies(
            wp_subst_formula(var, replacement, lhs),
            wp_subst_formula(var, replacement, rhs),
        ),

        Formula::Iff(lhs, rhs) => Formula::Iff(
            Box::new(wp_subst_formula(var, replacement, lhs)),
            Box::new(wp_subst_formula(var, replacement, rhs)),
        ),

        Formula::Forall(bound_var, ty, body) => {
            // If bound variable shadows the substitution target, skip body
            if bound_var.0 == var {
                f.clone()
            } else {
                // Note: Full capture-avoidance would require fresh variable generation
                // For WP computation, we assume variables don't conflict
                Formula::Forall(
                    *bound_var,
                    ty.clone(),
                    Box::new(wp_subst_formula(var, replacement, body)),
                )
            }
        }

        Formula::Exists(bound_var, ty, body) => {
            if bound_var.0 == var {
                f.clone()
            } else {
                Formula::Exists(
                    *bound_var,
                    ty.clone(),
                    Box::new(wp_subst_formula(var, replacement, body)),
                )
            }
        }

        Formula::Pred(name, arg) => {
            Formula::Pred(*name, Box::new(wp_subst_expr(var, replacement, arg)))
        }

        Formula::Expr(e) => Formula::Expr(Box::new(wp_subst_expr(var, replacement, e))),
    }
}

/// Substitute an expression for a variable in an expression
///
/// Computes `[replacement/var]expr`.
fn wp_subst_expr(var: VarId, replacement: &Expr, e: &Expr) -> Expr {
    let range = e.range;

    match &e.value {
        Expr_::Var(v) => {
            if *v == var {
                replacement.clone()
            } else {
                e.clone()
            }
        }

        // Leaf expressions - no substitution needed
        Expr_::Lit(_)
        | Expr_::Global(_)
        | Expr_::Continue { .. }
        | Expr_::Hole
        | Expr_::Error(_)
        | Expr_::Sizeof(_)
        | Expr_::Alignof(_) => e.clone(),

        // Unary operators
        Expr_::Unary(op, inner) => WithLoc::new(
            Expr_::Unary(*op, Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Deref(inner) => WithLoc::new(
            Expr_::Deref(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Borrow(inner) => WithLoc::new(
            Expr_::Borrow(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::BorrowMut(inner) => WithLoc::new(
            Expr_::BorrowMut(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Move(inner) => WithLoc::new(
            Expr_::Move(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Drop(inner) => WithLoc::new(
            Expr_::Drop(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Throw(inner) => WithLoc::new(
            Expr_::Throw(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Await(inner) => WithLoc::new(
            Expr_::Await(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Yield(inner) => WithLoc::new(
            Expr_::Yield(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Async(inner) => WithLoc::new(
            Expr_::Async(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Spawn(inner) => WithLoc::new(
            Expr_::Spawn(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Box(inner) => WithLoc::new(
            Expr_::Box(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        Expr_::Unsafe(inner) => WithLoc::new(
            Expr_::Unsafe(Box::new(wp_subst_expr(var, replacement, inner))),
            range,
        ),

        // Binary operators
        Expr_::Binary(op, e1, e2) => WithLoc::new(
            Expr_::Binary(
                *op,
                Box::new(wp_subst_expr(var, replacement, e1)),
                Box::new(wp_subst_expr(var, replacement, e2)),
            ),
            range,
        ),

        Expr_::Index(e1, e2) => WithLoc::new(
            Expr_::Index(
                Box::new(wp_subst_expr(var, replacement, e1)),
                Box::new(wp_subst_expr(var, replacement, e2)),
            ),
            range,
        ),

        Expr_::Assign(lhs, rhs) => WithLoc::new(
            Expr_::Assign(
                Box::new(wp_subst_expr(var, replacement, lhs)),
                Box::new(wp_subst_expr(var, replacement, rhs)),
            ),
            range,
        ),

        Expr_::Seq(e1, e2) => WithLoc::new(
            Expr_::Seq(
                Box::new(wp_subst_expr(var, replacement, e1)),
                Box::new(wp_subst_expr(var, replacement, e2)),
            ),
            range,
        ),

        // Control flow
        Expr_::If(cond, then_e, else_e) => WithLoc::new(
            Expr_::If(
                Box::new(wp_subst_expr(var, replacement, cond)),
                Box::new(wp_subst_expr(var, replacement, then_e)),
                Box::new(wp_subst_expr(var, replacement, else_e)),
            ),
            range,
        ),

        // Function calls
        Expr_::Call(callee, args) => WithLoc::new(
            Expr_::Call(
                Box::new(wp_subst_expr(var, replacement, callee)),
                args.iter()
                    .map(|a| wp_subst_expr(var, replacement, a))
                    .collect(),
            ),
            range,
        ),

        Expr_::MethodCall(recv, method, args) => WithLoc::new(
            Expr_::MethodCall(
                Box::new(wp_subst_expr(var, replacement, recv)),
                *method,
                args.iter()
                    .map(|a| wp_subst_expr(var, replacement, a))
                    .collect(),
            ),
            range,
        ),

        // Data construction
        Expr_::Tuple(elems) => WithLoc::new(
            Expr_::Tuple(
                elems
                    .iter()
                    .map(|e| wp_subst_expr(var, replacement, e))
                    .collect(),
            ),
            range,
        ),

        Expr_::Array(elems) => WithLoc::new(
            Expr_::Array(
                elems
                    .iter()
                    .map(|e| wp_subst_expr(var, replacement, e))
                    .collect(),
            ),
            range,
        ),

        Expr_::Block(elems) => WithLoc::new(
            Expr_::Block(
                elems
                    .iter()
                    .map(|e| wp_subst_expr(var, replacement, e))
                    .collect(),
            ),
            range,
        ),

        Expr_::Struct { name, fields } => WithLoc::new(
            Expr_::Struct {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(f, e)| (*f, wp_subst_expr(var, replacement, e)))
                    .collect(),
            },
            range,
        ),

        Expr_::Variant {
            type_name,
            variant,
            fields,
        } => WithLoc::new(
            Expr_::Variant {
                type_name: type_name.clone(),
                variant: *variant,
                fields: fields
                    .iter()
                    .map(|e| wp_subst_expr(var, replacement, e))
                    .collect(),
            },
            range,
        ),

        // Field access
        Expr_::Field(base, f) => WithLoc::new(
            Expr_::Field(Box::new(wp_subst_expr(var, replacement, base)), *f),
            range,
        ),

        Expr_::TupleProj(base, i) => WithLoc::new(
            Expr_::TupleProj(Box::new(wp_subst_expr(var, replacement, base)), *i),
            range,
        ),

        // Type operations
        Expr_::As(inner, ty) => WithLoc::new(
            Expr_::As(
                Box::new(wp_subst_expr(var, replacement, inner)),
                ty.clone(),
            ),
            range,
        ),

        Expr_::Is(inner, ty) => WithLoc::new(
            Expr_::Is(
                Box::new(wp_subst_expr(var, replacement, inner)),
                ty.clone(),
            ),
            range,
        ),

        // Control flow with optional values
        Expr_::Return(opt_e) => WithLoc::new(
            Expr_::Return(
                opt_e
                    .as_ref()
                    .map(|e| Box::new(wp_subst_expr(var, replacement, e))),
            ),
            range,
        ),

        Expr_::Break { label, value } => WithLoc::new(
            Expr_::Break {
                label: *label,
                value: value
                    .as_ref()
                    .map(|e| Box::new(wp_subst_expr(var, replacement, e))),
            },
            range,
        ),

        // Loops
        Expr_::Loop { label, body } => WithLoc::new(
            Expr_::Loop {
                label: *label,
                body: Box::new(wp_subst_expr(var, replacement, body)),
            },
            range,
        ),

        Expr_::While { label, cond, body } => WithLoc::new(
            Expr_::While {
                label: *label,
                cond: Box::new(wp_subst_expr(var, replacement, cond)),
                body: Box::new(wp_subst_expr(var, replacement, body)),
            },
            range,
        ),

        // For loop - bound variable may shadow
        Expr_::For {
            label,
            var: loop_var,
            iter,
            body,
        } => {
            let iter_subst = wp_subst_expr(var, replacement, iter);
            if *loop_var == var {
                // loop_var shadows var
                WithLoc::new(
                    Expr_::For {
                        label: *label,
                        var: *loop_var,
                        iter: Box::new(iter_subst),
                        body: body.clone(),
                    },
                    range,
                )
            } else {
                WithLoc::new(
                    Expr_::For {
                        label: *label,
                        var: *loop_var,
                        iter: Box::new(iter_subst),
                        body: Box::new(wp_subst_expr(var, replacement, body)),
                    },
                    range,
                )
            }
        }

        // Let binding - simplified (pattern binding not fully handled)
        Expr_::Let {
            pattern,
            ty,
            init,
            body,
        } => WithLoc::new(
            Expr_::Let {
                pattern: pattern.clone(),
                ty: ty.clone(),
                init: Box::new(wp_subst_expr(var, replacement, init)),
                body: Box::new(wp_subst_expr(var, replacement, body)),
            },
            range,
        ),

        // LetMut - bound variable may shadow
        Expr_::LetMut {
            var: bound_var,
            ty,
            init,
            body,
        } => {
            let init_subst = wp_subst_expr(var, replacement, init);
            if *bound_var == var {
                // bound_var shadows var
                WithLoc::new(
                    Expr_::LetMut {
                        var: *bound_var,
                        ty: ty.clone(),
                        init: Box::new(init_subst),
                        body: body.clone(),
                    },
                    range,
                )
            } else {
                WithLoc::new(
                    Expr_::LetMut {
                        var: *bound_var,
                        ty: ty.clone(),
                        init: Box::new(init_subst),
                        body: Box::new(wp_subst_expr(var, replacement, body)),
                    },
                    range,
                )
            }
        }

        // Lambda - bound parameters may shadow
        Expr_::Lambda { params, body } => {
            let binds_var = params.iter().any(|(p, _)| *p == var);
            if binds_var {
                e.clone()
            } else {
                WithLoc::new(
                    Expr_::Lambda {
                        params: params.clone(),
                        body: Box::new(wp_subst_expr(var, replacement, body)),
                    },
                    range,
                )
            }
        }

        // Closure - similar to lambda
        Expr_::Closure {
            params,
            captures,
            body,
        } => {
            let binds_var = params.iter().any(|(p, _)| *p == var);
            if binds_var {
                e.clone()
            } else {
                WithLoc::new(
                    Expr_::Closure {
                        params: params.clone(),
                        captures: captures.clone(),
                        body: Box::new(wp_subst_expr(var, replacement, body)),
                    },
                    range,
                )
            }
        }

        // Shift - bound variable may shadow
        Expr_::Shift {
            label,
            var: cont_var,
            body,
        } => {
            if *cont_var == var {
                e.clone()
            } else {
                WithLoc::new(
                    Expr_::Shift {
                        label: *label,
                        var: *cont_var,
                        body: Box::new(wp_subst_expr(var, replacement, body)),
                    },
                    range,
                )
            }
        }

        Expr_::Reset { label, body } => WithLoc::new(
            Expr_::Reset {
                label: *label,
                body: Box::new(wp_subst_expr(var, replacement, body)),
            },
            range,
        ),

        // Complex cases - simplified handling
        Expr_::Match(scrutinee, arms) => WithLoc::new(
            Expr_::Match(
                Box::new(wp_subst_expr(var, replacement, scrutinee)),
                arms.clone(), // Note: proper handling would substitute in arm bodies
            ),
            range,
        ),

        Expr_::Try {
            body,
            catches,
            finally,
        } => WithLoc::new(
            Expr_::Try {
                body: Box::new(wp_subst_expr(var, replacement, body)),
                catches: catches.clone(),
                finally: finally
                    .as_ref()
                    .map(|f| Box::new(wp_subst_expr(var, replacement, f))),
            },
            range,
        ),

        Expr_::Handle(inner, handler) => WithLoc::new(
            Expr_::Handle(
                Box::new(wp_subst_expr(var, replacement, inner)),
                handler.clone(),
            ),
            range,
        ),

        Expr_::Perform(op, args) => WithLoc::new(
            Expr_::Perform(
                op.clone(),
                args.iter()
                    .map(|a| wp_subst_expr(var, replacement, a))
                    .collect(),
            ),
            range,
        ),

        Expr_::Resume { var: k, value } => WithLoc::new(
            Expr_::Resume {
                var: *k,
                value: Box::new(wp_subst_expr(var, replacement, value)),
            },
            range,
        ),

        // Gradual cast: substitute in the inner expression
        Expr_::GradualCast { expr, from, to, kind, blame } => WithLoc::new(
            Expr_::GradualCast {
                expr: Box::new(wp_subst_expr(var, replacement, expr)),
                from: from.clone(),
                to: to.clone(),
                kind: kind.clone(),
                blame: blame.clone(),
            },
            range,
        ),

        // Control flow labels
        Expr_::Goto { label } => WithLoc::new(Expr_::Goto { label: *label }, range),
        Expr_::Labeled { label, body } => WithLoc::new(
            Expr_::Labeled {
                label: *label,
                body: Box::new(wp_subst_expr(var, replacement, body)),
            },
            range,
        ),
    }
}

/// Extract the variable being assigned to from an assignment LHS
fn get_assign_var(lhs: &Expr) -> Option<VarId> {
    match &lhs.value {
        Expr_::Var(v) => Some(*v),
        _ => None,
    }
}

// ============================================================================
// WEAKEST PRECONDITION COMPUTATION
// ============================================================================

/// Weakest precondition computation
///
/// Computes the weakest precondition wp(stmt, post) such that:
/// - If wp(stmt, post) holds before stmt
/// - Then post holds after stmt
///
/// Maps to F* Contracts.fst (lines 382-428):
/// ```fstar
/// let rec wp_compute (c: expr) (post: formula) : Tot formula (decreases c) =
///   match c with
///   | ELit _ | EVar _ -> post
///   | EAssign x e -> subst_formula x e post
///   | ELet x _ init body ->
///       let body_wp = wp_compute body post in
///       let init_wp = wp_compute init (subst_formula x (EVar "__result") body_wp) in
///       init_wp
///   | ESeq e1 e2 -> wp_compute e1 (wp_compute e2 post)
///   | EIf cond then_ else_ ->
///       FAnd (FImpl (FExpr cond) (wp_compute then_ post))
///            (FImpl (FNot (FExpr cond)) (wp_compute else_ post))
///   | EWhile { invariant; condition; body } ->
///       FAnd invariant
///            (FForall "__state" TUnit
///              (FImpl (FAnd invariant (FExpr condition))
///                     (wp_compute body invariant)))
///   | EBlock stmts -> fold_right wp_compute stmts post
///   | _ -> post
/// ```
///
/// # Arguments
/// * `stmt` - The statement/expression to compute WP for
/// * `post` - The postcondition to establish
///
/// # Returns
/// The weakest precondition formula
#[must_use]
pub fn wp_compute(stmt: &Expr, post: &Formula) -> Formula {
    match &stmt.value {
        // Pure expressions: WP(pure, Q) = Q
        Expr_::Lit(_) | Expr_::Var(_) | Expr_::Global(_) | Expr_::Hole => post.clone(),

        // Assignment: WP(x := e, Q) = Q[e/x]
        Expr_::Assign(lhs, rhs) => {
            if let Some(var) = get_assign_var(lhs) {
                wp_subst_formula(var, rhs, post)
            } else {
                // Complex LHS (e.g., field access) - not handled, return post
                post.clone()
            }
        }

        // Let binding: WP(let x = init in body, Q) = WP(init, Q'[__result/x])
        // where Q' = WP(body, Q)
        Expr_::Let { init, body, .. } => {
            // Simplified: treat let as sequence of init; body
            let body_wp = wp_compute(body, post);
            wp_compute(init, &body_wp)
        }

        // Mutable let: WP(let mut x = init in body, Q)
        Expr_::LetMut { var: _, init, body, .. } => {
            let body_wp = wp_compute(body, post);
            // Substitute a fresh result variable for x in body_wp
            // For simplicity, we compute WP of init with body_wp
            // A full implementation would use a result variable
            wp_compute(init, &body_wp)
        }

        // Sequence: WP(e1; e2, Q) = WP(e1, WP(e2, Q))
        Expr_::Seq(e1, e2) => {
            let wp_e2 = wp_compute(e2, post);
            wp_compute(e1, &wp_e2)
        }

        // Conditional: WP(if c then t else e, Q) =
        //   (c => WP(t, Q)) /\ (~c => WP(e, Q))
        Expr_::If(cond, then_e, else_e) => {
            let wp_then = wp_compute(then_e, post);
            let wp_else = wp_compute(else_e, post);

            let cond_formula = Formula::Expr(Box::new((**cond).clone()));

            formula_and(
                formula_implies(cond_formula.clone(), wp_then),
                formula_implies(formula_not(cond_formula), wp_else),
            )
        }

        // While loop: WP(while c { body }, Q) = Q (for non-annotated loops)
        // For partial correctness, we'd need an invariant
        Expr_::While { .. } => {
            // Without an invariant, we can only return Q
            // With an invariant I:
            //   WP = I /\ forall state. (I /\ c => WP(body, I)) /\ (I /\ ~c => Q)
            // For now, return post (unsound for loops that modify variables)
            post.clone()
        }

        // For loop: similar to while, needs invariant for soundness
        Expr_::For { .. } => {
            // For loops are typically desugared to while loops
            // Without invariant annotation, return post
            post.clone()
        }

        // Block: WP([e1, e2, ..., en], Q) = WP(e1, WP(e2, ... WP(en, Q)))
        Expr_::Block(stmts) => {
            // Fold right: process statements from last to first
            stmts.iter().rev().fold(post.clone(), |acc, stmt| {
                wp_compute(stmt, &acc)
            })
        }

        // Loop: infinite loop needs invariant, return True (everything provable)
        Expr_::Loop { .. } => {
            // Infinite loops don't terminate, so any postcondition is vacuously true
            Formula::True
        }

        // Return: postcondition should reference the return value
        Expr_::Return(_) => {
            // For a return statement, the postcondition should hold for the returned value
            // This is typically handled at the function level
            post.clone()
        }

        // Break/Continue: control flow - return True (vacuous)
        Expr_::Break { .. } | Expr_::Continue { .. } => Formula::True,

        // Throw: exceptional control flow
        Expr_::Throw(_) => Formula::True,

        // Pure operations: propagate WP through sub-expressions
        Expr_::Unary(_, inner) => wp_compute(inner, post),
        Expr_::Binary(_, e1, e2) => {
            let wp_e2 = wp_compute(e2, post);
            wp_compute(e1, &wp_e2)
        }

        // Function call: would need function contract for precise WP
        Expr_::Call(_, _) | Expr_::MethodCall(_, _, _) => post.clone(),

        // Data construction: pure, return post
        Expr_::Tuple(_)
        | Expr_::Array(_)
        | Expr_::Struct { .. }
        | Expr_::Variant { .. } => post.clone(),

        // Field access: pure
        Expr_::Field(e, _) => wp_compute(e, post),
        Expr_::Index(e1, e2) => {
            let wp_e2 = wp_compute(e2, post);
            wp_compute(e1, &wp_e2)
        }
        Expr_::TupleProj(e, _) => wp_compute(e, post),

        // Memory operations: need more sophisticated handling
        Expr_::Box(inner)
        | Expr_::Deref(inner)
        | Expr_::Borrow(inner)
        | Expr_::BorrowMut(inner)
        | Expr_::Move(inner)
        | Expr_::Drop(inner) => wp_compute(inner, post),

        // Type operations: pure
        Expr_::As(e, _) | Expr_::Is(e, _) => wp_compute(e, post),
        Expr_::Sizeof(_) | Expr_::Alignof(_) => post.clone(),

        // Lambda/Closure: creating a closure is pure
        Expr_::Lambda { .. } | Expr_::Closure { .. } => post.clone(),

        // Async/Concurrent: would need effect handling
        Expr_::Await(inner)
        | Expr_::Yield(inner)
        | Expr_::Async(inner)
        | Expr_::Spawn(inner) => wp_compute(inner, post),

        // Effect operations: need effect-aware WP
        Expr_::Handle(e, _) => wp_compute(e, post),
        Expr_::Perform(_, _) => post.clone(),
        Expr_::Resume { value, .. } => wp_compute(value, post),

        // Delimited continuations
        Expr_::Reset { body, .. } => wp_compute(body, post),
        Expr_::Shift { body, .. } => wp_compute(body, post),

        // Try: would need exception-aware WP
        Expr_::Try { body, .. } => wp_compute(body, post),

        // Match: would need to handle all arms
        Expr_::Match(scrutinee, _arms) => wp_compute(scrutinee, post),

        // Unsafe: same as contained expression
        Expr_::Unsafe(inner) => wp_compute(inner, post),

        // Error node
        Expr_::Error(_) => Formula::False,

        // Gradual cast: compute WP of the inner expression
        Expr_::GradualCast { expr, .. } => wp_compute(expr, post),

        // Control flow labels: Goto doesn't change state, Labeled wraps body
        Expr_::Goto { .. } => post.clone(),
        Expr_::Labeled { body, .. } => wp_compute(body, post),
    }
}

/// Compute WP for an annotated while loop with invariant
///
/// For a while loop with invariant I:
/// ```text
/// while cond invariant I { body }
/// ```
///
/// The WP is:
/// ```text
/// I /\ (forall state. (I /\ cond => WP(body, I)) /\ (I /\ ~cond => Q))
/// ```
///
/// This version uses the invariant from an AnnotatedWhile.
#[must_use]
pub fn wp_annotated_while(
    invariant: &Formula,
    condition: &Expr,
    body: &Expr,
    post: &Formula,
) -> Formula {
    let body_wp = wp_compute(body, invariant);
    let cond_formula = Formula::Expr(Box::new(condition.clone()));

    // I /\ cond => WP(body, I)
    let preservation = formula_implies(
        formula_and(invariant.clone(), cond_formula.clone()),
        body_wp,
    );

    // I /\ ~cond => Q
    let termination = formula_implies(
        formula_and(invariant.clone(), formula_not(cond_formula)),
        post.clone(),
    );

    // I /\ (preservation /\ termination)
    formula_and(invariant.clone(), formula_and(preservation, termination))
}

// ============================================================================
// VERIFICATION CONDITION GENERATION
// ============================================================================

use super::contracts::Contract;

/// Generate verification condition from contract and expression
///
/// Maps to F* Contracts.fst (lines 621-624):
/// ```fstar
/// let generate_vc (c: contract) (e: expr) : vc =
///   let wp_post = wp e c.postcondition in
///   VCImpl (VCFormula c.precondition) (VCFormula wp_post)
/// ```
///
/// The generated VC states: if the precondition holds, then after executing
/// the expression, the postcondition holds. This is the fundamental Hoare
/// triple verification condition: {Pre} expr {Post} is valid iff Pre => WP(expr, Post).
///
/// # Arguments
/// * `contract` - The contract containing pre and post conditions
/// * `expr` - The expression/statement to verify
///
/// # Returns
/// A verification condition: Pre => WP(expr, Post)
#[must_use]
pub fn generate_vc(contract: &Contract, expr: &Expr) -> VC {
    let wp = wp_compute(expr, &contract.postcondition);
    VC::Impl(
        Box::new(VC::Formula(contract.precondition.clone())),
        Box::new(VC::Formula(wp)),
    )
}

/// Generate VC with loop invariant annotations
///
/// Maps to F* Contracts.fst (lines 627-681).
///
/// For expressions containing loops with invariants, generates proper VCs:
/// - For while loops with invariant: Pre => Inv, Inv /\ cond => WP(body, Inv), Inv /\ ~cond => Post
/// - For sequences: VCs for both parts with proper intermediate conditions
/// - For conditionals: VCs for both branches under respective conditions
/// - For blocks: Fold through statements
/// - For other expressions: Fall back to simple generate_vc
///
/// # Arguments
/// * `contract` - The contract containing pre and post conditions
/// * `expr` - The expression/statement to verify
/// * `invariants` - Map from loop expressions to their invariants
///
/// # Returns
/// A verification condition covering all paths through the expression
#[must_use]
pub fn generate_vc_with_invariants(
    contract: &Contract,
    expr: &Expr,
    invariants: &[(Expr, Formula)],
) -> VC {
    generate_vc_with_invariants_impl(contract, expr, invariants, 100)
}

/// Internal implementation with fuel for termination
fn generate_vc_with_invariants_impl(
    contract: &Contract,
    expr: &Expr,
    invariants: &[(Expr, Formula)],
    fuel: usize,
) -> VC {
    if fuel == 0 {
        return VC::False;
    }

    match &expr.value {
        // While loop - check for invariant annotation
        Expr_::While { cond, body, .. } => {
            // Find invariant for this loop by matching condition and body
            let inv_opt = invariants.iter().find(|(loop_expr, _)| {
                match &loop_expr.value {
                    Expr_::While {
                        cond: loop_cond,
                        body: loop_body,
                        ..
                    } => {
                        // Compare condition and body structurally
                        **cond == **loop_cond && **body == **loop_body
                    }
                    _ => false,
                }
            });

            match inv_opt {
                Some((_, inv)) => {
                    // Generate VCs for the loop with invariant
                    loop_vcs(
                        &contract.precondition,
                        inv,
                        cond,
                        body,
                        &contract.postcondition,
                    )
                }
                None => {
                    // No invariant provided - cannot verify loop
                    VC::False
                }
            }
        }

        // Sequence: generate VCs for both parts
        Expr_::Seq(e1, e2) => {
            // For e1; e2 with contract {Pre}..{Post}:
            // - e1 must establish WP(e2, Post) as intermediate condition
            // - e2 must establish Post from intermediate
            let intermediate = wp_compute(e2, &contract.postcondition);
            let c1 = Contract::new(contract.precondition.clone(), intermediate);
            let c2 = Contract::new(wp_compute(e2, &contract.postcondition), contract.postcondition.clone());

            let vc1 = generate_vc_with_invariants_impl(&c1, e1, invariants, fuel - 1);
            let vc2 = generate_vc_with_invariants_impl(&c2, e2, invariants, fuel - 1);
            vc_and(vc1, vc2)
        }

        // Conditional: VCs for both branches
        Expr_::If(cond, then_e, else_e) => {
            let vc_then = generate_vc_with_invariants_impl(contract, then_e, invariants, fuel - 1);
            let vc_else = generate_vc_with_invariants_impl(contract, else_e, invariants, fuel - 1);

            let cond_vc = VC::Formula(Formula::Expr(Box::new((**cond).clone())));
            let not_cond_vc = vc_not(VC::Formula(Formula::Expr(Box::new((**cond).clone()))));

            vc_and(
                vc_impl(cond_vc, vc_then),
                vc_impl(not_cond_vc, vc_else),
            )
        }

        // Block: process statements in sequence
        Expr_::Block(stmts) => {
            if stmts.is_empty() {
                // Empty block: Pre => Post
                generate_vc(contract, expr)
            } else if stmts.len() == 1 {
                generate_vc_with_invariants_impl(contract, &stmts[0], invariants, fuel - 1)
            } else {
                // Multiple statements: fold from right
                let (last, rest) = stmts.split_last().unwrap();

                // Build intermediate contract for rest
                let intermediate = wp_compute(last, &contract.postcondition);
                let rest_contract = Contract::new(contract.precondition.clone(), intermediate);

                // Build a synthetic block for the rest
                let rest_block = WithLoc::new(Expr_::Block(rest.to_vec()), expr.range);

                let vc_rest = generate_vc_with_invariants_impl(&rest_contract, &rest_block, invariants, fuel - 1);
                let vc_last = generate_vc_with_invariants_impl(contract, last, invariants, fuel - 1);
                vc_and(vc_rest, vc_last)
            }
        }

        // For loop - similar to while, needs invariant
        Expr_::For { iter, body, .. } => {
            let inv_opt = invariants.iter().find(|(loop_expr, _)| {
                match &loop_expr.value {
                    Expr_::For {
                        iter: loop_iter,
                        body: loop_body,
                        ..
                    } => **iter == **loop_iter && **body == **loop_body,
                    _ => false,
                }
            });

            match inv_opt {
                Some((_, inv)) => {
                    // For loops are typically desugared to while loops
                    // Generate similar VCs
                    vc_and(
                        invariant_holds_initially(&contract.precondition, inv),
                        invariant_implies_post(inv, iter, &contract.postcondition),
                    )
                }
                None => VC::False,
            }
        }

        // Infinite loop - needs invariant for termination
        Expr_::Loop { body, .. } => {
            let inv_opt = invariants.iter().find(|(loop_expr, _)| {
                match &loop_expr.value {
                    Expr_::Loop {
                        body: loop_body, ..
                    } => **body == **loop_body,
                    _ => false,
                }
            });

            match inv_opt {
                Some((_, inv)) => {
                    // For infinite loops, we only check invariant establishment
                    // and inductiveness - no termination condition
                    vc_and(
                        invariant_holds_initially(&contract.precondition, inv),
                        // Invariant is inductive: Inv => WP(body, Inv)
                        VC::Impl(
                            Box::new(VC::Formula(inv.clone())),
                            Box::new(VC::Formula(wp_compute(body, inv))),
                        ),
                    )
                }
                None => VC::False,
            }
        }

        // Default: use simple VC generation
        _ => generate_vc(contract, expr),
    }
}

// ============================================================================
// LOOP INVARIANT VCs
// ============================================================================

/// Check that precondition establishes invariant
///
/// Maps to F* Contracts.fst (lines 779-780):
/// ```fstar
/// let invariant_holds_initially (pre: formula) (inv: formula) : vc =
///   VCImpl (VCFormula pre) (VCFormula inv)
/// ```
///
/// The generated VC states: Pre => Inv (precondition implies invariant).
/// This ensures the invariant holds when the loop is first entered.
///
/// # Arguments
/// * `pre` - The precondition (what holds before the loop)
/// * `inv` - The loop invariant
///
/// # Returns
/// A VC: Pre => Inv
#[must_use]
pub fn invariant_holds_initially(pre: &Formula, inv: &Formula) -> VC {
    VC::Impl(
        Box::new(VC::Formula(pre.clone())),
        Box::new(VC::Formula(inv.clone())),
    )
}

/// Check that invariant is preserved by loop body
///
/// Maps to F* Contracts.fst (lines 783-786):
/// ```fstar
/// let invariant_is_inductive (inv: formula) (cond: expr) (body: expr) : vc =
///   VCImpl
///     (VCAnd (VCFormula inv) (VCFormula (FExpr cond)))
///     (VCFormula (wp body inv))
/// ```
///
/// The generated VC states: (Inv /\ cond) => WP(body, Inv)
/// This ensures that if the invariant holds and the loop condition is true,
/// executing the body will re-establish the invariant.
///
/// # Arguments
/// * `inv` - The loop invariant
/// * `cond` - The loop condition expression
/// * `body` - The loop body expression
///
/// # Returns
/// A VC: (Inv /\ cond) => WP(body, Inv)
#[must_use]
pub fn invariant_is_inductive(inv: &Formula, cond: &Expr, body: &Expr) -> VC {
    let cond_formula = Formula::Expr(Box::new(cond.clone()));
    let body_wp = wp_compute(body, inv);

    VC::Impl(
        Box::new(vc_and(
            VC::Formula(inv.clone()),
            VC::Formula(cond_formula),
        )),
        Box::new(VC::Formula(body_wp)),
    )
}

/// Check that invariant with negated condition implies postcondition
///
/// Maps to F* Contracts.fst (lines 788-792):
/// ```fstar
/// let invariant_implies_post (inv: formula) (cond: expr) (post: formula) : vc =
///   VCImpl
///     (VCAnd (VCFormula inv) (VCNot (VCFormula (FExpr cond))))
///     (VCFormula post)
/// ```
///
/// The generated VC states: (Inv /\ ~cond) => Post
/// This ensures that when the loop terminates (condition becomes false),
/// the invariant plus negated condition implies the desired postcondition.
///
/// # Arguments
/// * `inv` - The loop invariant
/// * `cond` - The loop condition expression
/// * `post` - The desired postcondition
///
/// # Returns
/// A VC: (Inv /\ ~cond) => Post
#[must_use]
pub fn invariant_implies_post(inv: &Formula, cond: &Expr, post: &Formula) -> VC {
    let cond_formula = Formula::Expr(Box::new(cond.clone()));
    let not_cond = VC::Not(Box::new(VC::Formula(cond_formula)));

    VC::Impl(
        Box::new(vc_and(VC::Formula(inv.clone()), not_cond)),
        Box::new(VC::Formula(post.clone())),
    )
}

/// Generate all VCs for a while loop with invariant
///
/// Maps to F* Contracts.fst (lines 794-800):
/// ```fstar
/// let loop_vcs (pre: formula) (inv: formula) (cond: expr) (body: expr) (post: formula) : vc =
///   VCAnd
///     (invariant_holds_initially pre inv)
///     (VCAnd
///       (invariant_is_inductive inv cond body)
///       (invariant_implies_post inv cond post))
/// ```
///
/// Combines all three loop verification conditions:
/// 1. Pre => Inv (invariant holds initially)
/// 2. (Inv /\ cond) => WP(body, Inv) (invariant is inductive)
/// 3. (Inv /\ ~cond) => Post (invariant implies postcondition)
///
/// # Arguments
/// * `pre` - The precondition
/// * `inv` - The loop invariant
/// * `cond` - The loop condition expression
/// * `body` - The loop body expression
/// * `post` - The postcondition
///
/// # Returns
/// A VC combining all three loop VCs with conjunction
#[must_use]
pub fn loop_vcs(
    pre: &Formula,
    inv: &Formula,
    cond: &Expr,
    body: &Expr,
    post: &Formula,
) -> VC {
    vc_and(
        invariant_holds_initially(pre, inv),
        vc_and(
            invariant_is_inductive(inv, cond, body),
            invariant_implies_post(inv, cond, post),
        ),
    )
}

// ============================================================================
// CONTRACT VERIFICATION
// ============================================================================

/// Check a verification condition (simple syntactic check)
///
/// This performs a simple syntactic check for trivially true/false VCs.
/// For full verification, an SMT solver would be needed.
///
/// # Arguments
/// * `vc` - The verification condition to check
///
/// # Returns
/// `true` if the VC is trivially valid, `false` otherwise
#[must_use]
pub fn check_vc(vc: &VC) -> bool {
    is_trivially_true(vc)
}

/// Verify that a contract holds for an expression
///
/// Maps to F* Contracts.fst (lines 698-702):
/// ```fstar
/// let verify_contract (c: contract) (e: expr) : verification_result =
///   let vc = generate_vc c e in
///   let vc' = simplify_vc vc in
///   if check_vc vc' then Verified
///   else Failed vc'
/// ```
///
/// Generates a verification condition, simplifies it, and checks validity.
///
/// # Arguments
/// * `contract` - The contract with pre/post conditions
/// * `expr` - The expression to verify
///
/// # Returns
/// - `Valid` if the contract is verified
/// - `Invalid(Counterexample::new())` if verification fails
/// - `Unknown` if verification is inconclusive
#[must_use]
pub fn verify_contract(contract: &Contract, expr: &Expr) -> VerificationResult {
    let vc = generate_vc(contract, expr);
    let simplified = vc_simplify(vc);

    if check_vc(&simplified) {
        VerificationResult::Valid
    } else if is_trivially_false(&simplified) {
        VerificationResult::Invalid(Counterexample::new())
    } else {
        VerificationResult::Unknown {
            reason: "SMT solving not implemented".to_string(),
        }
    }
}

/// Verify a contract with loop invariant annotations
///
/// Maps to F* Contracts.fst (lines 705-710):
/// ```fstar
/// let verify_contract_with_invariants (c: contract) (e: expr)
///     (invariants: list (expr & formula)) : verification_result =
///   let vc = generate_vc_with_invariants 100 c e invariants in
///   let vc' = simplify_vc vc in
///   if check_vc vc' then Verified
///   else Failed vc'
/// ```
///
/// # Arguments
/// * `contract` - The contract with pre/post conditions
/// * `expr` - The expression to verify
/// * `invariants` - Map from loop expressions to their invariants
///
/// # Returns
/// Verification result
#[must_use]
pub fn verify_contract_with_invariants(
    contract: &Contract,
    expr: &Expr,
    invariants: &[(Expr, Formula)],
) -> VerificationResult {
    let vc = generate_vc_with_invariants(contract, expr, invariants);
    let simplified = vc_simplify(vc);

    if check_vc(&simplified) {
        VerificationResult::Valid
    } else if is_trivially_false(&simplified) {
        VerificationResult::Invalid(Counterexample::new())
    } else {
        VerificationResult::Unknown {
            reason: "SMT solving not implemented".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vc_and_simplification() {
        assert_eq!(vc_and(VC::True, VC::True), VC::True);
        assert_eq!(vc_and(VC::True, VC::False), VC::False);
        assert_eq!(vc_and(VC::False, VC::True), VC::False);
        assert_eq!(vc_and(VC::False, VC::False), VC::False);

        let formula = VC::Formula(Formula::True);
        assert_eq!(vc_and(VC::True, formula.clone()), formula);
        assert_eq!(vc_and(formula.clone(), VC::True), formula);
        assert_eq!(vc_and(VC::False, formula), VC::False);
    }

    #[test]
    fn test_vc_or_simplification() {
        assert_eq!(vc_or(VC::True, VC::True), VC::True);
        assert_eq!(vc_or(VC::True, VC::False), VC::True);
        assert_eq!(vc_or(VC::False, VC::True), VC::True);
        assert_eq!(vc_or(VC::False, VC::False), VC::False);

        let formula = VC::Formula(Formula::False);
        assert_eq!(vc_or(VC::False, formula.clone()), formula);
        assert_eq!(vc_or(formula.clone(), VC::False), formula);
        assert_eq!(vc_or(VC::True, formula), VC::True);
    }

    #[test]
    fn test_vc_not_simplification() {
        assert_eq!(vc_not(VC::True), VC::False);
        assert_eq!(vc_not(VC::False), VC::True);
        assert_eq!(vc_not(vc_not(VC::True)), VC::True);
    }

    #[test]
    fn test_vc_impl_simplification() {
        assert_eq!(vc_impl(VC::True, VC::True), VC::True);
        assert_eq!(vc_impl(VC::True, VC::False), VC::False);
        assert_eq!(vc_impl(VC::False, VC::True), VC::True);
        assert_eq!(vc_impl(VC::False, VC::False), VC::True);

        let formula = VC::Formula(Formula::True);
        assert_eq!(vc_impl(VC::True, formula.clone()), formula);
        assert_eq!(vc_impl(VC::False, formula.clone()), VC::True);
        assert_eq!(vc_impl(formula, VC::True), VC::True);
    }

    #[test]
    fn test_is_trivially_true() {
        assert!(is_trivially_true(&VC::True));
        assert!(!is_trivially_true(&VC::False));
        assert!(is_trivially_true(&VC::Formula(Formula::True)));
        assert!(!is_trivially_true(&VC::Formula(Formula::False)));

        // Implication with false antecedent
        let impl_false = VC::Impl(Box::new(VC::False), Box::new(VC::False));
        assert!(is_trivially_true(&impl_false));

        // Conjunction of true values
        let and_true = VC::And(Box::new(VC::True), Box::new(VC::True));
        assert!(is_trivially_true(&and_true));
    }

    #[test]
    fn test_is_trivially_false() {
        assert!(!is_trivially_false(&VC::True));
        assert!(is_trivially_false(&VC::False));
        assert!(!is_trivially_false(&VC::Formula(Formula::True)));
        assert!(is_trivially_false(&VC::Formula(Formula::False)));

        // Conjunction with false
        let and_false = VC::And(Box::new(VC::True), Box::new(VC::False));
        assert!(is_trivially_false(&and_false));

        // Disjunction of false values
        let or_false = VC::Or(Box::new(VC::False), Box::new(VC::False));
        assert!(is_trivially_false(&or_false));
    }

    #[test]
    fn test_vc_simplify() {
        // Deep simplification
        let complex = VC::And(
            Box::new(VC::Or(Box::new(VC::True), Box::new(VC::False))),
            Box::new(VC::Not(Box::new(VC::False))),
        );
        assert_eq!(vc_simplify(complex), VC::True);

        // Implication simplification
        let impl_vc = VC::Impl(Box::new(VC::True), Box::new(VC::True));
        assert_eq!(vc_simplify(impl_vc), VC::True);
    }

    #[test]
    fn test_vc_from_formula() {
        assert_eq!(vc_from_formula(Formula::True), VC::True);
        assert_eq!(vc_from_formula(Formula::False), VC::False);

        let nested = Formula::And(
            Box::new(Formula::True),
            Box::new(Formula::True),
        );
        assert_eq!(vc_from_formula(nested), VC::True);
    }

    #[test]
    fn test_verification_result() {
        let valid = VerificationResult::Valid;
        assert!(valid.is_valid());
        assert!(!valid.is_invalid());

        let cex = Counterexample::new();
        let invalid = VerificationResult::Invalid(cex);
        assert!(invalid.is_invalid());
        assert!(invalid.counterexample().is_some());

        let unknown = VerificationResult::Unknown {
            reason: "timeout".to_string(),
        };
        assert!(unknown.is_unknown());
    }

    #[test]
    fn test_counterexample() {
        let mut cex = Counterexample::new();
        let var = Spur::default();
        cex.add_binding(var, Value::Int(42));

        assert_eq!(cex.get(var), Some(&Value::Int(42)));
    }

    #[test]
    fn test_value_accessors() {
        let b = Value::Bool(true);
        assert!(b.is_bool());
        assert_eq!(b.as_bool(), Some(true));
        assert!(!b.is_int());

        let n = Value::Int(42);
        assert!(n.is_int());
        assert_eq!(n.as_int(), Some(42));
        assert!(!n.is_bool());
    }

    #[test]
    fn test_vc_method_chaining() {
        let result = VC::True
            .and(VC::True)
            .or(VC::False)
            .implies(VC::True);
        assert!(result.is_trivially_true());
    }
}
