//! Formula types for refinement predicates
//!
//! Mirrors F* DependentTypes.fsti formula type for first-order logic formulas
//! used in refinement types `{ x : T | phi }`.
//!
//! # Formula Structure
//! - Propositional: True, False, And, Or, Not, Impl, Iff
//! - Comparison: FCmp with CmpOp
//! - Quantifiers: Forall, Exists with bound variable and type
//! - Predicates: Named predicates P(e)
//! - Expression coercion: Lift boolean expressions to formulas

use std::collections::HashSet;

use lasso::Spur;
use serde::{Deserialize, Serialize};

use crate::expr::Expr;
use crate::types::BrrrType;

/// Dependent variable - bound variable in quantified formulas
///
/// Uses interned strings for efficient comparison and storage.
/// Represents variables bound by forall/exists quantifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DepVar(pub Spur);

impl DepVar {
    /// Create a new dependent variable from an interned string
    #[inline]
    pub const fn new(spur: Spur) -> Self {
        Self(spur)
    }

    /// Get the underlying interned string key
    #[inline]
    pub const fn key(self) -> Spur {
        self.0
    }
}

impl From<Spur> for DepVar {
    fn from(spur: Spur) -> Self {
        Self(spur)
    }
}

/// Comparison operators for refinement predicates
///
/// Maps to F*:
/// ```fstar
/// type cmp_op = | CmpEq | CmpNe | CmpLt | CmpLe | CmpGt | CmpGe
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum CmpOp {
    /// Equality `==`
    Eq = 0,
    /// Not equal `!=`
    Ne = 1,
    /// Less than `<`
    Lt = 2,
    /// Less or equal `<=`
    Le = 3,
    /// Greater than `>`
    Gt = 4,
    /// Greater or equal `>=`
    Ge = 5,
}

impl CmpOp {
    /// Negate the comparison operator
    ///
    /// Returns the operator that gives the opposite result:
    /// - `Eq` <-> `Ne`
    /// - `Lt` <-> `Ge`
    /// - `Le` <-> `Gt`
    #[must_use]
    pub const fn negate(self) -> Self {
        match self {
            Self::Eq => Self::Ne,
            Self::Ne => Self::Eq,
            Self::Lt => Self::Ge,
            Self::Le => Self::Gt,
            Self::Gt => Self::Le,
            Self::Ge => Self::Lt,
        }
    }

    /// Flip operands (reverse comparison direction)
    ///
    /// Returns the operator for `b op a` given `a self b`:
    /// - `Lt` <-> `Gt`
    /// - `Le` <-> `Ge`
    /// - `Eq`, `Ne` are symmetric
    #[must_use]
    pub const fn flip(self) -> Self {
        match self {
            Self::Eq => Self::Eq,
            Self::Ne => Self::Ne,
            Self::Lt => Self::Gt,
            Self::Le => Self::Ge,
            Self::Gt => Self::Lt,
            Self::Ge => Self::Le,
        }
    }

    /// Format as mathematical symbol
    pub const fn as_symbol(self) -> &'static str {
        match self {
            Self::Eq => "=",
            Self::Ne => "\u{2260}", // ≠
            Self::Lt => "<",
            Self::Le => "\u{2264}", // ≤
            Self::Gt => ">",
            Self::Ge => "\u{2265}", // ≥
        }
    }

    /// Format as ASCII symbol
    pub const fn as_ascii(self) -> &'static str {
        match self {
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
        }
    }

    /// Get binary discriminant for encoding
    pub const fn discriminant(self) -> u8 {
        self as u8
    }
}

/// First-order logic formula for refinement types
///
/// Maps to F*:
/// ```fstar
/// noeq type formula =
///   | FTrue    : formula
///   | FFalse   : formula
///   | FCmp     : cmp_op -> expr -> expr -> formula
///   | FAnd     : formula -> formula -> formula
///   | FOr      : formula -> formula -> formula
///   | FNot     : formula -> formula
///   | FImpl    : formula -> formula -> formula
///   | FIff     : formula -> formula -> formula
///   | FForall  : dep_var -> brrr_type -> formula -> formula
///   | FExists  : dep_var -> brrr_type -> formula -> formula
///   | FPred    : string -> expr -> formula
///   | FExpr    : expr -> formula
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Formula {
    /// Logical true `T`
    True,

    /// Logical false `F`
    False,

    /// Comparison `e1 op e2` (e.g., `x < 10`)
    Cmp(CmpOp, Box<Expr>, Box<Expr>),

    /// Conjunction `phi /\ psi`
    And(Box<Formula>, Box<Formula>),

    /// Disjunction `phi \/ psi`
    Or(Box<Formula>, Box<Formula>),

    /// Negation `~phi`
    Not(Box<Formula>),

    /// Implication `phi => psi`
    Impl(Box<Formula>, Box<Formula>),

    /// Bi-implication `phi <=> psi`
    Iff(Box<Formula>, Box<Formula>),

    /// Universal quantifier `forall x:T. phi`
    Forall(DepVar, BrrrType, Box<Formula>),

    /// Existential quantifier `exists x:T. phi`
    Exists(DepVar, BrrrType, Box<Formula>),

    /// Named predicate application `P(e)`
    Pred(Spur, Box<Expr>),

    /// Boolean expression coercion (lift bool expr to formula)
    Expr(Box<Expr>),
}

/// Constant for logical true
pub const TRUE: Formula = Formula::True;

/// Constant for logical false
pub const FALSE: Formula = Formula::False;

impl Formula {
    /// Create a comparison formula `e1 op e2`
    #[inline]
    pub fn cmp(op: CmpOp, lhs: Expr, rhs: Expr) -> Self {
        Self::Cmp(op, Box::new(lhs), Box::new(rhs))
    }

    /// Create an equality formula `e1 = e2`
    #[inline]
    pub fn eq(lhs: Expr, rhs: Expr) -> Self {
        Self::cmp(CmpOp::Eq, lhs, rhs)
    }

    /// Create an inequality formula `e1 != e2`
    #[inline]
    pub fn ne(lhs: Expr, rhs: Expr) -> Self {
        Self::cmp(CmpOp::Ne, lhs, rhs)
    }

    /// Create a less-than formula `e1 < e2`
    #[inline]
    pub fn lt(lhs: Expr, rhs: Expr) -> Self {
        Self::cmp(CmpOp::Lt, lhs, rhs)
    }

    /// Create a less-or-equal formula `e1 <= e2`
    #[inline]
    pub fn le(lhs: Expr, rhs: Expr) -> Self {
        Self::cmp(CmpOp::Le, lhs, rhs)
    }

    /// Create a greater-than formula `e1 > e2`
    #[inline]
    pub fn gt(lhs: Expr, rhs: Expr) -> Self {
        Self::cmp(CmpOp::Gt, lhs, rhs)
    }

    /// Create a greater-or-equal formula `e1 >= e2`
    #[inline]
    pub fn ge(lhs: Expr, rhs: Expr) -> Self {
        Self::cmp(CmpOp::Ge, lhs, rhs)
    }

    /// Create a named predicate `P(e)`
    #[inline]
    pub fn pred(name: Spur, arg: Expr) -> Self {
        Self::Pred(name, Box::new(arg))
    }

    /// Coerce a boolean expression to a formula
    #[inline]
    pub fn from_expr(e: Expr) -> Self {
        Self::Expr(Box::new(e))
    }

    /// Create universal quantification `forall x:T. phi`
    #[inline]
    pub fn forall(var: DepVar, ty: BrrrType, body: Self) -> Self {
        Self::Forall(var, ty, Box::new(body))
    }

    /// Create existential quantification `exists x:T. phi`
    #[inline]
    pub fn exists(var: DepVar, ty: BrrrType, body: Self) -> Self {
        Self::Exists(var, ty, Box::new(body))
    }

    /// Is this the trivially true formula?
    #[inline]
    pub const fn is_true(&self) -> bool {
        matches!(self, Self::True)
    }

    /// Is this the trivially false formula?
    #[inline]
    pub const fn is_false(&self) -> bool {
        matches!(self, Self::False)
    }

    /// Is this a propositional formula (no quantifiers)?
    pub fn is_propositional(&self) -> bool {
        match self {
            Self::True | Self::False | Self::Cmp(..) | Self::Pred(..) | Self::Expr(_) => true,
            Self::Not(inner) => inner.is_propositional(),
            Self::And(lhs, rhs)
            | Self::Or(lhs, rhs)
            | Self::Impl(lhs, rhs)
            | Self::Iff(lhs, rhs) => lhs.is_propositional() && rhs.is_propositional(),
            Self::Forall(..) | Self::Exists(..) => false,
        }
    }

    /// Is this a closed formula (no free dependent variables)?
    ///
    /// A formula is closed if all variables are bound by quantifiers.
    pub fn is_closed(&self) -> bool {
        self.free_vars().is_empty()
    }

    /// Collect all free dependent variables in the formula
    ///
    /// A variable is free if it appears in a Pred or Expr but is not
    /// bound by an enclosing Forall or Exists quantifier.
    pub fn free_vars(&self) -> HashSet<DepVar> {
        self.free_vars_with_bound(&HashSet::new())
    }

    /// Internal helper: collect free vars with a set of bound vars
    fn free_vars_with_bound(&self, bound: &HashSet<DepVar>) -> HashSet<DepVar> {
        match self {
            Self::True | Self::False => HashSet::new(),

            Self::Cmp(_, lhs, rhs) => {
                // Expressions may contain variable references
                // For now, we consider all DepVars in expressions as potentially free
                let mut vars = HashSet::new();
                collect_dep_vars_from_expr(lhs, bound, &mut vars);
                collect_dep_vars_from_expr(rhs, bound, &mut vars);
                vars
            }

            Self::And(lhs, rhs)
            | Self::Or(lhs, rhs)
            | Self::Impl(lhs, rhs)
            | Self::Iff(lhs, rhs) => {
                let mut vars = lhs.free_vars_with_bound(bound);
                vars.extend(rhs.free_vars_with_bound(bound));
                vars
            }

            Self::Not(inner) => inner.free_vars_with_bound(bound),

            Self::Forall(var, _, body) | Self::Exists(var, _, body) => {
                let mut new_bound = bound.clone();
                new_bound.insert(*var);
                body.free_vars_with_bound(&new_bound)
            }

            Self::Pred(_, arg) => {
                let mut vars = HashSet::new();
                collect_dep_vars_from_expr(arg, bound, &mut vars);
                vars
            }

            Self::Expr(e) => {
                let mut vars = HashSet::new();
                collect_dep_vars_from_expr(e, bound, &mut vars);
                vars
            }
        }
    }

    /// Get the discriminant tag for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::True => 0,
            Self::False => 1,
            Self::Cmp(..) => 2,
            Self::And(..) => 3,
            Self::Or(..) => 4,
            Self::Not(_) => 5,
            Self::Impl(..) => 6,
            Self::Iff(..) => 7,
            Self::Forall(..) => 8,
            Self::Exists(..) => 9,
            Self::Pred(..) => 10,
            Self::Expr(_) => 11,
        }
    }
}

/// Collect DepVar references from an expression
///
/// This is a placeholder - actual implementation would traverse
/// the expression AST looking for variable references that match DepVars.
/// For now, we conservatively return empty since Expr uses VarId (Spur)
/// directly, not DepVar.
fn collect_dep_vars_from_expr(_expr: &Expr, _bound: &HashSet<DepVar>, _out: &mut HashSet<DepVar>) {
    // Expression variables (VarId = Spur) and DepVar are both Spur-based
    // but represent different namespaces. In a full implementation,
    // we would need to track which Spurs correspond to quantified DepVars.
    //
    // For now, this is conservative: we don't report any free vars from
    // expressions, meaning is_closed() may return true even when there
    // are unbound references. A proper implementation would:
    // 1. Track a mapping from DepVar to VarId during formula construction
    // 2. Or use a different representation that unifies the two
}

impl Default for Formula {
    fn default() -> Self {
        Self::True
    }
}

// ============================================================================
// Helper functions for formula construction
// ============================================================================

/// Create a conjunction `phi /\ psi`
///
/// Performs basic simplification:
/// - `True /\ phi = phi`
/// - `False /\ phi = False`
/// - `phi /\ True = phi`
/// - `phi /\ False = False`
#[must_use]
pub fn formula_and(lhs: Formula, rhs: Formula) -> Formula {
    match (&lhs, &rhs) {
        (Formula::True, _) => rhs,
        (_, Formula::True) => lhs,
        (Formula::False, _) | (_, Formula::False) => Formula::False,
        _ => Formula::And(Box::new(lhs), Box::new(rhs)),
    }
}

/// Create a disjunction `phi \/ psi`
///
/// Performs basic simplification:
/// - `True \/ phi = True`
/// - `False \/ phi = phi`
/// - `phi \/ True = True`
/// - `phi \/ False = phi`
#[must_use]
pub fn formula_or(lhs: Formula, rhs: Formula) -> Formula {
    match (&lhs, &rhs) {
        (Formula::True, _) | (_, Formula::True) => Formula::True,
        (Formula::False, _) => rhs,
        (_, Formula::False) => lhs,
        _ => Formula::Or(Box::new(lhs), Box::new(rhs)),
    }
}

/// Create a negation `~phi`
///
/// Performs basic simplification:
/// - `~True = False`
/// - `~False = True`
/// - `~~phi = phi` (double negation elimination)
#[must_use]
pub fn formula_not(phi: Formula) -> Formula {
    match phi {
        Formula::True => Formula::False,
        Formula::False => Formula::True,
        Formula::Not(inner) => *inner,
        other => Formula::Not(Box::new(other)),
    }
}

/// Create an implication `phi => psi`
///
/// Performs basic simplification:
/// - `True => psi = psi`
/// - `False => psi = True`
/// - `phi => True = True`
/// - `phi => False = ~phi`
#[must_use]
pub fn formula_implies(lhs: Formula, rhs: Formula) -> Formula {
    match (&lhs, &rhs) {
        (Formula::True, _) => rhs,
        (Formula::False, _) => Formula::True,
        (_, Formula::True) => Formula::True,
        (_, Formula::False) => formula_not(lhs),
        _ => Formula::Impl(Box::new(lhs), Box::new(rhs)),
    }
}

/// Create a bi-implication `phi <=> psi`
///
/// Performs basic simplification:
/// - `True <=> psi = psi`
/// - `False <=> psi = ~psi`
/// - `phi <=> True = phi`
/// - `phi <=> False = ~phi`
#[must_use]
pub fn formula_iff(lhs: Formula, rhs: Formula) -> Formula {
    match (&lhs, &rhs) {
        (Formula::True, _) => rhs,
        (_, Formula::True) => lhs,
        (Formula::False, _) => formula_not(rhs),
        (_, Formula::False) => formula_not(lhs),
        _ => Formula::Iff(Box::new(lhs), Box::new(rhs)),
    }
}

/// Conjoin multiple formulas `phi_1 /\ phi_2 /\ ... /\ phi_n`
///
/// Returns `True` for empty input.
#[must_use]
pub fn formula_and_all<I: IntoIterator<Item = Formula>>(formulas: I) -> Formula {
    formulas
        .into_iter()
        .fold(Formula::True, |acc, f| formula_and(acc, f))
}

/// Disjoin multiple formulas `phi_1 \/ phi_2 \/ ... \/ phi_n`
///
/// Returns `False` for empty input.
#[must_use]
pub fn formula_or_all<I: IntoIterator<Item = Formula>>(formulas: I) -> Formula {
    formulas
        .into_iter()
        .fold(Formula::False, |acc, f| formula_or(acc, f))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{Expr_, Literal, WithLoc};

    fn make_int_expr(n: i32) -> Expr {
        WithLoc::synthetic(Expr_::Lit(Literal::i32(n)))
    }

    #[test]
    fn test_cmp_op_negate() {
        assert_eq!(CmpOp::Eq.negate(), CmpOp::Ne);
        assert_eq!(CmpOp::Ne.negate(), CmpOp::Eq);
        assert_eq!(CmpOp::Lt.negate(), CmpOp::Ge);
        assert_eq!(CmpOp::Ge.negate(), CmpOp::Lt);
        assert_eq!(CmpOp::Le.negate(), CmpOp::Gt);
        assert_eq!(CmpOp::Gt.negate(), CmpOp::Le);
    }

    #[test]
    fn test_cmp_op_flip() {
        assert_eq!(CmpOp::Lt.flip(), CmpOp::Gt);
        assert_eq!(CmpOp::Gt.flip(), CmpOp::Lt);
        assert_eq!(CmpOp::Le.flip(), CmpOp::Ge);
        assert_eq!(CmpOp::Ge.flip(), CmpOp::Le);
        assert_eq!(CmpOp::Eq.flip(), CmpOp::Eq);
        assert_eq!(CmpOp::Ne.flip(), CmpOp::Ne);
    }

    #[test]
    fn test_formula_constants() {
        assert!(TRUE.is_true());
        assert!(!TRUE.is_false());
        assert!(FALSE.is_false());
        assert!(!FALSE.is_true());
    }

    #[test]
    fn test_formula_and_simplification() {
        let phi = Formula::cmp(CmpOp::Lt, make_int_expr(1), make_int_expr(2));

        assert!(matches!(formula_and(Formula::True, phi.clone()), Formula::Cmp(..)));
        assert!(matches!(formula_and(phi.clone(), Formula::True), Formula::Cmp(..)));
        assert!(formula_and(Formula::False, phi.clone()).is_false());
        assert!(formula_and(phi, Formula::False).is_false());
    }

    #[test]
    fn test_formula_or_simplification() {
        let phi = Formula::cmp(CmpOp::Lt, make_int_expr(1), make_int_expr(2));

        assert!(formula_or(Formula::True, phi.clone()).is_true());
        assert!(formula_or(phi.clone(), Formula::True).is_true());
        assert!(matches!(formula_or(Formula::False, phi.clone()), Formula::Cmp(..)));
        assert!(matches!(formula_or(phi, Formula::False), Formula::Cmp(..)));
    }

    #[test]
    fn test_formula_not_simplification() {
        assert!(formula_not(Formula::True).is_false());
        assert!(formula_not(Formula::False).is_true());

        let phi = Formula::cmp(CmpOp::Lt, make_int_expr(1), make_int_expr(2));
        let not_phi = formula_not(phi.clone());
        assert!(matches!(not_phi, Formula::Not(_)));

        // Double negation elimination
        let not_not_phi = formula_not(not_phi);
        assert!(matches!(not_not_phi, Formula::Cmp(..)));
    }

    #[test]
    fn test_formula_implies_simplification() {
        let phi = Formula::cmp(CmpOp::Lt, make_int_expr(1), make_int_expr(2));

        // True => psi = psi
        assert!(matches!(formula_implies(Formula::True, phi.clone()), Formula::Cmp(..)));
        // False => psi = True
        assert!(formula_implies(Formula::False, phi.clone()).is_true());
        // phi => True = True
        assert!(formula_implies(phi.clone(), Formula::True).is_true());
        // phi => False = ~phi
        assert!(matches!(formula_implies(phi, Formula::False), Formula::Not(_)));
    }

    #[test]
    fn test_formula_iff_simplification() {
        let phi = Formula::cmp(CmpOp::Lt, make_int_expr(1), make_int_expr(2));

        // True <=> psi = psi
        assert!(matches!(formula_iff(Formula::True, phi.clone()), Formula::Cmp(..)));
        // psi <=> True = psi
        assert!(matches!(formula_iff(phi.clone(), Formula::True), Formula::Cmp(..)));
        // False <=> psi = ~psi
        assert!(matches!(formula_iff(Formula::False, phi.clone()), Formula::Not(_)));
        // psi <=> False = ~psi
        assert!(matches!(formula_iff(phi, Formula::False), Formula::Not(_)));
    }

    #[test]
    fn test_formula_and_all() {
        assert!(formula_and_all(std::iter::empty()).is_true());
        assert!(formula_and_all([Formula::True, Formula::True]).is_true());
        assert!(formula_and_all([Formula::True, Formula::False]).is_false());
    }

    #[test]
    fn test_formula_or_all() {
        assert!(formula_or_all(std::iter::empty()).is_false());
        assert!(formula_or_all([Formula::False, Formula::False]).is_false());
        assert!(formula_or_all([Formula::False, Formula::True]).is_true());
    }

    #[test]
    fn test_formula_discriminants() {
        assert_eq!(Formula::True.discriminant(), 0);
        assert_eq!(Formula::False.discriminant(), 1);
        assert_eq!(Formula::Not(Box::new(Formula::True)).discriminant(), 5);
    }

    #[test]
    fn test_is_propositional() {
        let phi = Formula::cmp(CmpOp::Lt, make_int_expr(1), make_int_expr(2));
        assert!(phi.is_propositional());
        assert!(formula_and(phi.clone(), phi.clone()).is_propositional());
        assert!(formula_not(phi.clone()).is_propositional());

        // Quantified formulas are not propositional
        let forall = Formula::forall(
            DepVar(lasso::Spur::default()),
            BrrrType::BOOL,
            phi,
        );
        assert!(!forall.is_propositional());
    }

    #[test]
    fn test_is_closed() {
        // Trivial formulas are closed
        assert!(Formula::True.is_closed());
        assert!(Formula::False.is_closed());

        // Comparisons with literals are closed (no dep vars)
        let cmp = Formula::cmp(CmpOp::Lt, make_int_expr(1), make_int_expr(2));
        assert!(cmp.is_closed());
    }
}
