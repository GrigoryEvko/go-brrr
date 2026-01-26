//! Dependent type constructors
//!
//! Mirrors F* DependentTypes.fsti dep_type definition.
//!
//! Dependent types extend the core type system with:
//! - Pi-types: `Pi(x:A).B` (dependent function types)
//! - Sigma-types: `Sigma(x:A).B` (dependent pair types)
//! - Refinement types: `{x:T | phi}` (types constrained by predicates)
//!
//! # Capture-Avoiding Substitution
//!
//! This module re-exports capture-avoiding substitution operations from
//! `crate::verification::subst`. These operations implement the F* specification
//! in DependentTypes.fst (lines 527-680):
//!
//! - [`is_free_in_expr`] - Check if a variable is free in an expression
//! - [`find_fresh_var`] - Generate a fresh variable avoiding a set
//! - [`alpha_rename_dep_type`] - Alpha-rename bound variables in a dependent type
//! - [`subst_dep_type`] - Capture-avoiding substitution in dependent types
//!
//! # Example: Capture-Avoiding Substitution
//!
//! ```ignore
//! use brrr_repr::types::dependent::{subst_dep_type, is_free_in_expr};
//!
//! // Substitution under Pi-type with potential capture:
//! // [y/x](Pi(y:Int).x + y) must become Pi(z:Int).y + z (not Pi(y:Int).y + y)
//! let result = subst_dep_type(x, &y_expr, &pi_type, &interner);
//! ```

use std::collections::HashSet;

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::{BrrrType, TypeVar};
use crate::expr::Expr;

// Re-export capture-avoiding substitution functions from verification::subst
// These implement F* DependentTypes.fst lines 527-680
pub use crate::verification::subst::{
    // Free variable checking (F* is_free_in_expr)
    is_free_in_expr,
    // Fresh variable generation (F* find_fresh_var)
    fresh_var as find_fresh_var,
    fresh_var_with_base,
    // Free variable collection
    free_vars_expr,
    free_vars_formula,
    free_vars_dep_type,
    // Alpha-renaming (F* alpha_rename_dep_type)
    alpha_rename_dep_type,
    alpha_rename_formula,
    // Capture-avoiding substitution (F* subst_dep_type)
    subst_dep_type,
    subst_formula,
    subst_expr,
    // Alpha-equivalence checking
    dep_type_alpha_eq,
    formula_alpha_eq,
};

/// Dependent variable identifier (interned string)
/// Corresponds to F* `type dep_var = string`
pub type DepVar = Spur;

/// Comparison operator for formulas
/// Maps to F* cmp_op
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CmpOp {
    /// Equality: `=`
    Eq,
    /// Inequality: `!=`
    Ne,
    /// Less than: `<`
    Lt,
    /// Less than or equal: `<=`
    Le,
    /// Greater than: `>`
    Gt,
    /// Greater than or equal: `>=`
    Ge,
}

/// Logical formula (refinement predicates)
///
/// Formulas represent logical assertions over terms. They are used in:
/// - Refinement types: `{x: t | phi(x)}`
/// - Pre/postconditions: `requires P`, `ensures Q`
/// - Loop invariants: `while c invariant I { ... }`
///
/// Maps to F* formula type in DependentTypes.fsti
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Formula {
    /// Boolean constant `true`
    True,

    /// Boolean constant `false`
    False,

    /// Comparison: `e1 op e2`
    Cmp(CmpOp, Box<Expr>, Box<Expr>),

    /// Conjunction: `phi1 /\ phi2`
    And(Box<Formula>, Box<Formula>),

    /// Disjunction: `phi1 \/ phi2`
    Or(Box<Formula>, Box<Formula>),

    /// Negation: `~phi`
    Not(Box<Formula>),

    /// Implication: `phi => psi`
    Impl(Box<Formula>, Box<Formula>),

    /// Biconditional: `phi <=> psi`
    Iff(Box<Formula>, Box<Formula>),

    /// Universal quantifier: `forall x:T. phi`
    Forall {
        var: DepVar,
        ty: BrrrType,
        body: Box<Formula>,
    },

    /// Existential quantifier: `exists x:T. phi`
    Exists {
        var: DepVar,
        ty: BrrrType,
        body: Box<Formula>,
    },

    /// Predicate application: `P(e)`
    Pred(Spur, Box<Expr>),

    /// Expression coerced to formula (for boolean expressions)
    Expr(Box<Expr>),
}

impl Formula {
    /// Create a conjunction of two formulas
    pub fn and(lhs: Formula, rhs: Formula) -> Self {
        Self::And(Box::new(lhs), Box::new(rhs))
    }

    /// Create a disjunction of two formulas
    pub fn or(lhs: Formula, rhs: Formula) -> Self {
        Self::Or(Box::new(lhs), Box::new(rhs))
    }

    /// Create an implication
    pub fn implies(premise: Formula, conclusion: Formula) -> Self {
        Self::Impl(Box::new(premise), Box::new(conclusion))
    }

    /// Create a negation
    pub fn not(inner: Formula) -> Self {
        Self::Not(Box::new(inner))
    }

    /// Create an equality comparison
    pub fn eq(lhs: Expr, rhs: Expr) -> Self {
        Self::Cmp(CmpOp::Eq, Box::new(lhs), Box::new(rhs))
    }

    /// Create a less-than comparison
    pub fn lt(lhs: Expr, rhs: Expr) -> Self {
        Self::Cmp(CmpOp::Lt, Box::new(lhs), Box::new(rhs))
    }

    /// Create a less-than-or-equal comparison
    pub fn le(lhs: Expr, rhs: Expr) -> Self {
        Self::Cmp(CmpOp::Le, Box::new(lhs), Box::new(rhs))
    }

    /// Create a greater-than comparison
    pub fn gt(lhs: Expr, rhs: Expr) -> Self {
        Self::Cmp(CmpOp::Gt, Box::new(lhs), Box::new(rhs))
    }

    /// Create a greater-than-or-equal comparison
    pub fn ge(lhs: Expr, rhs: Expr) -> Self {
        Self::Cmp(CmpOp::Ge, Box::new(lhs), Box::new(rhs))
    }

    /// Check if formula is trivially true
    pub const fn is_true(&self) -> bool {
        matches!(self, Self::True)
    }

    /// Check if formula is trivially false
    pub const fn is_false(&self) -> bool {
        matches!(self, Self::False)
    }

    /// Get the discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::True => 0,
            Self::False => 1,
            Self::Cmp(_, _, _) => 2,
            Self::And(_, _) => 3,
            Self::Or(_, _) => 4,
            Self::Not(_) => 5,
            Self::Impl(_, _) => 6,
            Self::Iff(_, _) => 7,
            Self::Forall { .. } => 8,
            Self::Exists { .. } => 9,
            Self::Pred(_, _) => 10,
            Self::Expr(_) => 11,
        }
    }

    /// Collect free dependent variables in this formula
    pub fn free_dep_vars(&self) -> HashSet<DepVar> {
        let mut vars = HashSet::new();
        self.collect_free_dep_vars(&mut vars, &HashSet::new());
        vars
    }

    /// Helper to collect free vars with bound var tracking
    fn collect_free_dep_vars(&self, free: &mut HashSet<DepVar>, bound: &HashSet<DepVar>) {
        match self {
            Self::True | Self::False => {}
            Self::Cmp(_, e1, e2) => {
                collect_expr_dep_vars(e1.as_ref(), free, bound);
                collect_expr_dep_vars(e2.as_ref(), free, bound);
            }
            Self::And(lhs, rhs)
            | Self::Or(lhs, rhs)
            | Self::Impl(lhs, rhs)
            | Self::Iff(lhs, rhs) => {
                lhs.collect_free_dep_vars(free, bound);
                rhs.collect_free_dep_vars(free, bound);
            }
            Self::Not(inner) => {
                inner.collect_free_dep_vars(free, bound);
            }
            Self::Forall { var, body, .. } | Self::Exists { var, body, .. } => {
                let mut new_bound = bound.clone();
                new_bound.insert(*var);
                body.collect_free_dep_vars(free, &new_bound);
            }
            Self::Pred(_, e) | Self::Expr(e) => {
                collect_expr_dep_vars(e.as_ref(), free, bound);
            }
        }
    }
}

impl Default for Formula {
    fn default() -> Self {
        Self::True
    }
}

/// Dependent type - extends base types with Pi, Sigma, Refinement
///
/// Maps to F* dep_type in DependentTypes.fsti:
/// ```fstar
/// noeq type dep_type =
///   | DBase      : brrr_type -> dep_type
///   | DPi        : dep_var -> dep_type -> dep_type -> dep_type
///   | DSigma     : dep_var -> dep_type -> dep_type -> dep_type
///   | DRefinement : dep_var -> dep_type -> formula -> dep_type
///   | DApp       : dep_type -> expr -> dep_type
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DepType {
    /// Lift base type: embed simple types into dependent types
    Base(BrrrType),

    /// Pi-type: dependent function type `Pi(x:A).B`
    /// When `x` does not occur in `B`, this is equivalent to `A -> B`
    Pi {
        /// Bound variable
        var: DepVar,
        /// Domain type
        domain: Box<DepType>,
        /// Codomain type (may depend on `var`)
        codomain: Box<DepType>,
    },

    /// Sigma-type: dependent pair type `Sigma(x:A).B`
    /// When `x` does not occur in `B`, this is equivalent to `A * B`
    Sigma {
        /// Bound variable
        var: DepVar,
        /// First component type
        fst: Box<DepType>,
        /// Second component type (may depend on `var`)
        snd: Box<DepType>,
    },

    /// Refinement type: `{x:T | phi}`
    /// Values of type `T` that satisfy predicate `phi`
    Refinement {
        /// Bound variable
        var: DepVar,
        /// Base type
        base: Box<DepType>,
        /// Refinement predicate
        predicate: Formula,
    },

    /// Type application (for higher-kinded dependent types)
    App(Box<DepType>, Box<Expr>),
}

impl DepType {
    /// Check if this is a simple (non-dependent) type
    ///
    /// Returns `true` only for `DBase` variants - all other constructors
    /// introduce dependent structure.
    pub const fn is_simple(&self) -> bool {
        matches!(self, Self::Base(_))
    }

    /// Extract the underlying simple type if this is a `DBase`
    ///
    /// Returns `None` for Pi, Sigma, Refinement, or App.
    pub fn to_simple(&self) -> Option<&BrrrType> {
        match self {
            Self::Base(ty) => Some(ty),
            _ => None,
        }
    }

    /// Extract the underlying simple type, consuming self
    pub fn into_simple(self) -> Option<BrrrType> {
        match self {
            Self::Base(ty) => Some(ty),
            _ => None,
        }
    }

    /// Collect free type variables in this dependent type
    ///
    /// Type variables are different from dependent variables:
    /// - TypeVar: polymorphic type parameters (e.g., `'a` in `List<'a>`)
    /// - DepVar: term-level variables that types depend on (e.g., `n` in `Vec<T, n>`)
    pub fn free_type_vars(&self) -> HashSet<TypeVar> {
        let mut vars = HashSet::new();
        self.collect_free_type_vars(&mut vars);
        vars
    }

    /// Helper to collect type vars recursively
    fn collect_free_type_vars(&self, vars: &mut HashSet<TypeVar>) {
        match self {
            Self::Base(ty) => {
                collect_type_vars_from_brrr_type(ty, vars);
            }
            Self::Pi { domain, codomain, .. } => {
                domain.collect_free_type_vars(vars);
                codomain.collect_free_type_vars(vars);
            }
            Self::Sigma { fst, snd, .. } => {
                fst.collect_free_type_vars(vars);
                snd.collect_free_type_vars(vars);
            }
            Self::Refinement { base, .. } => {
                base.collect_free_type_vars(vars);
            }
            Self::App(ty, _) => {
                ty.collect_free_type_vars(vars);
            }
        }
    }

    /// Collect free dependent variables in this type
    ///
    /// Dependent variables are term-level variables that appear in types.
    /// For example, in `{x:Int | x > 0}`, `x` is a dependent variable.
    pub fn free_dep_vars(&self) -> HashSet<DepVar> {
        let mut vars = HashSet::new();
        self.collect_free_dep_vars(&mut vars, &HashSet::new());
        vars
    }

    /// Helper to collect dep vars with bound tracking
    fn collect_free_dep_vars(&self, free: &mut HashSet<DepVar>, bound: &HashSet<DepVar>) {
        match self {
            Self::Base(_) => {
                // Base types don't contain dependent variables
            }
            Self::Pi { var, domain, codomain } => {
                domain.collect_free_dep_vars(free, bound);
                let mut new_bound = bound.clone();
                new_bound.insert(*var);
                codomain.collect_free_dep_vars(free, &new_bound);
            }
            Self::Sigma { var, fst, snd } => {
                fst.collect_free_dep_vars(free, bound);
                let mut new_bound = bound.clone();
                new_bound.insert(*var);
                snd.collect_free_dep_vars(free, &new_bound);
            }
            Self::Refinement { var, base, predicate } => {
                base.collect_free_dep_vars(free, bound);
                let mut new_bound = bound.clone();
                new_bound.insert(*var);
                predicate.collect_free_dep_vars(free, &new_bound);
            }
            Self::App(ty, expr) => {
                ty.collect_free_dep_vars(free, bound);
                collect_expr_dep_vars(expr.as_ref(), free, bound);
            }
        }
    }

    /// Create a simple arrow type (non-dependent function)
    /// `t1 -> t2` is sugar for `Pi(_:t1).t2` where `_` doesn't occur in `t2`
    pub fn arrow(domain: DepType, codomain: DepType, fresh_var: DepVar) -> Self {
        Self::Pi {
            var: fresh_var,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// Create a simple pair type (non-dependent product)
    /// `t1 * t2` is sugar for `Sigma(_:t1).t2` where `_` doesn't occur in `t2`
    pub fn pair(fst: DepType, snd: DepType, fresh_var: DepVar) -> Self {
        Self::Sigma {
            var: fresh_var,
            fst: Box::new(fst),
            snd: Box::new(snd),
        }
    }

    /// Lift a base type to dependent type
    pub fn base(ty: BrrrType) -> Self {
        Self::Base(ty)
    }

    /// Create a refinement type
    pub fn refinement(var: DepVar, base: DepType, predicate: Formula) -> Self {
        Self::Refinement {
            var,
            base: Box::new(base),
            predicate,
        }
    }

    /// Get the discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Base(_) => 0,
            Self::Pi { .. } => 1,
            Self::Sigma { .. } => 2,
            Self::Refinement { .. } => 3,
            Self::App(_, _) => 4,
        }
    }

    /// Check if this is a Pi-type
    pub const fn is_pi(&self) -> bool {
        matches!(self, Self::Pi { .. })
    }

    /// Check if this is a Sigma-type
    pub const fn is_sigma(&self) -> bool {
        matches!(self, Self::Sigma { .. })
    }

    /// Check if this is a refinement type
    pub const fn is_refinement(&self) -> bool {
        matches!(self, Self::Refinement { .. })
    }

    /// Extract the base type from a refinement, if applicable
    pub fn refinement_base(&self) -> Option<&DepType> {
        match self {
            Self::Refinement { base, .. } => Some(base.as_ref()),
            _ => None,
        }
    }

    /// Extract the predicate from a refinement, if applicable
    pub fn refinement_pred(&self) -> Option<&Formula> {
        match self {
            Self::Refinement { predicate, .. } => Some(predicate),
            _ => None,
        }
    }
}

impl Default for DepType {
    fn default() -> Self {
        Self::Base(BrrrType::UNIT)
    }
}

impl From<BrrrType> for DepType {
    fn from(ty: BrrrType) -> Self {
        Self::Base(ty)
    }
}

/// Collect type variables from a BrrrType
fn collect_type_vars_from_brrr_type(ty: &BrrrType, vars: &mut HashSet<TypeVar>) {
    match ty {
        BrrrType::Var(v) => {
            vars.insert(*v);
        }
        BrrrType::Wrap(_, inner) | BrrrType::SizedArray(_, inner) | BrrrType::Modal(_, inner) => {
            collect_type_vars_from_brrr_type(inner, vars);
        }
        BrrrType::Result(ok, err) => {
            collect_type_vars_from_brrr_type(ok, vars);
            collect_type_vars_from_brrr_type(err, vars);
        }
        BrrrType::Tuple(elems) => {
            for elem in elems {
                collect_type_vars_from_brrr_type(elem, vars);
            }
        }
        BrrrType::Func(f) => {
            for param in &f.params {
                collect_type_vars_from_brrr_type(&param.ty, vars);
            }
            collect_type_vars_from_brrr_type(&f.return_type, vars);
        }
        BrrrType::App(base, args) => {
            collect_type_vars_from_brrr_type(base, vars);
            for arg in args {
                collect_type_vars_from_brrr_type(arg, vars);
            }
        }
        BrrrType::Struct(s) => {
            for field in &s.fields {
                collect_type_vars_from_brrr_type(&field.ty, vars);
            }
        }
        BrrrType::Enum(e) => {
            for variant in &e.variants {
                for field_ty in &variant.fields {
                    collect_type_vars_from_brrr_type(field_ty, vars);
                }
            }
        }
        BrrrType::Interface(iface) => {
            // Collect type vars from method signatures
            for method in &iface.methods {
                for param in &method.params {
                    collect_type_vars_from_brrr_type(&param.ty, vars);
                }
                collect_type_vars_from_brrr_type(&method.return_type, vars);
            }
        }
        // Leaf types with no type variables
        BrrrType::Prim(_) | BrrrType::Numeric(_) | BrrrType::Named(_) => {}
    }
}

/// Collect dependent variables from an expression
/// This is a stub that works with the current expr structure
fn collect_expr_dep_vars(expr: &Expr, free: &mut HashSet<DepVar>, bound: &HashSet<DepVar>) {
    use crate::expr::Expr_;

    match &expr.value {
        Expr_::Var(v) => {
            if !bound.contains(v) {
                free.insert(*v);
            }
        }
        Expr_::Unary(_, e) | Expr_::Deref(e) | Expr_::Borrow(e) | Expr_::BorrowMut(e)
        | Expr_::Move(e) | Expr_::Drop(e) | Expr_::Throw(e) | Expr_::Await(e)
        | Expr_::Yield(e) | Expr_::Async(e) | Expr_::Spawn(e) | Expr_::Box(e)
        | Expr_::Unsafe(e) => {
            collect_expr_dep_vars(e.as_ref(), free, bound);
        }
        Expr_::Binary(_, e1, e2) | Expr_::Index(e1, e2) | Expr_::Assign(e1, e2)
        | Expr_::Seq(e1, e2) => {
            collect_expr_dep_vars(e1.as_ref(), free, bound);
            collect_expr_dep_vars(e2.as_ref(), free, bound);
        }
        Expr_::Call(callee, args) => {
            collect_expr_dep_vars(callee.as_ref(), free, bound);
            for arg in args {
                collect_expr_dep_vars(arg, free, bound);
            }
        }
        Expr_::MethodCall(recv, _, args) => {
            collect_expr_dep_vars(recv.as_ref(), free, bound);
            for arg in args {
                collect_expr_dep_vars(arg, free, bound);
            }
        }
        Expr_::Tuple(elems) | Expr_::Array(elems) | Expr_::Block(elems) => {
            for elem in elems {
                collect_expr_dep_vars(elem, free, bound);
            }
        }
        Expr_::Field(e, _) | Expr_::TupleProj(e, _) => {
            collect_expr_dep_vars(e.as_ref(), free, bound);
        }
        Expr_::If(cond, then_e, else_e) => {
            collect_expr_dep_vars(cond.as_ref(), free, bound);
            collect_expr_dep_vars(then_e.as_ref(), free, bound);
            collect_expr_dep_vars(else_e.as_ref(), free, bound);
        }
        Expr_::Let { pattern: _, init, body, .. } => {
            collect_expr_dep_vars(init.as_ref(), free, bound);
            // Note: proper handling would track pattern bindings
            collect_expr_dep_vars(body.as_ref(), free, bound);
        }
        Expr_::LetMut { var, init, body, .. } => {
            collect_expr_dep_vars(init.as_ref(), free, bound);
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_expr_dep_vars(body.as_ref(), free, &new_bound);
        }
        Expr_::Lambda { params, body } => {
            let mut new_bound = bound.clone();
            for (v, _) in params {
                new_bound.insert(*v);
            }
            collect_expr_dep_vars(body.as_ref(), free, &new_bound);
        }
        Expr_::Closure { params, body, captures } => {
            for v in captures {
                if !bound.contains(v) {
                    free.insert(*v);
                }
            }
            let mut new_bound = bound.clone();
            for (v, _) in params {
                new_bound.insert(*v);
            }
            collect_expr_dep_vars(body.as_ref(), free, &new_bound);
        }
        Expr_::Return(opt_e) | Expr_::Break { value: opt_e, .. } => {
            if let Some(e) = opt_e {
                collect_expr_dep_vars(e.as_ref(), free, bound);
            }
        }
        Expr_::As(e, _) | Expr_::Is(e, _) => {
            collect_expr_dep_vars(e.as_ref(), free, bound);
        }
        // Leaf expressions
        Expr_::Lit(_) | Expr_::Global(_) | Expr_::Continue { .. } | Expr_::Hole
        | Expr_::Error(_) | Expr_::Sizeof(_) | Expr_::Alignof(_) => {}
        // Complex cases - simplified handling
        Expr_::Match(scrutinee, _arms) => {
            collect_expr_dep_vars(scrutinee.as_ref(), free, bound);
            // Arms have patterns that bind - proper handling would track those
        }
        Expr_::Loop { body, .. } => {
            collect_expr_dep_vars(body.as_ref(), free, bound);
        }
        Expr_::While { cond, body, .. } => {
            collect_expr_dep_vars(cond.as_ref(), free, bound);
            collect_expr_dep_vars(body.as_ref(), free, bound);
        }
        Expr_::Reset { body, .. } => {
            collect_expr_dep_vars(body.as_ref(), free, bound);
        }
        Expr_::For { var, iter, body, .. } => {
            collect_expr_dep_vars(iter.as_ref(), free, bound);
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_expr_dep_vars(body.as_ref(), free, &new_bound);
        }
        Expr_::Struct { fields, .. } => {
            for (_, e) in fields {
                collect_expr_dep_vars(e, free, bound);
            }
        }
        Expr_::Variant { fields, .. } => {
            for e in fields {
                collect_expr_dep_vars(e, free, bound);
            }
        }
        Expr_::Try { body, finally, .. } => {
            collect_expr_dep_vars(body.as_ref(), free, bound);
            if let Some(f) = finally {
                collect_expr_dep_vars(f.as_ref(), free, bound);
            }
        }
        Expr_::Handle(e, _) => {
            collect_expr_dep_vars(e.as_ref(), free, bound);
        }
        Expr_::Perform(_, args) => {
            for arg in args {
                collect_expr_dep_vars(arg, free, bound);
            }
        }
        Expr_::Resume { value, .. } => {
            collect_expr_dep_vars(value.as_ref(), free, bound);
        }
        Expr_::Shift { var, body, .. } => {
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_expr_dep_vars(body.as_ref(), free, &new_bound);
        }
        Expr_::GradualCast { expr, .. } => {
            collect_expr_dep_vars(expr.as_ref(), free, bound);
        }
        // Control flow labels - Goto has no expressions, Labeled wraps body
        Expr_::Goto { .. } => {}
        Expr_::Labeled { body, .. } => {
            collect_expr_dep_vars(body.as_ref(), free, bound);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::ThreadedRodeo;

    #[test]
    fn test_dep_type_is_simple() {
        let base = DepType::Base(BrrrType::BOOL);
        assert!(base.is_simple());
        assert!(base.to_simple().is_some());

        // Create a Pi type to test non-simple case
        let rodeo = ThreadedRodeo::new();
        let x = rodeo.get_or_intern("x");
        let pi = DepType::Pi {
            var: x,
            domain: Box::new(DepType::Base(BrrrType::BOOL)),
            codomain: Box::new(DepType::Base(BrrrType::BOOL)),
        };
        assert!(!pi.is_simple());
        assert!(pi.to_simple().is_none());
    }

    #[test]
    fn test_dep_type_discriminants() {
        assert_eq!(DepType::Base(BrrrType::UNIT).discriminant(), 0);

        let rodeo = ThreadedRodeo::new();
        let x = rodeo.get_or_intern("x");

        let pi = DepType::Pi {
            var: x,
            domain: Box::new(DepType::Base(BrrrType::BOOL)),
            codomain: Box::new(DepType::Base(BrrrType::BOOL)),
        };
        assert_eq!(pi.discriminant(), 1);

        let sigma = DepType::Sigma {
            var: x,
            fst: Box::new(DepType::Base(BrrrType::BOOL)),
            snd: Box::new(DepType::Base(BrrrType::BOOL)),
        };
        assert_eq!(sigma.discriminant(), 2);

        let refinement = DepType::Refinement {
            var: x,
            base: Box::new(DepType::Base(BrrrType::BOOL)),
            predicate: Formula::True,
        };
        assert_eq!(refinement.discriminant(), 3);
    }

    #[test]
    fn test_formula_constructors() {
        let t = Formula::True;
        let f = Formula::False;

        assert!(t.is_true());
        assert!(!t.is_false());
        assert!(f.is_false());
        assert!(!f.is_true());

        let and = Formula::and(t.clone(), f.clone());
        assert_eq!(and.discriminant(), 3);

        let or = Formula::or(t.clone(), f.clone());
        assert_eq!(or.discriminant(), 4);

        let not = Formula::not(t);
        assert_eq!(not.discriminant(), 5);
    }

    #[test]
    fn test_from_brrr_type() {
        let bool_ty = BrrrType::BOOL;
        let dep: DepType = bool_ty.clone().into();
        assert!(dep.is_simple());
        assert_eq!(dep.to_simple(), Some(&bool_ty));
    }

    #[test]
    fn test_refinement_accessors() {
        let rodeo = ThreadedRodeo::new();
        let x = rodeo.get_or_intern("x");

        let base = DepType::Base(BrrrType::BOOL);
        let pred = Formula::True;

        let refinement = DepType::refinement(x, base.clone(), pred.clone());

        assert!(refinement.is_refinement());
        assert!(refinement.refinement_base().is_some());
        assert!(refinement.refinement_pred().is_some());
        assert_eq!(refinement.refinement_pred(), Some(&pred));
    }
}
