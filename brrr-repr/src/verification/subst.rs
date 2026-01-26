//! Capture-avoiding substitution for dependent types
//!
//! Mirrors F* DependentTypes.fst (lines 275-569) for:
//! - Expression substitution in expressions, formulas, and dependent types
//! - Alpha-renaming of bound variables
//! - Alpha-equivalence checking
//!
//! Capture-avoiding substitution prevents variable capture when substituting
//! under binders. For example:
//!   `[y/x](forall y. x + y)` must become `forall z. y + z` (rename bound y to z)
//!   NOT `forall y. y + y` (incorrect capture)

use std::collections::HashSet;
use std::sync::atomic::{AtomicU64, Ordering};

use lasso::ThreadedRodeo;

use crate::expr::{Expr, Expr_, WithLoc};
use crate::types::{DepType, DepVar, Formula};

// Used in tests
#[cfg(test)]
use crate::types::{BrrrType, CmpOp, IntType, NumericType};

/// Global counter for fresh variable generation
/// Used when no interner is available for generating truly unique names
static FRESH_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Generate a fresh variable that does not appear in the avoid set
///
/// Uses the provided interner to create a new interned string.
/// The fresh variable is named `_fresh_N` where N is a counter.
///
/// # Arguments
/// * `avoid` - Set of variables to avoid
/// * `interner` - Interner for creating new Spur values
///
/// # Returns
/// A fresh DepVar not in the avoid set
pub fn fresh_var(avoid: &HashSet<DepVar>, interner: &ThreadedRodeo) -> DepVar {
    loop {
        let counter = FRESH_COUNTER.fetch_add(1, Ordering::Relaxed);
        let name = format!("_fresh_{}", counter);
        let var = interner.get_or_intern(&name);
        if !avoid.contains(&var) {
            return var;
        }
    }
}

/// Generate a fresh variable with a specific base name
///
/// Appends `__cap_N` to the base name to avoid capturing.
///
/// # Arguments
/// * `base` - Base name for the fresh variable
/// * `avoid` - Set of variables to avoid
/// * `interner` - Interner for creating new Spur values
pub fn fresh_var_with_base(base: &str, avoid: &HashSet<DepVar>, interner: &ThreadedRodeo) -> DepVar {
    for counter in 0..1000 {
        let name = format!("{}__cap_{}", base, counter);
        let var = interner.get_or_intern(&name);
        if !avoid.contains(&var) {
            return var;
        }
    }
    // Fallback with global counter
    let counter = FRESH_COUNTER.fetch_add(1, Ordering::Relaxed);
    let name = format!("{}__cap_overflow_{}", base, counter);
    interner.get_or_intern(&name)
}

// ============================================================================
// FREE VARIABLES
// ============================================================================

/// Collect free variables in an expression
///
/// Returns all variable references that are not bound by an enclosing
/// let, lambda, for, or other binding form.
pub fn free_vars_expr(e: &Expr) -> HashSet<DepVar> {
    let mut vars = HashSet::new();
    collect_free_vars_expr(e, &HashSet::new(), &mut vars);
    vars
}

/// Helper to collect free vars with bound variable tracking
fn collect_free_vars_expr(e: &Expr, bound: &HashSet<DepVar>, free: &mut HashSet<DepVar>) {
    match &e.value {
        Expr_::Var(v) => {
            if !bound.contains(v) {
                free.insert(*v);
            }
        }
        Expr_::Lit(_) | Expr_::Global(_) | Expr_::Continue { .. } | Expr_::Hole
        | Expr_::Error(_) | Expr_::Sizeof(_) | Expr_::Alignof(_) => {}

        Expr_::Unary(_, inner)
        | Expr_::Deref(inner)
        | Expr_::Borrow(inner)
        | Expr_::BorrowMut(inner)
        | Expr_::Move(inner)
        | Expr_::Drop(inner)
        | Expr_::Throw(inner)
        | Expr_::Await(inner)
        | Expr_::Yield(inner)
        | Expr_::Async(inner)
        | Expr_::Spawn(inner)
        | Expr_::Box(inner)
        | Expr_::Unsafe(inner) => {
            collect_free_vars_expr(inner, bound, free);
        }

        Expr_::Binary(_, e1, e2)
        | Expr_::Index(e1, e2)
        | Expr_::Assign(e1, e2)
        | Expr_::Seq(e1, e2) => {
            collect_free_vars_expr(e1, bound, free);
            collect_free_vars_expr(e2, bound, free);
        }

        Expr_::If(cond, then_e, else_e) => {
            collect_free_vars_expr(cond, bound, free);
            collect_free_vars_expr(then_e, bound, free);
            collect_free_vars_expr(else_e, bound, free);
        }

        Expr_::Call(callee, args) => {
            collect_free_vars_expr(callee, bound, free);
            for arg in args {
                collect_free_vars_expr(arg, bound, free);
            }
        }

        Expr_::MethodCall(recv, _, args) => {
            collect_free_vars_expr(recv, bound, free);
            for arg in args {
                collect_free_vars_expr(arg, bound, free);
            }
        }

        Expr_::Tuple(elems) | Expr_::Array(elems) | Expr_::Block(elems) => {
            for elem in elems {
                collect_free_vars_expr(elem, bound, free);
            }
        }

        Expr_::Struct { fields, .. } => {
            for (_, e) in fields {
                collect_free_vars_expr(e, bound, free);
            }
        }

        Expr_::Variant { fields, .. } => {
            for e in fields {
                collect_free_vars_expr(e, bound, free);
            }
        }

        Expr_::Field(e, _) | Expr_::TupleProj(e, _) => {
            collect_free_vars_expr(e, bound, free);
        }

        Expr_::As(e, _) | Expr_::Is(e, _) => {
            collect_free_vars_expr(e, bound, free);
        }

        Expr_::Return(opt_e) | Expr_::Break { value: opt_e, .. } => {
            if let Some(e) = opt_e {
                collect_free_vars_expr(e, bound, free);
            }
        }

        // Binding forms
        Expr_::Let { pattern: _, init, body, .. } => {
            // Note: proper handling would extract variables from pattern
            collect_free_vars_expr(init, bound, free);
            collect_free_vars_expr(body, bound, free);
        }

        Expr_::LetMut { var, init, body, .. } => {
            collect_free_vars_expr(init, bound, free);
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_free_vars_expr(body, &new_bound, free);
        }

        Expr_::Lambda { params, body } => {
            let mut new_bound = bound.clone();
            for (v, _) in params {
                new_bound.insert(*v);
            }
            collect_free_vars_expr(body, &new_bound, free);
        }

        Expr_::Closure { params, captures, body } => {
            for v in captures {
                if !bound.contains(v) {
                    free.insert(*v);
                }
            }
            let mut new_bound = bound.clone();
            for (v, _) in params {
                new_bound.insert(*v);
            }
            collect_free_vars_expr(body, &new_bound, free);
        }

        Expr_::For { var, iter, body, .. } => {
            collect_free_vars_expr(iter, bound, free);
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_free_vars_expr(body, &new_bound, free);
        }

        Expr_::Shift { var, body, .. } => {
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_free_vars_expr(body, &new_bound, free);
        }

        Expr_::Loop { body, .. } => {
            collect_free_vars_expr(body, bound, free);
        }

        Expr_::While { cond, body, .. } => {
            collect_free_vars_expr(cond, bound, free);
            collect_free_vars_expr(body, bound, free);
        }

        Expr_::Reset { body, .. } => {
            collect_free_vars_expr(body, bound, free);
        }

        Expr_::Match(scrutinee, _arms) => {
            collect_free_vars_expr(scrutinee, bound, free);
            // Note: arms have pattern bindings - proper handling would track those
        }

        Expr_::Try { body, finally, .. } => {
            collect_free_vars_expr(body, bound, free);
            if let Some(f) = finally {
                collect_free_vars_expr(f, bound, free);
            }
        }

        Expr_::Handle(e, _) => {
            collect_free_vars_expr(e, bound, free);
        }

        Expr_::Perform(_, args) => {
            for arg in args {
                collect_free_vars_expr(arg, bound, free);
            }
        }

        Expr_::Resume { value, .. } => {
            collect_free_vars_expr(value, bound, free);
        }

        Expr_::GradualCast { expr, .. } => {
            collect_free_vars_expr(expr, bound, free);
        }

        // Control flow labels
        Expr_::Goto { .. } => {}
        Expr_::Labeled { body, .. } => {
            collect_free_vars_expr(body, bound, free);
        }
    }
}

/// Check if a variable is free in an expression
#[inline]
pub fn is_free_in_expr(var: DepVar, e: &Expr) -> bool {
    free_vars_expr(e).contains(&var)
}

/// Collect free variables in a formula
pub fn free_vars_formula(f: &Formula) -> HashSet<DepVar> {
    let mut vars = HashSet::new();
    collect_free_vars_formula(f, &HashSet::new(), &mut vars);
    vars
}

fn collect_free_vars_formula(f: &Formula, bound: &HashSet<DepVar>, free: &mut HashSet<DepVar>) {
    match f {
        Formula::True | Formula::False => {}

        Formula::Cmp(_, e1, e2) => {
            collect_free_vars_expr(e1, bound, free);
            collect_free_vars_expr(e2, bound, free);
        }

        Formula::And(lhs, rhs)
        | Formula::Or(lhs, rhs)
        | Formula::Impl(lhs, rhs)
        | Formula::Iff(lhs, rhs) => {
            collect_free_vars_formula(lhs, bound, free);
            collect_free_vars_formula(rhs, bound, free);
        }

        Formula::Not(inner) => {
            collect_free_vars_formula(inner, bound, free);
        }

        Formula::Forall { var, body, .. } | Formula::Exists { var, body, .. } => {
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_free_vars_formula(body, &new_bound, free);
        }

        Formula::Pred(_, e) | Formula::Expr(e) => {
            collect_free_vars_expr(e, bound, free);
        }
    }
}

/// Collect free variables in a dependent type
pub fn free_vars_dep_type(t: &DepType) -> HashSet<DepVar> {
    let mut vars = HashSet::new();
    collect_free_vars_dep_type(t, &HashSet::new(), &mut vars);
    vars
}

fn collect_free_vars_dep_type(t: &DepType, bound: &HashSet<DepVar>, free: &mut HashSet<DepVar>) {
    match t {
        DepType::Base(_) => {}

        DepType::Pi { var, domain, codomain } => {
            collect_free_vars_dep_type(domain, bound, free);
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_free_vars_dep_type(codomain, &new_bound, free);
        }

        DepType::Sigma { var, fst, snd } => {
            collect_free_vars_dep_type(fst, bound, free);
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_free_vars_dep_type(snd, &new_bound, free);
        }

        DepType::Refinement { var, base, predicate } => {
            collect_free_vars_dep_type(base, bound, free);
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_free_vars_formula(predicate, &new_bound, free);
        }

        DepType::App(ty, expr) => {
            collect_free_vars_dep_type(ty, bound, free);
            collect_free_vars_expr(expr, bound, free);
        }
    }
}

// ============================================================================
// EXPRESSION SUBSTITUTION IN EXPRESSIONS
// ============================================================================

/// Substitute expression for variable in an expression (capture-avoiding)
///
/// Computes `[replacement/var]e` - replaces all free occurrences of `var` in `e`
/// with `replacement`, avoiding variable capture under binders.
///
/// # Arguments
/// * `var` - Variable to replace
/// * `replacement` - Expression to substitute
/// * `e` - Target expression
/// * `interner` - Interner for fresh variable generation
pub fn subst_expr(var: DepVar, replacement: &Expr, e: &Expr, interner: &ThreadedRodeo) -> Expr {
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
            Expr_::Unary(*op, Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Deref(inner) => WithLoc::new(
            Expr_::Deref(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Borrow(inner) => WithLoc::new(
            Expr_::Borrow(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::BorrowMut(inner) => WithLoc::new(
            Expr_::BorrowMut(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Move(inner) => WithLoc::new(
            Expr_::Move(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Drop(inner) => WithLoc::new(
            Expr_::Drop(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Throw(inner) => WithLoc::new(
            Expr_::Throw(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Await(inner) => WithLoc::new(
            Expr_::Await(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Yield(inner) => WithLoc::new(
            Expr_::Yield(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Async(inner) => WithLoc::new(
            Expr_::Async(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Spawn(inner) => WithLoc::new(
            Expr_::Spawn(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Box(inner) => WithLoc::new(
            Expr_::Box(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        Expr_::Unsafe(inner) => WithLoc::new(
            Expr_::Unsafe(Box::new(subst_expr(var, replacement, inner, interner))),
            range,
        ),

        // Binary operators
        Expr_::Binary(op, e1, e2) => WithLoc::new(
            Expr_::Binary(
                *op,
                Box::new(subst_expr(var, replacement, e1, interner)),
                Box::new(subst_expr(var, replacement, e2, interner)),
            ),
            range,
        ),

        Expr_::Index(e1, e2) => WithLoc::new(
            Expr_::Index(
                Box::new(subst_expr(var, replacement, e1, interner)),
                Box::new(subst_expr(var, replacement, e2, interner)),
            ),
            range,
        ),

        Expr_::Assign(e1, e2) => WithLoc::new(
            Expr_::Assign(
                Box::new(subst_expr(var, replacement, e1, interner)),
                Box::new(subst_expr(var, replacement, e2, interner)),
            ),
            range,
        ),

        Expr_::Seq(e1, e2) => WithLoc::new(
            Expr_::Seq(
                Box::new(subst_expr(var, replacement, e1, interner)),
                Box::new(subst_expr(var, replacement, e2, interner)),
            ),
            range,
        ),

        // Control flow
        Expr_::If(cond, then_e, else_e) => WithLoc::new(
            Expr_::If(
                Box::new(subst_expr(var, replacement, cond, interner)),
                Box::new(subst_expr(var, replacement, then_e, interner)),
                Box::new(subst_expr(var, replacement, else_e, interner)),
            ),
            range,
        ),

        // Function calls
        Expr_::Call(callee, args) => WithLoc::new(
            Expr_::Call(
                Box::new(subst_expr(var, replacement, callee, interner)),
                args.iter()
                    .map(|a| subst_expr(var, replacement, a, interner))
                    .collect(),
            ),
            range,
        ),

        Expr_::MethodCall(recv, method, args) => WithLoc::new(
            Expr_::MethodCall(
                Box::new(subst_expr(var, replacement, recv, interner)),
                *method,
                args.iter()
                    .map(|a| subst_expr(var, replacement, a, interner))
                    .collect(),
            ),
            range,
        ),

        // Data construction
        Expr_::Tuple(elems) => WithLoc::new(
            Expr_::Tuple(
                elems
                    .iter()
                    .map(|e| subst_expr(var, replacement, e, interner))
                    .collect(),
            ),
            range,
        ),

        Expr_::Array(elems) => WithLoc::new(
            Expr_::Array(
                elems
                    .iter()
                    .map(|e| subst_expr(var, replacement, e, interner))
                    .collect(),
            ),
            range,
        ),

        Expr_::Block(elems) => WithLoc::new(
            Expr_::Block(
                elems
                    .iter()
                    .map(|e| subst_expr(var, replacement, e, interner))
                    .collect(),
            ),
            range,
        ),

        Expr_::Struct { name, fields } => WithLoc::new(
            Expr_::Struct {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(f, e)| (*f, subst_expr(var, replacement, e, interner)))
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
                    .map(|e| subst_expr(var, replacement, e, interner))
                    .collect(),
            },
            range,
        ),

        // Field access
        Expr_::Field(e, f) => WithLoc::new(
            Expr_::Field(Box::new(subst_expr(var, replacement, e, interner)), *f),
            range,
        ),

        Expr_::TupleProj(e, i) => WithLoc::new(
            Expr_::TupleProj(Box::new(subst_expr(var, replacement, e, interner)), *i),
            range,
        ),

        // Type operations
        Expr_::As(e, ty) => WithLoc::new(
            Expr_::As(Box::new(subst_expr(var, replacement, e, interner)), ty.clone()),
            range,
        ),

        Expr_::Is(e, ty) => WithLoc::new(
            Expr_::Is(Box::new(subst_expr(var, replacement, e, interner)), ty.clone()),
            range,
        ),

        // Control flow with optional values
        Expr_::Return(opt_e) => WithLoc::new(
            Expr_::Return(opt_e.as_ref().map(|e| Box::new(subst_expr(var, replacement, e, interner)))),
            range,
        ),

        Expr_::Break { label, value } => WithLoc::new(
            Expr_::Break {
                label: *label,
                value: value.as_ref().map(|e| Box::new(subst_expr(var, replacement, e, interner))),
            },
            range,
        ),

        // Loops
        Expr_::Loop { label, body } => WithLoc::new(
            Expr_::Loop {
                label: *label,
                body: Box::new(subst_expr(var, replacement, body, interner)),
            },
            range,
        ),

        Expr_::While { label, cond, body } => WithLoc::new(
            Expr_::While {
                label: *label,
                cond: Box::new(subst_expr(var, replacement, cond, interner)),
                body: Box::new(subst_expr(var, replacement, body, interner)),
            },
            range,
        ),

        // For loop: CAPTURE-AVOIDING
        Expr_::For {
            label,
            var: loop_var,
            iter,
            body,
        } => {
            let iter_subst = subst_expr(var, replacement, iter, interner);

            if *loop_var == var {
                // loop_var shadows var, no substitution in body
                WithLoc::new(
                    Expr_::For {
                        label: *label,
                        var: *loop_var,
                        iter: Box::new(iter_subst),
                        body: body.clone(),
                    },
                    range,
                )
            } else if is_free_in_expr(*loop_var, replacement) {
                // CAPTURE AVOIDANCE: rename loop_var
                let avoid = {
                    let mut s = free_vars_expr(replacement);
                    s.extend(free_vars_expr(body));
                    s
                };
                let fresh = fresh_var(&avoid, interner);
                let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
                let body_renamed = subst_expr(*loop_var, &var_expr, body, interner);
                let body_final = subst_expr(var, replacement, &body_renamed, interner);

                WithLoc::new(
                    Expr_::For {
                        label: *label,
                        var: fresh,
                        iter: Box::new(iter_subst),
                        body: Box::new(body_final),
                    },
                    range,
                )
            } else {
                WithLoc::new(
                    Expr_::For {
                        label: *label,
                        var: *loop_var,
                        iter: Box::new(iter_subst),
                        body: Box::new(subst_expr(var, replacement, body, interner)),
                    },
                    range,
                )
            }
        }

        // Let binding: CAPTURE-AVOIDING (simplified - only handles LetMut)
        Expr_::Let {
            pattern,
            ty,
            init,
            body,
        } => {
            // Note: For full capture avoidance we would need to extract variables from pattern
            // For now, substitute in both init and body
            WithLoc::new(
                Expr_::Let {
                    pattern: pattern.clone(),
                    ty: ty.clone(),
                    init: Box::new(subst_expr(var, replacement, init, interner)),
                    body: Box::new(subst_expr(var, replacement, body, interner)),
                },
                range,
            )
        }

        // LetMut: CAPTURE-AVOIDING
        Expr_::LetMut {
            var: bound_var,
            ty,
            init,
            body,
        } => {
            let init_subst = subst_expr(var, replacement, init, interner);

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
            } else if is_free_in_expr(*bound_var, replacement) {
                // CAPTURE AVOIDANCE: rename bound_var
                let avoid = {
                    let mut s = free_vars_expr(replacement);
                    s.extend(free_vars_expr(body));
                    s
                };
                let fresh = fresh_var(&avoid, interner);
                let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
                let body_renamed = subst_expr(*bound_var, &var_expr, body, interner);
                let body_final = subst_expr(var, replacement, &body_renamed, interner);

                WithLoc::new(
                    Expr_::LetMut {
                        var: fresh,
                        ty: ty.clone(),
                        init: Box::new(init_subst),
                        body: Box::new(body_final),
                    },
                    range,
                )
            } else {
                WithLoc::new(
                    Expr_::LetMut {
                        var: *bound_var,
                        ty: ty.clone(),
                        init: Box::new(init_subst),
                        body: Box::new(subst_expr(var, replacement, body, interner)),
                    },
                    range,
                )
            }
        }

        // Lambda: CAPTURE-AVOIDING
        Expr_::Lambda { params, body } => {
            let binds_var = params.iter().any(|(p, _)| *p == var);
            if binds_var {
                // var is shadowed by a parameter
                e.clone()
            } else {
                // Check if any param would capture a variable in replacement
                let captured_param = params.iter().find(|(p, _)| is_free_in_expr(*p, replacement));
                match captured_param {
                    None => WithLoc::new(
                        Expr_::Lambda {
                            params: params.clone(),
                            body: Box::new(subst_expr(var, replacement, body, interner)),
                        },
                        range,
                    ),
                    Some((captured, _)) => {
                        // CAPTURE AVOIDANCE: rename the captured parameter
                        let avoid = {
                            let mut s = free_vars_expr(replacement);
                            s.extend(free_vars_expr(body));
                            s.extend(params.iter().map(|(p, _)| *p));
                            s
                        };
                        let fresh = fresh_var(&avoid, interner);
                        let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
                        let body_renamed = subst_expr(*captured, &var_expr, body, interner);

                        let params_new: Vec<_> = params
                            .iter()
                            .map(|(p, t)| {
                                if *p == *captured {
                                    (fresh, t.clone())
                                } else {
                                    (*p, t.clone())
                                }
                            })
                            .collect();

                        let body_final = subst_expr(var, replacement, &body_renamed, interner);

                        WithLoc::new(
                            Expr_::Lambda {
                                params: params_new,
                                body: Box::new(body_final),
                            },
                            range,
                        )
                    }
                }
            }
        }

        // Closure: CAPTURE-AVOIDING
        Expr_::Closure {
            params,
            captures,
            body,
        } => {
            let binds_var = params.iter().any(|(p, _)| *p == var);
            if binds_var {
                e.clone()
            } else {
                let captured_param = params.iter().find(|(p, _)| is_free_in_expr(*p, replacement));
                match captured_param {
                    None => WithLoc::new(
                        Expr_::Closure {
                            params: params.clone(),
                            captures: captures.clone(),
                            body: Box::new(subst_expr(var, replacement, body, interner)),
                        },
                        range,
                    ),
                    Some((captured, _)) => {
                        let avoid = {
                            let mut s = free_vars_expr(replacement);
                            s.extend(free_vars_expr(body));
                            s.extend(params.iter().map(|(p, _)| *p));
                            s
                        };
                        let fresh = fresh_var(&avoid, interner);
                        let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
                        let body_renamed = subst_expr(*captured, &var_expr, body, interner);

                        let params_new: Vec<_> = params
                            .iter()
                            .map(|(p, t)| {
                                if *p == *captured {
                                    (fresh, t.clone())
                                } else {
                                    (*p, t.clone())
                                }
                            })
                            .collect();

                        let body_final = subst_expr(var, replacement, &body_renamed, interner);

                        WithLoc::new(
                            Expr_::Closure {
                                params: params_new,
                                captures: captures.clone(),
                                body: Box::new(body_final),
                            },
                            range,
                        )
                    }
                }
            }
        }

        // Shift: CAPTURE-AVOIDING
        Expr_::Shift {
            label,
            var: cont_var,
            body,
        } => {
            if *cont_var == var {
                e.clone()
            } else if is_free_in_expr(*cont_var, replacement) {
                let avoid = {
                    let mut s = free_vars_expr(replacement);
                    s.extend(free_vars_expr(body));
                    s
                };
                let fresh = fresh_var(&avoid, interner);
                let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
                let body_renamed = subst_expr(*cont_var, &var_expr, body, interner);
                let body_final = subst_expr(var, replacement, &body_renamed, interner);

                WithLoc::new(
                    Expr_::Shift {
                        label: *label,
                        var: fresh,
                        body: Box::new(body_final),
                    },
                    range,
                )
            } else {
                WithLoc::new(
                    Expr_::Shift {
                        label: *label,
                        var: *cont_var,
                        body: Box::new(subst_expr(var, replacement, body, interner)),
                    },
                    range,
                )
            }
        }

        Expr_::Reset { label, body } => WithLoc::new(
            Expr_::Reset {
                label: *label,
                body: Box::new(subst_expr(var, replacement, body, interner)),
            },
            range,
        ),

        // Complex cases - simplified handling
        Expr_::Match(scrutinee, arms) => WithLoc::new(
            Expr_::Match(
                Box::new(subst_expr(var, replacement, scrutinee, interner)),
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
                body: Box::new(subst_expr(var, replacement, body, interner)),
                catches: catches.clone(),
                finally: finally
                    .as_ref()
                    .map(|f| Box::new(subst_expr(var, replacement, f, interner))),
            },
            range,
        ),

        Expr_::Handle(e, handler) => WithLoc::new(
            Expr_::Handle(
                Box::new(subst_expr(var, replacement, e, interner)),
                handler.clone(),
            ),
            range,
        ),

        Expr_::Perform(op, args) => WithLoc::new(
            Expr_::Perform(
                op.clone(),
                args.iter()
                    .map(|a| subst_expr(var, replacement, a, interner))
                    .collect(),
            ),
            range,
        ),

        Expr_::Resume { var: k, value } => WithLoc::new(
            Expr_::Resume {
                var: *k,
                value: Box::new(subst_expr(var, replacement, value, interner)),
            },
            range,
        ),

        Expr_::GradualCast { expr, from, to, kind, blame } => WithLoc::new(
            Expr_::GradualCast {
                expr: Box::new(subst_expr(var, replacement, expr, interner)),
                from: from.clone(),
                to: to.clone(),
                kind: *kind,
                blame: blame.clone(),
            },
            range,
        ),

        // Control flow labels
        Expr_::Goto { label } => WithLoc::new(Expr_::Goto { label: *label }, range),
        Expr_::Labeled { label, body } => WithLoc::new(
            Expr_::Labeled {
                label: *label,
                body: Box::new(subst_expr(var, replacement, body, interner)),
            },
            range,
        ),
    }
}

// ============================================================================
// EXPRESSION SUBSTITUTION IN FORMULAS
// ============================================================================

/// Substitute expression for variable in a formula (capture-avoiding)
///
/// Computes `[replacement/var]f` - replaces all free occurrences of `var` in `f`
/// with `replacement`, avoiding variable capture under quantifiers.
pub fn subst_formula(
    var: DepVar,
    replacement: &Expr,
    f: &Formula,
    interner: &ThreadedRodeo,
) -> Formula {
    match f {
        Formula::True => Formula::True,
        Formula::False => Formula::False,

        Formula::Cmp(op, e1, e2) => Formula::Cmp(
            *op,
            Box::new(subst_expr(var, replacement, e1, interner)),
            Box::new(subst_expr(var, replacement, e2, interner)),
        ),

        Formula::And(lhs, rhs) => Formula::And(
            Box::new(subst_formula(var, replacement, lhs, interner)),
            Box::new(subst_formula(var, replacement, rhs, interner)),
        ),

        Formula::Or(lhs, rhs) => Formula::Or(
            Box::new(subst_formula(var, replacement, lhs, interner)),
            Box::new(subst_formula(var, replacement, rhs, interner)),
        ),

        Formula::Not(inner) => {
            Formula::Not(Box::new(subst_formula(var, replacement, inner, interner)))
        }

        Formula::Impl(lhs, rhs) => Formula::Impl(
            Box::new(subst_formula(var, replacement, lhs, interner)),
            Box::new(subst_formula(var, replacement, rhs, interner)),
        ),

        Formula::Iff(lhs, rhs) => Formula::Iff(
            Box::new(subst_formula(var, replacement, lhs, interner)),
            Box::new(subst_formula(var, replacement, rhs, interner)),
        ),

        // Forall: CAPTURE-AVOIDING
        Formula::Forall {
            var: bound_var,
            ty,
            body,
        } => {
            if *bound_var == var {
                // bound_var shadows var
                f.clone()
            } else if is_free_in_expr(*bound_var, replacement) {
                // CAPTURE AVOIDANCE
                let avoid = {
                    let mut s = free_vars_expr(replacement);
                    s.extend(free_vars_formula(body));
                    s
                };
                let fresh = fresh_var(&avoid, interner);
                let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
                let body_renamed = subst_formula(*bound_var, &var_expr, body, interner);
                let body_final = subst_formula(var, replacement, &body_renamed, interner);

                Formula::Forall {
                    var: fresh,
                    ty: ty.clone(),
                    body: Box::new(body_final),
                }
            } else {
                Formula::Forall {
                    var: *bound_var,
                    ty: ty.clone(),
                    body: Box::new(subst_formula(var, replacement, body, interner)),
                }
            }
        }

        // Exists: CAPTURE-AVOIDING
        Formula::Exists {
            var: bound_var,
            ty,
            body,
        } => {
            if *bound_var == var {
                f.clone()
            } else if is_free_in_expr(*bound_var, replacement) {
                let avoid = {
                    let mut s = free_vars_expr(replacement);
                    s.extend(free_vars_formula(body));
                    s
                };
                let fresh = fresh_var(&avoid, interner);
                let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
                let body_renamed = subst_formula(*bound_var, &var_expr, body, interner);
                let body_final = subst_formula(var, replacement, &body_renamed, interner);

                Formula::Exists {
                    var: fresh,
                    ty: ty.clone(),
                    body: Box::new(body_final),
                }
            } else {
                Formula::Exists {
                    var: *bound_var,
                    ty: ty.clone(),
                    body: Box::new(subst_formula(var, replacement, body, interner)),
                }
            }
        }

        Formula::Pred(name, e) => {
            Formula::Pred(*name, Box::new(subst_expr(var, replacement, e, interner)))
        }

        Formula::Expr(e) => Formula::Expr(Box::new(subst_expr(var, replacement, e, interner))),
    }
}

// ============================================================================
// EXPRESSION SUBSTITUTION IN DEPENDENT TYPES
// ============================================================================

/// Substitute expression for variable in a dependent type (capture-avoiding)
///
/// Computes `[replacement/var]t` - replaces all free occurrences of `var` in `t`
/// with `replacement`, avoiding variable capture under Pi, Sigma, Refinement binders.
pub fn subst_dep_type(
    var: DepVar,
    replacement: &Expr,
    t: &DepType,
    interner: &ThreadedRodeo,
) -> DepType {
    match t {
        DepType::Base(_) => t.clone(),

        // Pi: CAPTURE-AVOIDING
        DepType::Pi {
            var: bound_var,
            domain,
            codomain,
        } => {
            let domain_subst = subst_dep_type(var, replacement, domain, interner);

            if *bound_var == var {
                DepType::Pi {
                    var: *bound_var,
                    domain: Box::new(domain_subst),
                    codomain: codomain.clone(),
                }
            } else if is_free_in_expr(*bound_var, replacement) {
                let avoid = {
                    let mut s = free_vars_expr(replacement);
                    s.extend(free_vars_dep_type(codomain));
                    s
                };
                let fresh = fresh_var(&avoid, interner);
                let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
                let codomain_renamed = subst_dep_type(*bound_var, &var_expr, codomain, interner);
                let codomain_final = subst_dep_type(var, replacement, &codomain_renamed, interner);

                DepType::Pi {
                    var: fresh,
                    domain: Box::new(domain_subst),
                    codomain: Box::new(codomain_final),
                }
            } else {
                DepType::Pi {
                    var: *bound_var,
                    domain: Box::new(domain_subst),
                    codomain: Box::new(subst_dep_type(var, replacement, codomain, interner)),
                }
            }
        }

        // Sigma: CAPTURE-AVOIDING
        DepType::Sigma {
            var: bound_var,
            fst,
            snd,
        } => {
            let fst_subst = subst_dep_type(var, replacement, fst, interner);

            if *bound_var == var {
                DepType::Sigma {
                    var: *bound_var,
                    fst: Box::new(fst_subst),
                    snd: snd.clone(),
                }
            } else if is_free_in_expr(*bound_var, replacement) {
                let avoid = {
                    let mut s = free_vars_expr(replacement);
                    s.extend(free_vars_dep_type(snd));
                    s
                };
                let fresh = fresh_var(&avoid, interner);
                let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
                let snd_renamed = subst_dep_type(*bound_var, &var_expr, snd, interner);
                let snd_final = subst_dep_type(var, replacement, &snd_renamed, interner);

                DepType::Sigma {
                    var: fresh,
                    fst: Box::new(fst_subst),
                    snd: Box::new(snd_final),
                }
            } else {
                DepType::Sigma {
                    var: *bound_var,
                    fst: Box::new(fst_subst),
                    snd: Box::new(subst_dep_type(var, replacement, snd, interner)),
                }
            }
        }

        // Refinement: CAPTURE-AVOIDING
        DepType::Refinement {
            var: bound_var,
            base,
            predicate,
        } => {
            let base_subst = subst_dep_type(var, replacement, base, interner);

            if *bound_var == var {
                DepType::Refinement {
                    var: *bound_var,
                    base: Box::new(base_subst),
                    predicate: predicate.clone(),
                }
            } else if is_free_in_expr(*bound_var, replacement) {
                let avoid = {
                    let mut s = free_vars_expr(replacement);
                    s.extend(free_vars_formula(predicate));
                    s
                };
                let fresh = fresh_var(&avoid, interner);
                let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
                let pred_renamed = subst_formula(*bound_var, &var_expr, predicate, interner);
                let pred_final = subst_formula(var, replacement, &pred_renamed, interner);

                DepType::Refinement {
                    var: fresh,
                    base: Box::new(base_subst),
                    predicate: pred_final,
                }
            } else {
                DepType::Refinement {
                    var: *bound_var,
                    base: Box::new(base_subst),
                    predicate: subst_formula(var, replacement, predicate, interner),
                }
            }
        }

        DepType::App(ty, expr) => DepType::App(
            Box::new(subst_dep_type(var, replacement, ty, interner)),
            Box::new(subst_expr(var, replacement, expr, interner)),
        ),
    }
}

// ============================================================================
// ALPHA-RENAMING
// ============================================================================

/// Alpha-rename bound variable in a formula
///
/// Renames binding occurrences of `old_var` to `new_var`, and substitutes
/// `new_var` for `old_var` in the bodies of those bindings.
pub fn alpha_rename_formula(
    old_var: DepVar,
    new_var: DepVar,
    f: &Formula,
    interner: &ThreadedRodeo,
) -> Formula {
    match f {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Cmp(op, e1, e2) => Formula::Cmp(*op, e1.clone(), e2.clone()),

        Formula::And(lhs, rhs) => Formula::And(
            Box::new(alpha_rename_formula(old_var, new_var, lhs, interner)),
            Box::new(alpha_rename_formula(old_var, new_var, rhs, interner)),
        ),

        Formula::Or(lhs, rhs) => Formula::Or(
            Box::new(alpha_rename_formula(old_var, new_var, lhs, interner)),
            Box::new(alpha_rename_formula(old_var, new_var, rhs, interner)),
        ),

        Formula::Not(inner) => {
            Formula::Not(Box::new(alpha_rename_formula(old_var, new_var, inner, interner)))
        }

        Formula::Impl(lhs, rhs) => Formula::Impl(
            Box::new(alpha_rename_formula(old_var, new_var, lhs, interner)),
            Box::new(alpha_rename_formula(old_var, new_var, rhs, interner)),
        ),

        Formula::Iff(lhs, rhs) => Formula::Iff(
            Box::new(alpha_rename_formula(old_var, new_var, lhs, interner)),
            Box::new(alpha_rename_formula(old_var, new_var, rhs, interner)),
        ),

        Formula::Forall { var, ty, body } => {
            if *var == old_var {
                // Rename this binding
                let var_expr = WithLoc::synthetic(Expr_::Var(new_var));
                let body_subst = subst_formula(old_var, &var_expr, body, interner);
                Formula::Forall {
                    var: new_var,
                    ty: ty.clone(),
                    body: Box::new(body_subst),
                }
            } else {
                Formula::Forall {
                    var: *var,
                    ty: ty.clone(),
                    body: Box::new(alpha_rename_formula(old_var, new_var, body, interner)),
                }
            }
        }

        Formula::Exists { var, ty, body } => {
            if *var == old_var {
                let var_expr = WithLoc::synthetic(Expr_::Var(new_var));
                let body_subst = subst_formula(old_var, &var_expr, body, interner);
                Formula::Exists {
                    var: new_var,
                    ty: ty.clone(),
                    body: Box::new(body_subst),
                }
            } else {
                Formula::Exists {
                    var: *var,
                    ty: ty.clone(),
                    body: Box::new(alpha_rename_formula(old_var, new_var, body, interner)),
                }
            }
        }

        Formula::Pred(name, e) => Formula::Pred(*name, e.clone()),
        Formula::Expr(e) => Formula::Expr(e.clone()),
    }
}

/// Alpha-rename bound variable in a dependent type
///
/// Renames binding occurrences of `old_var` to `new_var` in Pi, Sigma, Refinement.
pub fn alpha_rename_dep_type(
    old_var: DepVar,
    new_var: DepVar,
    t: &DepType,
    interner: &ThreadedRodeo,
) -> DepType {
    match t {
        DepType::Base(bt) => DepType::Base(bt.clone()),

        DepType::Pi { var, domain, codomain } => {
            let domain_renamed = alpha_rename_dep_type(old_var, new_var, domain, interner);
            if *var == old_var {
                let var_expr = WithLoc::synthetic(Expr_::Var(new_var));
                let codomain_subst = subst_dep_type(old_var, &var_expr, codomain, interner);
                DepType::Pi {
                    var: new_var,
                    domain: Box::new(domain_renamed),
                    codomain: Box::new(codomain_subst),
                }
            } else {
                DepType::Pi {
                    var: *var,
                    domain: Box::new(domain_renamed),
                    codomain: Box::new(alpha_rename_dep_type(old_var, new_var, codomain, interner)),
                }
            }
        }

        DepType::Sigma { var, fst, snd } => {
            let fst_renamed = alpha_rename_dep_type(old_var, new_var, fst, interner);
            if *var == old_var {
                let var_expr = WithLoc::synthetic(Expr_::Var(new_var));
                let snd_subst = subst_dep_type(old_var, &var_expr, snd, interner);
                DepType::Sigma {
                    var: new_var,
                    fst: Box::new(fst_renamed),
                    snd: Box::new(snd_subst),
                }
            } else {
                DepType::Sigma {
                    var: *var,
                    fst: Box::new(fst_renamed),
                    snd: Box::new(alpha_rename_dep_type(old_var, new_var, snd, interner)),
                }
            }
        }

        DepType::Refinement { var, base, predicate } => {
            let base_renamed = alpha_rename_dep_type(old_var, new_var, base, interner);
            if *var == old_var {
                let var_expr = WithLoc::synthetic(Expr_::Var(new_var));
                let pred_subst = subst_formula(old_var, &var_expr, predicate, interner);
                DepType::Refinement {
                    var: new_var,
                    base: Box::new(base_renamed),
                    predicate: pred_subst,
                }
            } else {
                DepType::Refinement {
                    var: *var,
                    base: Box::new(base_renamed),
                    predicate: alpha_rename_formula(old_var, new_var, predicate, interner),
                }
            }
        }

        DepType::App(ty, e) => DepType::App(
            Box::new(alpha_rename_dep_type(old_var, new_var, ty, interner)),
            e.clone(),
        ),
    }
}

// ============================================================================
// ALPHA-EQUIVALENCE
// ============================================================================

/// Collect bound variables in a formula
fn formula_bound_vars(f: &Formula) -> HashSet<DepVar> {
    let mut vars = HashSet::new();
    collect_formula_bound_vars(f, &mut vars);
    vars
}

fn collect_formula_bound_vars(f: &Formula, vars: &mut HashSet<DepVar>) {
    match f {
        Formula::True | Formula::False | Formula::Cmp(..) | Formula::Pred(..) | Formula::Expr(_) => {
        }

        Formula::And(lhs, rhs)
        | Formula::Or(lhs, rhs)
        | Formula::Impl(lhs, rhs)
        | Formula::Iff(lhs, rhs) => {
            collect_formula_bound_vars(lhs, vars);
            collect_formula_bound_vars(rhs, vars);
        }

        Formula::Not(inner) => {
            collect_formula_bound_vars(inner, vars);
        }

        Formula::Forall { var, body, .. } | Formula::Exists { var, body, .. } => {
            vars.insert(*var);
            collect_formula_bound_vars(body, vars);
        }
    }
}

/// Collect bound variables in a dependent type
fn dep_type_bound_vars(t: &DepType) -> HashSet<DepVar> {
    let mut vars = HashSet::new();
    collect_dep_type_bound_vars(t, &mut vars);
    vars
}

fn collect_dep_type_bound_vars(t: &DepType, vars: &mut HashSet<DepVar>) {
    match t {
        DepType::Base(_) => {}

        DepType::Pi { var, domain, codomain } => {
            vars.insert(*var);
            collect_dep_type_bound_vars(domain, vars);
            collect_dep_type_bound_vars(codomain, vars);
        }

        DepType::Sigma { var, fst, snd } => {
            vars.insert(*var);
            collect_dep_type_bound_vars(fst, vars);
            collect_dep_type_bound_vars(snd, vars);
        }

        DepType::Refinement { var, base, predicate } => {
            vars.insert(*var);
            collect_dep_type_bound_vars(base, vars);
            collect_formula_bound_vars(predicate, vars);
        }

        DepType::App(ty, _) => {
            collect_dep_type_bound_vars(ty, vars);
        }
    }
}

/// Normalize a formula by renaming all bound variables to fresh canonical names
fn normalize_formula(f: &Formula, counter: &mut u64, interner: &ThreadedRodeo) -> Formula {
    match f {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Cmp(op, e1, e2) => Formula::Cmp(*op, e1.clone(), e2.clone()),

        Formula::And(lhs, rhs) => Formula::And(
            Box::new(normalize_formula(lhs, counter, interner)),
            Box::new(normalize_formula(rhs, counter, interner)),
        ),

        Formula::Or(lhs, rhs) => Formula::Or(
            Box::new(normalize_formula(lhs, counter, interner)),
            Box::new(normalize_formula(rhs, counter, interner)),
        ),

        Formula::Not(inner) => Formula::Not(Box::new(normalize_formula(inner, counter, interner))),

        Formula::Impl(lhs, rhs) => Formula::Impl(
            Box::new(normalize_formula(lhs, counter, interner)),
            Box::new(normalize_formula(rhs, counter, interner)),
        ),

        Formula::Iff(lhs, rhs) => Formula::Iff(
            Box::new(normalize_formula(lhs, counter, interner)),
            Box::new(normalize_formula(rhs, counter, interner)),
        ),

        Formula::Forall { var, ty, body } => {
            let fresh_name = format!("_norm_{}", *counter);
            *counter += 1;
            let fresh = interner.get_or_intern(&fresh_name);
            let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
            let body_renamed = subst_formula(*var, &var_expr, body, interner);
            let body_norm = normalize_formula(&body_renamed, counter, interner);
            Formula::Forall {
                var: fresh,
                ty: ty.clone(),
                body: Box::new(body_norm),
            }
        }

        Formula::Exists { var, ty, body } => {
            let fresh_name = format!("_norm_{}", *counter);
            *counter += 1;
            let fresh = interner.get_or_intern(&fresh_name);
            let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
            let body_renamed = subst_formula(*var, &var_expr, body, interner);
            let body_norm = normalize_formula(&body_renamed, counter, interner);
            Formula::Exists {
                var: fresh,
                ty: ty.clone(),
                body: Box::new(body_norm),
            }
        }

        Formula::Pred(name, e) => Formula::Pred(*name, e.clone()),
        Formula::Expr(e) => Formula::Expr(e.clone()),
    }
}

/// Normalize a dependent type by renaming all bound variables to fresh canonical names
fn normalize_dep_type(t: &DepType, counter: &mut u64, interner: &ThreadedRodeo) -> DepType {
    match t {
        DepType::Base(bt) => DepType::Base(bt.clone()),

        DepType::Pi { var, domain, codomain } => {
            let domain_norm = normalize_dep_type(domain, counter, interner);
            let fresh_name = format!("_norm_{}", *counter);
            *counter += 1;
            let fresh = interner.get_or_intern(&fresh_name);
            let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
            let codomain_renamed = subst_dep_type(*var, &var_expr, codomain, interner);
            let codomain_norm = normalize_dep_type(&codomain_renamed, counter, interner);
            DepType::Pi {
                var: fresh,
                domain: Box::new(domain_norm),
                codomain: Box::new(codomain_norm),
            }
        }

        DepType::Sigma { var, fst, snd } => {
            let fst_norm = normalize_dep_type(fst, counter, interner);
            let fresh_name = format!("_norm_{}", *counter);
            *counter += 1;
            let fresh = interner.get_or_intern(&fresh_name);
            let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
            let snd_renamed = subst_dep_type(*var, &var_expr, snd, interner);
            let snd_norm = normalize_dep_type(&snd_renamed, counter, interner);
            DepType::Sigma {
                var: fresh,
                fst: Box::new(fst_norm),
                snd: Box::new(snd_norm),
            }
        }

        DepType::Refinement { var, base, predicate } => {
            let base_norm = normalize_dep_type(base, counter, interner);
            let fresh_name = format!("_norm_{}", *counter);
            *counter += 1;
            let fresh = interner.get_or_intern(&fresh_name);
            let var_expr = WithLoc::synthetic(Expr_::Var(fresh));
            let pred_renamed = subst_formula(*var, &var_expr, predicate, interner);
            let pred_norm = normalize_formula(&pred_renamed, counter, interner);
            DepType::Refinement {
                var: fresh,
                base: Box::new(base_norm),
                predicate: pred_norm,
            }
        }

        DepType::App(ty, e) => DepType::App(
            Box::new(normalize_dep_type(ty, counter, interner)),
            e.clone(),
        ),
    }
}

/// Check if two formulas are structurally equal (not alpha-equivalent)
fn formula_eq_structural(f1: &Formula, f2: &Formula) -> bool {
    match (f1, f2) {
        (Formula::True, Formula::True) => true,
        (Formula::False, Formula::False) => true,
        (Formula::Cmp(op1, e1a, e1b), Formula::Cmp(op2, e2a, e2b)) => {
            op1 == op2 && e1a == e2a && e1b == e2b
        }
        (Formula::And(l1, r1), Formula::And(l2, r2)) => {
            formula_eq_structural(l1, l2) && formula_eq_structural(r1, r2)
        }
        (Formula::Or(l1, r1), Formula::Or(l2, r2)) => {
            formula_eq_structural(l1, l2) && formula_eq_structural(r1, r2)
        }
        (Formula::Not(i1), Formula::Not(i2)) => formula_eq_structural(i1, i2),
        (Formula::Impl(l1, r1), Formula::Impl(l2, r2)) => {
            formula_eq_structural(l1, l2) && formula_eq_structural(r1, r2)
        }
        (Formula::Iff(l1, r1), Formula::Iff(l2, r2)) => {
            formula_eq_structural(l1, l2) && formula_eq_structural(r1, r2)
        }
        (
            Formula::Forall {
                var: v1,
                ty: t1,
                body: b1,
            },
            Formula::Forall {
                var: v2,
                ty: t2,
                body: b2,
            },
        ) => v1 == v2 && t1 == t2 && formula_eq_structural(b1, b2),
        (
            Formula::Exists {
                var: v1,
                ty: t1,
                body: b1,
            },
            Formula::Exists {
                var: v2,
                ty: t2,
                body: b2,
            },
        ) => v1 == v2 && t1 == t2 && formula_eq_structural(b1, b2),
        (Formula::Pred(n1, e1), Formula::Pred(n2, e2)) => n1 == n2 && e1 == e2,
        (Formula::Expr(e1), Formula::Expr(e2)) => e1 == e2,
        _ => false,
    }
}

/// Check if two dependent types are structurally equal
fn dep_type_eq_structural(t1: &DepType, t2: &DepType) -> bool {
    match (t1, t2) {
        (DepType::Base(b1), DepType::Base(b2)) => b1 == b2,
        (
            DepType::Pi {
                var: v1,
                domain: d1,
                codomain: c1,
            },
            DepType::Pi {
                var: v2,
                domain: d2,
                codomain: c2,
            },
        ) => v1 == v2 && dep_type_eq_structural(d1, d2) && dep_type_eq_structural(c1, c2),
        (
            DepType::Sigma {
                var: v1,
                fst: f1,
                snd: s1,
            },
            DepType::Sigma {
                var: v2,
                fst: f2,
                snd: s2,
            },
        ) => v1 == v2 && dep_type_eq_structural(f1, f2) && dep_type_eq_structural(s1, s2),
        (
            DepType::Refinement {
                var: v1,
                base: b1,
                predicate: p1,
            },
            DepType::Refinement {
                var: v2,
                base: b2,
                predicate: p2,
            },
        ) => v1 == v2 && dep_type_eq_structural(b1, b2) && formula_eq_structural(p1, p2),
        (DepType::App(ty1, e1), DepType::App(ty2, e2)) => {
            dep_type_eq_structural(ty1, ty2) && e1 == e2
        }
        _ => false,
    }
}

/// Check alpha-equivalence of two dependent types
///
/// Two types are alpha-equivalent if they differ only in the names of bound variables.
/// For example: `Pi(x:Int).x -> x` is alpha-equivalent to `Pi(y:Int).y -> y`
///
/// Algorithm: Normalize both types to use the same fresh variable names,
/// then check structural equality.
pub fn dep_type_alpha_eq(t1: &DepType, t2: &DepType, interner: &ThreadedRodeo) -> bool {
    // Both normalizations start with counter 0, ensuring identical types
    // normalize to structurally equal results
    let mut counter1 = 0u64;
    let mut counter2 = 0u64;
    let t1_norm = normalize_dep_type(t1, &mut counter1, interner);
    let t2_norm = normalize_dep_type(t2, &mut counter2, interner);
    dep_type_eq_structural(&t1_norm, &t2_norm)
}

/// Check alpha-equivalence of two formulas
pub fn formula_alpha_eq(f1: &Formula, f2: &Formula, interner: &ThreadedRodeo) -> bool {
    let mut counter1 = 0u64;
    let mut counter2 = 0u64;
    let f1_norm = normalize_formula(f1, &mut counter1, interner);
    let f2_norm = normalize_formula(f2, &mut counter2, interner);
    formula_eq_structural(&f1_norm, &f2_norm)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Literal;

    fn make_interner() -> ThreadedRodeo {
        ThreadedRodeo::new()
    }

    fn var_expr(var: DepVar) -> Expr {
        WithLoc::synthetic(Expr_::Var(var))
    }

    fn int_expr(n: i32) -> Expr {
        WithLoc::synthetic(Expr_::Lit(Literal::i32(n)))
    }

    fn i32_type() -> BrrrType {
        BrrrType::Numeric(NumericType::Int(IntType::I32))
    }

    #[test]
    fn test_fresh_var() {
        let interner = make_interner();
        let avoid = HashSet::new();
        let v1 = fresh_var(&avoid, &interner);
        let v2 = fresh_var(&avoid, &interner);
        assert_ne!(v1, v2);
    }

    #[test]
    fn test_free_vars_expr_simple() {
        let interner = make_interner();
        let x = interner.get_or_intern("x");
        let e = var_expr(x);
        let fv = free_vars_expr(&e);
        assert!(fv.contains(&x));
    }

    #[test]
    fn test_free_vars_expr_let_mut() {
        let interner = make_interner();
        let x = interner.get_or_intern("x");
        let y = interner.get_or_intern("y");

        // let mut x = 1 in x + y
        let e = WithLoc::synthetic(Expr_::LetMut {
            var: x,
            ty: None,
            init: Box::new(int_expr(1)),
            body: Box::new(WithLoc::synthetic(Expr_::Binary(
                crate::expr::BinaryOp::Add,
                Box::new(var_expr(x)),
                Box::new(var_expr(y)),
            ))),
        });

        let fv = free_vars_expr(&e);
        assert!(!fv.contains(&x)); // x is bound
        assert!(fv.contains(&y)); // y is free
    }

    #[test]
    fn test_subst_expr_var() {
        let interner = make_interner();
        let x = interner.get_or_intern("x");
        let e = var_expr(x);
        let replacement = int_expr(42);

        let result = subst_expr(x, &replacement, &e, &interner);
        assert_eq!(result, replacement);
    }

    #[test]
    fn test_subst_expr_capture_avoidance() {
        let interner = make_interner();
        let x = interner.get_or_intern("x");
        let y = interner.get_or_intern("y");

        // for y in [1,2,3] { x }
        let for_expr = WithLoc::synthetic(Expr_::For {
            label: None,
            var: y,
            iter: Box::new(WithLoc::synthetic(Expr_::Array(vec![
                int_expr(1),
                int_expr(2),
                int_expr(3),
            ]))),
            body: Box::new(var_expr(x)),
        });

        // Substitute [y/x] - should trigger capture avoidance
        let replacement = var_expr(y);
        let result = subst_expr(x, &replacement, &for_expr, &interner);

        // The result should have renamed the bound y to avoid capture
        if let Expr_::For { var: new_var, body, .. } = &result.value {
            assert_ne!(*new_var, y); // y should have been renamed
            // The body should now contain the replacement (y)
            if let Expr_::Var(v) = &body.value {
                assert_eq!(*v, y);
            } else {
                panic!("Expected Var in body");
            }
        } else {
            panic!("Expected For");
        }
    }

    #[test]
    fn test_subst_formula() {
        let interner = make_interner();
        let x = interner.get_or_intern("x");

        let formula = Formula::Cmp(
            CmpOp::Gt,
            Box::new(var_expr(x)),
            Box::new(int_expr(0)),
        );

        let replacement = int_expr(5);
        let result = subst_formula(x, &replacement, &formula, &interner);

        if let Formula::Cmp(CmpOp::Gt, lhs, rhs) = result {
            assert_eq!(*lhs, int_expr(5));
            assert_eq!(*rhs, int_expr(0));
        } else {
            panic!("Expected Cmp formula");
        }
    }

    #[test]
    fn test_subst_formula_forall_capture() {
        let interner = make_interner();
        let x = interner.get_or_intern("x");
        let y = interner.get_or_intern("y");

        // forall y:Int. x + y > 0
        let formula = Formula::Forall {
            var: y,
            ty: i32_type(),
            body: Box::new(Formula::Cmp(
                CmpOp::Gt,
                Box::new(WithLoc::synthetic(Expr_::Binary(
                    crate::expr::BinaryOp::Add,
                    Box::new(var_expr(x)),
                    Box::new(var_expr(y)),
                ))),
                Box::new(int_expr(0)),
            )),
        };

        // Substitute [y/x] - should trigger capture avoidance
        let replacement = var_expr(y);
        let result = subst_formula(x, &replacement, &formula, &interner);

        if let Formula::Forall { var: new_var, .. } = result {
            assert_ne!(new_var, y); // y should have been renamed
        } else {
            panic!("Expected Forall");
        }
    }

    #[test]
    fn test_dep_type_alpha_eq() {
        let interner = make_interner();
        let x = interner.get_or_intern("x");
        let y = interner.get_or_intern("y");

        // Pi(x:Int).Int
        let t1 = DepType::Pi {
            var: x,
            domain: Box::new(DepType::Base(i32_type())),
            codomain: Box::new(DepType::Base(i32_type())),
        };

        // Pi(y:Int).Int
        let t2 = DepType::Pi {
            var: y,
            domain: Box::new(DepType::Base(i32_type())),
            codomain: Box::new(DepType::Base(i32_type())),
        };

        assert!(dep_type_alpha_eq(&t1, &t2, &interner));
    }

    #[test]
    fn test_dep_type_alpha_eq_refinement() {
        let interner = make_interner();
        let x = interner.get_or_intern("x");
        let y = interner.get_or_intern("y");

        // {x:Int | x > 0}
        let t1 = DepType::Refinement {
            var: x,
            base: Box::new(DepType::Base(i32_type())),
            predicate: Formula::Cmp(CmpOp::Gt, Box::new(var_expr(x)), Box::new(int_expr(0))),
        };

        // {y:Int | y > 0}
        let t2 = DepType::Refinement {
            var: y,
            base: Box::new(DepType::Base(i32_type())),
            predicate: Formula::Cmp(CmpOp::Gt, Box::new(var_expr(y)), Box::new(int_expr(0))),
        };

        assert!(dep_type_alpha_eq(&t1, &t2, &interner));
    }

    #[test]
    fn test_dep_type_not_alpha_eq() {
        let interner = make_interner();
        let x = interner.get_or_intern("x");
        let y = interner.get_or_intern("y");

        // {x:Int | x > 0}
        let t1 = DepType::Refinement {
            var: x,
            base: Box::new(DepType::Base(i32_type())),
            predicate: Formula::Cmp(CmpOp::Gt, Box::new(var_expr(x)), Box::new(int_expr(0))),
        };

        // {y:Int | y > 1}  (different constant)
        let t2 = DepType::Refinement {
            var: y,
            base: Box::new(DepType::Base(i32_type())),
            predicate: Formula::Cmp(CmpOp::Gt, Box::new(var_expr(y)), Box::new(int_expr(1))),
        };

        assert!(!dep_type_alpha_eq(&t1, &t2, &interner));
    }

    #[test]
    fn test_alpha_rename_formula() {
        let interner = make_interner();
        let x = interner.get_or_intern("x");
        let y = interner.get_or_intern("y");

        // forall x. x > 0
        let formula = Formula::Forall {
            var: x,
            ty: i32_type(),
            body: Box::new(Formula::Cmp(
                CmpOp::Gt,
                Box::new(var_expr(x)),
                Box::new(int_expr(0)),
            )),
        };

        let renamed = alpha_rename_formula(x, y, &formula, &interner);

        if let Formula::Forall { var, body, .. } = renamed {
            assert_eq!(var, y);
            if let Formula::Cmp(_, lhs, _) = body.as_ref() {
                if let Expr_::Var(v) = &lhs.value {
                    assert_eq!(*v, y);
                }
            }
        }
    }
}
