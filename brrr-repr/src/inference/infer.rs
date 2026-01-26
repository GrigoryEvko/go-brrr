//! Core type inference functions
//!
//! Implements bidirectional Hindley-Milner type inference with:
//! - `infer_expr`: Synthesize a type for an expression (bottom-up)
//! - `check_expr`: Check an expression against an expected type (top-down)
//! - `unify`: Unification algorithm for type equality
//! - `generalize`/`instantiate`: Let-polymorphism support

use std::collections::HashMap;

use crate::expr::{BinaryOp, Expr, Expr_, Literal, Pattern_, Range, UnaryOp};
use crate::types::{
    BrrrType, FuncType, IntType, KindedVar, NumericType, ParamType, TypeScheme, TypeVar,
};

use super::types::{
    apply_substitution, free_type_vars, InferenceState, TypeConstraint, TypeCtx, TypeError,
    TypeErrorKind,
};

// ============================================================================
// Type Inference (Synthesis)
// ============================================================================

/// Infer the type of an expression in the given context.
///
/// This is the "synthesis" direction of bidirectional typing: we produce
/// a type from the expression without an expected type.
///
/// # Arguments
/// * `ctx` - The typing context with variable bindings
/// * `expr` - The expression to infer
/// * `state` - Mutable inference state for constraints and fresh variables
/// * `intern` - Closure to intern fresh variable names
///
/// # Returns
/// The inferred type. If inference fails, an error is recorded in `state`
/// and a fresh type variable is returned as a placeholder.
pub fn infer_expr<F>(
    ctx: &TypeCtx,
    expr: &Expr,
    state: &mut InferenceState,
    intern: &mut F,
) -> BrrrType
where
    F: FnMut(&str) -> TypeVar,
{
    let span = expr.range;
    match &expr.value {
        // === Literals ===
        Expr_::Lit(lit) => infer_literal(lit),

        // === Variables ===
        Expr_::Var(var) => match ctx.lookup(var) {
            Some(scheme) => instantiate(scheme, state, intern),
            None => {
                state.add_error(TypeError::unbound_variable(*var, span));
                state.fresh_type(intern)
            }
        },

        // === Global references ===
        Expr_::Global(name) => match ctx.lookup(name) {
            Some(scheme) => instantiate(scheme, state, intern),
            None => {
                state.add_error(TypeError::unbound_variable(*name, span));
                state.fresh_type(intern)
            }
        },

        // === Lambda ===
        Expr_::Lambda { params, body } => {
            // Create a child context with parameter bindings
            let mut child_ctx = ctx.child();
            let param_types: Vec<ParamType> = params
                .iter()
                .map(|(name, ty)| {
                    child_ctx.extend_mono(*name, ty.clone());
                    ParamType::named(*name, ty.clone())
                })
                .collect();

            // Infer body type
            let body_ty = infer_expr(&child_ctx, body, state, intern);

            BrrrType::Func(Box::new(FuncType::pure(param_types, body_ty)))
        }

        // === Function Call ===
        Expr_::Call(func, args) => {
            let func_ty = infer_expr(ctx, func, state, intern);

            // Generate a fresh type variable for the result
            let result_ty = state.fresh_type(intern);

            // Build expected function type: (arg_types) -> result_ty
            let arg_types: Vec<BrrrType> =
                args.iter().map(|a| infer_expr(ctx, a, state, intern)).collect();

            let expected_func = BrrrType::Func(Box::new(FuncType::pure(
                arg_types.iter().map(|t| ParamType::unnamed(t.clone())).collect(),
                result_ty.clone(),
            )));

            // Constrain: func_ty = expected_func
            state.constrain_equal(func_ty, expected_func, span);

            result_ty
        }

        // === If-then-else ===
        Expr_::If(cond, then_branch, else_branch) => {
            // Condition must be Bool
            let cond_ty = infer_expr(ctx, cond, state, intern);
            state.constrain_equal(cond_ty, BrrrType::BOOL, cond.range);

            // Both branches must have the same type
            let then_ty = infer_expr(ctx, then_branch, state, intern);
            let else_ty = infer_expr(ctx, else_branch, state, intern);

            state.constrain_equal(then_ty.clone(), else_ty, span);

            then_ty
        }

        // === Let binding ===
        Expr_::Let {
            pattern,
            ty: anno_ty,
            init,
            body,
        } => {
            // Infer initializer type
            let init_ty = if let Some(expected) = anno_ty {
                // If annotated, check against annotation
                check_expr(ctx, init, expected, state, intern);
                expected.clone()
            } else {
                infer_expr(ctx, init, state, intern)
            };

            // Generalize the type at let-binding site
            let scheme = generalize(ctx, &state.apply(&init_ty));

            // Extend context with pattern bindings
            let mut child_ctx = ctx.child();
            bind_pattern(&pattern.value, &scheme, &mut child_ctx);

            // Infer body type
            infer_expr(&child_ctx, body, state, intern)
        }

        // === Mutable let binding ===
        Expr_::LetMut { var, ty, init, body } => {
            // Infer initializer type
            let init_ty = if let Some(expected) = ty {
                check_expr(ctx, init, expected, state, intern);
                expected.clone()
            } else {
                infer_expr(ctx, init, state, intern)
            };

            // Mutable bindings are not generalized (monomorphic)
            let mut child_ctx = ctx.child();
            child_ctx.extend_mono(*var, init_ty);

            infer_expr(&child_ctx, body, state, intern)
        }

        // === Binary operations ===
        Expr_::Binary(op, lhs, rhs) => infer_binary_op(ctx, *op, lhs, rhs, state, intern),

        // === Unary operations ===
        Expr_::Unary(op, operand) => infer_unary_op(ctx, *op, operand, state, intern),

        // === Tuple ===
        Expr_::Tuple(elems) => {
            let elem_types: Vec<BrrrType> =
                elems.iter().map(|e| infer_expr(ctx, e, state, intern)).collect();
            BrrrType::Tuple(elem_types)
        }

        // === Array ===
        Expr_::Array(elems) => {
            if elems.is_empty() {
                // Empty array: polymorphic element type
                let elem_ty = state.fresh_type(intern);
                BrrrType::array(elem_ty)
            } else {
                // Infer first element, constrain rest to match
                let first_ty = infer_expr(ctx, &elems[0], state, intern);
                for elem in &elems[1..] {
                    let elem_ty = infer_expr(ctx, elem, state, intern);
                    state.constrain_equal(first_ty.clone(), elem_ty, elem.range);
                }
                BrrrType::array(first_ty)
            }
        }

        // === Field access ===
        Expr_::Field(base, field) => {
            let base_ty = infer_expr(ctx, base, state, intern);
            let result_ty = state.fresh_type(intern);

            // Add constraint: base_ty has field `field` of type result_ty
            // Note: This requires struct resolution during constraint solving
            // We use the Spur's internal key as a numeric identifier
            state.add_constraint(TypeConstraint::has_field(
                base_ty,
                format!("spur_{}", field.into_inner()),
                result_ty.clone(),
                span,
            ));

            result_ty
        }

        // === Tuple projection ===
        Expr_::TupleProj(base, idx) => {
            let base_ty = infer_expr(ctx, base, state, intern);

            // We need to constrain base_ty to be a tuple with at least idx+1 elements
            // For now, generate a placeholder and add a constraint
            let result_ty = state.fresh_type(intern);

            // Add field constraint using numeric index
            state.add_constraint(TypeConstraint::has_field(
                base_ty,
                idx.to_string(),
                result_ty.clone(),
                span,
            ));

            result_ty
        }

        // === Index access ===
        Expr_::Index(base, index) => {
            let base_ty = infer_expr(ctx, base, state, intern);
            let index_ty = infer_expr(ctx, index, state, intern);

            // Index should be an integer type
            // For simplicity, we accept any numeric type but ideally would be usize
            let result_ty = state.fresh_type(intern);

            // Base should be an array/slice of result_ty
            let expected_base = BrrrType::array(result_ty.clone());
            state.constrain_equal(base_ty, expected_base, span);

            // Index should be a size type (u32/u64/usize)
            // For simplicity, just check it's numeric
            let _ = index_ty; // Used for effect tracking but not constrained here

            result_ty
        }

        // === Block ===
        Expr_::Block(exprs) => {
            if exprs.is_empty() {
                BrrrType::UNIT
            } else {
                // Infer all but last, return type of last
                for e in &exprs[..exprs.len() - 1] {
                    let _ = infer_expr(ctx, e, state, intern);
                }
                infer_expr(ctx, exprs.last().unwrap(), state, intern)
            }
        }

        // === Sequence ===
        Expr_::Seq(first, second) => {
            let _ = infer_expr(ctx, first, state, intern);
            infer_expr(ctx, second, state, intern)
        }

        // === Return ===
        Expr_::Return(opt_val) => {
            if let Some(val) = opt_val {
                let _ = infer_expr(ctx, val, state, intern);
            }
            // Return has type Never (doesn't return normally)
            BrrrType::NEVER
        }

        // === Type cast ===
        Expr_::As(expr, target_ty) => {
            // Infer expression type, result is the target type
            let _ = infer_expr(ctx, expr, state, intern);
            target_ty.clone()
        }

        // === Type test ===
        Expr_::Is(expr, _) => {
            // Infer expression type, result is Bool
            let _ = infer_expr(ctx, expr, state, intern);
            BrrrType::BOOL
        }

        // === Sizeof/Alignof ===
        Expr_::Sizeof(_) | Expr_::Alignof(_) => {
            // Returns a size type (usize)
            BrrrType::Numeric(NumericType::Int(IntType::U64))
        }

        // === Box ===
        Expr_::Box(inner) => {
            let inner_ty = infer_expr(ctx, inner, state, intern);
            BrrrType::boxed(inner_ty)
        }

        // === Deref ===
        Expr_::Deref(inner) => {
            let inner_ty = infer_expr(ctx, inner, state, intern);
            let result_ty = state.fresh_type(intern);

            // inner_ty should be a reference/box to result_ty
            let expected = BrrrType::ref_shared(result_ty.clone());
            state.constrain_equal(inner_ty, expected, span);

            result_ty
        }

        // === Borrow ===
        Expr_::Borrow(inner) => {
            let inner_ty = infer_expr(ctx, inner, state, intern);
            BrrrType::ref_shared(inner_ty)
        }

        // === Mutable borrow ===
        Expr_::BorrowMut(inner) => {
            let inner_ty = infer_expr(ctx, inner, state, intern);
            BrrrType::ref_mut(inner_ty)
        }

        // === Assignment ===
        Expr_::Assign(lhs, rhs) => {
            let lhs_ty = infer_expr(ctx, lhs, state, intern);
            let rhs_ty = infer_expr(ctx, rhs, state, intern);

            // lhs_ty should be a mutable reference to rhs_ty
            let expected_lhs = BrrrType::ref_mut(rhs_ty);
            state.constrain_equal(lhs_ty, expected_lhs, span);

            BrrrType::UNIT
        }

        // === Hole ===
        Expr_::Hole => {
            // Hole is a placeholder: give it a fresh type variable
            state.fresh_type(intern)
        }

        // === Error ===
        Expr_::Error(_) => {
            // Error node: give it a fresh type variable
            state.fresh_type(intern)
        }

        // === Other expressions (not yet implemented) ===
        _ => {
            // For unimplemented expressions, return a fresh type variable
            state.fresh_type(intern)
        }
    }
}

// ============================================================================
// Type Checking (Analysis)
// ============================================================================

/// Check an expression against an expected type.
///
/// This is the "analysis" direction of bidirectional typing: we propagate
/// type information downward from the expected type.
///
/// # Arguments
/// * `ctx` - The typing context
/// * `expr` - The expression to check
/// * `expected` - The expected type
/// * `state` - Mutable inference state
/// * `intern` - Closure to intern fresh variable names
pub fn check_expr<F>(
    ctx: &TypeCtx,
    expr: &Expr,
    expected: &BrrrType,
    state: &mut InferenceState,
    intern: &mut F,
) where
    F: FnMut(&str) -> TypeVar,
{
    let span = expr.range;
    match &expr.value {
        // === Lambda with expected function type ===
        Expr_::Lambda { params, body } => {
            if let BrrrType::Func(ft) = expected {
                if params.len() != ft.params.len() {
                    state.add_error(TypeError::arity_mismatch(
                        ft.params.len(),
                        params.len(),
                        span,
                    ));
                    return;
                }

                // Check each parameter type matches
                let mut child_ctx = ctx.child();
                for ((name, param_ty), expected_param) in params.iter().zip(ft.params.iter()) {
                    state.constrain_equal(param_ty.clone(), expected_param.ty.clone(), span);
                    child_ctx.extend_mono(*name, param_ty.clone());
                }

                // Check body against expected return type
                check_expr(&child_ctx, body, &ft.return_type, state, intern);
            } else {
                // Expected is not a function type
                state.add_error(TypeError::new(TypeErrorKind::NotAFunction, span));
            }
        }

        // === If-then-else with expected type ===
        Expr_::If(cond, then_branch, else_branch) => {
            // Check condition is Bool
            check_expr(ctx, cond, &BrrrType::BOOL, state, intern);

            // Check both branches against expected type
            check_expr(ctx, then_branch, expected, state, intern);
            check_expr(ctx, else_branch, expected, state, intern);
        }

        // === Tuple with expected tuple type ===
        Expr_::Tuple(elems) => {
            if let BrrrType::Tuple(expected_elems) = expected {
                if elems.len() != expected_elems.len() {
                    state.add_error(TypeError::arity_mismatch(
                        expected_elems.len(),
                        elems.len(),
                        span,
                    ));
                    return;
                }

                for (elem, expected_ty) in elems.iter().zip(expected_elems.iter()) {
                    check_expr(ctx, elem, expected_ty, state, intern);
                }
            } else {
                // Expected is not a tuple type, fall back to synthesis
                let inferred = infer_expr(ctx, expr, state, intern);
                state.constrain_equal(inferred, expected.clone(), span);
            }
        }

        // === Let binding ===
        Expr_::Let {
            pattern,
            ty: anno_ty,
            init,
            body,
        } => {
            // Infer/check initializer
            let init_ty = if let Some(expected_init) = anno_ty {
                check_expr(ctx, init, expected_init, state, intern);
                expected_init.clone()
            } else {
                infer_expr(ctx, init, state, intern)
            };

            // Generalize and bind
            let scheme = generalize(ctx, &state.apply(&init_ty));
            let mut child_ctx = ctx.child();
            bind_pattern(&pattern.value, &scheme, &mut child_ctx);

            // Check body against expected type
            check_expr(&child_ctx, body, expected, state, intern);
        }

        // === Block ===
        Expr_::Block(exprs) => {
            if exprs.is_empty() {
                state.constrain_equal(BrrrType::UNIT, expected.clone(), span);
            } else {
                for e in &exprs[..exprs.len() - 1] {
                    let _ = infer_expr(ctx, e, state, intern);
                }
                check_expr(ctx, exprs.last().unwrap(), expected, state, intern);
            }
        }

        // === Fall back to synthesis ===
        _ => {
            let inferred = infer_expr(ctx, expr, state, intern);
            state.constrain_equal(inferred, expected.clone(), span);
        }
    }
}

// ============================================================================
// Unification
// ============================================================================

/// Unify two types, extending the substitution in the state.
///
/// Returns `Ok(())` on success, `Err(TypeError)` on failure.
/// On success, the substitution in `state` is extended.
pub fn unify<F>(
    t1: &BrrrType,
    t2: &BrrrType,
    span: Range,
    state: &mut InferenceState,
    intern: &mut F,
) -> Result<(), TypeError>
where
    F: FnMut(&str) -> TypeVar,
{
    // Apply current substitution first
    let t1 = state.apply(t1);
    let t2 = state.apply(t2);

    match (&t1, &t2) {
        // Same types unify trivially
        _ if t1 == t2 => Ok(()),

        // Type variable on the left
        (BrrrType::Var(v), _) => {
            if occurs_check(*v, &t2) {
                Err(TypeError::infinite_type(t1, t2, span))
            } else {
                state.extend_substitution(*v, t2);
                Ok(())
            }
        }

        // Type variable on the right
        (_, BrrrType::Var(v)) => {
            if occurs_check(*v, &t1) {
                Err(TypeError::infinite_type(t2, t1, span))
            } else {
                state.extend_substitution(*v, t1);
                Ok(())
            }
        }

        // Function types
        (BrrrType::Func(f1), BrrrType::Func(f2)) => {
            if f1.params.len() != f2.params.len() {
                return Err(TypeError::arity_mismatch(f1.params.len(), f2.params.len(), span));
            }

            // Unify parameter types
            for (p1, p2) in f1.params.iter().zip(f2.params.iter()) {
                unify(&p1.ty, &p2.ty, span, state, intern)?;
            }

            // Unify return types
            unify(&f1.return_type, &f2.return_type, span, state, intern)
        }

        // Wrapper types
        (BrrrType::Wrap(k1, inner1), BrrrType::Wrap(k2, inner2)) if k1 == k2 => {
            unify(inner1, inner2, span, state, intern)
        }

        // Modal types
        (BrrrType::Modal(k1, inner1), BrrrType::Modal(k2, inner2)) if k1 == k2 => {
            unify(inner1, inner2, span, state, intern)
        }

        // Result types
        (BrrrType::Result(ok1, err1), BrrrType::Result(ok2, err2)) => {
            unify(ok1, ok2, span, state, intern)?;
            unify(err1, err2, span, state, intern)
        }

        // Tuple types
        (BrrrType::Tuple(elems1), BrrrType::Tuple(elems2)) => {
            if elems1.len() != elems2.len() {
                return Err(TypeError::arity_mismatch(elems1.len(), elems2.len(), span));
            }
            for (e1, e2) in elems1.iter().zip(elems2.iter()) {
                unify(e1, e2, span, state, intern)?;
            }
            Ok(())
        }

        // Type application
        (BrrrType::App(f1, args1), BrrrType::App(f2, args2)) => {
            if args1.len() != args2.len() {
                return Err(TypeError::arity_mismatch(args1.len(), args2.len(), span));
            }
            unify(f1, f2, span, state, intern)?;
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                unify(a1, a2, span, state, intern)?;
            }
            Ok(())
        }

        // Type mismatch
        _ => Err(TypeError::mismatch(t1, t2, span)),
    }
}

/// Occurs check: does the type variable occur in the type?
///
/// This prevents infinite types like `a = List<a>`.
fn occurs_check(var: TypeVar, ty: &BrrrType) -> bool {
    free_type_vars(ty).contains(&var)
}

// ============================================================================
// Generalization and Instantiation
// ============================================================================

/// Generalize a type to a type scheme by quantifying over free variables
/// that are not in the context.
///
/// This implements let-polymorphism: `let x = e1 in e2` generalizes the
/// type of `e1` so that `x` can be used polymorphically in `e2`.
#[must_use]
pub fn generalize(ctx: &TypeCtx, ty: &BrrrType) -> TypeScheme {
    let ty_vars = free_type_vars(ty);
    let ctx_vars = ctx.free_vars();

    // Generalize over type variables free in ty but not in ctx
    let gen_vars: Vec<KindedVar> = ty_vars
        .into_iter()
        .filter(|v| !ctx_vars.contains(v))
        .map(KindedVar::of_type) // Assume kind * for now
        .collect();

    if gen_vars.is_empty() {
        TypeScheme::mono(ty.clone())
    } else {
        TypeScheme::poly_kinded(gen_vars, ty.clone())
    }
}

/// Instantiate a type scheme with fresh type variables.
///
/// This creates fresh instances of quantified type variables so that
/// each use of a polymorphic binding gets independent type variables.
pub fn instantiate<F>(scheme: &TypeScheme, state: &mut InferenceState, intern: &mut F) -> BrrrType
where
    F: FnMut(&str) -> TypeVar,
{
    if scheme.is_mono() {
        return scheme.body.clone();
    }

    // Generate fresh type variables for each quantified variable
    let mut subst = HashMap::new();
    for kv in &scheme.type_vars {
        let fresh = state.fresh_type_var(&mut *intern);
        subst.insert(kv.var, BrrrType::Var(fresh));
    }

    apply_substitution(&scheme.body, &subst)
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Infer the type of a literal.
fn infer_literal(lit: &Literal) -> BrrrType {
    match lit {
        Literal::Unit => BrrrType::UNIT,
        Literal::Bool(_) => BrrrType::BOOL,
        Literal::Int(_, int_type) => BrrrType::Numeric(NumericType::Int(*int_type)),
        Literal::Float(_, prec) => BrrrType::Numeric(NumericType::Float(*prec)),
        Literal::String(_) => BrrrType::STRING,
        Literal::Char(_) => BrrrType::CHAR,
    }
}

/// Infer the type of a binary operation.
fn infer_binary_op<F>(
    ctx: &TypeCtx,
    op: BinaryOp,
    lhs: &Expr,
    rhs: &Expr,
    state: &mut InferenceState,
    intern: &mut F,
) -> BrrrType
where
    F: FnMut(&str) -> TypeVar,
{
    let span = lhs.range.union(rhs.range);
    let lhs_ty = infer_expr(ctx, lhs, state, intern);
    let rhs_ty = infer_expr(ctx, rhs, state, intern);

    match op {
        // Arithmetic operators: operands must be the same numeric type
        BinaryOp::Add
        | BinaryOp::Sub
        | BinaryOp::Mul
        | BinaryOp::Div
        | BinaryOp::Mod
        | BinaryOp::AddWrapping
        | BinaryOp::SubWrapping
        | BinaryOp::MulWrapping
        | BinaryOp::AddSaturating
        | BinaryOp::SubSaturating
        | BinaryOp::MulSaturating => {
            state.constrain_equal(lhs_ty.clone(), rhs_ty, span);
            lhs_ty
        }

        // Checked arithmetic: returns Option<T>
        BinaryOp::AddChecked | BinaryOp::SubChecked | BinaryOp::MulChecked => {
            state.constrain_equal(lhs_ty.clone(), rhs_ty, span);
            BrrrType::option(lhs_ty)
        }

        // Comparison operators: operands must be the same type, result is Bool
        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
            state.constrain_equal(lhs_ty, rhs_ty, span);
            BrrrType::BOOL
        }

        // Logical operators: operands must be Bool
        BinaryOp::And | BinaryOp::Or => {
            state.constrain_equal(lhs_ty, BrrrType::BOOL, lhs.range);
            state.constrain_equal(rhs_ty, BrrrType::BOOL, rhs.range);
            BrrrType::BOOL
        }

        // Bitwise operators: operands must be the same integer type
        BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor => {
            state.constrain_equal(lhs_ty.clone(), rhs_ty, span);
            lhs_ty
        }

        // Shift operators: lhs is integer, rhs is shift amount (also integer)
        BinaryOp::Shl | BinaryOp::Shr | BinaryOp::UShr => {
            // rhs is constrained to be an integer but can differ from lhs
            // For simplicity, we just return lhs type
            lhs_ty
        }
    }
}

/// Infer the type of a unary operation.
fn infer_unary_op<F>(
    ctx: &TypeCtx,
    op: UnaryOp,
    operand: &Expr,
    state: &mut InferenceState,
    intern: &mut F,
) -> BrrrType
where
    F: FnMut(&str) -> TypeVar,
{
    let span = operand.range;
    let operand_ty = infer_expr(ctx, operand, state, intern);

    match op {
        // Negation: numeric types
        UnaryOp::Neg => operand_ty,

        // Logical not: Bool -> Bool
        UnaryOp::Not => {
            state.constrain_equal(operand_ty, BrrrType::BOOL, span);
            BrrrType::BOOL
        }

        // Bitwise not: integer types
        UnaryOp::BitNot => operand_ty,

        // Dereference: Ref<T> -> T
        UnaryOp::Deref => {
            let inner_ty = state.fresh_type(intern);
            let ref_ty = BrrrType::ref_shared(inner_ty.clone());
            state.constrain_equal(operand_ty, ref_ty, span);
            inner_ty
        }

        // Reference: T -> Ref<T>
        UnaryOp::Ref => BrrrType::ref_shared(operand_ty),

        // Mutable reference: T -> RefMut<T>
        UnaryOp::RefMut => BrrrType::ref_mut(operand_ty),
    }
}

/// Bind pattern variables in the context with the given type scheme.
fn bind_pattern(pat: &Pattern_, scheme: &TypeScheme, ctx: &mut TypeCtx) {
    match pat {
        Pattern_::Var(v) => {
            ctx.extend(*v, scheme.clone());
        }
        Pattern_::Wild => {}
        Pattern_::Tuple(pats) => {
            // For tuples, we'd need to destructure the scheme body
            // For now, just bind each sub-pattern with the whole scheme
            // (This is a simplification; proper implementation would
            // destructure the type)
            for p in pats {
                bind_pattern(&p.value, scheme, ctx);
            }
        }
        Pattern_::As(inner, v) => {
            bind_pattern(&inner.value, scheme, ctx);
            ctx.extend(*v, scheme.clone());
        }
        _ => {
            // Other patterns: recursively process sub-patterns
            // Simplified for now
        }
    }
}

// ============================================================================
// Constraint Solving
// ============================================================================

/// Solve all constraints in the inference state.
///
/// This iterates through constraints, unifying types and recording errors.
/// Returns `true` if all constraints were solved successfully.
pub fn solve_constraints<F>(state: &mut InferenceState, intern: &mut F) -> bool
where
    F: FnMut(&str) -> TypeVar,
{
    let constraints = std::mem::take(&mut state.constraints);
    let mut success = true;

    for constraint in constraints {
        match constraint {
            TypeConstraint::Equal(t1, t2, span) => {
                if let Err(err) = unify(&t1, &t2, span, state, intern) {
                    state.add_error(err);
                    success = false;
                }
            }
            TypeConstraint::Subtype(sub, sup, span) => {
                // For now, treat subtyping as equality
                // A proper subtyping algorithm would be more complex
                if let Err(err) = unify(&sub, &sup, span, state, intern) {
                    state.add_error(err);
                    success = false;
                }
            }
            TypeConstraint::HasField(base, field, result, span) => {
                // Resolve the base type
                let base = state.apply(&base);

                match &base {
                    BrrrType::Struct(st) => {
                        // Look up field in struct
                        let found = st.fields.iter().find(|f| {
                            // Compare field name using the same numeric format
                            format!("spur_{}", f.name.into_inner()) == field
                        });
                        if let Some(f) = found {
                            if let Err(err) = unify(&f.ty, &result, span, state, intern) {
                                state.add_error(err);
                                success = false;
                            }
                        } else {
                            state.add_error(TypeError::field_not_found(&field, base.clone(), span));
                            success = false;
                        }
                    }
                    BrrrType::Tuple(elems) => {
                        // Parse index from field name
                        if let Ok(idx) = field.parse::<usize>() {
                            if idx < elems.len() {
                                if let Err(err) = unify(&elems[idx], &result, span, state, intern) {
                                    state.add_error(err);
                                    success = false;
                                }
                            } else {
                                state.add_error(TypeError::field_not_found(&field, base.clone(), span));
                                success = false;
                            }
                        } else {
                            state.add_error(TypeError::field_not_found(&field, base.clone(), span));
                            success = false;
                        }
                    }
                    BrrrType::Var(_) => {
                        // Base is still a variable - constraint cannot be resolved yet
                        // In a more complete implementation, we'd defer this constraint
                        // For now, we leave the result as-is
                    }
                    _ => {
                        state.add_error(TypeError::field_not_found(&field, base.clone(), span));
                        success = false;
                    }
                }
            }
            TypeConstraint::Instantiate(scheme, args, result, span) => {
                // Instantiate the scheme and unify with result
                let instantiated = instantiate(&scheme, state, intern);

                // Apply type arguments (simplified)
                let final_ty = if args.is_empty() {
                    instantiated
                } else {
                    // Would need to apply args to the instantiated type
                    // For now, just use the instantiated type
                    instantiated
                };

                if let Err(err) = unify(&final_ty, &result, span, state, intern) {
                    state.add_error(err);
                    success = false;
                }
            }
        }
    }

    success
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::WithLoc;
    use lasso::Rodeo;

    fn make_test_env() -> (Rodeo, TypeCtx, InferenceState) {
        (Rodeo::default(), TypeCtx::new(), InferenceState::new())
    }

    #[test]
    fn test_infer_literal() {
        assert_eq!(infer_literal(&Literal::Unit), BrrrType::UNIT);
        assert_eq!(infer_literal(&Literal::Bool(true)), BrrrType::BOOL);
        assert_eq!(
            infer_literal(&Literal::i32(42)),
            BrrrType::Numeric(NumericType::Int(IntType::I32))
        );
        assert_eq!(infer_literal(&Literal::string("hello")), BrrrType::STRING);
    }

    #[test]
    fn test_infer_var() {
        let (mut rodeo, mut ctx, mut state) = make_test_env();
        let x = rodeo.get_or_intern("x");

        ctx.extend_mono(x, BrrrType::BOOL);

        let expr = WithLoc::synthetic(Expr_::Var(x));
        let ty = infer_expr(&ctx, &expr, &mut state, &mut |s| rodeo.get_or_intern(s));

        assert_eq!(ty, BrrrType::BOOL);
        assert!(!state.has_errors());
    }

    #[test]
    fn test_infer_unbound_var() {
        let (mut rodeo, ctx, mut state) = make_test_env();
        let x = rodeo.get_or_intern("x");

        let expr = WithLoc::synthetic(Expr_::Var(x));
        let _ = infer_expr(&ctx, &expr, &mut state, &mut |s| rodeo.get_or_intern(s));

        assert!(state.has_errors());
        assert!(matches!(
            state.errors[0].kind,
            TypeErrorKind::UnboundVariable(_)
        ));
    }

    #[test]
    fn test_infer_lambda() {
        let (mut rodeo, ctx, mut state) = make_test_env();
        let x = rodeo.get_or_intern("x");

        // Lambda: fn(x: Bool) -> x
        let body = WithLoc::synthetic(Expr_::Var(x));
        let lambda = WithLoc::synthetic(Expr_::Lambda {
            params: vec![(x, BrrrType::BOOL)],
            body: Box::new(body),
        });

        let ty = infer_expr(&ctx, &lambda, &mut state, &mut |s| rodeo.get_or_intern(s));

        assert!(!state.has_errors());
        if let BrrrType::Func(ft) = ty {
            assert_eq!(ft.params.len(), 1);
            assert_eq!(ft.params[0].ty, BrrrType::BOOL);
            assert_eq!(ft.return_type, BrrrType::BOOL);
        } else {
            panic!("Expected function type");
        }
    }

    #[test]
    fn test_infer_if_then_else() {
        let (mut rodeo, ctx, mut state) = make_test_env();

        let cond = WithLoc::synthetic(Expr_::Lit(Literal::Bool(true)));
        let then_br = WithLoc::synthetic(Expr_::Lit(Literal::i32(1)));
        let else_br = WithLoc::synthetic(Expr_::Lit(Literal::i32(2)));

        let if_expr = WithLoc::synthetic(Expr_::If(
            Box::new(cond),
            Box::new(then_br),
            Box::new(else_br),
        ));

        let ty = infer_expr(&ctx, &if_expr, &mut state, &mut |s| rodeo.get_or_intern(s));

        assert_eq!(ty, BrrrType::Numeric(NumericType::Int(IntType::I32)));
        assert!(!state.has_errors());
    }

    #[test]
    fn test_infer_tuple() {
        let (mut rodeo, ctx, mut state) = make_test_env();

        let tuple = WithLoc::synthetic(Expr_::Tuple(vec![
            WithLoc::synthetic(Expr_::Lit(Literal::Bool(true))),
            WithLoc::synthetic(Expr_::Lit(Literal::i32(42))),
        ]));

        let ty = infer_expr(&ctx, &tuple, &mut state, &mut |s| rodeo.get_or_intern(s));

        if let BrrrType::Tuple(elems) = ty {
            assert_eq!(elems.len(), 2);
            assert_eq!(elems[0], BrrrType::BOOL);
            assert_eq!(elems[1], BrrrType::Numeric(NumericType::Int(IntType::I32)));
        } else {
            panic!("Expected tuple type");
        }
    }

    #[test]
    fn test_unify_simple() {
        let (mut rodeo, _, mut state) = make_test_env();

        let result = unify(
            &BrrrType::BOOL,
            &BrrrType::BOOL,
            Range::SYNTHETIC,
            &mut state,
            &mut |s| rodeo.get_or_intern(s),
        );

        assert!(result.is_ok());
    }

    #[test]
    fn test_unify_var() {
        let (mut rodeo, _, mut state) = make_test_env();
        let alpha = rodeo.get_or_intern("alpha");

        let result = unify(
            &BrrrType::Var(alpha),
            &BrrrType::BOOL,
            Range::SYNTHETIC,
            &mut state,
            &mut |s| rodeo.get_or_intern(s),
        );

        assert!(result.is_ok());
        assert_eq!(state.substitution.get(&alpha), Some(&BrrrType::BOOL));
    }

    #[test]
    fn test_unify_occurs_check() {
        let (mut rodeo, _, mut state) = make_test_env();
        let alpha = rodeo.get_or_intern("alpha");

        // Try to unify alpha with Option<alpha> - should fail
        let recursive_ty = BrrrType::option(BrrrType::Var(alpha));
        let result = unify(
            &BrrrType::Var(alpha),
            &recursive_ty,
            Range::SYNTHETIC,
            &mut state,
            &mut |s| rodeo.get_or_intern(s),
        );

        assert!(result.is_err());
        if let Err(err) = result {
            assert!(matches!(err.kind, TypeErrorKind::InfiniteType));
        }
    }

    #[test]
    fn test_generalize() {
        let (mut rodeo, ctx, _) = make_test_env();
        let alpha = rodeo.get_or_intern("alpha");

        // Generalize a type with free variable alpha
        let ty = BrrrType::Var(alpha);
        let scheme = generalize(&ctx, &ty);

        assert!(!scheme.is_mono());
        assert_eq!(scheme.type_vars.len(), 1);
    }

    #[test]
    fn test_generalize_with_context() {
        let (mut rodeo, mut ctx, _) = make_test_env();
        let alpha = rodeo.get_or_intern("alpha");
        let x = rodeo.get_or_intern("x");

        // Add x: alpha to context
        ctx.extend_mono(x, BrrrType::Var(alpha));

        // Generalize alpha -> alpha should NOT generalize alpha
        // since it's free in the context
        let ty = BrrrType::Var(alpha);
        let scheme = generalize(&ctx, &ty);

        assert!(scheme.is_mono());
    }

    #[test]
    fn test_instantiate() {
        let (mut rodeo, _, mut state) = make_test_env();
        let alpha = rodeo.get_or_intern("alpha");

        // Create polymorphic identity: forall a. a -> a
        let scheme = TypeScheme::poly(
            vec![alpha],
            BrrrType::Func(Box::new(FuncType::pure(
                vec![ParamType::unnamed(BrrrType::Var(alpha))],
                BrrrType::Var(alpha),
            ))),
        );

        let inst1 = instantiate(&scheme, &mut state, &mut |s| rodeo.get_or_intern(s));
        let inst2 = instantiate(&scheme, &mut state, &mut |s| rodeo.get_or_intern(s));

        // Each instantiation should produce different type variables
        assert_ne!(inst1, inst2);
    }

    #[test]
    fn test_solve_constraints() {
        let (mut rodeo, _, mut state) = make_test_env();
        let alpha = rodeo.get_or_intern("alpha");

        // Add constraint: alpha = Bool
        state.constrain_equal(BrrrType::Var(alpha), BrrrType::BOOL, Range::SYNTHETIC);

        let success = solve_constraints(&mut state, &mut |s| rodeo.get_or_intern(s));

        assert!(success);
        assert!(!state.has_errors());
        assert_eq!(state.apply(&BrrrType::Var(alpha)), BrrrType::BOOL);
    }
}
