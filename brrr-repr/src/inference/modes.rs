//! Mode (linearity) checking pass
//!
//! Implements linear type checking following F* Modes.fsti patterns.
//!
//! # Overview
//!
//! Mode checking verifies that linear resources are used exactly once,
//! affine resources at most once, and relevant resources at least once.
//!
//! The algorithm traverses expressions and maintains a linear context (`LinCtx`)
//! that tracks the usage state of each bound variable.
//!
//! # Core Rules
//!
//! - **Var**: Mark variable as used, fail if already consumed (for linear/affine)
//! - **Let**: Extend context with binding, check body, verify consumed at end
//! - **Lambda**: Check body with params in context, verify linearity constraints
//! - **If/Match**: Split context for branches, join after
//! - **Move**: Consume the variable (mode becomes consumed)
//! - **Borrow**: Create temporary reference without consuming
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::inference::modes::{mode_check_function, ModeError};
//! use brrr_repr::decl::FunctionDef;
//!
//! let errors = mode_check_function(&func);
//! if errors.is_empty() {
//!     println!("Mode checking passed");
//! } else {
//!     for error in errors {
//!         println!("Mode error: {:?}", error);
//!     }
//! }
//! ```

use crate::decl::FunctionDef;
use crate::expr::{
    CatchArm, Expr, Expr_, HandlerClause, MatchArm, Pattern, Pattern_, Range, VarId,
};
use crate::modes::{ExtendedMode, LinCtx, LinEntry, Mode};

/// Mode checking error types
///
/// These errors indicate violations of linearity constraints during
/// mode checking. Each variant provides context about what went wrong.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModeError {
    /// Linear variable used more than once
    ///
    /// Linear variables (Mode::One with ExtendedMode::Linear) must be used
    /// exactly once. This error occurs when attempting a second use.
    LinearUsedMultipleTimes {
        /// The variable that was used multiple times
        var: VarId,
        /// Source location of the second use
        span: Range,
    },

    /// Linear variable not consumed before scope exit
    ///
    /// Linear variables must be used exactly once before going out of scope.
    /// This error occurs when a linear variable remains unused at the end
    /// of its scope.
    LinearNotConsumed {
        /// The variable that was not consumed
        var: VarId,
        /// Source location where the scope ends
        span: Range,
    },

    /// Affine variable used more than once
    ///
    /// Affine variables (ExtendedMode::Affine) can be used at most once.
    /// This error occurs when attempting a second use.
    AffineUsedMultipleTimes {
        /// The variable that was used multiple times
        var: VarId,
        /// Number of times it was used
        count: usize,
        /// Source location of the violation
        span: Range,
    },

    /// Relevant variable never used
    ///
    /// Relevant variables (ExtendedMode::Relevant) must be used at least once.
    /// This error occurs when a relevant variable is never used.
    RelevantNotUsed {
        /// The variable that was not used
        var: VarId,
        /// Source location where the scope ends
        span: Range,
    },

    /// Mode incompatibility
    ///
    /// The actual usage pattern of a variable is incompatible with its
    /// declared mode.
    ModeIncompatible {
        /// The variable with incompatible mode
        var: VarId,
        /// Expected mode based on declaration
        expected: Mode,
        /// Actual mode based on usage
        found: Mode,
        /// Source location of the incompatibility
        span: Range,
    },

    /// Variable not found in context
    ///
    /// Attempted to use a variable that is not bound in the current scope.
    VariableNotFound {
        /// The unbound variable
        var: VarId,
        /// Source location of the reference
        span: Range,
    },

    /// Borrow of moved value
    ///
    /// Attempted to borrow a value that has already been moved.
    BorrowAfterMove {
        /// The variable that was moved
        var: VarId,
        /// Source location of the borrow attempt
        span: Range,
    },

    /// Use of moved value
    ///
    /// Attempted to use a value that has already been moved.
    UseAfterMove {
        /// The variable that was moved
        var: VarId,
        /// Source location of the use attempt
        span: Range,
    },

    /// Branches have inconsistent linear resource usage
    ///
    /// In if/match expressions, all branches must consume linear resources
    /// consistently. This error occurs when branches differ.
    InconsistentBranchUsage {
        /// Variables with inconsistent usage across branches
        vars: Vec<VarId>,
        /// Source location of the branching expression
        span: Range,
    },

    /// Continuation used incorrectly
    ///
    /// One-shot continuations must be used exactly once; multi-shot can be
    /// used any number of times.
    ContinuationMisuse {
        /// The continuation variable
        var: VarId,
        /// Expected linearity
        expected_one_shot: bool,
        /// Source location
        span: Range,
    },
}

impl ModeError {
    /// Get the source span where this error occurred
    pub fn span(&self) -> Range {
        match self {
            Self::LinearUsedMultipleTimes { span, .. } => *span,
            Self::LinearNotConsumed { span, .. } => *span,
            Self::AffineUsedMultipleTimes { span, .. } => *span,
            Self::RelevantNotUsed { span, .. } => *span,
            Self::ModeIncompatible { span, .. } => *span,
            Self::VariableNotFound { span, .. } => *span,
            Self::BorrowAfterMove { span, .. } => *span,
            Self::UseAfterMove { span, .. } => *span,
            Self::InconsistentBranchUsage { span, .. } => *span,
            Self::ContinuationMisuse { span, .. } => *span,
        }
    }

    /// Get the variable(s) involved in this error
    pub fn vars(&self) -> Vec<VarId> {
        match self {
            Self::LinearUsedMultipleTimes { var, .. } => vec![*var],
            Self::LinearNotConsumed { var, .. } => vec![*var],
            Self::AffineUsedMultipleTimes { var, .. } => vec![*var],
            Self::RelevantNotUsed { var, .. } => vec![*var],
            Self::ModeIncompatible { var, .. } => vec![*var],
            Self::VariableNotFound { var, .. } => vec![*var],
            Self::BorrowAfterMove { var, .. } => vec![*var],
            Self::UseAfterMove { var, .. } => vec![*var],
            Self::InconsistentBranchUsage { vars, .. } => vars.clone(),
            Self::ContinuationMisuse { var, .. } => vec![*var],
        }
    }
}

/// Mode checking state
///
/// Maintains the linear context and accumulates errors during mode checking.
#[derive(Debug, Clone)]
pub struct ModeCheckState {
    /// Current linear context tracking variable usage
    pub ctx: LinCtx,
    /// Accumulated mode checking errors
    pub errors: Vec<ModeError>,
}

impl ModeCheckState {
    /// Create a new empty mode check state
    pub fn new() -> Self {
        Self {
            ctx: LinCtx::empty(),
            errors: Vec::new(),
        }
    }

    /// Create a mode check state with a pre-initialized context
    pub fn with_context(ctx: LinCtx) -> Self {
        Self {
            ctx,
            errors: Vec::new(),
        }
    }

    /// Add an error to the error list
    pub fn add_error(&mut self, error: ModeError) {
        self.errors.push(error);
    }

    /// Check if any errors occurred
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Take all errors, leaving the error list empty
    pub fn take_errors(&mut self) -> Vec<ModeError> {
        std::mem::take(&mut self.errors)
    }

    /// Get the number of errors
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }
}

impl Default for ModeCheckState {
    fn default() -> Self {
        Self::new()
    }
}

/// Check mode constraints for an expression
///
/// This is the core mode checking function. It traverses the expression tree
/// and verifies that all linearity constraints are satisfied.
///
/// # Arguments
///
/// * `expr` - The expression to check
/// * `state` - Mutable reference to the mode check state
///
/// # Returns
///
/// Returns `Ok(())` if mode checking succeeds for this expression,
/// or `Err(ModeError)` for the first error encountered.
///
/// Note: Even on error, checking continues and more errors may be
/// accumulated in `state.errors`.
pub fn mode_check_expr(expr: &Expr, state: &mut ModeCheckState) -> Result<(), ModeError> {
    match &expr.value {
        // === Literals and globals: no linear resources ===
        Expr_::Lit(_) | Expr_::Global(_) | Expr_::Hole | Expr_::Error(_) => Ok(()),

        // === Variable reference: mark as used ===
        Expr_::Var(var) => {
            use_variable(*var, expr.range, state)
        }

        // === Unary operations ===
        Expr_::Unary(_, operand) => {
            mode_check_expr(operand, state)
        }

        // === Binary operations ===
        Expr_::Binary(_, left, right) => {
            mode_check_expr(left, state)?;
            mode_check_expr(right, state)
        }

        // === Function call ===
        Expr_::Call(func, args) => {
            mode_check_expr(func, state)?;
            for arg in args {
                mode_check_expr(arg, state)?;
            }
            Ok(())
        }

        // === Method call ===
        Expr_::MethodCall(receiver, _method, args) => {
            mode_check_expr(receiver, state)?;
            for arg in args {
                mode_check_expr(arg, state)?;
            }
            Ok(())
        }

        // === Tuples and arrays ===
        Expr_::Tuple(elems) | Expr_::Array(elems) => {
            for elem in elems {
                mode_check_expr(elem, state)?;
            }
            Ok(())
        }

        // === Struct construction ===
        Expr_::Struct { fields, .. } => {
            for (_, field_expr) in fields {
                mode_check_expr(field_expr, state)?;
            }
            Ok(())
        }

        // === Enum variant construction ===
        Expr_::Variant { fields, .. } => {
            for field in fields {
                mode_check_expr(field, state)?;
            }
            Ok(())
        }

        // === Field access ===
        Expr_::Field(base, _field) => {
            mode_check_expr(base, state)
        }

        // === Index access ===
        Expr_::Index(base, index) => {
            mode_check_expr(base, state)?;
            mode_check_expr(index, state)
        }

        // === Tuple projection ===
        Expr_::TupleProj(base, _idx) => {
            mode_check_expr(base, state)
        }

        // === If-then-else: split context for branches ===
        Expr_::If(cond, then_branch, else_branch) => {
            mode_check_expr(cond, state)?;
            mode_check_if(then_branch, else_branch, expr.range, state)
        }

        // === Pattern match: split context for each arm ===
        Expr_::Match(scrutinee, arms) => {
            mode_check_expr(scrutinee, state)?;
            mode_check_match(arms, expr.range, state)
        }

        // === Loops ===
        Expr_::Loop { body, .. } => {
            // Loop body is checked, but linear resources cannot escape
            mode_check_expr(body, state)
        }

        Expr_::While { cond, body, .. } => {
            mode_check_expr(cond, state)?;
            mode_check_expr(body, state)
        }

        Expr_::For { var, iter, body, .. } => {
            mode_check_expr(iter, state)?;
            // Add loop variable as unrestricted (rebound each iteration)
            state.ctx.extend(LinEntry::unrestricted(*var));
            let result = mode_check_expr(body, state);
            // Loop variable goes out of scope
            let _ = state.ctx.remove(*var);
            result
        }

        // === Control flow ===
        Expr_::Break { value, .. } => {
            if let Some(val) = value {
                mode_check_expr(val, state)?;
            }
            Ok(())
        }

        Expr_::Continue { .. } => Ok(()),

        Expr_::Return(value) => {
            if let Some(val) = value {
                mode_check_expr(val, state)?;
            }
            Ok(())
        }

        // === Let binding ===
        Expr_::Let { pattern, init, body, .. } => {
            mode_check_expr(init, state)?;
            mode_check_let(pattern, body, expr.range, state)
        }

        // === Mutable let binding ===
        Expr_::LetMut { var, init, body, .. } => {
            mode_check_expr(init, state)?;
            // Mutable bindings are unrestricted (can be assigned multiple times)
            state.ctx.extend(LinEntry::unrestricted(*var));
            let result = mode_check_expr(body, state);
            let _ = state.ctx.remove(*var);
            result
        }

        // === Assignment ===
        Expr_::Assign(target, value) => {
            mode_check_expr(target, state)?;
            mode_check_expr(value, state)
        }

        // === Lambda ===
        Expr_::Lambda { params, body } => {
            mode_check_lambda(params, body, expr.range, state)
        }

        // === Closure ===
        Expr_::Closure { params, captures, body } => {
            // Check that captured variables are available
            for cap in captures {
                use_variable(*cap, expr.range, state)?;
            }
            mode_check_lambda(params, body, expr.range, state)
        }

        // === Box allocation ===
        Expr_::Box(inner) => {
            mode_check_expr(inner, state)
        }

        // === Dereference ===
        Expr_::Deref(inner) => {
            mode_check_expr(inner, state)
        }

        // === Borrow (shared) ===
        Expr_::Borrow(inner) => {
            // Borrowing doesn't consume the value, just creates a reference
            mode_check_borrow(inner, expr.range, state)
        }

        // === Borrow (mutable) ===
        Expr_::BorrowMut(inner) => {
            // Mutable borrow is like shared borrow for mode checking
            mode_check_borrow(inner, expr.range, state)
        }

        // === Move ===
        Expr_::Move(inner) => {
            mode_check_move(inner, expr.range, state)
        }

        // === Drop ===
        Expr_::Drop(inner) => {
            // Drop consumes the value
            mode_check_expr(inner, state)
        }

        // === Exception handling ===
        Expr_::Throw(inner) => {
            mode_check_expr(inner, state)
        }

        Expr_::Try { body, catches, finally } => {
            mode_check_expr(body, state)?;
            for catch in catches {
                mode_check_catch(catch, state)?;
            }
            if let Some(fin) = finally {
                mode_check_expr(fin, state)?;
            }
            Ok(())
        }

        // === Async/Concurrency ===
        Expr_::Await(inner) | Expr_::Yield(inner) | Expr_::Async(inner) | Expr_::Spawn(inner) => {
            mode_check_expr(inner, state)
        }

        // === Effect handling ===
        Expr_::Handle(body, handler) => {
            mode_check_expr(body, state)?;
            for clause in &handler.clauses {
                mode_check_handler_clause(clause, state)?;
            }
            if let Some((var, return_body)) = &handler.return_clause {
                state.ctx.extend(LinEntry::unrestricted(*var));
                let result = mode_check_expr(return_body, state);
                let _ = state.ctx.remove(*var);
                result?;
            }
            Ok(())
        }

        Expr_::Perform(_op, args) => {
            for arg in args {
                mode_check_expr(arg, state)?;
            }
            Ok(())
        }

        Expr_::Resume { var, value } => {
            // Resuming a continuation - check if one-shot
            use_variable(*var, expr.range, state)?;
            mode_check_expr(value, state)
        }

        // === Delimited continuations ===
        Expr_::Reset { body, .. } => {
            mode_check_expr(body, state)
        }

        Expr_::Shift { var, body, .. } => {
            // Continuation variable is linear by default (one-shot)
            state.ctx.extend(LinEntry::linear(*var));
            let result = mode_check_expr(body, state);
            check_consumed(*var, expr.range, state)?;
            result
        }

        // === Type operations ===
        Expr_::As(inner, _) | Expr_::Is(inner, _) => {
            mode_check_expr(inner, state)
        }

        Expr_::Sizeof(_) | Expr_::Alignof(_) => Ok(()),

        // === Blocks ===
        Expr_::Block(stmts) => {
            for stmt in stmts {
                mode_check_expr(stmt, state)?;
            }
            Ok(())
        }

        Expr_::Seq(first, second) => {
            mode_check_expr(first, state)?;
            mode_check_expr(second, state)
        }

        Expr_::Unsafe(inner) => {
            mode_check_expr(inner, state)
        }

        // === Gradual typing cast ===
        Expr_::GradualCast { expr, .. } => {
            mode_check_expr(expr, state)
        }

        // === Control flow labels ===
        Expr_::Goto { .. } => Ok(()),
        Expr_::Labeled { body, .. } => mode_check_expr(body, state),
    }
}

/// Use a variable, marking it as consumed in the linear context
fn use_variable(var: VarId, span: Range, state: &mut ModeCheckState) -> Result<(), ModeError> {
    match state.ctx.lookup(var) {
        None => {
            // Variable not found - might be a global or external
            // We don't error here as it could be resolved elsewhere
            Ok(())
        }
        Some(entry) => {
            if entry.used && !entry.allows_reuse() {
                // Already used and can't be reused
                let error = if entry.extended == ExtendedMode::Linear {
                    ModeError::LinearUsedMultipleTimes { var, span }
                } else if entry.extended == ExtendedMode::Affine {
                    ModeError::AffineUsedMultipleTimes {
                        var,
                        count: 2,
                        span,
                    }
                } else {
                    ModeError::UseAfterMove { var, span }
                };
                state.add_error(error.clone());
                Err(error)
            } else {
                // Mark as used
                if let Some(new_ctx) = state.ctx.use_var(var) {
                    state.ctx = new_ctx;
                }
                Ok(())
            }
        }
    }
}

/// Check that a variable has been consumed (for linear/relevant)
fn check_consumed(var: VarId, span: Range, state: &mut ModeCheckState) -> Result<(), ModeError> {
    if let Some(entry) = state.ctx.lookup(var) {
        if entry.must_be_used() && !entry.used {
            let error = if entry.extended == ExtendedMode::Relevant {
                ModeError::RelevantNotUsed { var, span }
            } else {
                ModeError::LinearNotConsumed { var, span }
            };
            state.add_error(error.clone());
            return Err(error);
        }
    }
    // Remove from context
    let _ = state.ctx.remove(var);
    Ok(())
}

/// Mode check if-then-else expression
fn mode_check_if(
    then_branch: &Expr,
    else_branch: &Expr,
    span: Range,
    state: &mut ModeCheckState,
) -> Result<(), ModeError> {
    // Split context for both branches
    let (left_ctx, right_ctx) = state.ctx.split();

    // Check then branch
    let mut then_state = ModeCheckState::with_context(left_ctx);
    let then_result = mode_check_expr(then_branch, &mut then_state);
    state.errors.extend(then_state.errors);

    // Check else branch
    let mut else_state = ModeCheckState::with_context(right_ctx);
    let else_result = mode_check_expr(else_branch, &mut else_state);
    state.errors.extend(else_state.errors);

    // Join contexts
    state.ctx = then_state.ctx.join(&else_state.ctx);

    // Check for inconsistent usage
    let inconsistent = find_inconsistent_usage(&then_state.ctx, &else_state.ctx);
    if !inconsistent.is_empty() {
        let error = ModeError::InconsistentBranchUsage {
            vars: inconsistent,
            span,
        };
        state.add_error(error);
    }

    then_result.and(else_result)
}

/// Mode check match expression
fn mode_check_match(
    arms: &[MatchArm],
    span: Range,
    state: &mut ModeCheckState,
) -> Result<(), ModeError> {
    if arms.is_empty() {
        return Ok(());
    }

    let mut arm_contexts = Vec::with_capacity(arms.len());
    let mut first_result = Ok(());

    for (i, arm) in arms.iter().enumerate() {
        // Split off a fresh context for this arm
        let (arm_ctx, _) = if i == arms.len() - 1 {
            // Last arm gets the remaining context
            (state.ctx.clone(), LinCtx::empty())
        } else {
            state.ctx.split()
        };

        let mut arm_state = ModeCheckState::with_context(arm_ctx);

        // Add pattern bindings
        extend_pattern_bindings(&arm.pattern, &mut arm_state);

        // Check guard if present
        if let Some(guard) = &arm.guard {
            if let Err(e) = mode_check_expr(guard, &mut arm_state) {
                if first_result.is_ok() {
                    first_result = Err(e);
                }
            }
        }

        // Check body
        if let Err(e) = mode_check_expr(&arm.body, &mut arm_state) {
            if first_result.is_ok() {
                first_result = Err(e);
            }
        }

        // Remove pattern bindings and check consumption
        remove_pattern_bindings(&arm.pattern, arm.range, &mut arm_state);

        state.errors.extend(arm_state.errors);
        arm_contexts.push(arm_state.ctx);
    }

    // Join all arm contexts
    if let Some(first) = arm_contexts.first() {
        let mut joined = first.clone();
        for ctx in arm_contexts.iter().skip(1) {
            joined = joined.join(ctx);
        }
        state.ctx = joined;
    }

    // Check for inconsistencies between arms
    if arm_contexts.len() >= 2 {
        for i in 1..arm_contexts.len() {
            let inconsistent = find_inconsistent_usage(&arm_contexts[0], &arm_contexts[i]);
            if !inconsistent.is_empty() {
                state.add_error(ModeError::InconsistentBranchUsage {
                    vars: inconsistent,
                    span,
                });
            }
        }
    }

    first_result
}

/// Find variables with inconsistent usage between two contexts
fn find_inconsistent_usage(ctx1: &LinCtx, ctx2: &LinCtx) -> Vec<VarId> {
    let mut inconsistent = Vec::new();

    for entry in ctx1.iter() {
        if let Some(other) = ctx2.lookup(entry.var) {
            // For linear vars, both must have same used status
            if entry.must_be_used() && entry.used != other.used {
                inconsistent.push(entry.var);
            }
        }
    }

    inconsistent
}

/// Mode check let binding
fn mode_check_let(
    pattern: &Pattern,
    body: &Expr,
    span: Range,
    state: &mut ModeCheckState,
) -> Result<(), ModeError> {
    // Add pattern bindings to context
    extend_pattern_bindings(pattern, state);

    // Check body
    let result = mode_check_expr(body, state);

    // Remove bindings and check consumption
    remove_pattern_bindings(pattern, span, state);

    result
}

/// Extend context with pattern bindings
fn extend_pattern_bindings(pattern: &Pattern, state: &mut ModeCheckState) {
    extend_pattern_bindings_inner(&pattern.value, state);
}

fn extend_pattern_bindings_inner(pattern: &Pattern_, state: &mut ModeCheckState) {
    match pattern {
        Pattern_::Var(var) => {
            // Default to linear for let bindings - can be overridden by type info
            state.ctx.extend(LinEntry::linear(*var));
        }
        Pattern_::Wild | Pattern_::Lit(_) | Pattern_::Rest(None) => {}
        Pattern_::Rest(Some(var)) => {
            state.ctx.extend(LinEntry::unrestricted(*var));
        }
        Pattern_::As(inner, var) => {
            extend_pattern_bindings(inner, state);
            state.ctx.extend(LinEntry::linear(*var));
        }
        Pattern_::Tuple(pats) => {
            for p in pats {
                extend_pattern_bindings(p, state);
            }
        }
        Pattern_::Struct { fields, .. } => {
            for (_, p) in fields {
                extend_pattern_bindings(p, state);
            }
        }
        Pattern_::Variant { fields, .. } => {
            for p in fields {
                extend_pattern_bindings(p, state);
            }
        }
        Pattern_::Or(left, _right) => {
            // Or patterns bind the same variables in both branches
            extend_pattern_bindings(left, state);
        }
        Pattern_::Guard(inner, _) | Pattern_::Ref(inner) | Pattern_::Box(inner) => {
            extend_pattern_bindings(inner, state);
        }
        // Type pattern may optionally bind a variable
        Pattern_::Type { binding: Some(var), .. } => {
            state.ctx.extend(LinEntry::linear(*var));
        }
        Pattern_::Type { binding: None, .. } => {}
    }
}

/// Remove pattern bindings from context and check consumption
fn remove_pattern_bindings(pattern: &Pattern, span: Range, state: &mut ModeCheckState) {
    remove_pattern_bindings_inner(&pattern.value, span, state);
}

fn remove_pattern_bindings_inner(pattern: &Pattern_, span: Range, state: &mut ModeCheckState) {
    match pattern {
        Pattern_::Var(var) => {
            let _ = check_consumed(*var, span, state);
        }
        Pattern_::Wild | Pattern_::Lit(_) | Pattern_::Rest(None) => {}
        Pattern_::Rest(Some(var)) => {
            let _ = state.ctx.remove(*var);
        }
        Pattern_::As(inner, var) => {
            remove_pattern_bindings(inner, span, state);
            let _ = check_consumed(*var, span, state);
        }
        Pattern_::Tuple(pats) => {
            for p in pats {
                remove_pattern_bindings(p, span, state);
            }
        }
        Pattern_::Struct { fields, .. } => {
            for (_, p) in fields {
                remove_pattern_bindings(p, span, state);
            }
        }
        Pattern_::Variant { fields, .. } => {
            for p in fields {
                remove_pattern_bindings(p, span, state);
            }
        }
        Pattern_::Or(left, _right) => {
            remove_pattern_bindings(left, span, state);
        }
        Pattern_::Guard(inner, _) | Pattern_::Ref(inner) | Pattern_::Box(inner) => {
            remove_pattern_bindings(inner, span, state);
        }
        // Type pattern may optionally bind a variable
        Pattern_::Type { binding: Some(var), .. } => {
            let _ = check_consumed(*var, span, state);
        }
        Pattern_::Type { binding: None, .. } => {}
    }
}

/// Mode check lambda expression
fn mode_check_lambda(
    params: &[(VarId, crate::types::BrrrType)],
    body: &Expr,
    span: Range,
    state: &mut ModeCheckState,
) -> Result<(), ModeError> {
    // Add parameters to context with their declared modes
    // For now, assume all params are linear unless specified otherwise
    for (var, _ty) in params {
        state.ctx.extend(LinEntry::linear(*var));
    }

    // Check body
    let result = mode_check_expr(body, state);

    // Check that linear params are consumed and remove them
    for (var, _ty) in params {
        let _ = check_consumed(*var, span, state);
    }

    result
}

/// Mode check borrow expression
fn mode_check_borrow(
    inner: &Expr,
    span: Range,
    state: &mut ModeCheckState,
) -> Result<(), ModeError> {
    // For borrowing, we need to check that the value hasn't been moved
    if let Expr_::Var(var) = &inner.value {
        if let Some(entry) = state.ctx.lookup(*var) {
            if entry.mode == Mode::Zero {
                let error = ModeError::BorrowAfterMove { var: *var, span };
                state.add_error(error.clone());
                return Err(error);
            }
        }
        // Borrowing doesn't consume the value for mode checking purposes
        Ok(())
    } else {
        // For complex expressions, just check them normally
        mode_check_expr(inner, state)
    }
}

/// Mode check move expression
fn mode_check_move(
    inner: &Expr,
    span: Range,
    state: &mut ModeCheckState,
) -> Result<(), ModeError> {
    if let Expr_::Var(var) = &inner.value {
        use_variable(*var, span, state)
    } else {
        mode_check_expr(inner, state)
    }
}

/// Mode check catch arm
fn mode_check_catch(catch: &CatchArm, state: &mut ModeCheckState) -> Result<(), ModeError> {
    // Add pattern bindings
    extend_pattern_bindings(&catch.pattern, state);

    // Check body
    let result = mode_check_expr(&catch.body, state);

    // Remove bindings
    remove_pattern_bindings(&catch.pattern, catch.range, state);

    result
}

/// Mode check handler clause
fn mode_check_handler_clause(
    clause: &HandlerClause,
    state: &mut ModeCheckState,
) -> Result<(), ModeError> {
    // Add parameters
    for var in &clause.params {
        state.ctx.extend(LinEntry::unrestricted(*var));
    }

    // Add continuation - one-shot is linear, multi-shot is unrestricted
    if clause.continuation_linearity.is_one_shot() {
        state.ctx.extend(LinEntry::linear(clause.continuation));
    } else {
        state.ctx.extend(LinEntry::unrestricted(clause.continuation));
    }

    // Check body
    let result = mode_check_expr(&clause.body, state);

    // Check continuation consumption for one-shot
    if clause.continuation_linearity.is_one_shot() {
        if let Some(entry) = state.ctx.lookup(clause.continuation) {
            if !entry.used {
                state.add_error(ModeError::ContinuationMisuse {
                    var: clause.continuation,
                    expected_one_shot: true,
                    span: clause.body.range,
                });
            }
        }
    }

    // Remove params and continuation
    for var in &clause.params {
        let _ = state.ctx.remove(*var);
    }
    let _ = state.ctx.remove(clause.continuation);

    result
}

/// Mode check a function definition
///
/// This is the top-level entry point for mode checking a function.
/// It initializes the context with function parameters and checks the body.
///
/// # Arguments
///
/// * `func` - The function definition to check
///
/// # Returns
///
/// A vector of mode errors. Empty if the function passes mode checking.
pub fn mode_check_function(func: &FunctionDef) -> Vec<ModeError> {
    let mut state = ModeCheckState::new();

    // Add parameters to context with their declared modes
    for param in &func.params {
        if let Some(name) = param.name {
            let extended = match param.mode {
                Mode::Zero => ExtendedMode::Affine, // Consumed/absent
                Mode::One => ExtendedMode::Linear,  // Use exactly once
                Mode::Omega => ExtendedMode::Unrestricted,
            };
            state.ctx.extend(LinEntry::new(name, param.mode, extended));
        }
    }

    // Check body if present
    if let Some(body) = &func.body {
        let _ = mode_check_expr(body, &mut state);

        // Check that linear parameters are consumed
        for param in &func.params {
            if let Some(name) = param.name {
                if param.mode == Mode::One {
                    let _ = check_consumed(name, func.span, &mut state);
                }
            }
        }
    }

    state.take_errors()
}

/// Mode check with a specific extended mode for pattern bindings
pub fn extend_pattern_with_mode(
    pattern: &Pattern,
    mode: Mode,
    extended: ExtendedMode,
    state: &mut ModeCheckState,
) {
    extend_pattern_with_mode_inner(&pattern.value, mode, extended, state);
}

fn extend_pattern_with_mode_inner(
    pattern: &Pattern_,
    mode: Mode,
    extended: ExtendedMode,
    state: &mut ModeCheckState,
) {
    match pattern {
        Pattern_::Var(var) => {
            state.ctx.extend(LinEntry::new(*var, mode, extended));
        }
        Pattern_::Wild | Pattern_::Lit(_) | Pattern_::Rest(None) => {}
        Pattern_::Rest(Some(var)) => {
            state.ctx.extend(LinEntry::new(*var, mode, extended));
        }
        Pattern_::As(inner, var) => {
            extend_pattern_with_mode(inner, mode, extended, state);
            state.ctx.extend(LinEntry::new(*var, mode, extended));
        }
        Pattern_::Tuple(pats) => {
            for p in pats {
                extend_pattern_with_mode(p, mode, extended, state);
            }
        }
        Pattern_::Struct { fields, .. } => {
            for (_, p) in fields {
                extend_pattern_with_mode(p, mode, extended, state);
            }
        }
        Pattern_::Variant { fields, .. } => {
            for p in fields {
                extend_pattern_with_mode(p, mode, extended, state);
            }
        }
        Pattern_::Or(left, _right) => {
            extend_pattern_with_mode(left, mode, extended, state);
        }
        Pattern_::Guard(inner, _) | Pattern_::Ref(inner) | Pattern_::Box(inner) => {
            extend_pattern_with_mode(inner, mode, extended, state);
        }
        // Type pattern may optionally bind a variable
        Pattern_::Type { binding: Some(var), .. } => {
            state.ctx.extend(LinEntry::new(*var, mode, extended));
        }
        Pattern_::Type { binding: None, .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{Expr_, Literal, WithLoc};
    use crate::types::{BrrrType, ParamType};
    use lasso::Rodeo;

    fn make_var_expr(rodeo: &mut Rodeo, name: &str) -> Expr {
        let var = rodeo.get_or_intern(name);
        WithLoc::synthetic(Expr_::Var(var))
    }

    fn make_lit_expr() -> Expr {
        WithLoc::synthetic(Expr_::Lit(Literal::i32(42)))
    }

    fn make_let_expr(var: VarId, init: Expr, body: Expr) -> Expr {
        WithLoc::synthetic(Expr_::Let {
            pattern: Pattern::var(var),
            ty: None,
            init: Box::new(init),
            body: Box::new(body),
        })
    }

    #[test]
    fn test_literal_passes() {
        let mut state = ModeCheckState::new();
        let expr = make_lit_expr();
        let result = mode_check_expr(&expr, &mut state);
        assert!(result.is_ok());
        assert!(state.errors.is_empty());
    }

    #[test]
    fn test_var_use_once_passes() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let mut state = ModeCheckState::new();
        state.ctx.extend(LinEntry::linear(x));

        let expr = make_var_expr(&mut rodeo, "x");
        let result = mode_check_expr(&expr, &mut state);

        assert!(result.is_ok());
        assert!(state.ctx.lookup(x).unwrap().used);
    }

    #[test]
    fn test_linear_used_twice_fails() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let mut state = ModeCheckState::new();
        state.ctx.extend(LinEntry::linear(x));

        // First use
        let expr1 = make_var_expr(&mut rodeo, "x");
        let _ = mode_check_expr(&expr1, &mut state);

        // Second use should fail
        let expr2 = make_var_expr(&mut rodeo, "x");
        let result = mode_check_expr(&expr2, &mut state);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            ModeError::LinearUsedMultipleTimes { .. }
        ));
    }

    #[test]
    fn test_unrestricted_used_multiple_times_passes() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let mut state = ModeCheckState::new();
        state.ctx.extend(LinEntry::unrestricted(x));

        // Multiple uses
        let expr = make_var_expr(&mut rodeo, "x");
        for _ in 0..3 {
            let result = mode_check_expr(&expr, &mut state);
            assert!(result.is_ok());
        }
    }

    #[test]
    fn test_let_binding_linear_consumed() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let init = make_lit_expr();
        let body = make_var_expr(&mut rodeo, "x");
        let expr = make_let_expr(x, init, body);

        let mut state = ModeCheckState::new();
        let result = mode_check_expr(&expr, &mut state);

        assert!(result.is_ok());
        assert!(state.errors.is_empty());
    }

    #[test]
    fn test_let_binding_linear_not_consumed_fails() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let init = make_lit_expr();
        // Body doesn't use x
        let body = make_lit_expr();
        let expr = make_let_expr(x, init, body);

        let mut state = ModeCheckState::new();
        let _ = mode_check_expr(&expr, &mut state);

        // Should have an error about x not being consumed
        assert!(!state.errors.is_empty());
        assert!(matches!(
            state.errors[0],
            ModeError::LinearNotConsumed { .. }
        ));
    }

    #[test]
    fn test_if_both_branches_use_linear() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");
        let cond = rodeo.get_or_intern("cond");

        let mut state = ModeCheckState::new();
        state.ctx.extend(LinEntry::linear(x));
        state.ctx.extend(LinEntry::unrestricted(cond));

        // if cond then x else x
        let cond_expr = make_var_expr(&mut rodeo, "cond");
        let then_expr = make_var_expr(&mut rodeo, "x");
        let else_expr = make_var_expr(&mut rodeo, "x");

        let expr = WithLoc::synthetic(Expr_::If(
            Box::new(cond_expr),
            Box::new(then_expr),
            Box::new(else_expr),
        ));

        let result = mode_check_expr(&expr, &mut state);
        assert!(result.is_ok());
    }

    #[test]
    fn test_function_def_mode_check() {
        let mut rodeo = Rodeo::default();
        let func_name = rodeo.get_or_intern("id");
        let x = rodeo.get_or_intern("x");

        let param = ParamType {
            name: Some(x),
            ty: BrrrType::BOOL,
            mode: Mode::One,
        };

        let body = WithLoc::synthetic(Expr_::Var(x));

        let func = FunctionDef::with_body(func_name, vec![param], BrrrType::BOOL, body);

        let errors = mode_check_function(&func);
        assert!(errors.is_empty());
    }

    #[test]
    fn test_function_def_linear_param_not_used() {
        let mut rodeo = Rodeo::default();
        let func_name = rodeo.get_or_intern("ignore");
        let x = rodeo.get_or_intern("x");

        let param = ParamType {
            name: Some(x),
            ty: BrrrType::BOOL,
            mode: Mode::One,
        };

        // Body doesn't use x
        let body = make_lit_expr();

        let func = FunctionDef::with_body(func_name, vec![param], BrrrType::BOOL, body);

        let errors = mode_check_function(&func);
        assert!(!errors.is_empty());
        assert!(matches!(errors[0], ModeError::LinearNotConsumed { .. }));
    }

    #[test]
    fn test_affine_can_be_unused() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let mut state = ModeCheckState::new();
        state.ctx.extend(LinEntry::affine(x));

        // Don't use x
        let expr = make_lit_expr();
        let _ = mode_check_expr(&expr, &mut state);

        // Affine can be dropped, so no error from usage
        // But check_consumed would pass for affine
        let _ = check_consumed(x, Range::SYNTHETIC, &mut state);
        assert!(state.errors.is_empty());
    }

    #[test]
    fn test_relevant_must_be_used() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let mut state = ModeCheckState::new();
        state.ctx.extend(LinEntry::relevant(x));

        // Don't use x
        let expr = make_lit_expr();
        let _ = mode_check_expr(&expr, &mut state);

        // Check consumption - should fail for relevant
        let result = check_consumed(x, Range::SYNTHETIC, &mut state);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ModeError::RelevantNotUsed { .. }));
    }

    #[test]
    fn test_relevant_can_be_used_multiple_times() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let mut state = ModeCheckState::new();
        state.ctx.extend(LinEntry::relevant(x));

        let expr = make_var_expr(&mut rodeo, "x");

        // First use
        let result1 = mode_check_expr(&expr, &mut state);
        assert!(result1.is_ok());

        // Second use - should also pass for relevant
        let result2 = mode_check_expr(&expr, &mut state);
        assert!(result2.is_ok());
    }

    #[test]
    fn test_mode_error_span() {
        use lasso::Key;

        let span = Range::new(
            crate::expr::Pos::new(0, 10, 5),
            crate::expr::Pos::new(0, 10, 15),
        );

        let error = ModeError::LinearUsedMultipleTimes {
            var: lasso::Spur::try_from_usize(0).unwrap(),
            span,
        };

        assert_eq!(error.span(), span);
    }
}
