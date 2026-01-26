//! Coeffect inference module
//!
//! Implements coeffect inference for tracking resource requirements in expressions.
//!
//! # Overview
//!
//! Coeffects are dual to effects: while effects track what a computation DOES to its
//! environment, coeffects track what a computation REQUIRES from its environment.
//!
//! This module infers three kinds of coeffects:
//! - **Liveness**: Whether a variable is needed (live) or not (dead)
//! - **Usage**: How many times a variable is used (zero, once, many)
//! - **Capabilities**: What flat capabilities are required (console, network, etc.)
//!
//! # Semiring Structure
//!
//! Coeffects form semirings with:
//! - Addition (join): parallel composition for branches
//! - Multiplication: sequential composition for sequencing
//!
//! # Inference Algorithm
//!
//! The algorithm traverses expressions and maintains a coeffect context (`CoeffectCtx`)
//! mapping each variable to its combined `CoeffectInfo`.
//!
//! Core rules:
//! - **Var**: Mark variable as Live, increment usage
//! - **Let**: Combine initializer and body coeffects
//! - **Lambda**: Abstract over free variable coeffects
//! - **If/Match**: Join branch coeffects (max usage, join liveness)
//! - **Call**: Multiply callee coeffects with argument coeffects
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::inference::coeffects::{infer_coeffects, CoeffectInferenceState};
//!
//! let mut state = CoeffectInferenceState::new();
//! let info = infer_coeffects(&expr, &mut state);
//!
//! if state.has_errors() {
//!     for error in &state.errors {
//!         println!("Coeffect error: {:?}", error);
//!     }
//! }
//! ```

use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::coeffects::{FlatCoeffect, Liveness, Usage, VarId};
use crate::expr::{
    CatchArm, Expr, Expr_, HandlerClause, MatchArm, Pattern, Pattern_, Range,
};

// ============================================================================
// Coeffect Information
// ============================================================================

/// Combined coeffect information for a variable.
///
/// Tracks all three dimensions of coeffect analysis:
/// - Liveness: is the variable needed?
/// - Usage: how many times is it used?
/// - Flat: what capabilities does accessing it require?
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoeffectInfo {
    /// Liveness status: Dead or Live
    pub liveness: Liveness,
    /// Usage count: Zero, One, or Many
    pub usage: Usage,
    /// Flat capability requirements
    pub flat: FlatCoeffect,
}

impl CoeffectInfo {
    /// Create a coeffect info representing no requirements (dead, unused, pure).
    #[must_use]
    pub fn zero() -> Self {
        Self {
            liveness: Liveness::Dead,
            usage: Usage::Zero,
            flat: FlatCoeffect::Pure,
        }
    }

    /// Create a coeffect info representing a single use.
    #[must_use]
    pub fn one() -> Self {
        Self {
            liveness: Liveness::Live,
            usage: Usage::One,
            flat: FlatCoeffect::Pure,
        }
    }

    /// Create a coeffect info from just liveness.
    #[must_use]
    pub fn from_liveness(liveness: Liveness) -> Self {
        Self {
            liveness,
            usage: if liveness.is_live() {
                Usage::One
            } else {
                Usage::Zero
            },
            flat: FlatCoeffect::Pure,
        }
    }

    /// Create a coeffect info from just usage.
    #[must_use]
    pub fn from_usage(usage: Usage) -> Self {
        Self {
            liveness: if usage.is_zero() {
                Liveness::Dead
            } else {
                Liveness::Live
            },
            usage,
            flat: FlatCoeffect::Pure,
        }
    }

    /// Create a coeffect info with a specific capability.
    #[must_use]
    pub fn with_capability(capability: FlatCoeffect) -> Self {
        Self {
            liveness: Liveness::Live,
            usage: Usage::One,
            flat: capability,
        }
    }

    /// Semiring addition (parallel composition / join).
    ///
    /// Used for branches: `if cond then e1 else e2` combines the coeffects
    /// of both branches since either may execute.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self {
            liveness: self.liveness.add(other.liveness),
            usage: self.usage.add(other.usage),
            flat: self.flat.clone().combine(other.flat.clone()),
        }
    }

    /// Semiring multiplication (sequential composition).
    ///
    /// Used for sequencing: `e1; e2` combines coeffects sequentially.
    /// If the first computation doesn't need a variable (Dead), the result
    /// doesn't either.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        Self {
            liveness: self.liveness.mul(other.liveness),
            usage: self.usage.mul(other.usage),
            flat: self.flat.clone().combine(other.flat.clone()),
        }
    }

    /// Join (least upper bound) in the coeffect lattice.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        Self {
            liveness: self.liveness.join(other.liveness),
            usage: self.usage.join(other.usage),
            flat: self.flat.clone().combine(other.flat.clone()),
        }
    }

    /// Check if this represents zero coeffect (not needed).
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.liveness.is_dead() && self.usage.is_zero()
    }

    /// Check if this represents exactly one use.
    #[must_use]
    pub fn is_one(&self) -> bool {
        self.liveness.is_live() && self.usage.is_one()
    }
}

impl Default for CoeffectInfo {
    fn default() -> Self {
        Self::zero()
    }
}

// ============================================================================
// Coeffect Context
// ============================================================================

/// Coeffect context mapping variables to their coeffect information.
pub type CoeffectCtx = HashMap<VarId, CoeffectInfo>;

/// Create an empty coeffect context.
#[must_use]
pub fn empty_coeffect_ctx() -> CoeffectCtx {
    HashMap::new()
}

/// Look up a variable in the coeffect context.
#[must_use]
pub fn lookup_coeffect(ctx: &CoeffectCtx, var: VarId) -> CoeffectInfo {
    ctx.get(&var).cloned().unwrap_or_default()
}

/// Set a variable's coeffect in the context.
pub fn set_coeffect(ctx: &mut CoeffectCtx, var: VarId, info: CoeffectInfo) {
    ctx.insert(var, info);
}

/// Mark a variable as live with a single use.
pub fn mark_used(ctx: &mut CoeffectCtx, var: VarId) {
    let current = ctx.get(&var).cloned().unwrap_or_default();
    ctx.insert(var, current.add(&CoeffectInfo::one()));
}

/// Remove a variable from the context, returning its coeffect.
pub fn remove_coeffect(ctx: &mut CoeffectCtx, var: VarId) -> Option<CoeffectInfo> {
    ctx.remove(&var)
}

// ============================================================================
// Context Operations
// ============================================================================

/// Join two coeffect contexts pointwise.
///
/// For each variable, takes the join of the coeffects from both contexts.
/// This is used for branches (if/match) where either path may execute.
#[must_use]
pub fn coeffect_ctx_join(ctx1: &CoeffectCtx, ctx2: &CoeffectCtx) -> CoeffectCtx {
    let mut result = ctx1.clone();
    for (&var, info) in ctx2 {
        let current = result.get(&var).cloned().unwrap_or_default();
        result.insert(var, current.join(info));
    }
    result
}

/// Sequence two coeffect contexts.
///
/// For each variable, combines coeffects using semiring multiplication.
/// This is used for sequential composition where both parts execute.
#[must_use]
pub fn coeffect_ctx_sequence(ctx1: &CoeffectCtx, ctx2: &CoeffectCtx) -> CoeffectCtx {
    let mut result = ctx1.clone();
    for (&var, info) in ctx2 {
        let current = result.get(&var).cloned().unwrap_or_default();
        // For sequencing, we add the usages (both parts contribute)
        result.insert(var, current.add(info));
    }
    result
}

/// Scale a coeffect context by a scalar coeffect.
///
/// Multiplies all coeffects in the context by the scalar.
/// Used for applying a surrounding context (e.g., a lambda called N times
/// scales its body's coeffects by N).
#[must_use]
pub fn scale_coeffect_ctx(scalar: &CoeffectInfo, ctx: &CoeffectCtx) -> CoeffectCtx {
    let mut result = HashMap::with_capacity(ctx.len());
    for (&var, info) in ctx {
        result.insert(var, scalar.mul(info));
    }
    result
}

/// Restrict a context to a set of variables (remove all others).
#[must_use]
pub fn restrict_coeffect_ctx(ctx: &CoeffectCtx, vars: &HashSet<VarId>) -> CoeffectCtx {
    ctx.iter()
        .filter(|(v, _)| vars.contains(v))
        .map(|(&v, i)| (v, i.clone()))
        .collect()
}

/// Extend context with a new variable, shadowing any previous binding.
pub fn extend_coeffect_ctx(ctx: &mut CoeffectCtx, var: VarId, info: CoeffectInfo) {
    ctx.insert(var, info);
}

// ============================================================================
// Coeffect Errors
// ============================================================================

/// Error during coeffect inference or checking.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CoeffectError {
    /// Attempted to use a variable that is dead (not live).
    DeadVariableUsed {
        /// The variable that was used
        var: VarId,
        /// Source location
        span: Range,
    },

    /// Usage bound exceeded for a variable.
    ///
    /// This occurs when a variable with a usage annotation (e.g., "use at most once")
    /// is used more times than allowed.
    UsageBoundExceeded {
        /// The variable
        var: VarId,
        /// The declared usage bound
        bound: Usage,
        /// Actual usage count
        actual: usize,
        /// Source location
        span: Range,
    },

    /// Required capability not available.
    ///
    /// The computation requires a capability that is not provided in the
    /// available capabilities set.
    MissingCapability {
        /// The required capability
        required: FlatCoeffect,
        /// Source location
        span: Range,
    },

    /// Variable not found in coeffect context.
    UnboundVariable {
        /// The variable
        var: VarId,
        /// Source location
        span: Range,
    },

    /// Inconsistent usage between branches.
    ///
    /// In if/match, some variables have different usage patterns in different
    /// branches, which may indicate a problem.
    InconsistentBranchUsage {
        /// Variables with inconsistent usage
        vars: Vec<VarId>,
        /// Source location
        span: Range,
    },
}

impl CoeffectError {
    /// Get the source span where this error occurred.
    #[must_use]
    pub fn span(&self) -> Range {
        match self {
            Self::DeadVariableUsed { span, .. }
            | Self::UsageBoundExceeded { span, .. }
            | Self::MissingCapability { span, .. }
            | Self::UnboundVariable { span, .. }
            | Self::InconsistentBranchUsage { span, .. } => *span,
        }
    }

    /// Get the variables involved in this error.
    #[must_use]
    pub fn vars(&self) -> Vec<VarId> {
        match self {
            Self::DeadVariableUsed { var, .. }
            | Self::UsageBoundExceeded { var, .. }
            | Self::UnboundVariable { var, .. } => vec![*var],
            Self::MissingCapability { .. } => vec![],
            Self::InconsistentBranchUsage { vars, .. } => vars.clone(),
        }
    }

    /// Format as a diagnostic message.
    #[must_use]
    pub fn format(&self) -> String {
        match self {
            Self::DeadVariableUsed { var, .. } => {
                format!("variable {:?} is dead but was used", var)
            }
            Self::UsageBoundExceeded {
                var,
                bound,
                actual,
                ..
            } => {
                format!(
                    "variable {:?} exceeded usage bound {:?} (used {} times)",
                    var, bound, actual
                )
            }
            Self::MissingCapability { required, .. } => {
                format!("missing required capability: {:?}", required)
            }
            Self::UnboundVariable { var, .. } => {
                format!("variable {:?} not found in coeffect context", var)
            }
            Self::InconsistentBranchUsage { vars, .. } => {
                format!("inconsistent usage for variables: {:?}", vars)
            }
        }
    }
}

impl std::fmt::Display for CoeffectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format())
    }
}

impl std::error::Error for CoeffectError {}

// ============================================================================
// Inference State
// ============================================================================

/// State maintained during coeffect inference.
///
/// Tracks the coeffect context, accumulated errors, and available capabilities.
#[derive(Debug, Clone)]
pub struct CoeffectInferenceState {
    /// Current coeffect context mapping variables to their coeffects
    pub ctx: CoeffectCtx,
    /// Accumulated errors during inference
    pub errors: Vec<CoeffectError>,
    /// Available capabilities in the current scope
    pub available_capabilities: HashSet<FlatCoeffect>,
    /// Usage bounds declared for variables
    pub usage_bounds: HashMap<VarId, Usage>,
}

impl CoeffectInferenceState {
    /// Create a new empty inference state.
    #[must_use]
    pub fn new() -> Self {
        Self {
            ctx: empty_coeffect_ctx(),
            errors: Vec::new(),
            available_capabilities: HashSet::new(),
            usage_bounds: HashMap::new(),
        }
    }

    /// Create a state with a pre-initialized context.
    #[must_use]
    pub fn with_context(ctx: CoeffectCtx) -> Self {
        Self {
            ctx,
            errors: Vec::new(),
            available_capabilities: HashSet::new(),
            usage_bounds: HashMap::new(),
        }
    }

    /// Add a capability to the available set.
    pub fn add_capability(&mut self, cap: FlatCoeffect) {
        self.available_capabilities.insert(cap);
    }

    /// Remove a capability from the available set.
    pub fn remove_capability(&mut self, cap: &FlatCoeffect) {
        self.available_capabilities.remove(cap);
    }

    /// Check if a capability is available.
    #[must_use]
    pub fn has_capability(&self, cap: &FlatCoeffect) -> bool {
        if cap.is_pure() {
            return true;
        }
        self.available_capabilities.contains(cap)
    }

    /// Set a usage bound for a variable.
    pub fn set_usage_bound(&mut self, var: VarId, bound: Usage) {
        self.usage_bounds.insert(var, bound);
    }

    /// Get the usage bound for a variable.
    #[must_use]
    pub fn get_usage_bound(&self, var: VarId) -> Option<Usage> {
        self.usage_bounds.get(&var).copied()
    }

    /// Add an error.
    pub fn add_error(&mut self, error: CoeffectError) {
        self.errors.push(error);
    }

    /// Check if any errors occurred.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get the error count.
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Take all errors, leaving the list empty.
    pub fn take_errors(&mut self) -> Vec<CoeffectError> {
        std::mem::take(&mut self.errors)
    }

    /// Lookup and mark a variable as used.
    ///
    /// The span parameter is retained for future error reporting when
    /// usage bounds are exceeded.
    pub fn use_variable(&mut self, var: VarId, _span: Range) -> CoeffectInfo {
        mark_used(&mut self.ctx, var);
        lookup_coeffect(&self.ctx, var)
    }

    /// Create a child state for a nested scope.
    #[must_use]
    pub fn child(&self) -> Self {
        Self {
            ctx: self.ctx.clone(),
            errors: Vec::new(),
            available_capabilities: self.available_capabilities.clone(),
            usage_bounds: self.usage_bounds.clone(),
        }
    }

    /// Merge errors from a child state.
    pub fn merge_errors(&mut self, child: &Self) {
        self.errors.extend(child.errors.iter().cloned());
    }
}

impl Default for CoeffectInferenceState {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Capability Checking
// ============================================================================

/// Check if a required capability is available.
///
/// Returns `true` if the capability is satisfied, `false` otherwise.
#[must_use]
pub fn check_capability(required: &FlatCoeffect, available: &HashSet<FlatCoeffect>) -> bool {
    match required {
        FlatCoeffect::Pure => true,
        FlatCoeffect::Many(caps) => caps.iter().all(|c| check_capability(c, available)),
        _ => available.contains(required),
    }
}

/// Require a capability, recording an error if not available.
pub fn require_capability(
    required: FlatCoeffect,
    span: Range,
    state: &mut CoeffectInferenceState,
) {
    if !check_capability(&required, &state.available_capabilities) {
        state.add_error(CoeffectError::MissingCapability { required, span });
    }
}

// ============================================================================
// Core Inference Function
// ============================================================================

/// Infer coeffects for an expression.
///
/// This is the core coeffect inference function. It traverses the expression
/// tree and computes the combined coeffect information.
///
/// # Arguments
///
/// * `expr` - The expression to analyze
/// * `state` - Mutable reference to the inference state
///
/// # Returns
///
/// The combined coeffect information for the expression.
pub fn infer_coeffects(expr: &Expr, state: &mut CoeffectInferenceState) -> CoeffectInfo {
    match &expr.value {
        // === Literals and globals: no coeffect requirements ===
        Expr_::Lit(_) | Expr_::Global(_) | Expr_::Hole | Expr_::Error(_) => CoeffectInfo::zero(),

        // === Variable reference: mark as used ===
        Expr_::Var(var) => {
            state.use_variable(*var, expr.range)
        }

        // === Unary operations ===
        Expr_::Unary(_, operand) => infer_coeffects(operand, state),

        // === Binary operations ===
        Expr_::Binary(_, left, right) => {
            let left_info = infer_coeffects(left, state);
            let right_info = infer_coeffects(right, state);
            // Both operands are evaluated, so add their coeffects
            left_info.add(&right_info)
        }

        // === Function call ===
        Expr_::Call(func, args) => {
            let func_info = infer_coeffects(func, state);
            let mut result = func_info;
            for arg in args {
                let arg_info = infer_coeffects(arg, state);
                result = result.add(&arg_info);
            }
            result
        }

        // === Method call ===
        Expr_::MethodCall(receiver, _method, args) => {
            let recv_info = infer_coeffects(receiver, state);
            let mut result = recv_info;
            for arg in args {
                let arg_info = infer_coeffects(arg, state);
                result = result.add(&arg_info);
            }
            result
        }

        // === Tuples and arrays ===
        Expr_::Tuple(elems) | Expr_::Array(elems) => {
            let mut result = CoeffectInfo::zero();
            for elem in elems {
                let elem_info = infer_coeffects(elem, state);
                result = result.add(&elem_info);
            }
            result
        }

        // === Struct construction ===
        Expr_::Struct { fields, .. } => {
            let mut result = CoeffectInfo::zero();
            for (_, field_expr) in fields {
                let field_info = infer_coeffects(field_expr, state);
                result = result.add(&field_info);
            }
            result
        }

        // === Enum variant construction ===
        Expr_::Variant { fields, .. } => {
            let mut result = CoeffectInfo::zero();
            for field in fields {
                let field_info = infer_coeffects(field, state);
                result = result.add(&field_info);
            }
            result
        }

        // === Field access ===
        Expr_::Field(base, _field) => infer_coeffects(base, state),

        // === Index access ===
        Expr_::Index(base, index) => {
            let base_info = infer_coeffects(base, state);
            let index_info = infer_coeffects(index, state);
            base_info.add(&index_info)
        }

        // === Tuple projection ===
        Expr_::TupleProj(base, _idx) => infer_coeffects(base, state),

        // === If-then-else: join branch coeffects ===
        Expr_::If(cond, then_branch, else_branch) => {
            let cond_info = infer_coeffects(cond, state);
            infer_if_coeffects(then_branch, else_branch, expr.range, state, cond_info)
        }

        // === Pattern match ===
        Expr_::Match(scrutinee, arms) => {
            let scrutinee_info = infer_coeffects(scrutinee, state);
            let arms_info = infer_match_coeffects(arms, expr.range, state);
            scrutinee_info.add(&arms_info)
        }

        // === Loops ===
        Expr_::Loop { body, .. } => {
            // Loops may execute body many times - scale by Many
            let body_info = infer_coeffects(body, state);
            CoeffectInfo::from_usage(Usage::Many).mul(&body_info)
        }

        Expr_::While { cond, body, .. } => {
            let cond_info = infer_coeffects(cond, state);
            let body_info = infer_coeffects(body, state);
            // While may execute 0+ times, join with zero
            let loop_info = CoeffectInfo::from_usage(Usage::Many).mul(&body_info);
            cond_info.add(&loop_info)
        }

        Expr_::For { var, iter, body, .. } => {
            let iter_info = infer_coeffects(iter, state);

            // Bind loop variable
            extend_coeffect_ctx(&mut state.ctx, *var, CoeffectInfo::zero());
            let body_info = infer_coeffects(body, state);
            remove_coeffect(&mut state.ctx, *var);

            // Loop body may execute many times
            let loop_info = CoeffectInfo::from_usage(Usage::Many).mul(&body_info);
            iter_info.add(&loop_info)
        }

        // === Control flow ===
        Expr_::Break { value, .. } => {
            if let Some(val) = value {
                infer_coeffects(val, state)
            } else {
                CoeffectInfo::zero()
            }
        }

        Expr_::Continue { .. } => CoeffectInfo::zero(),

        Expr_::Return(value) => {
            if let Some(val) = value {
                infer_coeffects(val, state)
            } else {
                CoeffectInfo::zero()
            }
        }

        // === Let binding ===
        Expr_::Let { pattern, init, body, .. } => {
            let init_info = infer_coeffects(init, state);
            infer_let_coeffects(pattern, body, state, init_info)
        }

        // === Mutable let binding ===
        Expr_::LetMut { var, init, body, .. } => {
            let init_info = infer_coeffects(init, state);

            // Bind variable
            extend_coeffect_ctx(&mut state.ctx, *var, CoeffectInfo::zero());
            let body_info = infer_coeffects(body, state);
            let var_info = remove_coeffect(&mut state.ctx, *var).unwrap_or_default();

            init_info.add(&body_info).add(&var_info)
        }

        // === Assignment ===
        Expr_::Assign(target, value) => {
            let target_info = infer_coeffects(target, state);
            let value_info = infer_coeffects(value, state);
            target_info.add(&value_info)
        }

        // === Lambda ===
        Expr_::Lambda { params, body } => infer_lambda_coeffects(params, body, state),

        // === Closure ===
        Expr_::Closure { params, captures, body } => {
            // Captures are used when the closure is created
            for cap in captures {
                state.use_variable(*cap, expr.range);
            }
            infer_lambda_coeffects(params, body, state)
        }

        // === Memory operations ===
        Expr_::Box(inner)
        | Expr_::Deref(inner)
        | Expr_::Borrow(inner)
        | Expr_::BorrowMut(inner)
        | Expr_::Move(inner)
        | Expr_::Drop(inner) => infer_coeffects(inner, state),

        // === Exception handling ===
        Expr_::Throw(inner) => infer_coeffects(inner, state),

        Expr_::Try { body, catches, finally } => {
            let body_info = infer_coeffects(body, state);
            let mut catch_info = CoeffectInfo::zero();
            for catch in catches {
                let c_info = infer_catch_coeffects(catch, state);
                catch_info = catch_info.join(&c_info);
            }
            let finally_info = if let Some(fin) = finally {
                infer_coeffects(fin, state)
            } else {
                CoeffectInfo::zero()
            };
            body_info.add(&catch_info).add(&finally_info)
        }

        // === Async/Concurrency ===
        Expr_::Await(inner) | Expr_::Yield(inner) | Expr_::Async(inner) | Expr_::Spawn(inner) => {
            infer_coeffects(inner, state)
        }

        // === Effect handling ===
        Expr_::Handle(body, handler) => {
            let body_info = infer_coeffects(body, state);
            let mut handler_info = CoeffectInfo::zero();
            for clause in &handler.clauses {
                let c_info = infer_handler_clause_coeffects(clause, state);
                handler_info = handler_info.add(&c_info);
            }
            if let Some((var, return_body)) = &handler.return_clause {
                extend_coeffect_ctx(&mut state.ctx, *var, CoeffectInfo::zero());
                let ret_info = infer_coeffects(return_body, state);
                remove_coeffect(&mut state.ctx, *var);
                handler_info = handler_info.add(&ret_info);
            }
            body_info.add(&handler_info)
        }

        Expr_::Perform(_op, args) => {
            let mut result = CoeffectInfo::zero();
            for arg in args {
                let arg_info = infer_coeffects(arg, state);
                result = result.add(&arg_info);
            }
            result
        }

        Expr_::Resume { var, value } => {
            let var_info = state.use_variable(*var, expr.range);
            let value_info = infer_coeffects(value, state);
            var_info.add(&value_info)
        }

        // === Delimited continuations ===
        Expr_::Reset { body, .. } => infer_coeffects(body, state),

        Expr_::Shift { var, body, .. } => {
            // Continuation variable is bound in shift body
            extend_coeffect_ctx(&mut state.ctx, *var, CoeffectInfo::zero());
            let body_info = infer_coeffects(body, state);
            let var_info = remove_coeffect(&mut state.ctx, *var).unwrap_or_default();
            body_info.add(&var_info)
        }

        // === Type operations ===
        Expr_::As(inner, _) | Expr_::Is(inner, _) => infer_coeffects(inner, state),

        Expr_::Sizeof(_) | Expr_::Alignof(_) => CoeffectInfo::zero(),

        // === Blocks ===
        Expr_::Block(stmts) => {
            let mut result = CoeffectInfo::zero();
            for stmt in stmts {
                let stmt_info = infer_coeffects(stmt, state);
                result = result.add(&stmt_info);
            }
            result
        }

        Expr_::Seq(first, second) => {
            let first_info = infer_coeffects(first, state);
            let second_info = infer_coeffects(second, state);
            first_info.add(&second_info)
        }

        Expr_::Unsafe(inner) => infer_coeffects(inner, state),

        // === Gradual typing ===
        Expr_::GradualCast { expr, .. } => infer_coeffects(expr, state),

        // === Control flow labels ===
        Expr_::Goto { .. } => CoeffectInfo::zero(),
        Expr_::Labeled { body, .. } => infer_coeffects(body, state),
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Infer coeffects for if-then-else expression.
fn infer_if_coeffects(
    then_branch: &Expr,
    else_branch: &Expr,
    span: Range,
    state: &mut CoeffectInferenceState,
    cond_info: CoeffectInfo,
) -> CoeffectInfo {
    // Create child states for branches
    let mut then_state = state.child();
    let then_info = infer_coeffects(then_branch, &mut then_state);

    let mut else_state = state.child();
    let else_info = infer_coeffects(else_branch, &mut else_state);

    // Merge errors
    state.merge_errors(&then_state);
    state.merge_errors(&else_state);

    // Join branch contexts
    state.ctx = coeffect_ctx_join(&then_state.ctx, &else_state.ctx);

    // Check for inconsistent usage
    let inconsistent = find_inconsistent_usage(&then_state.ctx, &else_state.ctx);
    if !inconsistent.is_empty() {
        state.add_error(CoeffectError::InconsistentBranchUsage {
            vars: inconsistent,
            span,
        });
    }

    // Join the branch coeffects (since either may execute)
    cond_info.add(&then_info.join(&else_info))
}

/// Infer coeffects for match arms.
fn infer_match_coeffects(
    arms: &[MatchArm],
    span: Range,
    state: &mut CoeffectInferenceState,
) -> CoeffectInfo {
    if arms.is_empty() {
        return CoeffectInfo::zero();
    }

    let mut arm_infos = Vec::with_capacity(arms.len());
    let mut arm_contexts = Vec::with_capacity(arms.len());

    for arm in arms {
        let mut arm_state = state.child();

        // Bind pattern variables
        extend_pattern_bindings(&arm.pattern, &mut arm_state);

        // Check guard
        let guard_info = if let Some(guard) = &arm.guard {
            infer_coeffects(guard, &mut arm_state)
        } else {
            CoeffectInfo::zero()
        };

        // Check body
        let body_info = infer_coeffects(&arm.body, &mut arm_state);

        // Remove pattern bindings
        remove_pattern_bindings(&arm.pattern, &mut arm_state);

        state.merge_errors(&arm_state);
        arm_infos.push(guard_info.add(&body_info));
        arm_contexts.push(arm_state.ctx);
    }

    // Join all arm contexts
    if let Some(first) = arm_contexts.first() {
        let mut joined = first.clone();
        for ctx in arm_contexts.iter().skip(1) {
            joined = coeffect_ctx_join(&joined, ctx);
        }
        state.ctx = joined;
    }

    // Check for inconsistencies
    if arm_contexts.len() >= 2 {
        for i in 1..arm_contexts.len() {
            let inconsistent = find_inconsistent_usage(&arm_contexts[0], &arm_contexts[i]);
            if !inconsistent.is_empty() {
                state.add_error(CoeffectError::InconsistentBranchUsage {
                    vars: inconsistent,
                    span,
                });
            }
        }
    }

    // Join all arm coeffects
    let mut result = arm_infos.first().cloned().unwrap_or_default();
    for info in arm_infos.iter().skip(1) {
        result = result.join(info);
    }
    result
}

/// Find variables with inconsistent usage between two contexts.
fn find_inconsistent_usage(ctx1: &CoeffectCtx, ctx2: &CoeffectCtx) -> Vec<VarId> {
    let mut inconsistent = Vec::new();

    for (&var, info1) in ctx1 {
        if let Some(info2) = ctx2.get(&var) {
            // Check if usage differs significantly
            // (One in one branch, Many in another is inconsistent)
            if info1.usage != info2.usage && !info1.usage.is_zero() && !info2.usage.is_zero() {
                inconsistent.push(var);
            }
        }
    }

    inconsistent
}

/// Infer coeffects for let binding.
fn infer_let_coeffects(
    pattern: &Pattern,
    body: &Expr,
    state: &mut CoeffectInferenceState,
    init_info: CoeffectInfo,
) -> CoeffectInfo {
    // Bind pattern variables
    extend_pattern_bindings(pattern, state);

    // Infer body coeffects
    let body_info = infer_coeffects(body, state);

    // Get coeffects of bound variables before removing them
    let mut bound_info = CoeffectInfo::zero();
    for var in pattern.value.bound_vars() {
        if let Some(var_info) = remove_coeffect(&mut state.ctx, var) {
            bound_info = bound_info.add(&var_info);
        }
    }

    init_info.add(&body_info)
}

/// Infer coeffects for lambda expression.
fn infer_lambda_coeffects(
    params: &[(VarId, crate::types::BrrrType)],
    body: &Expr,
    state: &mut CoeffectInferenceState,
) -> CoeffectInfo {
    // Bind parameters
    for (var, _ty) in params {
        extend_coeffect_ctx(&mut state.ctx, *var, CoeffectInfo::zero());
    }

    // Infer body coeffects
    let body_info = infer_coeffects(body, state);

    // Remove parameters and collect their usage
    let mut param_info = CoeffectInfo::zero();
    for (var, _ty) in params {
        if let Some(var_info) = remove_coeffect(&mut state.ctx, *var) {
            param_info = param_info.add(&var_info);
        }
    }

    body_info
}

/// Infer coeffects for catch arm.
fn infer_catch_coeffects(catch: &CatchArm, state: &mut CoeffectInferenceState) -> CoeffectInfo {
    // Bind pattern variables
    extend_pattern_bindings(&catch.pattern, state);

    // Infer body coeffects
    let body_info = infer_coeffects(&catch.body, state);

    // Remove pattern bindings
    remove_pattern_bindings(&catch.pattern, state);

    body_info
}

/// Infer coeffects for handler clause.
fn infer_handler_clause_coeffects(
    clause: &HandlerClause,
    state: &mut CoeffectInferenceState,
) -> CoeffectInfo {
    // Bind parameters
    for var in &clause.params {
        extend_coeffect_ctx(&mut state.ctx, *var, CoeffectInfo::zero());
    }

    // Bind continuation
    extend_coeffect_ctx(&mut state.ctx, clause.continuation, CoeffectInfo::zero());

    // Infer body coeffects
    let body_info = infer_coeffects(&clause.body, state);

    // Remove bindings
    for var in &clause.params {
        remove_coeffect(&mut state.ctx, *var);
    }
    remove_coeffect(&mut state.ctx, clause.continuation);

    body_info
}

/// Extend context with pattern bindings.
fn extend_pattern_bindings(pattern: &Pattern, state: &mut CoeffectInferenceState) {
    extend_pattern_bindings_inner(&pattern.value, state);
}

fn extend_pattern_bindings_inner(pattern: &Pattern_, state: &mut CoeffectInferenceState) {
    match pattern {
        Pattern_::Var(var) => {
            extend_coeffect_ctx(&mut state.ctx, *var, CoeffectInfo::zero());
        }
        Pattern_::Wild | Pattern_::Lit(_) | Pattern_::Rest(None) => {}
        Pattern_::Rest(Some(var)) => {
            extend_coeffect_ctx(&mut state.ctx, *var, CoeffectInfo::zero());
        }
        Pattern_::As(inner, var) => {
            extend_pattern_bindings(inner, state);
            extend_coeffect_ctx(&mut state.ctx, *var, CoeffectInfo::zero());
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
            extend_pattern_bindings(left, state);
        }
        Pattern_::Guard(inner, _) | Pattern_::Ref(inner) | Pattern_::Box(inner) => {
            extend_pattern_bindings(inner, state);
        }
        // Type pattern may optionally bind a variable
        Pattern_::Type { binding: Some(var), .. } => {
            extend_coeffect_ctx(&mut state.ctx, *var, CoeffectInfo::zero());
        }
        Pattern_::Type { binding: None, .. } => {}
    }
}

/// Remove pattern bindings from context.
fn remove_pattern_bindings(pattern: &Pattern, state: &mut CoeffectInferenceState) {
    remove_pattern_bindings_inner(&pattern.value, state);
}

fn remove_pattern_bindings_inner(pattern: &Pattern_, state: &mut CoeffectInferenceState) {
    match pattern {
        Pattern_::Var(var) | Pattern_::Rest(Some(var)) => {
            remove_coeffect(&mut state.ctx, *var);
        }
        Pattern_::Wild | Pattern_::Lit(_) | Pattern_::Rest(None) => {}
        Pattern_::As(inner, var) => {
            remove_pattern_bindings(inner, state);
            remove_coeffect(&mut state.ctx, *var);
        }
        Pattern_::Tuple(pats) => {
            for p in pats {
                remove_pattern_bindings(p, state);
            }
        }
        Pattern_::Struct { fields, .. } => {
            for (_, p) in fields {
                remove_pattern_bindings(p, state);
            }
        }
        Pattern_::Variant { fields, .. } => {
            for p in fields {
                remove_pattern_bindings(p, state);
            }
        }
        Pattern_::Or(left, _right) => {
            remove_pattern_bindings(left, state);
        }
        Pattern_::Guard(inner, _) | Pattern_::Ref(inner) | Pattern_::Box(inner) => {
            remove_pattern_bindings(inner, state);
        }
        // Type pattern may optionally bind a variable
        Pattern_::Type { binding: Some(var), .. } => {
            remove_coeffect(&mut state.ctx, *var);
        }
        Pattern_::Type { binding: None, .. } => {}
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{Literal, WithLoc};
    use lasso::{Key, Rodeo};

    fn var(n: usize) -> VarId {
        lasso::Spur::try_from_usize(n).unwrap()
    }

    fn make_var_expr(rodeo: &mut Rodeo, name: &str) -> Expr {
        let v = rodeo.get_or_intern(name);
        WithLoc::synthetic(Expr_::Var(v))
    }

    fn make_lit_expr() -> Expr {
        WithLoc::synthetic(Expr_::Lit(Literal::i32(42)))
    }

    // ========== CoeffectInfo Tests ==========

    #[test]
    fn test_coeffect_info_zero() {
        let zero = CoeffectInfo::zero();
        assert!(zero.is_zero());
        assert!(zero.liveness.is_dead());
        assert!(zero.usage.is_zero());
        assert!(zero.flat.is_pure());
    }

    #[test]
    fn test_coeffect_info_one() {
        let one = CoeffectInfo::one();
        assert!(one.is_one());
        assert!(one.liveness.is_live());
        assert!(one.usage.is_one());
    }

    #[test]
    fn test_coeffect_info_add() {
        let zero = CoeffectInfo::zero();
        let one = CoeffectInfo::one();

        // zero + one = one
        let result = zero.add(&one);
        assert!(result.liveness.is_live());
        assert!(result.usage.is_one());

        // one + one = many
        let result = one.add(&one);
        assert!(result.liveness.is_live());
        assert!(result.usage.is_many());
    }

    #[test]
    fn test_coeffect_info_mul() {
        let zero = CoeffectInfo::zero();
        let one = CoeffectInfo::one();

        // zero * one = zero (dead annihilates)
        let result = zero.mul(&one);
        assert!(result.liveness.is_dead());

        // one * one = one
        let result = one.mul(&one);
        assert!(result.is_one());
    }

    #[test]
    fn test_coeffect_info_with_capability() {
        let info = CoeffectInfo::with_capability(FlatCoeffect::Network);
        assert!(info.flat.requires(&FlatCoeffect::Network));
    }

    // ========== Context Tests ==========

    #[test]
    fn test_coeffect_ctx_operations() {
        let mut ctx = empty_coeffect_ctx();
        let x = var(1);
        let y = var(2);

        set_coeffect(&mut ctx, x, CoeffectInfo::one());
        set_coeffect(&mut ctx, y, CoeffectInfo::zero());

        assert!(lookup_coeffect(&ctx, x).is_one());
        assert!(lookup_coeffect(&ctx, y).is_zero());

        mark_used(&mut ctx, x);
        assert!(lookup_coeffect(&ctx, x).usage.is_many());
    }

    #[test]
    fn test_coeffect_ctx_join() {
        let mut ctx1 = empty_coeffect_ctx();
        let mut ctx2 = empty_coeffect_ctx();

        let x = var(1);
        let y = var(2);
        let z = var(3);

        set_coeffect(&mut ctx1, x, CoeffectInfo::one());
        set_coeffect(&mut ctx1, y, CoeffectInfo::zero());

        set_coeffect(&mut ctx2, y, CoeffectInfo::one());
        set_coeffect(&mut ctx2, z, CoeffectInfo::one());

        let joined = coeffect_ctx_join(&ctx1, &ctx2);

        // x: one (from ctx1)
        assert!(lookup_coeffect(&joined, x).is_one());
        // y: zero join one = one
        assert!(lookup_coeffect(&joined, y).is_one());
        // z: one (from ctx2)
        assert!(lookup_coeffect(&joined, z).is_one());
    }

    #[test]
    fn test_coeffect_ctx_sequence() {
        let mut ctx1 = empty_coeffect_ctx();
        let mut ctx2 = empty_coeffect_ctx();

        let x = var(1);

        set_coeffect(&mut ctx1, x, CoeffectInfo::one());
        set_coeffect(&mut ctx2, x, CoeffectInfo::one());

        let sequenced = coeffect_ctx_sequence(&ctx1, &ctx2);

        // x: one + one = many
        assert!(lookup_coeffect(&sequenced, x).usage.is_many());
    }

    // ========== Capability Tests ==========

    #[test]
    fn test_check_capability() {
        let mut available = HashSet::new();
        available.insert(FlatCoeffect::Console);
        available.insert(FlatCoeffect::Network);

        assert!(check_capability(&FlatCoeffect::Pure, &available));
        assert!(check_capability(&FlatCoeffect::Console, &available));
        assert!(check_capability(&FlatCoeffect::Network, &available));
        assert!(!check_capability(&FlatCoeffect::FileSystem, &available));
    }

    #[test]
    fn test_require_capability_error() {
        let mut state = CoeffectInferenceState::new();
        state.add_capability(FlatCoeffect::Console);

        // This should not add an error
        require_capability(FlatCoeffect::Console, Range::SYNTHETIC, &mut state);
        assert!(!state.has_errors());

        // This should add an error
        require_capability(FlatCoeffect::Network, Range::SYNTHETIC, &mut state);
        assert!(state.has_errors());
        assert_eq!(state.error_count(), 1);
    }

    // ========== Inference Tests ==========

    #[test]
    fn test_infer_literal() {
        let mut state = CoeffectInferenceState::new();
        let expr = make_lit_expr();
        let info = infer_coeffects(&expr, &mut state);

        assert!(info.is_zero());
        assert!(!state.has_errors());
    }

    #[test]
    fn test_infer_variable() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let mut state = CoeffectInferenceState::new();
        extend_coeffect_ctx(&mut state.ctx, x, CoeffectInfo::zero());

        let expr = make_var_expr(&mut rodeo, "x");
        let _ = infer_coeffects(&expr, &mut state);

        // Variable should be marked as used
        let var_info = lookup_coeffect(&state.ctx, x);
        assert!(var_info.liveness.is_live());
        assert!(var_info.usage.is_one());
    }

    #[test]
    fn test_infer_binary() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");
        let y = rodeo.get_or_intern("y");

        let mut state = CoeffectInferenceState::new();
        extend_coeffect_ctx(&mut state.ctx, x, CoeffectInfo::zero());
        extend_coeffect_ctx(&mut state.ctx, y, CoeffectInfo::zero());

        let left = make_var_expr(&mut rodeo, "x");
        let right = make_var_expr(&mut rodeo, "y");
        let expr = WithLoc::synthetic(Expr_::Binary(
            crate::expr::BinaryOp::Add,
            Box::new(left),
            Box::new(right),
        ));

        let info = infer_coeffects(&expr, &mut state);

        // Both variables used
        assert!(lookup_coeffect(&state.ctx, x).usage.is_one());
        assert!(lookup_coeffect(&state.ctx, y).usage.is_one());

        // Result has combined coeffects
        assert!(info.liveness.is_live());
    }

    #[test]
    fn test_infer_if() {
        let mut rodeo = Rodeo::default();
        let cond_var = rodeo.get_or_intern("cond");
        let x = rodeo.get_or_intern("x");

        let mut state = CoeffectInferenceState::new();
        extend_coeffect_ctx(&mut state.ctx, cond_var, CoeffectInfo::zero());
        extend_coeffect_ctx(&mut state.ctx, x, CoeffectInfo::zero());

        // if cond then x else x
        let cond_expr = make_var_expr(&mut rodeo, "cond");
        let then_expr = make_var_expr(&mut rodeo, "x");
        let else_expr = make_var_expr(&mut rodeo, "x");

        let expr = WithLoc::synthetic(Expr_::If(
            Box::new(cond_expr),
            Box::new(then_expr),
            Box::new(else_expr),
        ));

        let _ = infer_coeffects(&expr, &mut state);

        // Both branches use x, so usage should be joined (one, since same in both)
        let x_info = lookup_coeffect(&state.ctx, x);
        assert!(x_info.liveness.is_live());
    }

    #[test]
    fn test_infer_let() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let init = make_lit_expr();
        let body = make_var_expr(&mut rodeo, "x");
        let pattern = crate::expr::Pattern::var(x);

        let expr = WithLoc::synthetic(Expr_::Let {
            pattern,
            ty: None,
            init: Box::new(init),
            body: Box::new(body),
        });

        let mut state = CoeffectInferenceState::new();
        let _ = infer_coeffects(&expr, &mut state);

        // x should be removed from context after let
        assert!(state.ctx.get(&x).is_none());
    }

    // ========== Error Tests ==========

    #[test]
    fn test_coeffect_error_span() {
        let span = Range::new(
            crate::expr::Pos::new(0, 10, 5),
            crate::expr::Pos::new(0, 10, 15),
        );

        let error = CoeffectError::DeadVariableUsed { var: var(1), span };
        assert_eq!(error.span(), span);
    }

    #[test]
    fn test_coeffect_error_format() {
        let error = CoeffectError::MissingCapability {
            required: FlatCoeffect::Network,
            span: Range::SYNTHETIC,
        };
        let msg = error.format();
        assert!(msg.contains("Network"));
    }

    #[test]
    fn test_state_child() {
        let mut state = CoeffectInferenceState::new();
        state.add_capability(FlatCoeffect::Console);
        extend_coeffect_ctx(&mut state.ctx, var(1), CoeffectInfo::one());

        let child = state.child();

        // Child inherits capabilities
        assert!(child.has_capability(&FlatCoeffect::Console));

        // Child has copied context
        assert!(lookup_coeffect(&child.ctx, var(1)).is_one());

        // Child has empty errors
        assert!(!child.has_errors());
    }
}
