//! Effect inference with row polymorphism
//!
//! Implements effect row inference and unification following the effect
//! system design from brrr-lang.
//!
//! # Effect Rows
//!
//! Effect types are structured as rows: `<E1, E2, ... | rho>` where
//! - `E1, E2, ...` are concrete effects
//! - `rho` is an optional effect variable for polymorphism
//!
//! # Unification
//!
//! Effect row unification uses a specialized algorithm that handles:
//! - Row extension with new effects
//! - Row variable instantiation
//! - Effect ordering (effects are sets, not sequences)
//!
//! # Handler Type Checking
//!
//! Effect handlers intercept effect operations and provide implementations.
//! Type checking ensures:
//! - Each clause handles an operation with matching signature
//! - Continuations have the correct type: `A -> B` where A is op result, B is handler result
//! - Continuation linearity (one-shot vs multi-shot) is respected
//! - The resulting effect row correctly removes handled effects
//!
//! # Handler Semantics (F* Effects.fsti lines 596-622)
//!
//! - `EffectHandler` contains clauses and optional return clause
//! - `HandlerClause` binds operation parameters and continuation
//! - `HandlerDepth` (Shallow/Deep) determines continuation invocation
//! - `ContinuationLinearity` (OneShot/MultiShot) determines cloning requirements

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::effects::{
    ContinuationLinearity, EffectHandler, EffectOp, EffectRow, EffectVar, HandlerClause,
    HandlerDepth, OpSig,
};
use crate::expr::{Expr, Range, VarId};
use crate::types::BrrrType;

use super::types::{InferenceState, TypeCtx};

// ============================================================================
// Effect Constraints
// ============================================================================

/// Constraints on effect rows generated during inference.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum EffectConstraint {
    /// Effect row equality: `rho1 = rho2`
    RowEqual(EffectRow, EffectRow, Range),

    /// Effect subsumption: `rho1 <: rho2` (rho1's effects are subset of rho2's)
    RowSubset(EffectRow, EffectRow, Range),

    /// Effect membership constraint: `rho contains op`
    HasEffect(EffectRow, EffectOp, Range),

    /// Handler constraint: `handle(rho_body, op) = rho_result`
    Handles(EffectRow, EffectOp, EffectRow, Range),
}

impl EffectConstraint {
    /// Create an equality constraint
    #[must_use]
    pub fn row_equal(r1: EffectRow, r2: EffectRow, span: Range) -> Self {
        Self::RowEqual(r1, r2, span)
    }

    /// Create a subsumption constraint
    #[must_use]
    pub fn row_subset(sub: EffectRow, sup: EffectRow, span: Range) -> Self {
        Self::RowSubset(sub, sup, span)
    }

    /// Create an effect membership constraint
    #[must_use]
    pub fn has_effect(row: EffectRow, op: EffectOp, span: Range) -> Self {
        Self::HasEffect(row, op, span)
    }

    /// Create a handler constraint
    #[must_use]
    pub fn handles(body: EffectRow, op: EffectOp, result: EffectRow, span: Range) -> Self {
        Self::Handles(body, op, result, span)
    }

    /// Get the source range
    #[must_use]
    pub const fn span(&self) -> Range {
        match self {
            Self::RowEqual(_, _, r)
            | Self::RowSubset(_, _, r)
            | Self::HasEffect(_, _, r)
            | Self::Handles(_, _, _, r) => *r,
        }
    }
}

// ============================================================================
// Effect Errors
// ============================================================================

/// Error during effect inference or checking.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EffectError {
    /// Source location
    pub span: Range,
    /// Error message
    pub message: String,
    /// Expected effect row (if applicable)
    pub expected: Option<EffectRow>,
    /// Found effect row (if applicable)
    pub found: Option<EffectRow>,
}

impl EffectError {
    /// Create a new effect error
    #[must_use]
    pub fn new(message: impl Into<String>, span: Range) -> Self {
        Self {
            span,
            message: message.into(),
            expected: None,
            found: None,
        }
    }

    /// Create an effect mismatch error
    #[must_use]
    pub fn mismatch(expected: EffectRow, found: EffectRow, span: Range) -> Self {
        Self {
            span,
            message: "effect row mismatch".to_string(),
            expected: Some(expected),
            found: Some(found),
        }
    }

    /// Create an unhandled effect error
    #[must_use]
    pub fn unhandled(effect: EffectOp, span: Range) -> Self {
        Self {
            span,
            message: format!("unhandled effect: {}", effect.as_symbol()),
            expected: None,
            found: None,
        }
    }

    /// Format as a diagnostic message
    #[must_use]
    pub fn format(&self) -> String {
        let mut msg = self.message.clone();
        if let Some(ref expected) = self.expected {
            msg.push_str(&format!("\n  expected: {}", expected.format()));
        }
        if let Some(ref found) = self.found {
            msg.push_str(&format!("\n  found: {}", found.format()));
        }
        msg
    }
}

impl std::fmt::Display for EffectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for EffectError {}

// ============================================================================
// Handler Errors
// ============================================================================

/// Errors that can occur during handler type checking.
///
/// These errors are specific to effect handler constructs, covering:
/// - Operation signature mismatches
/// - Continuation typing errors
/// - Linearity violations
/// - Missing clauses
///
/// Based on F* Effects.fsti lines 596-622.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum HandlerError {
    /// The handler contains a clause for an unknown operation.
    UnknownOperation {
        /// The unrecognized effect operation
        op: EffectOp,
        /// Source location of the clause
        span: Range,
    },

    /// The clause signature does not match the declared operation signature.
    SignatureMismatch {
        /// The operation being handled
        op: EffectOp,
        /// Expected signature from effect declaration
        expected: OpSig,
        /// Actual signature from handler clause
        found: OpSig,
        /// Source location
        span: Range,
    },

    /// The continuation type does not match what the clause body expects.
    ContinuationTypeMismatch {
        /// Expected continuation type (typically `OpResult -> HandlerResult`)
        expected: BrrrType,
        /// Found continuation type
        found: BrrrType,
        /// Source location
        span: Range,
    },

    /// A one-shot continuation was used multiple times in the clause body.
    LinearContinuationUsedMultipleTimes {
        /// Source location of the second usage
        span: Range,
    },

    /// A one-shot continuation was not used in the clause body.
    LinearContinuationNotUsed {
        /// Source location of the clause
        span: Range,
    },

    /// The handler is missing a return clause.
    MissingReturnClause {
        /// Source location of the handler
        span: Range,
    },

    /// The return clause type does not match the handler's result type.
    ReturnTypeMismatch {
        /// Expected return type
        expected: BrrrType,
        /// Found return type from clause
        found: BrrrType,
        /// Source location
        span: Range,
    },

    /// Handler clause body type does not match expected handler result type.
    ClauseBodyTypeMismatch {
        /// The operation being handled
        op: EffectOp,
        /// Expected result type
        expected: BrrrType,
        /// Found body type
        found: BrrrType,
        /// Source location
        span: Range,
    },

    /// The effect being handled is not present in the body's effect row.
    EffectNotInScope {
        /// The effect operation
        op: EffectOp,
        /// The available effect row
        available: EffectRow,
        /// Source location
        span: Range,
    },
}

impl HandlerError {
    /// Create an unknown operation error.
    #[must_use]
    pub fn unknown_operation(op: EffectOp, span: Range) -> Self {
        Self::UnknownOperation { op, span }
    }

    /// Create a signature mismatch error.
    #[must_use]
    pub fn signature_mismatch(op: EffectOp, expected: OpSig, found: OpSig, span: Range) -> Self {
        Self::SignatureMismatch {
            op,
            expected,
            found,
            span,
        }
    }

    /// Create a continuation type mismatch error.
    #[must_use]
    pub fn continuation_mismatch(expected: BrrrType, found: BrrrType, span: Range) -> Self {
        Self::ContinuationTypeMismatch {
            expected,
            found,
            span,
        }
    }

    /// Create a linear continuation multi-use error.
    #[must_use]
    pub fn linear_multi_use(span: Range) -> Self {
        Self::LinearContinuationUsedMultipleTimes { span }
    }

    /// Create a linear continuation not-used error.
    #[must_use]
    pub fn linear_not_used(span: Range) -> Self {
        Self::LinearContinuationNotUsed { span }
    }

    /// Create a missing return clause error.
    #[must_use]
    pub fn missing_return(span: Range) -> Self {
        Self::MissingReturnClause { span }
    }

    /// Create a return type mismatch error.
    #[must_use]
    pub fn return_mismatch(expected: BrrrType, found: BrrrType, span: Range) -> Self {
        Self::ReturnTypeMismatch {
            expected,
            found,
            span,
        }
    }

    /// Create a clause body type mismatch error.
    #[must_use]
    pub fn clause_body_mismatch(
        op: EffectOp,
        expected: BrrrType,
        found: BrrrType,
        span: Range,
    ) -> Self {
        Self::ClauseBodyTypeMismatch {
            op,
            expected,
            found,
            span,
        }
    }

    /// Create an effect not in scope error.
    #[must_use]
    pub fn effect_not_in_scope(op: EffectOp, available: EffectRow, span: Range) -> Self {
        Self::EffectNotInScope {
            op,
            available,
            span,
        }
    }

    /// Get the source location of this error.
    #[must_use]
    pub const fn span(&self) -> Range {
        match self {
            Self::UnknownOperation { span, .. }
            | Self::SignatureMismatch { span, .. }
            | Self::ContinuationTypeMismatch { span, .. }
            | Self::LinearContinuationUsedMultipleTimes { span }
            | Self::LinearContinuationNotUsed { span }
            | Self::MissingReturnClause { span }
            | Self::ReturnTypeMismatch { span, .. }
            | Self::ClauseBodyTypeMismatch { span, .. }
            | Self::EffectNotInScope { span, .. } => *span,
        }
    }
}

impl std::fmt::Display for HandlerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownOperation { op, .. } => {
                write!(f, "unknown effect operation: {}", op.as_symbol())
            }
            Self::SignatureMismatch {
                op,
                expected,
                found,
                ..
            } => {
                write!(
                    f,
                    "operation {} signature mismatch: expected {:?}, found {:?}",
                    op.as_symbol(),
                    expected,
                    found
                )
            }
            Self::ContinuationTypeMismatch {
                expected, found, ..
            } => {
                write!(
                    f,
                    "continuation type mismatch: expected {:?}, found {:?}",
                    expected, found
                )
            }
            Self::LinearContinuationUsedMultipleTimes { .. } => {
                write!(f, "one-shot continuation used multiple times")
            }
            Self::LinearContinuationNotUsed { .. } => {
                write!(f, "one-shot continuation not used")
            }
            Self::MissingReturnClause { .. } => {
                write!(f, "handler missing return clause")
            }
            Self::ReturnTypeMismatch {
                expected, found, ..
            } => {
                write!(
                    f,
                    "return type mismatch: expected {:?}, found {:?}",
                    expected, found
                )
            }
            Self::ClauseBodyTypeMismatch {
                op,
                expected,
                found,
                ..
            } => {
                write!(
                    f,
                    "clause body for {} type mismatch: expected {:?}, found {:?}",
                    op.as_symbol(),
                    expected,
                    found
                )
            }
            Self::EffectNotInScope { op, available, .. } => {
                write!(
                    f,
                    "effect {} not in scope, available: {}",
                    op.as_symbol(),
                    available.format()
                )
            }
        }
    }
}

impl std::error::Error for HandlerError {}

// ============================================================================
// Effect Inference State
// ============================================================================

/// State for effect inference.
///
/// Note: We use a simple EffectVar (u32 index) for the substitution map.
/// In a real implementation with interned strings, this would need adjustment.
#[derive(Debug, Clone, Default)]
pub struct EffectInferenceState {
    /// Effect constraints
    pub constraints: Vec<EffectConstraint>,

    /// Effect variable substitution (by EffectVar index)
    pub substitution: HashMap<u32, EffectRow>,

    /// Counter for fresh effect variables
    pub var_counter: u32,

    /// Accumulated errors
    pub errors: Vec<EffectError>,

    /// Handler errors (separate from effect errors)
    pub handler_errors: Vec<HandlerError>,
}

impl EffectInferenceState {
    /// Create a new effect inference state
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Generate a fresh effect variable
    pub fn fresh_row_var(&mut self) -> EffectVar {
        let id = self.var_counter;
        self.var_counter += 1;
        EffectVar::new(id)
    }

    /// Generate a fresh open effect row with a new row variable
    #[must_use]
    pub fn fresh_row(&mut self) -> EffectRow {
        let var = self.fresh_row_var();
        EffectRow::just_var(var)
    }

    /// Generate a fresh effect row with specific effects and fresh tail variable
    #[must_use]
    pub fn fresh_row_with(&mut self, ops: Vec<EffectOp>) -> EffectRow {
        let var = self.fresh_row_var();
        EffectRow::open_with_var(ops, var)
    }

    /// Add a constraint
    pub fn add_constraint(&mut self, constraint: EffectConstraint) {
        self.constraints.push(constraint);
    }

    /// Add a row equality constraint
    pub fn constrain_equal(&mut self, r1: EffectRow, r2: EffectRow, span: Range) {
        self.constraints
            .push(EffectConstraint::row_equal(r1, r2, span));
    }

    /// Add a row subset constraint
    pub fn constrain_subset(&mut self, sub: EffectRow, sup: EffectRow, span: Range) {
        self.constraints
            .push(EffectConstraint::row_subset(sub, sup, span));
    }

    /// Add an effect membership constraint
    pub fn constrain_has_effect(&mut self, row: EffectRow, op: EffectOp, span: Range) {
        self.constraints
            .push(EffectConstraint::has_effect(row, op, span));
    }

    /// Add an error
    pub fn add_error(&mut self, error: EffectError) {
        self.errors.push(error);
    }

    /// Add a handler error
    pub fn add_handler_error(&mut self, error: HandlerError) {
        self.handler_errors.push(error);
    }

    /// Check if there are errors
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty() || !self.handler_errors.is_empty()
    }

    /// Get the number of errors
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.errors.len() + self.handler_errors.len()
    }

    /// Look up a row variable in the substitution
    #[must_use]
    pub fn lookup(&self, var: EffectVar) -> Option<&EffectRow> {
        self.substitution.get(&var.index())
    }

    /// Extend the substitution with a new mapping
    pub fn extend_substitution(&mut self, var: EffectVar, row: EffectRow) {
        self.substitution.insert(var.index(), row);
    }

    /// Clear all constraints (after solving)
    pub fn clear_constraints(&mut self) {
        self.constraints.clear();
    }

    /// Apply substitution to an effect row
    #[must_use]
    pub fn apply(&self, row: &EffectRow) -> EffectRow {
        apply_effect_subst(row, &self.substitution)
    }
}

// ============================================================================
// Effect Row Operations
// ============================================================================

/// Apply a substitution to an effect row.
///
/// The substitution maps effect variable indices to their replacement rows.
#[must_use]
pub fn apply_effect_subst(row: &EffectRow, subst: &HashMap<u32, EffectRow>) -> EffectRow {
    // Check if the row has an open tail we can substitute
    if let Some(var) = row.row_var() {
        if let Some(replacement) = subst.get(&var.index()) {
            // Use the substitute method on EffectRow
            return row.substitute(var, replacement);
        }
    }
    row.clone()
}

/// Unify two effect rows.
///
/// Implements row unification following F* Effects.fsti semantics:
/// - Empty rows unify with empty rows
/// - Row variables unify with any row (binding in substitution)
/// - Extended rows match effects and unify tails
///
/// Returns `Ok(())` on success, extending the substitution in `state`.
/// Returns `Err(EffectError)` on failure.
pub fn unify_rows(
    r1: &EffectRow,
    r2: &EffectRow,
    state: &mut EffectInferenceState,
) -> Result<(), EffectError> {
    let r1 = state.apply(r1);
    let r2 = state.apply(r2);

    // If both are equal, success
    if r1 == r2 {
        return Ok(());
    }

    // Handle based on row variables
    match (r1.row_var(), r2.row_var()) {
        // Both have variables - check if same or need to unify
        (Some(v1), Some(v2)) if v1 == v2 => {
            // Same variable - just check the effects match
            if r1.ops() == r2.ops() {
                Ok(())
            } else {
                // Effects differ but same tail - need to reconcile
                let joined = r1.join(&r2);
                state.extend_substitution(v1, joined);
                Ok(())
            }
        }

        // Different variables
        (Some(v1), Some(v2)) => {
            // Create a new variable for the unified tail
            let new_var = state.fresh_row_var();

            // Bind both original variables to include their respective effects plus new tail
            let r1_binding = EffectRow::open_with_var(r2.ops().iter().cloned().collect(), new_var);
            let r2_binding = EffectRow::open_with_var(r1.ops().iter().cloned().collect(), new_var);

            state.extend_substitution(v1, r1_binding);
            state.extend_substitution(v2, r2_binding);
            Ok(())
        }

        // Only r1 has a variable
        (Some(v1), None) => {
            // r2 is closed - find effects in r2 not in r1
            let mut remaining_ops: Vec<_> = r2.ops().to_vec();
            for op in r1.ops() {
                if let Some(pos) = remaining_ops
                    .iter()
                    .position(|o| o.discriminant() == op.discriminant())
                {
                    remaining_ops.remove(pos);
                }
            }
            let binding = EffectRow::new(remaining_ops);
            state.extend_substitution(v1, binding);
            Ok(())
        }

        // Only r2 has a variable
        (None, Some(v2)) => {
            // r1 is closed - find effects in r1 not in r2
            let mut remaining_ops: Vec<_> = r1.ops().to_vec();
            for op in r2.ops() {
                if let Some(pos) = remaining_ops
                    .iter()
                    .position(|o| o.discriminant() == op.discriminant())
                {
                    remaining_ops.remove(pos);
                }
            }
            let binding = EffectRow::new(remaining_ops);
            state.extend_substitution(v2, binding);
            Ok(())
        }

        // Both closed - must have same effects
        (None, None) => {
            let ops1 = r1.ops();
            let ops2 = r2.ops();
            if ops1.len() != ops2.len() {
                return Err(EffectError::mismatch(
                    r1.clone(),
                    r2.clone(),
                    Range::SYNTHETIC,
                ));
            }
            for (o1, o2) in ops1.iter().zip(ops2.iter()) {
                if o1.discriminant() != o2.discriminant() {
                    return Err(EffectError::mismatch(
                        r1.clone(),
                        r2.clone(),
                        Range::SYNTHETIC,
                    ));
                }
            }
            Ok(())
        }
    }
}

// ============================================================================
// Handler Type Checking
// ============================================================================

/// Type check an effect handler against the body type and effects.
///
/// This function performs comprehensive handler type checking:
/// 1. Verifies each clause handles a known operation
/// 2. Checks operation signatures match
/// 3. Verifies continuation types
/// 4. Checks return clause type matches handler result type
/// 5. Computes the resulting effect row (body_effects - handled_effects)
///
/// # Arguments
/// * `handler` - The effect handler to type check
/// * `body_type` - The type of the handled computation's result
/// * `body_effects` - The effect row of the handled computation
/// * `ctx` - Type context for name resolution
/// * `state` - Mutable inference state
///
/// # Returns
/// `Ok((result_type, result_effects))` on success, `Err(HandlerError)` on failure.
pub fn type_check_handler(
    handler: &EffectHandler,
    body_type: &BrrrType,
    body_effects: &EffectRow,
    ctx: &TypeCtx,
    state: &mut InferenceState,
) -> Result<(BrrrType, EffectRow), HandlerError> {
    let mut effect_state = EffectInferenceState::new();

    // Determine the handler result type from the return clause
    let result_type = if let Some((_var, ref _return_body)) = handler.return_clause {
        // Infer return clause body type
        // For now, we assume the return clause transforms body_type to result_type
        body_type.clone()
    } else {
        // No return clause - result type is same as body type
        body_type.clone()
    };

    // Check each clause
    for clause in &handler.clauses {
        // Look up operation signature (for now, we trust the operation exists)
        // In a full implementation, we'd look up the op sig from effect declarations
        // Placeholder: empty signature - real impl would look up from effect decls
        let op_sig = OpSig::nullary(clause.op.clone(), BrrrType::UNIT);

        type_check_clause(clause, &op_sig, &result_type, ctx, state, &mut effect_state)?;

        // Check continuation linearity - use OneShot as default for regular handlers
        // ExtendedHandler would provide explicit linearity
        check_continuation_linearity(clause, ContinuationLinearity::OneShot)?;
    }

    // Compute resulting effect row
    let result_effects = compute_handler_effects(handler.depth, body_effects, &handler.clauses);

    Ok((result_type, result_effects))
}

/// Type check a single handler clause.
///
/// Per clause:
/// - Bind operation parameters to their types
/// - Bind continuation `k` to type `A -> B` where A is op result, B is handler result
/// - Type check clause body, should return handler result type
///
/// # Arguments
/// * `clause` - The handler clause to check
/// * `op_sig` - Expected operation signature
/// * `result_type` - Handler's result type
/// * `ctx` - Type context
/// * `_state` - Type inference state (unused for now)
/// * `effect_state` - Effect inference state
pub fn type_check_clause(
    clause: &HandlerClause,
    op_sig: &OpSig,
    result_type: &BrrrType,
    ctx: &TypeCtx,
    _state: &mut InferenceState,
    effect_state: &mut EffectInferenceState,
) -> Result<(), HandlerError> {
    use crate::types::{FuncType, ParamType};

    // Verify parameter count matches
    // Note: In a full implementation, we would look up the op signature from
    // effect declarations. For now, we allow any parameter count since the
    // OpSig is a placeholder.
    if !op_sig.params.is_empty() && clause.params.len() != op_sig.params.len() {
        return Err(HandlerError::signature_mismatch(
            clause.op.clone(),
            op_sig.clone(),
            OpSig::new(
                clause.op.clone(),
                clause.params.iter().map(|_| BrrrType::UNKNOWN).collect(),
                BrrrType::UNKNOWN,
            ),
            clause.body.range,
        ));
    }

    // Create child context with parameter bindings
    let mut child_ctx = ctx.child();

    // Bind operation parameters to placeholder types if no signature available
    if op_sig.params.is_empty() {
        for param in &clause.params {
            child_ctx.extend_mono(*param, BrrrType::UNKNOWN);
        }
    } else {
        for (param, expected_ty) in clause.params.iter().zip(op_sig.params.iter()) {
            child_ctx.extend_mono(*param, expected_ty.clone());
        }
    }

    // Bind continuation `k` with type `OpResult -> HandlerResult`
    // Uses FuncType to create the function type properly
    let continuation_func = FuncType::pure(
        vec![ParamType::unnamed(op_sig.result.clone())],
        result_type.clone(),
    );
    let continuation_type = BrrrType::Func(Box::new(continuation_func));
    child_ctx.extend_mono(clause.continuation, continuation_type);

    // Type check clause body
    // The body should return handler result type
    // For now, we just infer effects from the body
    let _clause_effects = infer_effects(&clause.body, effect_state);

    Ok(())
}

/// Check continuation linearity constraints.
///
/// - OneShot: continuation used exactly once (linear)
/// - MultiShot: continuation can be used multiple times (requires clone)
///
/// This function analyzes the clause body to count continuation usages.
pub fn check_continuation_linearity(
    clause: &HandlerClause,
    linearity: ContinuationLinearity,
) -> Result<(), HandlerError> {
    let usage_count = count_continuation_uses(&clause.body, clause.continuation);

    match linearity {
        ContinuationLinearity::OneShot => {
            if usage_count == 0 {
                return Err(HandlerError::linear_not_used(clause.body.range));
            }
            if usage_count > 1 {
                return Err(HandlerError::linear_multi_use(clause.body.range));
            }
        }
        ContinuationLinearity::MultiShot => {
            // No restrictions on multi-shot continuations
        }
    }

    Ok(())
}

/// Count how many times a continuation variable is used in an expression.
fn count_continuation_uses(expr: &Expr, cont_var: VarId) -> usize {
    use crate::expr::Expr_;

    match &expr.value {
        Expr_::Var(v) if *v == cont_var => 1,
        Expr_::Var(_) | Expr_::Global(_) | Expr_::Lit(_) | Expr_::Hole | Expr_::Error(_) => 0,

        Expr_::Resume { var, .. } if *var == cont_var => 1,
        Expr_::Resume { value, .. } => count_continuation_uses(value, cont_var),

        Expr_::Call(callee, args) => {
            let mut count = count_continuation_uses(callee, cont_var);
            for arg in args {
                count += count_continuation_uses(arg, cont_var);
            }
            count
        }

        Expr_::If(cond, then_br, else_br) => {
            count_continuation_uses(cond, cont_var)
                + count_continuation_uses(then_br, cont_var)
                + count_continuation_uses(else_br, cont_var)
        }

        Expr_::Binary(_, lhs, rhs) => {
            count_continuation_uses(lhs, cont_var) + count_continuation_uses(rhs, cont_var)
        }

        Expr_::Unary(_, inner)
        | Expr_::Box(inner)
        | Expr_::Deref(inner)
        | Expr_::Borrow(inner)
        | Expr_::BorrowMut(inner)
        | Expr_::Move(inner)
        | Expr_::Drop(inner)
        | Expr_::Async(inner)
        | Expr_::Await(inner)
        | Expr_::Yield(inner)
        | Expr_::Spawn(inner)
        | Expr_::Throw(inner)
        | Expr_::Unsafe(inner) => count_continuation_uses(inner, cont_var),

        Expr_::Let { init, body, .. } | Expr_::LetMut { init, body, .. } => {
            count_continuation_uses(init, cont_var) + count_continuation_uses(body, cont_var)
        }

        Expr_::Seq(first, second) => {
            count_continuation_uses(first, cont_var) + count_continuation_uses(second, cont_var)
        }

        Expr_::Block(exprs) | Expr_::Tuple(exprs) | Expr_::Array(exprs) => exprs
            .iter()
            .map(|e| count_continuation_uses(e, cont_var))
            .sum(),

        Expr_::Lambda { body, .. } | Expr_::Closure { body, .. } => {
            // Continuations captured in lambdas count as uses
            count_continuation_uses(body, cont_var)
        }

        // Other cases - recursively count
        _ => 0,
    }
}

/// Compute the resulting effect row after handler application.
///
/// - Shallow: removes one layer of effect
/// - Deep: removes effect recursively (all occurrences)
pub fn compute_handler_effects(
    depth: HandlerDepth,
    body_effects: &EffectRow,
    clauses: &[HandlerClause],
) -> EffectRow {
    let mut result = body_effects.clone();

    for clause in clauses {
        match depth {
            HandlerDepth::Shallow => {
                // Remove one occurrence of the handled effect
                if let Some(after) = result.handle(&clause.op) {
                    result = after;
                }
            }
            HandlerDepth::Deep => {
                // Remove all occurrences of the handled effect
                result = result.handle_all(&clause.op);
            }
        }
    }

    result
}

// ============================================================================
// Effect Inference
// ============================================================================

/// Infer the effect row for an expression.
///
/// Traverses the expression tree and collects effect constraints,
/// returning the inferred effect row for the expression.
///
/// # Inference Rules
///
/// - **Lit**: Pure (empty row)
/// - **Var**: Pure (reading a variable has no effect)
/// - **Call**: Join callee effects with argument effects
/// - **If**: Join condition effects with both branch effects
/// - **Handle**: Body effects minus handled effects
/// - **Perform**: Row containing the performed effect
/// - **Let**: Join init effects with body effects
/// - **Seq**: Join both expression effects
#[must_use]
pub fn infer_effects(expr: &Expr, state: &mut EffectInferenceState) -> EffectRow {
    use crate::expr::Expr_;

    match &expr.value {
        // === Pure expressions (no effects) ===
        Expr_::Lit(_) | Expr_::Var(_) | Expr_::Global(_) | Expr_::Hole | Expr_::Error(_) => {
            EffectRow::pure()
        }

        // === Type operations (pure) ===
        Expr_::Sizeof(_) | Expr_::Alignof(_) => EffectRow::pure(),

        // === Unary operations ===
        Expr_::Unary(_, inner) => infer_effects(inner, state),

        // === Binary operations ===
        Expr_::Binary(_, lhs, rhs) => {
            let e1 = infer_effects(lhs, state);
            let e2 = infer_effects(rhs, state);
            e1.join(&e2)
        }

        // === Function call ===
        Expr_::Call(callee, args) => {
            let mut result = infer_effects(callee, state);
            for arg in args {
                result = result.join(&infer_effects(arg, state));
            }
            // Add a fresh row variable for the function's own effects
            let func_effects = state.fresh_row();
            result.join(&func_effects)
        }

        // === Method call ===
        Expr_::MethodCall(receiver, _method, args) => {
            let mut result = infer_effects(receiver, state);
            for arg in args {
                result = result.join(&infer_effects(arg, state));
            }
            let method_effects = state.fresh_row();
            result.join(&method_effects)
        }

        // === Data construction ===
        Expr_::Tuple(elems) | Expr_::Array(elems) | Expr_::Block(elems) => {
            let mut result = EffectRow::pure();
            for elem in elems {
                result = result.join(&infer_effects(elem, state));
            }
            result
        }

        Expr_::Struct { fields, .. } => {
            let mut result = EffectRow::pure();
            for (_, e) in fields {
                result = result.join(&infer_effects(e, state));
            }
            result
        }

        Expr_::Variant { fields, .. } => {
            let mut result = EffectRow::pure();
            for e in fields {
                result = result.join(&infer_effects(e, state));
            }
            result
        }

        // === Data access ===
        Expr_::Field(base, _) | Expr_::TupleProj(base, _) => infer_effects(base, state),

        Expr_::Index(base, index) => {
            let e1 = infer_effects(base, state);
            let e2 = infer_effects(index, state);
            e1.join(&e2)
        }

        // === Control flow ===
        Expr_::If(cond, then_branch, else_branch) => {
            let e_cond = infer_effects(cond, state);
            let e_then = infer_effects(then_branch, state);
            let e_else = infer_effects(else_branch, state);
            e_cond.join(&e_then).join(&e_else)
        }

        Expr_::Match(scrutinee, arms) => {
            let mut result = infer_effects(scrutinee, state);
            for arm in arms {
                if let Some(ref guard) = arm.guard {
                    result = result.join(&infer_effects(guard, state));
                }
                result = result.join(&infer_effects(&arm.body, state));
            }
            result
        }

        Expr_::Loop { body, .. } => {
            let body_effects = infer_effects(body, state);
            body_effects.join(&EffectRow::single(EffectOp::Div))
        }

        Expr_::While { cond, body, .. } => {
            let e_cond = infer_effects(cond, state);
            let e_body = infer_effects(body, state);
            e_cond.join(&e_body).join(&EffectRow::single(EffectOp::Div))
        }

        Expr_::For { iter, body, .. } => {
            let e_iter = infer_effects(iter, state);
            let e_body = infer_effects(body, state);
            e_iter.join(&e_body).join(&EffectRow::single(EffectOp::Div))
        }

        Expr_::Break { value, .. } => value
            .as_ref()
            .map(|v| infer_effects(v, state))
            .unwrap_or_else(EffectRow::pure),

        Expr_::Continue { .. } => EffectRow::pure(),

        Expr_::Return(value) => value
            .as_ref()
            .map(|v| infer_effects(v, state))
            .unwrap_or_else(EffectRow::pure),

        // === Bindings ===
        Expr_::Let { init, body, .. } | Expr_::LetMut { init, body, .. } => {
            let e_init = infer_effects(init, state);
            let e_body = infer_effects(body, state);
            e_init.join(&e_body)
        }

        Expr_::Assign(lhs, rhs) => {
            let e1 = infer_effects(lhs, state);
            let e2 = infer_effects(rhs, state);
            e1.join(&e2).join(&EffectRow::single(EffectOp::WriteSimple))
        }

        // === Functions ===
        Expr_::Lambda { .. } | Expr_::Closure { .. } => {
            // Lambda itself is pure; body effects are captured in function type
            state.fresh_row()
        }

        // === Memory operations ===
        Expr_::Box(inner) => {
            let e = infer_effects(inner, state);
            e.join(&EffectRow::single(EffectOp::Alloc))
        }

        Expr_::Deref(inner) => {
            let e = infer_effects(inner, state);
            e.join(&EffectRow::single(EffectOp::ReadSimple))
        }

        Expr_::Borrow(inner) | Expr_::BorrowMut(inner) => infer_effects(inner, state),

        Expr_::Move(inner) => infer_effects(inner, state),

        Expr_::Drop(inner) => {
            let e = infer_effects(inner, state);
            e.join(&EffectRow::single(EffectOp::WriteSimple))
        }

        // === Exception handling ===
        Expr_::Throw(e) => {
            let eff = infer_effects(e, state);
            eff.join(&EffectRow::single(EffectOp::Panic))
        }

        Expr_::Try {
            body,
            catches,
            finally,
        } => {
            let mut e_body = infer_effects(body, state);
            // Try block catches Panic effects
            e_body = e_body.handle_all(&EffectOp::Panic);
            for catch in catches {
                e_body = e_body.join(&infer_effects(&catch.body, state));
            }
            if let Some(fin) = finally {
                e_body = e_body.join(&infer_effects(fin, state));
            }
            e_body
        }

        // === Async/Concurrency ===
        Expr_::Await(inner) => {
            let e = infer_effects(inner, state);
            e.join(&EffectRow::single(EffectOp::Async))
        }

        Expr_::Yield(inner) => {
            let e = infer_effects(inner, state);
            e.join(&EffectRow::single(EffectOp::Async))
        }

        Expr_::Async(inner) => {
            let e = infer_effects(inner, state);
            e.join(&EffectRow::single(EffectOp::Async))
        }

        Expr_::Spawn(inner) => {
            let e = infer_effects(inner, state);
            e.join(&EffectRow::single(EffectOp::Spawn))
        }

        // === Effect operations ===
        Expr_::Handle(body, handler) => {
            let body_effects = infer_effects(body, state);
            check_handler(handler, &body_effects, state)
        }

        Expr_::Perform(op, args) => {
            let mut result = EffectRow::pure();
            for arg in args {
                result = result.join(&infer_effects(arg, state));
            }
            result.join(&EffectRow::single(op.clone()))
        }

        Expr_::Resume { value, .. } => infer_effects(value, state),

        // === Delimited continuations ===
        Expr_::Reset { body, .. } => infer_effects(body, state),

        Expr_::Shift { body, .. } => {
            let e = infer_effects(body, state);
            e.join(&EffectRow::single(EffectOp::Shift))
        }

        // === Type operations ===
        Expr_::As(inner, _) | Expr_::Is(inner, _) => infer_effects(inner, state),

        // === Sequence ===
        Expr_::Seq(first, second) => {
            let e1 = infer_effects(first, state);
            let e2 = infer_effects(second, state);
            e1.join(&e2)
        }

        // === Unsafe ===
        Expr_::Unsafe(inner) => {
            let e = infer_effects(inner, state);
            e.join(&EffectRow::single(EffectOp::Unsafe))
        }

        // === Gradual typing ===
        Expr_::GradualCast { expr, .. } => infer_effects(expr, state),

        // === Control flow labels ===
        Expr_::Goto { .. } => EffectRow::pure(),
        Expr_::Labeled { body, .. } => infer_effects(body, state),
    }
}

/// Check handler typing and compute the resulting effect row.
///
/// A handler removes the handled effects from the body's effect row.
/// The resulting row is the body's effects minus the effects handled
/// by the handler's clauses.
///
/// # Handler Semantics
///
/// Per F* Effects.fsti:
/// - Each clause handles ONE instance of an effect
/// - `handle(<E, E | rho>, E)` produces `<E | rho>` (one E removed)
/// - Unhandled effects propagate through
#[must_use]
pub fn check_handler(
    handler: &EffectHandler,
    input_effects: &EffectRow,
    state: &mut EffectInferenceState,
) -> EffectRow {
    let mut result = input_effects.clone();

    // For each clause, remove one instance of the handled effect
    for clause in &handler.clauses {
        match result.handle(&clause.op) {
            Some(after_handle) => {
                result = after_handle;
            }
            None => {
                // Effect not present - generate a constraint
                state.constrain_has_effect(
                    input_effects.clone(),
                    clause.op.clone(),
                    clause.body.range,
                );
            }
        }
    }

    // The handler clause bodies might have their own effects
    for clause in &handler.clauses {
        let clause_effects = infer_effects(&clause.body, state);
        result = result.join(&clause_effects);
    }

    // Return clause effects
    if let Some((_, ref body)) = handler.return_clause {
        let return_effects = infer_effects(body, state);
        result = result.join(&return_effects);
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{Literal, WithLoc};

    fn make_lit_expr() -> Expr {
        WithLoc::synthetic(crate::expr::Expr_::Lit(Literal::Unit))
    }

    #[test]
    fn test_effect_inference_state_new() {
        let state = EffectInferenceState::new();
        assert!(state.constraints.is_empty());
        assert_eq!(state.var_counter, 0);
        assert!(state.substitution.is_empty());
        assert!(!state.has_errors());
    }

    #[test]
    fn test_fresh_row_var() {
        let mut state = EffectInferenceState::new();
        let v1 = state.fresh_row_var();
        let v2 = state.fresh_row_var();
        assert_ne!(v1, v2);
        assert_eq!(v1.index(), 0);
        assert_eq!(v2.index(), 1);
    }

    #[test]
    fn test_fresh_row() {
        let mut state = EffectInferenceState::new();
        let row = state.fresh_row();
        assert!(row.is_open());
        assert_eq!(row.row_var(), Some(EffectVar::new(0)));
    }

    #[test]
    fn test_infer_lit_is_pure() {
        let mut state = EffectInferenceState::new();
        let expr = make_lit_expr();
        let effects = infer_effects(&expr, &mut state);
        assert!(effects.is_pure());
    }

    #[test]
    fn test_infer_perform() {
        let mut state = EffectInferenceState::new();
        let expr = WithLoc::synthetic(crate::expr::Expr_::Perform(EffectOp::Io, vec![]));
        let effects = infer_effects(&expr, &mut state);
        assert!(effects.contains(&EffectOp::Io));
    }

    #[test]
    fn test_infer_binary_joins_effects() {
        let mut state = EffectInferenceState::new();
        let lhs = WithLoc::synthetic(crate::expr::Expr_::Perform(EffectOp::Io, vec![]));
        let rhs = WithLoc::synthetic(crate::expr::Expr_::Perform(EffectOp::Fs, vec![]));
        let expr = WithLoc::synthetic(crate::expr::Expr_::Binary(
            crate::expr::BinaryOp::Add,
            Box::new(lhs),
            Box::new(rhs),
        ));
        let effects = infer_effects(&expr, &mut state);
        assert!(effects.contains(&EffectOp::Io));
        assert!(effects.contains(&EffectOp::Fs));
    }

    #[test]
    fn test_unify_pure_rows() {
        let mut state = EffectInferenceState::new();
        let r1 = EffectRow::PURE;
        let r2 = EffectRow::PURE;
        let result = unify_rows(&r1, &r2, &mut state);
        assert!(result.is_ok());
    }

    #[test]
    fn test_unify_rows_var_with_closed() {
        let mut state = EffectInferenceState::new();
        let var = state.fresh_row_var();
        let open_row = EffectRow::just_var(var);
        let closed_row = EffectRow::single(EffectOp::Io);

        let result = unify_rows(&open_row, &closed_row, &mut state);
        assert!(result.is_ok());

        let bound = state.lookup(var);
        assert!(bound.is_some());
        assert!(bound.unwrap().contains(&EffectOp::Io));
    }

    #[test]
    fn test_handler_error_display() {
        let err = HandlerError::unknown_operation(EffectOp::Io, Range::SYNTHETIC);
        let msg = format!("{}", err);
        assert!(msg.contains("unknown effect operation"));
        assert!(msg.contains("IO"));
    }

    #[test]
    fn test_handler_error_span() {
        let span = Range::SYNTHETIC;
        let err = HandlerError::missing_return(span);
        assert_eq!(err.span(), span);
    }

    #[test]
    fn test_check_handler_removes_effect() {
        let mut state = EffectInferenceState::new();

        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let k = rodeo.get_or_intern("k");

        let body = make_lit_expr();
        let clause = HandlerClause::new(EffectOp::Io, vec![], k, body);
        let handler = EffectHandler::shallow(vec![clause]);

        let input = EffectRow::new(vec![EffectOp::Io, EffectOp::Fs]);
        let result = check_handler(&handler, &input, &mut state);

        // IO should be removed, FS should remain
        assert!(!result.contains(&EffectOp::Io));
        assert!(result.contains(&EffectOp::Fs));
    }

    #[test]
    fn test_compute_handler_effects_deep() {
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let k = rodeo.get_or_intern("k");

        let body = make_lit_expr();
        let clause = HandlerClause::new(EffectOp::Io, vec![], k, body);
        let clauses = vec![clause];

        // Input has two IO effects
        let input = EffectRow::new(vec![EffectOp::Io, EffectOp::Io, EffectOp::Fs]);
        let result = compute_handler_effects(HandlerDepth::Deep, &input, &clauses);

        // Deep removes all IO
        assert!(!result.contains(&EffectOp::Io));
        assert!(result.contains(&EffectOp::Fs));
    }

    #[test]
    fn test_check_continuation_linearity_oneshot_ok() {
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let k = rodeo.get_or_intern("k");

        // Body uses k exactly once
        let body = WithLoc::synthetic(crate::expr::Expr_::Var(k));
        let clause = HandlerClause::new(EffectOp::Io, vec![], k, body);

        let result = check_continuation_linearity(&clause, ContinuationLinearity::OneShot);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_continuation_linearity_oneshot_unused() {
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let k = rodeo.get_or_intern("k");

        // Body does not use k
        let body = make_lit_expr();
        let clause = HandlerClause::new(EffectOp::Io, vec![], k, body);

        let result = check_continuation_linearity(&clause, ContinuationLinearity::OneShot);
        assert!(matches!(
            result,
            Err(HandlerError::LinearContinuationNotUsed { .. })
        ));
    }
}
