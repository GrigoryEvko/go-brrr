//! Gradual typing cast elaboration
//!
//! Implements cast insertion for AGT (Abstracting Gradual Typing).
//! When expressions involve the dynamic type `?`, this module inserts
//! explicit runtime casts to maintain type safety with blame tracking.
//!
//! # AGT Cast Insertion Rules
//!
//! - Upcast (T -> ?): Always succeeds, wraps value in dynamic container
//! - Downcast (? -> T): May fail at runtime, requires blame tracking
//! - FuncCast ((A->B) -> (A'->B')): Wraps function with argument/return casts
//!
//! # Blame Tracking
//!
//! Each cast carries a blame label with positive and negative parties:
//! - Positive blame: the code that produced the value
//! - Negative blame: the code that consumes the value
//!
//! When a downcast fails, blame is assigned to help identify the source of type errors.
//!
//! # F* Specification Reference
//! ```fstar
//! type cast_kind = | Upcast | Downcast | FuncCast
//!
//! type blame_label = {
//!   positive: string;
//!   negative: string;
//! }
//!
//! type cast = {
//!   cast_from: gradual_type;
//!   cast_to: gradual_type;
//!   cast_kind: cast_kind;
//!   cast_evidence: evidence;
//!   cast_blame: blame_label;
//! }
//!
//! val elaborate_expr: expr -> gradual_type -> gradual_ctx ->
//!   ML (expr & evidence)
//!
//! val insert_cast_if_needed: expr -> gradual_type -> gradual_type ->
//!   blame_label -> ML expr
//! ```

use std::collections::HashMap;

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::types::{Evidence, GradualType};
use crate::expr::{Expr, Expr_, Range, VarId, WithLoc};
use crate::types::BrrrType;

/// Kind of runtime cast for gradual typing
///
/// Classifies casts by their direction relative to the dynamic type `?`.
///
/// # Safety Properties
/// - `Upcast`: Always safe, introduces imprecision
/// - `Downcast`: May fail at runtime, requires blame tracking
/// - `FuncCast`: Deferred cast on function boundaries
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CastKind {
    /// Upcast: T -> ?
    ///
    /// Wraps a statically-typed value in a dynamic container.
    /// Always succeeds at runtime. Introduces type imprecision.
    ///
    /// Example: `let x: ? = 42` (Int -> ?)
    Upcast,

    /// Downcast: ? -> T
    ///
    /// Extracts a value from a dynamic container, asserting its type.
    /// May fail at runtime if the actual type doesn't match T.
    /// Carries blame information for error reporting.
    ///
    /// Example: `let y: Int = x` where x: ?
    Downcast,

    /// Function cast: (A -> B) -> (A' -> B')
    ///
    /// Wraps a function to cast its arguments and return value.
    /// Combines contravariant argument casts with covariant return cast.
    /// May fail when the wrapped function is called.
    ///
    /// Example: `(? -> Int) -> (String -> ?)` wraps argument and return casts
    FuncCast,

    /// Reference cast: &T -> &T' or &mut T -> &mut T'
    ///
    /// Casts a reference to a compatible gradual type.
    /// Requires care with mutability - mutable references need invariant casting.
    RefCast,
}

impl CastKind {
    /// Returns true if this cast may fail at runtime
    #[inline]
    pub const fn may_fail(&self) -> bool {
        matches!(self, Self::Downcast | Self::FuncCast | Self::RefCast)
    }

    /// Returns true if this cast always succeeds
    #[inline]
    pub const fn always_succeeds(&self) -> bool {
        matches!(self, Self::Upcast)
    }

    /// Returns true if this is a function cast requiring wrapper
    #[inline]
    pub const fn is_function_cast(&self) -> bool {
        matches!(self, Self::FuncCast)
    }
}

impl std::fmt::Display for CastKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Upcast => write!(f, "upcast"),
            Self::Downcast => write!(f, "downcast"),
            Self::FuncCast => write!(f, "funccast"),
            Self::RefCast => write!(f, "refcast"),
        }
    }
}

/// Blame label for tracking responsibility in gradual type errors
///
/// When a runtime cast fails, blame labels help identify which code is responsible:
/// - Positive blame: the producer of the value (e.g., function returning wrong type)
/// - Negative blame: the consumer expecting a specific type
///
/// # Blame Semantics
///
/// In the expression `f(x)` where `f: ? -> Int`:
/// - If `f` returns a non-Int, positive blame goes to `f`
/// - The call site has negative blame for expecting Int
///
/// This follows the "blame theorem" from gradual typing literature:
/// well-typed code cannot be blamed for type errors.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BlameLabel {
    /// Positive blame: who produced the value
    /// Typically the function/expression that created the dynamically-typed value
    pub positive: String,

    /// Negative blame: who consumed/expected a specific type
    /// Typically the context expecting a statically-typed value
    pub negative: String,

    /// Source location where the cast was inserted
    pub source_range: Range,
}

impl BlameLabel {
    /// Create a new blame label
    pub fn new(positive: impl Into<String>, negative: impl Into<String>) -> Self {
        Self {
            positive: positive.into(),
            negative: negative.into(),
            source_range: Range::SYNTHETIC,
        }
    }

    /// Create a blame label with source location
    pub fn with_range(
        positive: impl Into<String>,
        negative: impl Into<String>,
        range: Range,
    ) -> Self {
        Self {
            positive: positive.into(),
            negative: negative.into(),
            source_range: range,
        }
    }

    /// Create a synthetic blame label for compiler-generated casts
    pub fn synthetic(context: impl Into<String>) -> Self {
        let ctx = context.into();
        Self {
            positive: format!("<synthetic:{}>", ctx),
            negative: format!("<synthetic:{}>", ctx),
            source_range: Range::SYNTHETIC,
        }
    }

    /// Swap positive and negative blame (for contravariant positions)
    ///
    /// In function argument positions, blame is reversed:
    /// the caller becomes the producer, callee becomes consumer.
    #[must_use]
    pub fn swap(&self) -> Self {
        Self {
            positive: self.negative.clone(),
            negative: self.positive.clone(),
            source_range: self.source_range,
        }
    }

    /// Extend the positive blame with additional context
    #[must_use]
    pub fn with_positive_context(&self, context: &str) -> Self {
        Self {
            positive: format!("{}:{}", self.positive, context),
            negative: self.negative.clone(),
            source_range: self.source_range,
        }
    }

    /// Extend the negative blame with additional context
    #[must_use]
    pub fn with_negative_context(&self, context: &str) -> Self {
        Self {
            positive: self.positive.clone(),
            negative: format!("{}:{}", self.negative, context),
            source_range: self.source_range,
        }
    }
}

impl Default for BlameLabel {
    fn default() -> Self {
        Self::synthetic("unknown")
    }
}

impl std::fmt::Display for BlameLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[+:{}, -:{}]", self.positive, self.negative)
    }
}

/// A runtime cast for gradual typing
///
/// Represents an explicit cast operation inserted during elaboration.
/// Contains all information needed for runtime type checking and blame assignment.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Cast {
    /// Source gradual type
    pub from: GradualType,

    /// Target gradual type
    pub to: GradualType,

    /// Kind of cast operation
    pub kind: CastKind,

    /// Evidence for how consistency was established
    pub evidence: Evidence,

    /// Blame label for error reporting
    pub blame: BlameLabel,
}

impl Cast {
    /// Create a new cast
    pub fn new(
        from: GradualType,
        to: GradualType,
        kind: CastKind,
        evidence: Evidence,
        blame: BlameLabel,
    ) -> Self {
        Self {
            from,
            to,
            kind,
            evidence,
            blame,
        }
    }

    /// Create an upcast (T -> ?)
    pub fn upcast(from: GradualType, blame: BlameLabel) -> Self {
        let evidence = Evidence::dyn_right(from.clone());
        Self {
            from,
            to: GradualType::Dynamic,
            kind: CastKind::Upcast,
            evidence,
            blame,
        }
    }

    /// Create a downcast (? -> T)
    pub fn downcast(to: GradualType, blame: BlameLabel) -> Self {
        let evidence = Evidence::dyn_left(to.clone());
        Self {
            from: GradualType::Dynamic,
            to,
            kind: CastKind::Downcast,
            evidence,
            blame,
        }
    }

    /// Check if this cast may fail at runtime
    #[inline]
    pub const fn may_fail(&self) -> bool {
        self.kind.may_fail()
    }

    /// Check if this is a trivial cast (same type)
    pub fn is_trivial(&self) -> bool {
        self.from == self.to
    }
}

/// Errors that can occur during gradual type elaboration
#[derive(Debug, Clone, PartialEq)]
pub enum GradualError {
    /// Types are not consistent (no valid cast exists)
    Inconsistent {
        t1: GradualType,
        t2: GradualType,
        span: Range,
    },

    /// Runtime blame error (cast failure)
    BlameError {
        label: BlameLabel,
        expected: GradualType,
        found: GradualType,
    },

    /// Variable not found in context
    UnboundVariable {
        var: VarId,
        span: Range,
    },

    /// Type mismatch in function application
    ApplicationError {
        expected_args: usize,
        found_args: usize,
        span: Range,
    },

    /// Cannot cast between incompatible type constructors
    IncompatibleTypes {
        from: GradualType,
        to: GradualType,
        reason: String,
        span: Range,
    },
}

impl GradualError {
    /// Create an inconsistency error
    pub fn inconsistent(t1: GradualType, t2: GradualType, span: Range) -> Self {
        Self::Inconsistent { t1, t2, span }
    }

    /// Create a blame error
    pub fn blame(label: BlameLabel, expected: GradualType, found: GradualType) -> Self {
        Self::BlameError {
            label,
            expected,
            found,
        }
    }

    /// Create an unbound variable error
    pub fn unbound(var: VarId, span: Range) -> Self {
        Self::UnboundVariable { var, span }
    }

    /// Get the source range of this error
    pub fn span(&self) -> Range {
        match self {
            Self::Inconsistent { span, .. } => *span,
            Self::BlameError { label, .. } => label.source_range,
            Self::UnboundVariable { span, .. } => *span,
            Self::ApplicationError { span, .. } => *span,
            Self::IncompatibleTypes { span, .. } => *span,
        }
    }
}

impl std::fmt::Display for GradualError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Inconsistent { t1, t2, .. } => {
                write!(f, "Types {:?} and {:?} are not consistent", t1, t2)
            }
            Self::BlameError {
                label,
                expected,
                found,
            } => {
                write!(
                    f,
                    "Blame {} : expected {:?}, found {:?}",
                    label, expected, found
                )
            }
            Self::UnboundVariable { var, .. } => {
                write!(f, "Unbound variable: {:?}", var)
            }
            Self::ApplicationError {
                expected_args,
                found_args,
                ..
            } => {
                write!(
                    f,
                    "Function expects {} arguments, but {} were provided",
                    expected_args, found_args
                )
            }
            Self::IncompatibleTypes { from, to, reason, .. } => {
                write!(
                    f,
                    "Cannot cast {:?} to {:?}: {}",
                    from, to, reason
                )
            }
        }
    }
}

impl std::error::Error for GradualError {}

/// Typing context for gradual type elaboration
///
/// Maps variables to their gradual types during elaboration.
#[derive(Debug, Clone)]
pub struct GradualCtx {
    /// Variable bindings: var -> gradual type
    bindings: HashMap<VarId, GradualType>,

    /// Current function name for blame labels
    current_function: Option<String>,

    /// Blame label counter for unique names
    blame_counter: u32,
}

impl GradualCtx {
    /// Create an empty context
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            current_function: None,
            blame_counter: 0,
        }
    }

    /// Create a context with initial bindings
    pub fn with_bindings(bindings: HashMap<VarId, GradualType>) -> Self {
        Self {
            bindings,
            current_function: None,
            blame_counter: 0,
        }
    }

    /// Set the current function name for blame tracking
    pub fn set_function(&mut self, name: impl Into<String>) {
        self.current_function = Some(name.into());
    }

    /// Look up a variable's type
    pub fn lookup(&self, var: VarId) -> Option<&GradualType> {
        self.bindings.get(&var)
    }

    /// Bind a variable to a type
    pub fn bind(&mut self, var: VarId, ty: GradualType) {
        self.bindings.insert(var, ty);
    }

    /// Remove a binding
    pub fn unbind(&mut self, var: VarId) {
        self.bindings.remove(&var);
    }

    /// Create a child context (for entering a scope)
    #[must_use]
    pub fn child(&self) -> Self {
        Self {
            bindings: self.bindings.clone(),
            current_function: self.current_function.clone(),
            blame_counter: self.blame_counter,
        }
    }

    /// Generate a fresh blame label
    pub fn fresh_blame(&mut self, context: &str) -> BlameLabel {
        self.blame_counter += 1;
        let func = self.current_function.as_deref().unwrap_or("anonymous");
        BlameLabel::new(
            format!("{}:{}:{}", func, context, self.blame_counter),
            format!("{}:{}:{}", func, context, self.blame_counter),
        )
    }
}

impl Default for GradualCtx {
    fn default() -> Self {
        Self::new()
    }
}

/// Determine the cast kind needed between two gradual types
///
/// # Rules
/// - If `from` is Dynamic and `to` is not -> Downcast
/// - If `to` is Dynamic and `from` is not -> Upcast
/// - If both are functions -> FuncCast
/// - If both are references -> RefCast
/// - Otherwise -> depends on structure
pub fn determine_cast_kind(from: &GradualType, to: &GradualType) -> Option<CastKind> {
    match (from, to) {
        // Same type - no cast needed
        (f, t) if f == t => None,

        // ? -> T : Downcast
        (GradualType::Dynamic, _) => Some(CastKind::Downcast),

        // T -> ? : Upcast
        (_, GradualType::Dynamic) => Some(CastKind::Upcast),

        // (A -> B) -> (A' -> B') : FuncCast
        (GradualType::GFunc(_, _), GradualType::GFunc(_, _)) => Some(CastKind::FuncCast),

        // &T -> &T' : RefCast
        (GradualType::GRef(_), GradualType::GRef(_)) => Some(CastKind::RefCast),

        // Ground to Ground with same underlying type - no cast
        (GradualType::Ground(t1), GradualType::Ground(t2)) if t1 == t2 => None,

        // Ground to Ground with different types - inconsistent
        (GradualType::Ground(_), GradualType::Ground(_)) => None,

        // Function to non-function or vice versa
        _ => None,
    }
}

/// Create evidence for a cast between two gradual types
///
/// Evidence records how type consistency was established.
pub fn create_evidence(from: &GradualType, to: &GradualType) -> Option<Evidence> {
    match (from, to) {
        // Same type - reflexive evidence
        (f, t) if f == t => Some(Evidence::refl(f.clone())),

        // ? -> T : DynL evidence
        (GradualType::Dynamic, t) => Some(Evidence::dyn_left(t.clone())),

        // T -> ? : DynR evidence
        (f, GradualType::Dynamic) => Some(Evidence::dyn_right(f.clone())),

        // Function types: combine evidence for params (contravariant) and return (covariant)
        (GradualType::GFunc(params1, ret1), GradualType::GFunc(params2, ret2)) => {
            if params1.len() != params2.len() {
                return None;
            }

            // Contravariant: evidence from param2 -> param1
            let param_evs: Option<Vec<_>> = params1
                .iter()
                .zip(params2.iter())
                .map(|(p1, p2)| create_evidence(p2, p1)) // Note: reversed for contravariance
                .collect();

            // Covariant: evidence from ret1 -> ret2
            let ret_ev = create_evidence(ret1, ret2)?;

            Some(Evidence::func(param_evs?, ret_ev))
        }

        // Reference types: evidence for inner type
        (GradualType::GRef(inner1), GradualType::GRef(inner2)) => {
            // References need bidirectional consistency for safety
            // For now, require exact match or dynamic
            if inner1.is_consistent_with(inner2) {
                create_evidence(inner1, inner2)
            } else {
                None
            }
        }

        // Ground types: must be equal
        (GradualType::Ground(t1), GradualType::Ground(t2)) => {
            if t1 == t2 {
                Some(Evidence::refl(from.clone()))
            } else {
                None
            }
        }

        // Incompatible type constructors
        _ => None,
    }
}

/// Insert a cast if needed between two gradual types
///
/// Returns the original expression unchanged if no cast is needed,
/// or wraps it in a GradualCast node with appropriate evidence.
///
/// # Arguments
/// * `expr` - The expression to potentially cast
/// * `from` - The current gradual type of the expression
/// * `to` - The expected/target gradual type
/// * `blame` - Blame label for runtime error tracking
///
/// # Returns
/// * `Ok(expr)` - The (possibly wrapped) expression
/// * `Err(GradualError)` - If types are inconsistent
pub fn insert_cast_if_needed(
    expr: Expr,
    from: &GradualType,
    to: &GradualType,
    blame: &BlameLabel,
) -> Result<Expr, GradualError> {
    // Check consistency first
    if !from.is_consistent_with(to) {
        return Err(GradualError::inconsistent(
            from.clone(),
            to.clone(),
            expr.range,
        ));
    }

    // If types are equal, no cast needed
    if from == to {
        return Ok(expr);
    }

    // Determine cast kind
    let kind = match determine_cast_kind(from, to) {
        Some(k) => k,
        None => return Ok(expr), // No cast needed (types are equivalent)
    };

    // Create evidence (currently unused but validates types are consistent)
    let _evidence = create_evidence(from, to).ok_or_else(|| {
        GradualError::inconsistent(from.clone(), to.clone(), expr.range)
    })?;

    // Wrap in GradualCast
    let range = expr.range;
    let cast_expr = Expr_::GradualCast {
        expr: Box::new(expr),
        from: from.clone(),
        to: to.clone(),
        kind,
        blame: blame.clone(),
    };

    Ok(WithLoc::new(cast_expr, range))
}

/// Result of expression elaboration
pub struct ElaborationResult {
    /// The elaborated expression (with casts inserted)
    pub expr: Expr,

    /// The inferred gradual type
    pub ty: GradualType,

    /// Evidence for the inferred type
    pub evidence: Evidence,
}

impl ElaborationResult {
    /// Create a new elaboration result
    pub fn new(expr: Expr, ty: GradualType, evidence: Evidence) -> Self {
        Self { expr, ty, evidence }
    }

    /// Create result with reflexive evidence
    pub fn reflexive(expr: Expr, ty: GradualType) -> Self {
        let evidence = Evidence::refl(ty.clone());
        Self { expr, ty, evidence }
    }
}

/// Elaborate an expression, inserting casts as needed
///
/// This is the main entry point for cast insertion. It traverses the expression
/// tree, infers gradual types, and inserts casts where types are not statically
/// consistent.
///
/// # Arguments
/// * `expr` - The expression to elaborate
/// * `expected` - The expected gradual type (from context)
/// * `ctx` - The typing context with variable bindings
///
/// # Returns
/// * `Ok((expr, evidence))` - The elaborated expression and evidence
/// * `Err(GradualError)` - If elaboration fails
pub fn elaborate_expr(
    expr: &Expr,
    expected: &GradualType,
    ctx: &mut GradualCtx,
) -> Result<(Expr, Evidence), GradualError> {
    let result = elaborate_expr_infer(expr, ctx)?;

    // Check consistency with expected type
    if !result.ty.is_consistent_with(expected) {
        return Err(GradualError::inconsistent(
            result.ty.clone(),
            expected.clone(),
            expr.range,
        ));
    }

    // Insert cast if needed
    let blame = ctx.fresh_blame("check");
    let cast_expr = insert_cast_if_needed(result.expr, &result.ty, expected, &blame)?;

    // Compose evidence
    let expected_evidence = create_evidence(&result.ty, expected)
        .unwrap_or_else(|| Evidence::refl(expected.clone()));

    let composed = result.evidence.compose(&expected_evidence);
    let final_evidence = match composed {
        super::types::EvidenceResult::Ok(ev) => ev,
        super::types::EvidenceResult::Fail { from, to } => {
            return Err(GradualError::inconsistent(from, to, expr.range));
        }
    };

    Ok((cast_expr, final_evidence))
}

/// Infer the gradual type of an expression without checking against expected type
///
/// Internal function that performs type inference and cast insertion.
fn elaborate_expr_infer(
    expr: &Expr,
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    match &expr.value {
        // === Literals ===
        Expr_::Lit(lit) => {
            let ty = GradualType::from_literal(lit);
            Ok(ElaborationResult::reflexive(expr.clone(), ty))
        }

        // === Variables ===
        Expr_::Var(var) => {
            let ty = ctx
                .lookup(*var)
                .cloned()
                .ok_or_else(|| GradualError::unbound(*var, expr.range))?;
            Ok(ElaborationResult::reflexive(expr.clone(), ty))
        }

        // === Function Application ===
        Expr_::Call(func, args) => {
            elaborate_call(expr.range, func, args, ctx)
        }

        // === If-then-else ===
        Expr_::If(cond, then_branch, else_branch) => {
            elaborate_if(expr.range, cond, then_branch, else_branch, ctx)
        }

        // === Let binding ===
        Expr_::Let { pattern, ty, init, body } => {
            elaborate_let(expr.range, pattern, ty.as_ref(), init, body, ctx)
        }

        // === Lambda ===
        Expr_::Lambda { params, body } => {
            elaborate_lambda(expr.range, params, body, ctx)
        }

        // === Block ===
        Expr_::Block(stmts) => {
            elaborate_block(expr.range, stmts, ctx)
        }

        // === Sequence ===
        Expr_::Seq(first, second) => {
            // Elaborate first, discard its type
            let _ = elaborate_expr_infer(first, ctx)?;
            // Return type of second
            elaborate_expr_infer(second, ctx)
        }

        // === Binary operations ===
        Expr_::Binary(op, lhs, rhs) => {
            elaborate_binary(expr.range, *op, lhs, rhs, ctx)
        }

        // === Unary operations ===
        Expr_::Unary(op, operand) => {
            elaborate_unary(expr.range, *op, operand, ctx)
        }

        // === Field access ===
        Expr_::Field(base, field) => {
            elaborate_field(expr.range, base, *field, ctx)
        }

        // === Index access ===
        Expr_::Index(base, index) => {
            elaborate_index(expr.range, base, index, ctx)
        }

        // === Tuple ===
        Expr_::Tuple(elems) => {
            elaborate_tuple(expr.range, elems, ctx)
        }

        // === Array ===
        Expr_::Array(elems) => {
            elaborate_array(expr.range, elems, ctx)
        }

        // === Match ===
        Expr_::Match(scrutinee, arms) => {
            elaborate_match(expr.range, scrutinee, arms, ctx)
        }

        // === Type cast (static) ===
        Expr_::As(inner, target_ty) => {
            let result = elaborate_expr_infer(inner, ctx)?;
            let target = GradualType::Ground(target_ty.clone());
            let blame = ctx.fresh_blame("as_cast");
            let cast_expr = insert_cast_if_needed(result.expr, &result.ty, &target, &blame)?;
            Ok(ElaborationResult::reflexive(cast_expr, target))
        }

        // === Hole/Error - treat as dynamic ===
        Expr_::Hole | Expr_::Error(_) => {
            Ok(ElaborationResult::reflexive(expr.clone(), GradualType::Dynamic))
        }

        // === Already a gradual cast - return as-is ===
        Expr_::GradualCast { to, .. } => {
            Ok(ElaborationResult::reflexive(expr.clone(), to.clone()))
        }

        // === Default case: treat expression type as dynamic ===
        // This handles cases not yet implemented
        _ => {
            Ok(ElaborationResult::reflexive(expr.clone(), GradualType::Dynamic))
        }
    }
}

/// Elaborate a function call
fn elaborate_call(
    range: Range,
    func: &Expr,
    args: &[Expr],
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    // Elaborate the function
    let func_result = elaborate_expr_infer(func, ctx)?;

    // Get parameter and return types
    let (param_types, ret_type) = match &func_result.ty {
        GradualType::GFunc(params, ret) => (params.clone(), ret.as_ref().clone()),
        GradualType::Dynamic => {
            // Dynamic function - all args are dynamic, return is dynamic
            let dynamic_params: Vec<_> = args.iter().map(|_| GradualType::Dynamic).collect();
            (dynamic_params, GradualType::Dynamic)
        }
        GradualType::Ground(ref ty) if *ty == BrrrType::NEVER => {
            // Never type propagates
            return Ok(ElaborationResult::reflexive(
                WithLoc::new(Expr_::Call(Box::new(func_result.expr), args.to_vec()), range),
                GradualType::Ground(BrrrType::NEVER),
            ));
        }
        _ => {
            return Err(GradualError::IncompatibleTypes {
                from: func_result.ty.clone(),
                to: GradualType::Dynamic,
                reason: "not a function type".to_string(),
                span: func.range,
            });
        }
    };

    // Check argument count
    if param_types.len() != args.len() {
        return Err(GradualError::ApplicationError {
            expected_args: param_types.len(),
            found_args: args.len(),
            span: range,
        });
    }

    // Elaborate each argument and insert casts
    let mut elaborated_args = Vec::with_capacity(args.len());
    for (arg, param_ty) in args.iter().zip(param_types.iter()) {
        let arg_result = elaborate_expr_infer(arg, ctx)?;
        let blame = ctx.fresh_blame("arg");
        let cast_arg = insert_cast_if_needed(arg_result.expr, &arg_result.ty, param_ty, &blame)?;
        elaborated_args.push(cast_arg);
    }

    // Build the elaborated call
    let call_expr = Expr_::Call(Box::new(func_result.expr), elaborated_args);
    Ok(ElaborationResult::reflexive(
        WithLoc::new(call_expr, range),
        ret_type,
    ))
}

/// Elaborate an if-then-else expression
fn elaborate_if(
    range: Range,
    cond: &Expr,
    then_branch: &Expr,
    else_branch: &Expr,
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    // Condition must be Bool (or consistent with Bool)
    let cond_result = elaborate_expr_infer(cond, ctx)?;
    let bool_ty = GradualType::Ground(BrrrType::BOOL);
    let blame_cond = ctx.fresh_blame("if_cond");
    let cast_cond = insert_cast_if_needed(cond_result.expr, &cond_result.ty, &bool_ty, &blame_cond)?;

    // Elaborate branches
    let then_result = elaborate_expr_infer(then_branch, ctx)?;
    let else_result = elaborate_expr_infer(else_branch, ctx)?;

    // Join the branch types
    let joined_ty = then_result.ty.join(&else_result.ty).unwrap_or(GradualType::Dynamic);

    // Cast branches to joined type
    let blame_then = ctx.fresh_blame("if_then");
    let blame_else = ctx.fresh_blame("if_else");
    let cast_then = insert_cast_if_needed(then_result.expr, &then_result.ty, &joined_ty, &blame_then)?;
    let cast_else = insert_cast_if_needed(else_result.expr, &else_result.ty, &joined_ty, &blame_else)?;

    let if_expr = Expr_::If(
        Box::new(cast_cond),
        Box::new(cast_then),
        Box::new(cast_else),
    );
    Ok(ElaborationResult::reflexive(
        WithLoc::new(if_expr, range),
        joined_ty,
    ))
}

/// Elaborate a let binding
fn elaborate_let(
    range: Range,
    pattern: &crate::expr::Pattern,
    ty_annotation: Option<&BrrrType>,
    init: &Expr,
    body: &Expr,
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    // Elaborate the initializer
    let init_result = elaborate_expr_infer(init, ctx)?;

    // Determine the binding type
    let binding_ty = if let Some(ann) = ty_annotation {
        let ann_ty = GradualType::Ground(ann.clone());
        let blame = ctx.fresh_blame("let_ann");
        let _ = insert_cast_if_needed(init_result.expr.clone(), &init_result.ty, &ann_ty, &blame)?;
        ann_ty
    } else {
        init_result.ty.clone()
    };

    // Bind pattern variables
    let mut child_ctx = ctx.child();
    bind_pattern_vars(pattern, &binding_ty, &mut child_ctx);

    // Elaborate body with extended context
    let body_result = elaborate_expr_infer(body, &mut child_ctx)?;

    let let_expr = Expr_::Let {
        pattern: pattern.clone(),
        ty: ty_annotation.cloned(),
        init: Box::new(init_result.expr),
        body: Box::new(body_result.expr),
    };
    Ok(ElaborationResult::reflexive(
        WithLoc::new(let_expr, range),
        body_result.ty,
    ))
}

/// Bind pattern variables to types in context
fn bind_pattern_vars(pattern: &crate::expr::Pattern, ty: &GradualType, ctx: &mut GradualCtx) {
    use crate::expr::Pattern_;
    match &pattern.value {
        Pattern_::Var(var) => {
            ctx.bind(*var, ty.clone());
        }
        Pattern_::Tuple(pats) => {
            // For tuples, we'd need to extract element types
            // For now, bind each to dynamic
            for pat in pats {
                bind_pattern_vars(pat, &GradualType::Dynamic, ctx);
            }
        }
        Pattern_::Wild | Pattern_::Lit(_) => {
            // No bindings
        }
        _ => {
            // Default: treat as dynamic
        }
    }
}

/// Elaborate a lambda expression
fn elaborate_lambda(
    range: Range,
    params: &[(VarId, BrrrType)],
    body: &Expr,
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    // Create child context with parameter bindings
    let mut child_ctx = ctx.child();
    let param_types: Vec<GradualType> = params
        .iter()
        .map(|(var, ty)| {
            let g_ty = GradualType::Ground(ty.clone());
            child_ctx.bind(*var, g_ty.clone());
            g_ty
        })
        .collect();

    // Elaborate body
    let body_result = elaborate_expr_infer(body, &mut child_ctx)?;

    // Build function type
    let func_ty = GradualType::GFunc(param_types, Box::new(body_result.ty));

    let lambda_expr = Expr_::Lambda {
        params: params.to_vec(),
        body: Box::new(body_result.expr),
    };
    Ok(ElaborationResult::reflexive(
        WithLoc::new(lambda_expr, range),
        func_ty,
    ))
}

/// Elaborate a block expression
fn elaborate_block(
    range: Range,
    stmts: &[Expr],
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    if stmts.is_empty() {
        return Ok(ElaborationResult::reflexive(
            WithLoc::new(Expr_::Block(vec![]), range),
            GradualType::Ground(BrrrType::UNIT),
        ));
    }

    let mut elaborated_stmts = Vec::with_capacity(stmts.len());
    let mut last_ty = GradualType::Ground(BrrrType::UNIT);

    for stmt in stmts {
        let result = elaborate_expr_infer(stmt, ctx)?;
        elaborated_stmts.push(result.expr);
        last_ty = result.ty;
    }

    Ok(ElaborationResult::reflexive(
        WithLoc::new(Expr_::Block(elaborated_stmts), range),
        last_ty,
    ))
}

/// Elaborate a binary operation
fn elaborate_binary(
    range: Range,
    op: crate::expr::BinaryOp,
    lhs: &Expr,
    rhs: &Expr,
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    use crate::expr::BinaryOp;

    let lhs_result = elaborate_expr_infer(lhs, ctx)?;
    let rhs_result = elaborate_expr_infer(rhs, ctx)?;

    // Determine result type based on operator
    let result_ty = match op {
        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
            GradualType::Ground(BrrrType::BOOL)
        }
        BinaryOp::And | BinaryOp::Or => GradualType::Ground(BrrrType::BOOL),
        _ => {
            // Arithmetic operations - join operand types
            lhs_result.ty.join(&rhs_result.ty).unwrap_or(GradualType::Dynamic)
        }
    };

    let binary_expr = Expr_::Binary(op, Box::new(lhs_result.expr), Box::new(rhs_result.expr));
    Ok(ElaborationResult::reflexive(
        WithLoc::new(binary_expr, range),
        result_ty,
    ))
}

/// Elaborate a unary operation
fn elaborate_unary(
    range: Range,
    op: crate::expr::UnaryOp,
    operand: &Expr,
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    use crate::expr::UnaryOp;

    let operand_result = elaborate_expr_infer(operand, ctx)?;

    let result_ty = match op {
        UnaryOp::Not => GradualType::Ground(BrrrType::BOOL),
        UnaryOp::Deref => {
            // Deref of &T or &mut T
            match &operand_result.ty {
                GradualType::GRef(inner) => inner.as_ref().clone(),
                GradualType::Dynamic => GradualType::Dynamic,
                _ => operand_result.ty.clone(),
            }
        }
        UnaryOp::Ref => GradualType::GRef(Box::new(operand_result.ty.clone())),
        UnaryOp::RefMut => GradualType::GRef(Box::new(operand_result.ty.clone())),
        _ => operand_result.ty.clone(),
    };

    let unary_expr = Expr_::Unary(op, Box::new(operand_result.expr));
    Ok(ElaborationResult::reflexive(
        WithLoc::new(unary_expr, range),
        result_ty,
    ))
}

/// Elaborate field access
fn elaborate_field(
    range: Range,
    base: &Expr,
    _field: Spur,
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    let base_result = elaborate_expr_infer(base, ctx)?;

    // Field access on dynamic type returns dynamic
    let result_ty = match &base_result.ty {
        GradualType::Dynamic => GradualType::Dynamic,
        // For ground types, we'd need type information to determine field type
        // For now, return dynamic
        _ => GradualType::Dynamic,
    };

    let field_expr = Expr_::Field(Box::new(base_result.expr), _field);
    Ok(ElaborationResult::reflexive(
        WithLoc::new(field_expr, range),
        result_ty,
    ))
}

/// Elaborate index access
fn elaborate_index(
    range: Range,
    base: &Expr,
    index: &Expr,
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    let base_result = elaborate_expr_infer(base, ctx)?;
    let index_result = elaborate_expr_infer(index, ctx)?;

    // Index should be integer
    let int_ty = GradualType::Ground(BrrrType::Numeric(crate::types::NumericType::Int(
        crate::types::IntType::USize,
    )));
    let blame = ctx.fresh_blame("index");
    let cast_index = insert_cast_if_needed(index_result.expr, &index_result.ty, &int_ty, &blame)?;

    // Result type is dynamic unless we can infer from array type
    let result_ty = match &base_result.ty {
        GradualType::Dynamic => GradualType::Dynamic,
        // For array types, element type would be extracted
        _ => GradualType::Dynamic,
    };

    let index_expr = Expr_::Index(Box::new(base_result.expr), Box::new(cast_index));
    Ok(ElaborationResult::reflexive(
        WithLoc::new(index_expr, range),
        result_ty,
    ))
}

/// Elaborate a tuple expression
fn elaborate_tuple(
    range: Range,
    elems: &[Expr],
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    let mut elaborated_elems = Vec::with_capacity(elems.len());

    for elem in elems {
        let result = elaborate_expr_infer(elem, ctx)?;
        elaborated_elems.push(result.expr);
    }

    // For now, tuple type is treated as dynamic
    // A full implementation would track element types
    let tuple_expr = Expr_::Tuple(elaborated_elems);
    Ok(ElaborationResult::reflexive(
        WithLoc::new(tuple_expr, range),
        GradualType::Dynamic,
    ))
}

/// Elaborate an array expression
fn elaborate_array(
    range: Range,
    elems: &[Expr],
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    if elems.is_empty() {
        return Ok(ElaborationResult::reflexive(
            WithLoc::new(Expr_::Array(vec![]), range),
            GradualType::Dynamic,
        ));
    }

    let mut elaborated_elems = Vec::with_capacity(elems.len());
    let mut elem_ty = GradualType::Dynamic;

    for elem in elems {
        let result = elaborate_expr_infer(elem, ctx)?;
        elem_ty = elem_ty.join(&result.ty).unwrap_or(GradualType::Dynamic);
        elaborated_elems.push(result.expr);
    }

    // Cast all elements to the joined type
    let mut cast_elems = Vec::with_capacity(elaborated_elems.len());
    for (i, elem) in elaborated_elems.into_iter().enumerate() {
        let _blame = ctx.fresh_blame(&format!("array_elem_{}", i));
        // Re-infer type for casting (simplified - just use the element as-is)
        cast_elems.push(elem);
    }

    let array_expr = Expr_::Array(cast_elems);
    Ok(ElaborationResult::reflexive(
        WithLoc::new(array_expr, range),
        GradualType::Dynamic, // Array type would be more precise
    ))
}

/// Elaborate a match expression
fn elaborate_match(
    range: Range,
    scrutinee: &Expr,
    arms: &[crate::expr::MatchArm],
    ctx: &mut GradualCtx,
) -> Result<ElaborationResult, GradualError> {
    let scrutinee_result = elaborate_expr_infer(scrutinee, ctx)?;

    let mut elaborated_arms = Vec::with_capacity(arms.len());
    let mut result_ty = GradualType::Ground(BrrrType::NEVER);

    for arm in arms {
        // Create child context with pattern bindings
        let mut child_ctx = ctx.child();
        bind_pattern_vars(&arm.pattern, &scrutinee_result.ty, &mut child_ctx);

        // Elaborate guard if present
        let elaborated_guard = if let Some(guard) = &arm.guard {
            let guard_result = elaborate_expr_infer(guard, &mut child_ctx)?;
            let bool_ty = GradualType::Ground(BrrrType::BOOL);
            let blame = ctx.fresh_blame("match_guard");
            Some(insert_cast_if_needed(guard_result.expr, &guard_result.ty, &bool_ty, &blame)?)
        } else {
            None
        };

        // Elaborate body
        let body_result = elaborate_expr_infer(&arm.body, &mut child_ctx)?;
        result_ty = result_ty.join(&body_result.ty).unwrap_or(GradualType::Dynamic);

        elaborated_arms.push(crate::expr::MatchArm {
            range: arm.range,
            pattern: arm.pattern.clone(),
            guard: elaborated_guard,
            body: body_result.expr,
        });
    }

    let match_expr = Expr_::Match(Box::new(scrutinee_result.expr), elaborated_arms);
    Ok(ElaborationResult::reflexive(
        WithLoc::new(match_expr, range),
        result_ty,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Literal;

    fn make_int_expr(n: i32) -> Expr {
        WithLoc::synthetic(Expr_::Lit(Literal::i32(n)))
    }

    fn make_bool_expr(b: bool) -> Expr {
        WithLoc::synthetic(Expr_::Lit(Literal::Bool(b)))
    }

    #[test]
    fn test_cast_kind_properties() {
        assert!(!CastKind::Upcast.may_fail());
        assert!(CastKind::Upcast.always_succeeds());

        assert!(CastKind::Downcast.may_fail());
        assert!(!CastKind::Downcast.always_succeeds());

        assert!(CastKind::FuncCast.may_fail());
        assert!(CastKind::FuncCast.is_function_cast());
    }

    #[test]
    fn test_blame_label() {
        let label = BlameLabel::new("producer", "consumer");
        assert_eq!(label.positive, "producer");
        assert_eq!(label.negative, "consumer");

        let swapped = label.swap();
        assert_eq!(swapped.positive, "consumer");
        assert_eq!(swapped.negative, "producer");
    }

    #[test]
    fn test_cast_creation() {
        let int_ty = GradualType::Ground(BrrrType::Numeric(crate::types::NumericType::Int(
            crate::types::IntType::I32,
        )));
        let blame = BlameLabel::new("test", "test");

        let upcast = Cast::upcast(int_ty.clone(), blame.clone());
        assert_eq!(upcast.kind, CastKind::Upcast);
        assert!(!upcast.may_fail());

        let downcast = Cast::downcast(int_ty, blame);
        assert_eq!(downcast.kind, CastKind::Downcast);
        assert!(downcast.may_fail());
    }

    #[test]
    fn test_determine_cast_kind() {
        let int_ty = GradualType::Ground(BrrrType::BOOL);
        let dyn_ty = GradualType::Dynamic;

        // Same type - no cast
        assert!(determine_cast_kind(&int_ty, &int_ty).is_none());

        // T -> ? : Upcast
        assert_eq!(determine_cast_kind(&int_ty, &dyn_ty), Some(CastKind::Upcast));

        // ? -> T : Downcast
        assert_eq!(determine_cast_kind(&dyn_ty, &int_ty), Some(CastKind::Downcast));

        // Function cast
        let func1 = GradualType::func(vec![int_ty.clone()], int_ty.clone());
        let func2 = GradualType::func(vec![dyn_ty.clone()], dyn_ty.clone());
        assert_eq!(determine_cast_kind(&func1, &func2), Some(CastKind::FuncCast));
    }

    #[test]
    fn test_create_evidence() {
        let bool_ty = GradualType::Ground(BrrrType::BOOL);
        let dyn_ty = GradualType::Dynamic;

        // Reflexive evidence
        let ev = create_evidence(&bool_ty, &bool_ty);
        assert!(matches!(ev, Some(Evidence::Refl(_))));

        // DynR evidence (upcast)
        let ev = create_evidence(&bool_ty, &dyn_ty);
        assert!(matches!(ev, Some(Evidence::DynR(_))));

        // DynL evidence (downcast)
        let ev = create_evidence(&dyn_ty, &bool_ty);
        assert!(matches!(ev, Some(Evidence::DynL(_))));
    }

    #[test]
    fn test_insert_cast_no_cast_needed() {
        let expr = make_int_expr(42);
        let int_ty = GradualType::Ground(BrrrType::Numeric(crate::types::NumericType::Int(
            crate::types::IntType::I32,
        )));
        let blame = BlameLabel::new("test", "test");

        let result = insert_cast_if_needed(expr.clone(), &int_ty, &int_ty, &blame);
        assert!(result.is_ok());

        let cast_expr = result.unwrap();
        // Should be the same expression (no cast wrapper)
        assert!(!matches!(cast_expr.value, Expr_::GradualCast { .. }));
    }

    #[test]
    fn test_insert_cast_upcast() {
        let expr = make_int_expr(42);
        let int_ty = GradualType::Ground(BrrrType::Numeric(crate::types::NumericType::Int(
            crate::types::IntType::I32,
        )));
        let dyn_ty = GradualType::Dynamic;
        let blame = BlameLabel::new("test", "test");

        let result = insert_cast_if_needed(expr, &int_ty, &dyn_ty, &blame);
        assert!(result.is_ok());

        let cast_expr = result.unwrap();
        match cast_expr.value {
            Expr_::GradualCast { kind, .. } => assert_eq!(kind, CastKind::Upcast),
            _ => panic!("Expected GradualCast"),
        }
    }

    #[test]
    fn test_insert_cast_downcast() {
        let expr = make_int_expr(42);
        let int_ty = GradualType::Ground(BrrrType::Numeric(crate::types::NumericType::Int(
            crate::types::IntType::I32,
        )));
        let dyn_ty = GradualType::Dynamic;
        let blame = BlameLabel::new("test", "test");

        let result = insert_cast_if_needed(expr, &dyn_ty, &int_ty, &blame);
        assert!(result.is_ok());

        let cast_expr = result.unwrap();
        match cast_expr.value {
            Expr_::GradualCast { kind, .. } => assert_eq!(kind, CastKind::Downcast),
            _ => panic!("Expected GradualCast"),
        }
    }

    #[test]
    fn test_insert_cast_inconsistent() {
        let expr = make_int_expr(42);
        let int_ty = GradualType::Ground(BrrrType::Numeric(crate::types::NumericType::Int(
            crate::types::IntType::I32,
        )));
        let bool_ty = GradualType::Ground(BrrrType::BOOL);
        let blame = BlameLabel::new("test", "test");

        // Int and Bool are not consistent
        let result = insert_cast_if_needed(expr, &int_ty, &bool_ty, &blame);
        assert!(result.is_err());
        assert!(matches!(result, Err(GradualError::Inconsistent { .. })));
    }

    #[test]
    fn test_gradual_ctx() {
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let mut ctx = GradualCtx::new();
        ctx.set_function("test_fn");

        let ty = GradualType::Ground(BrrrType::BOOL);
        ctx.bind(x, ty.clone());

        assert_eq!(ctx.lookup(x), Some(&ty));

        let blame = ctx.fresh_blame("call");
        assert!(blame.positive.contains("test_fn"));
    }

    #[test]
    fn test_elaborate_literal() {
        let expr = make_int_expr(42);
        let dyn_ty = GradualType::Dynamic;
        let mut ctx = GradualCtx::new();

        let result = elaborate_expr(&expr, &dyn_ty, &mut ctx);
        assert!(result.is_ok());

        let (elaborated, _evidence) = result.unwrap();
        // Should have upcast wrapper since literal is Int, expected is Dynamic
        assert!(matches!(elaborated.value, Expr_::GradualCast { kind: CastKind::Upcast, .. }));
    }

    #[test]
    fn test_elaborate_literal_same_type() {
        let expr = make_bool_expr(true);
        let bool_ty = GradualType::Ground(BrrrType::BOOL);
        let mut ctx = GradualCtx::new();

        let result = elaborate_expr(&expr, &bool_ty, &mut ctx);
        assert!(result.is_ok());

        let (elaborated, _evidence) = result.unwrap();
        // No cast needed - types match
        assert!(!matches!(elaborated.value, Expr_::GradualCast { .. }));
    }

    #[test]
    fn test_gradual_error_display() {
        let int_ty = GradualType::Ground(BrrrType::BOOL);
        let string_ty = GradualType::Ground(BrrrType::STRING);

        let err = GradualError::inconsistent(int_ty, string_ty, Range::SYNTHETIC);
        let msg = format!("{}", err);
        assert!(msg.contains("not consistent"));
    }

    #[test]
    fn test_evidence_composition_in_elaboration() {
        let bool_ty = GradualType::Ground(BrrrType::BOOL);
        let dyn_ty = GradualType::Dynamic;

        // DynL composed with DynR should give Refl
        let ev1 = Evidence::dyn_left(bool_ty.clone());
        let ev2 = Evidence::dyn_right(bool_ty.clone());

        let result = ev1.compose(&ev2);
        assert!(matches!(result, super::super::types::EvidenceResult::Ok(Evidence::Refl(_))));
    }
}
