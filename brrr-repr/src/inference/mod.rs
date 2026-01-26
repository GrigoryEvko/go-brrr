//! Type inference module
//!
//! Implements bidirectional Hindley-Milner type inference following F* patterns.
//!
//! # Core Algorithm
//!
//! The inference algorithm is based on Algorithm W with bidirectional typing:
//!
//! 1. **Synthesis** (`infer_expr`): Infers a type for an expression without guidance.
//!    Works bottom-up, synthesizing types from sub-expressions.
//!
//! 2. **Analysis** (`check_expr`): Checks an expression against an expected type.
//!    Works top-down, propagating type information to sub-expressions.
//!
//! 3. **Unification** (`unify`): Solves type equality constraints by finding
//!    a most general unifier for two types.
//!
//! 4. **Generalization** (`generalize`): Quantifies over free type variables
//!    at let-binding sites to enable polymorphism.
//!
//! 5. **Instantiation** (`instantiate`): Creates fresh type variables for
//!    quantified variables when using a polymorphic binding.
//!
//! # Modules
//!
//! - `types` - Type inference state, constraints, and errors
//! - `infer` - Core inference functions (infer_expr, check_expr, unify, etc.)
//! - `effects` - Effect inference with row polymorphism
//! - `modes` - Mode (linearity) checking pass
//! - `session` - Session type checking
//! - `coeffects` - Coeffect inference (liveness, usage, capabilities)
//! - `regions` - Region (lifetime) inference for borrow checking
//!
//! # Example Usage
//!
//! ```ignore
//! use lasso::Rodeo;
//! use brrr_repr::inference::{InferenceState, TypeCtx, infer_expr, solve_constraints};
//! use brrr_repr::BrrrType;
//!
//! let mut rodeo = Rodeo::default();
//! let mut ctx = TypeCtx::new();
//! let mut state = InferenceState::new();
//!
//! // Add variable binding: x : Bool
//! let x = rodeo.get_or_intern("x");
//! ctx.extend_mono(x, BrrrType::BOOL);
//!
//! // Infer type of expression
//! let ty = infer_expr(&ctx, &expr, &mut state, &mut |s| rodeo.get_or_intern(s));
//!
//! // Solve accumulated constraints
//! solve_constraints(&mut state, &mut |s| rodeo.get_or_intern(s));
//!
//! // Apply final substitution
//! let final_ty = state.apply(&ty);
//! ```

pub mod coeffects;
mod effects;
mod infer;
pub mod modes;
pub mod regions;
pub mod resolve;
mod session;
mod types;

// Re-export from effects module
pub use effects::{
    apply_effect_subst, check_handler, infer_effects, unify_rows,
    EffectConstraint, EffectError, EffectInferenceState,
};

// Re-export from types module
pub use types::{
    apply_substitution, free_type_vars, InferenceState, TypeConstraint, TypeCtx, TypeError,
    TypeErrorKind,
};

// Re-export from infer module
pub use infer::{
    // Core inference functions
    infer_expr, check_expr,
    // Unification
    unify,
    // Generalization and instantiation
    generalize, instantiate,
    // Constraint solving
    solve_constraints,
};

// Re-export from session module
pub use session::{
    // State and errors
    SessionCheckState, SessionError, SessionCheckResult,
    // Core checking functions
    check_send, check_recv, check_select, check_branch,
    check_new_channel, check_new_channel_explicit, check_close,
    advance_branch,
    // Verification functions
    verify_duality, verify_all_sessions_ended, verify_all_sessions_ended_at,
    // Helpers
    is_session_ended,
};

// Re-export from modes module
pub use modes::{
    // State and errors
    ModeCheckState, ModeError,
    // Core checking functions
    mode_check_expr, mode_check_function,
    // Pattern mode extension
    extend_pattern_with_mode,
};

// Re-export from coeffects module
pub use coeffects::{
    // Coeffect info type
    CoeffectInfo,
    // Context type and operations
    CoeffectCtx, empty_coeffect_ctx, lookup_coeffect, set_coeffect, mark_used, remove_coeffect,
    // Context combination operations
    coeffect_ctx_join, coeffect_ctx_sequence, scale_coeffect_ctx, restrict_coeffect_ctx,
    extend_coeffect_ctx,
    // Inference state and errors
    CoeffectInferenceState, CoeffectError,
    // Capability checking
    check_capability, require_capability,
    // Core inference function
    infer_coeffects,
};

// Re-export from regions module
pub use regions::{
    // Region variable type
    RegionVar,
    // Inference state
    RegionInferenceState,
    // Constraint types
    RegionConstraint,
    // Error types
    RegionError,
    // Core inference function
    infer_regions,
    // Constraint solving
    solve_region_constraints,
    // Borrow checker integration
    check_borrow_regions,
    // Helper functions
    scope_region, static_region, is_concrete_region,
};

// Re-export from resolve module
pub use resolve::{
    // State types
    ResolutionState, Scope, VarBinding, TypeBinding, GlobalRef,
    // Error types
    ResolutionError, ResolutionErrorKind,
    // Core resolution functions
    resolve_module, resolve_expr,
};
