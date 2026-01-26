//! .brrr Representation Engine
//!
//! This module provides serialization/deserialization for the brrr-lang IR
//! into efficient binary (.brrr) and human-readable text (.brrrx) formats.
//!
//! # UTF-8 Only
//! Uses proper mathematical Unicode symbols throughout - no ASCII fallback.
//!
//! # Format Overview
//! - `.brrr` - Binary format with columnar storage, string interning, content hashing
//! - `.brrrx` - Text format with UTF-8 math notation for debugging/inspection

pub mod types;
pub mod expr;
pub mod effects;
pub mod coeffects;
pub mod modes;
pub mod session;
pub mod borrow;
pub mod boundary;
pub mod encoding;
pub mod security;
pub mod verification;
pub mod gradual;
pub mod inference;
pub mod decl;
pub mod pipeline;
mod error;
mod api;

#[cfg(test)]
mod tests;

pub use api::{BrrrDecoder, BrrrEncoder, BrrrModule, Format};
pub use error::{DecodeError, EncodeError, ReprError, ReprResult};
pub use types::{BrrrType, FuncType, NumericType, ParamType, PrimKind, WrapperKind};
pub use expr::{Expr, Expr_, Literal, Pattern, Pattern_, Pos, Range, WithLoc};
pub use effects::{AbstractLoc, EffectOp, EffectRow, EffectRowKind, EffectVar, IoSink, IoSource};
pub use coeffects::{
    // Liveness coeffect
    Liveness, liveness_add, liveness_mul,
    // Usage coeffect
    Usage, usage_add, usage_mul,
    // Flat and structural coeffects
    FlatCoeffect, StructuralCoeffect,
    // Context types and helpers
    CoeffectCtx, UsageCtx, empty_liveness_ctx, empty_usage_ctx,
    join_liveness_ctx, join_usage_ctx, mark_live, mark_dead, is_live, use_var,
};
pub use modes::{
    Mode, RefKind, ExtendedMode, VarId as ModeVarId,
    // Linear context types and operations
    LinEntry, LinCtx,
    empty_lin_ctx, lookup_lin, extend_lin, use_lin,
    split_lin_ctx, join_lin_ctx, is_fully_consumed,
    weaken_lin, contract_lin,
};
pub use session::{SessionType, SessionVar};
// Note: borrow module has pre-existing export issues, importing specific types directly
// pub use borrow::{LoanId, ...};
pub use security::{
    Confidentiality, Integrity, SanitizerAnnotation, SecurityLabel, SecurityRole, SinkAnnotation,
    SourceAnnotation, TaintKind,
};
pub use boundary::{
    BoundaryIssue, BoundaryIssueSeverity, FfiSafeType, NodeId, NodeIdCounter, TaintSource,
    check_ffi_safe, check_ffi_safe_at, describe_issue, issue_location, severity,
};
pub use verification::{
    // Formula types
    CmpOp, DepVar, Formula, FALSE, TRUE,
    // Formula constructors
    formula_and, formula_and_all, formula_iff, formula_implies, formula_not, formula_or,
    formula_or_all,
    // Contract types
    AnnotatedWhile, Assertion, Contract, ContractedFunction, OldRef, VarId,
    // Contract helpers
    spec_old, spec_result, trivial_contract, OLD_VAR_PREFIX, RESULT_VAR_NAME,
    // Propositional equality
    EqProof, EqWitness, DecEqResult,
    refl, sym, trans, cong,
    has_decidable_eq, syntactic_eq,
};
pub use gradual::{Evidence, GradualType};
pub use inference::{
    // Type inference types
    InferenceState, TypeConstraint, TypeCtx, TypeError, TypeErrorKind,
    // Type inference functions
    infer_expr, check_expr, unify, generalize, instantiate, solve_constraints,
    // Substitution operations
    apply_substitution, free_type_vars,
    // Effect inference types
    EffectConstraint, EffectError, EffectInferenceState,
    // Effect inference functions
    apply_effect_subst, check_handler, infer_effects, unify_rows,
    // Session type checking
    SessionCheckState, SessionError, SessionCheckResult,
    check_send, check_recv, check_select, check_branch,
    check_new_channel, check_new_channel_explicit, check_close,
    advance_branch, verify_duality, verify_all_sessions_ended,
    verify_all_sessions_ended_at, is_session_ended,
    // Mode (linearity) checking
    ModeCheckState, ModeError, mode_check_expr, mode_check_function,
    extend_pattern_with_mode,
    // Coeffect inference types
    CoeffectInfo, CoeffectInferenceState, CoeffectError,
    // Coeffect inference functions
    infer_coeffects, check_capability, require_capability,
    // Coeffect context operations
    empty_coeffect_ctx, lookup_coeffect, set_coeffect, mark_used, remove_coeffect,
    coeffect_ctx_join, coeffect_ctx_sequence, scale_coeffect_ctx, restrict_coeffect_ctx,
    extend_coeffect_ctx,
    // Region inference types
    RegionVar, RegionInferenceState, RegionConstraint, RegionError,
    // Region inference functions
    infer_regions, solve_region_constraints, check_borrow_regions,
    // Region helper functions
    scope_region, static_region, is_concrete_region,
};
pub use decl::{
    // Module identity
    ModuleId, ModuleIdCounter, QualifiedName,
    // Import system
    Import, ImportItem, ImportItems,
    // Export system
    Export,
    // Module structure (simple)
    Declaration, Module, SourceFile,
    // Full compilation unit
    BrrrModuleData,
    // Detailed declaration types
    FunctionDef, TypeDef, TraitDef, ImplBlock,
    // Associated types and trait references
    AssocTypeDef, AssocTypeBinding, TraitRef,
    // Extern items
    ExternItem,
    // Full declaration enum
    FullDeclaration,
};
pub use pipeline::{
    // Configuration
    CompilationConfig,
    // Compilation functions
    compile, compile_with_recovery, compile_to_brrrx,
    // Result types
    CompilationResult, CompilationError, CompilationWarning,
    // Error types
    ErrorCategory, VerificationError, VerificationErrorKind,
    ResolutionError, ResolutionErrorKind, WarningKind,
    // Analysis info types
    TypeInfo, EffectInfo, BorrowInfo,
    HandlerInfo, LoanOrigin, RegionConstraint as PipelineRegionConstraint,
    VerificationCondition,
    // Pass identification
    PassId,
    // Analysis context
    AnalysisContext,
};
