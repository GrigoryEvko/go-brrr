//! Gradual typing for AGT (Abstracting Gradual Typing)
//!
//! Implements the evidence-based blame tracking system enabling safe
//! interoperation between statically-typed and dynamically-typed code.
//!
//! # Overview
//!
//! Gradual typing allows mixing static and dynamic typing in a principled way:
//! - The dynamic type `?` is consistent with all types
//! - Evidence tracks how consistency was established for blame assignment
//! - Runtime casts are inserted where types are not statically known
//!
//! # AGT Semantics
//!
//! AGT (Abstracting Gradual Typing) interprets gradual types as sets of static types:
//! - `gamma(?) = { all types }` - dynamic type represents all possible types
//! - `gamma(Ground(T)) = { T }` - ground type represents just T
//! - Consistency `G1 ~ G2` iff `gamma(G1) ∩ gamma(G2) ≠ ∅`
//!
//! # Evidence-Based Blame Tracking
//!
//! Evidence records how type consistency was established:
//! - `Refl(G)` - type is consistent with itself (no cast needed)
//! - `DynL(G)` - `? ~ G` (cast from dynamic, may fail at runtime)
//! - `DynR(G)` - `G ~ ?` (cast to dynamic, always succeeds)
//! - `Func(evs, ev)` - function consistency with contravariant/covariant evidence
//!
//! # Cast Elaboration
//!
//! When expressions involve gradual types, explicit casts are inserted:
//! - `Upcast`: T -> ? (always succeeds)
//! - `Downcast`: ? -> T (may fail at runtime, carries blame)
//! - `FuncCast`: (A -> B) -> (A' -> B') (wraps function with casts)
//!
//! The `elaborate_expr` function traverses expressions and inserts `GradualCast`
//! nodes wherever type consistency requires runtime checks.
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::gradual::{GradualType, Evidence};
//! use brrr_repr::types::BrrrType;
//!
//! // A function from ? to Bool
//! let func_ty = GradualType::func(
//!     vec![GradualType::dynamic()],
//!     GradualType::ground(BrrrType::BOOL),
//! );
//!
//! assert!(func_ty.contains_dynamic());
//! assert!(!func_ty.is_static());
//! ```
//!
//! # References
//!
//! - Garcia, Cimini (2015). Abstracting Gradual Typing.
//! - Siek, Vitousek, et al. (2015). Refined Criteria for Gradual Typing.

pub mod elaborate;
pub mod types;

pub use elaborate::{
    BlameLabel, Cast, CastKind, ElaborationResult, GradualCtx, GradualError,
    create_evidence, determine_cast_kind, elaborate_expr, insert_cast_if_needed,
};
pub use types::{compose_evidence, ConcretizationResult, Evidence, EvidenceResult, GradualType};
