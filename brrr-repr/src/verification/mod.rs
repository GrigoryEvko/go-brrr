//! Verification types for refinement predicates and contracts
//!
//! Mirrors F* DependentTypes.fsti for first-order logic formulas used
//! in refinement types `{ x : T | phi }` and Contracts.fst for
//! Hoare-style function contracts.
//!
//! # Overview
//!
//! This module provides:
//! - [`Formula`] - First-order logic formulas for refinements
//! - [`CmpOp`] - Comparison operators for predicates
//! - [`DepVar`] - Dependent variables bound by quantifiers
//! - [`Contract`] - Hoare-style pre/post conditions
//! - [`ContractedFunction`] - Functions with attached contracts
//! - [`AnnotatedWhile`] - Loops with invariant annotations
//! - [`Assertion`] - Runtime assertions
//! - [`EqWitness`] - Propositional equality witnesses
//! - [`EqProof`] - Symbolic equality proofs
//! - Helper functions for formula and contract construction
//!
//! # Formula Example
//!
//! ```ignore
//! use brrr_repr::verification::{Formula, CmpOp, formula_and, formula_implies};
//!
//! // x > 0 /\ x < 100
//! let in_range = formula_and(
//!     Formula::cmp(CmpOp::Gt, x_expr, zero_expr),
//!     Formula::cmp(CmpOp::Lt, x_expr, hundred_expr),
//! );
//!
//! // in_range => x != 0
//! let implication = formula_implies(in_range, Formula::ne(x_expr, zero_expr));
//! ```
//!
//! # Contract Example
//!
//! ```ignore
//! use brrr_repr::verification::{Contract, Formula, CmpOp, trivial_contract};
//!
//! // val abs: x:i32 -> Pure i32 (requires True) (ensures fun r -> r >= 0)
//! let contract = Contract::new(
//!     Formula::True,
//!     Formula::ge(result_expr, zero_expr),
//! );
//! ```
//!
//! # Propositional Equality Example
//!
//! ```ignore
//! use brrr_repr::verification::{refl, sym, trans, cong, EqWitness};
//!
//! // Reflexivity: x = x
//! let x_eq_x = refl(&int_type, x.clone());
//!
//! // Symmetry: if x = y then y = x
//! let y_eq_x = sym(x_eq_y);
//!
//! // Transitivity: if x = y and y = z then x = z
//! let x_eq_z = trans(x_eq_y, y_eq_z)?;
//!
//! // Congruence: if x = y then f(x) = f(y)
//! let fx_eq_fy = cong(f, x_eq_y);
//! ```

pub mod contracts;
pub mod equality;
pub mod formula;
pub mod subst;
pub mod vc;

pub use contracts::{
    // Types
    AnnotatedWhile, Assertion, Contract, ContractedFunction, OldRef, VarId,
    // Functions
    spec_old, spec_result, trivial_contract,
    // Constants
    OLD_VAR_PREFIX, RESULT_VAR_NAME,
};
pub use formula::{
    // Constants
    FALSE, TRUE,
    // Types
    CmpOp, DepVar, Formula,
    // Constructors
    formula_and, formula_and_all, formula_iff, formula_implies, formula_not, formula_or,
    formula_or_all,
};
pub use vc::{
    // Core VC type
    VC,
    // Helper functions
    vc_and, vc_or, vc_not, vc_impl,
    vc_from_formula, vc_simplify,
    // Trivial checks
    is_trivially_true, is_trivially_false,
    // Verification results
    VerificationResult, Counterexample, Value,
    // WP computation
    wp_compute, wp_annotated_while,
    // VC generation
    generate_vc, generate_vc_with_invariants,
    // Loop invariant VCs
    invariant_holds_initially, invariant_is_inductive, invariant_implies_post, loop_vcs,
    // Contract verification
    check_vc, verify_contract, verify_contract_with_invariants,
};
pub use subst::{
    // Fresh variable generation
    fresh_var, fresh_var_with_base,
    // Free variable collection
    free_vars_expr, free_vars_formula, free_vars_dep_type, is_free_in_expr,
    // Capture-avoiding substitution
    subst_expr, subst_formula, subst_dep_type,
    // Alpha-renaming
    alpha_rename_formula, alpha_rename_dep_type,
    // Alpha-equivalence
    dep_type_alpha_eq, formula_alpha_eq,
};
pub use equality::{
    // Core types
    EqProof, EqWitness, DecEqResult,
    // Construction functions
    refl, sym, trans, cong,
    // Utilities
    has_decidable_eq, syntactic_eq,
};
