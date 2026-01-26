//! Borrow checking types and state tracking
//!
//! Mirrors F* BorrowChecker.fst for ownership and borrowing semantics.
//!
//! # Overview
//!
//! This module provides types for tracking variable ownership state during
//! borrow checking analysis. The core type is `VarState` which represents
//! the current ownership status of a variable.
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::borrow::{VarState, VarEntry, can_move, can_borrow_shared};
//!
//! // Create an owned variable
//! let mut entry = VarEntry::new(var_id, BrrrType::BOOL, Mode::One);
//! assert!(entry.can_move());
//!
//! // Borrow it
//! entry.add_borrow(loan_id);
//! assert!(!entry.can_move()); // Cannot move while borrowed
//! assert!(entry.can_borrow_shared()); // Can add more shared borrows
//!
//! // End borrow
//! entry.end_borrow(loan_id);
//! assert!(entry.can_move()); // Can move again
//! ```
//!
//! # Lifetime Constraints
//!
//! The module also provides lifetime constraint types for tracking region relationships:
//!
//! ```ignore
//! use brrr_repr::borrow::{LifetimeConstraint, add_constraint, constraints_satisfiable};
//! use brrr_repr::types::Region;
//!
//! let mut constraints = vec![];
//!
//! // Region r1 must outlive r2
//! let c = LifetimeConstraint::outlives(Region::Static, Region::Scope(1));
//! constraints = add_constraint(constraints, c);
//!
//! assert!(constraints_satisfiable(&constraints));
//! ```

mod checker;
mod error;
mod lifetime;
mod state;
mod types;

pub use types::{
    // Types
    LoanId, LoanCounter as TypesLoanCounter, BorrowKind as TypesBorrowKind,
    Loan as TypesLoan, RefBoxDiamond, VarId, VarEntry, VarState,
    // State predicates
    can_borrow_mut, can_borrow_shared, can_move, is_available, is_ref_counted,
    // State transitions
    add_shared_borrow, clone_shared, drop_shared_ref, end_mut_borrow, end_shared_borrow,
    // Loan operations
    loan_conflicts as types_loan_conflicts,
    begin_shared_borrow, begin_exclusive_borrow, end_borrow,
};

pub use lifetime::{
    // Lifetime constraint types
    LifetimeConstraint,
    LifetimeConstraints,
    // Constraint operations
    add_constraint,
    constraints_satisfiable,
    solve_constraints,
    // Region lifetime helpers
    region_outlives,
    borrow_constraint,
};

pub use state::{
    // Borrow kind and loans
    BorrowKind,
    Loan,
    LoanCounter,
    loan_conflicts,
    // Borrow state
    BorrowState,
    ExtendedBorrowState,
    ExtendedVarEntry,
    // Region tracking
    RegionCap,
    RegionCounter,
    RegionCtx,
    add_region_cap,
    has_region_cap,
    invalidate_region,
    // Control flow merging
    merge_var_state,
    merge_var_entry,
    merge_var_lists,
    merge_loans,
    merge_borrow_states,
};

pub use error::{
    // Error types
    OwnershipError,
    BorrowResult,
    // Error helpers
    error_location,
};

pub use checker::{
    // Core check functions
    check_var_use,
    check_move,
    check_borrow_shared,
    check_borrow_exclusive,
    check_drop,
    // Expression-level borrow checking
    borrow_check_expr,
    check_expr,
    // State management
    extend_var,
    end_borrow_in_state,
    merge_borrow_states as checker_merge_borrow_states,
    // Constants
    DEFAULT_FUEL,
};
