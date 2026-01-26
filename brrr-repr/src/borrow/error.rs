//! Ownership and borrowing error types
//!
//! Mirrors F* BorrowChecker.fst lines 94-128:
//! ```fstar
//! type ownership_error = ...
//! type borrow_result (a: Type) = ...
//! ```
//!
//! # Overview
//!
//! This module provides error types for borrow checking failures.
//! Each error variant corresponds to a specific violation of Rust's
//! ownership and borrowing rules.
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::borrow::{OwnershipError, BorrowResult};
//!
//! fn check_move(var: VarId, is_borrowed: bool) -> BorrowResult<()> {
//!     if is_borrowed {
//!         Err(OwnershipError::MoveWhileBorrowed { var, loan: some_loan })
//!     } else {
//!         Ok(())
//!     }
//! }
//! ```

use serde::{Deserialize, Serialize};

use super::LoanId;
use crate::types::Region;

/// Variable identifier (interned string)
///
/// Re-exported from types for convenience in error construction.
pub type VarId = lasso::Spur;

/// Ownership and borrowing error
///
/// Maps to F* BorrowChecker.fst lines 94-115:
/// ```fstar
/// type ownership_error =
///   | ErrUseAfterMove : var:var_id -> ownership_error
///   | ErrMoveWhileBorrowed : var:var_id -> loan_id:loan_id -> ownership_error
///   | ErrDoubleMove : var:var_id -> ownership_error
///   | ... (18 variants total)
/// ```
///
/// Each variant represents a specific violation that the borrow checker
/// must detect and report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum OwnershipError {
    /// Attempted to use a variable after it was moved
    ///
    /// Example: `let y = x; let z = x;` where x is not Copy
    UseAfterMove {
        /// The moved variable
        var: VarId,
    },

    /// Attempted to move a variable while it has active borrows
    ///
    /// Example: `let r = &x; let y = x;` while r is still live
    MoveWhileBorrowed {
        /// The variable being moved
        var: VarId,
        /// The loan preventing the move
        loan: LoanId,
    },

    /// Attempted to move a variable that was already moved
    ///
    /// Example: `let y = x; let z = x;` where x is not Copy
    DoubleMove {
        /// The variable that was moved twice
        var: VarId,
    },

    /// Attempted to borrow a variable that was already moved
    ///
    /// Example: `let y = x; let r = &x;` where x was moved
    BorrowWhileMoved {
        /// The moved variable
        var: VarId,
    },

    /// Attempted mutable borrow while shared borrows are active
    ///
    /// Example: `let r1 = &x; let r2 = &mut x;`
    MutBorrowWhileBorrowed {
        /// The variable being borrowed
        var: VarId,
        /// Active shared loans preventing mut borrow
        loans: Vec<LoanId>,
    },

    /// Attempted shared borrow while mutable borrow is active
    ///
    /// Example: `let r1 = &mut x; let r2 = &x;`
    BorrowWhileMutBorrowed {
        /// The variable being borrowed
        var: VarId,
        /// The active exclusive loan
        loan: LoanId,
    },

    /// Attempted multiple mutable borrows of the same variable
    ///
    /// Example: `let r1 = &mut x; let r2 = &mut x;`
    MultipleMutBorrows {
        /// The variable being borrowed
        var: VarId,
        /// Existing mutable loans
        loans: Vec<LoanId>,
    },

    /// Borrow outlives the borrowed value
    ///
    /// Example: Returning a reference to a local variable
    BorrowOutlivesValue {
        /// The variable whose lifetime is ending
        var: VarId,
        /// The loan that would outlive it
        loan: LoanId,
    },

    /// Reference points to deallocated memory
    ///
    /// Example: Using a reference after the value is dropped
    DanglingReference {
        /// The variable with the dangling reference
        var: VarId,
    },

    /// Region escapes its scope
    ///
    /// Example: `letregion 'a in { return &'a x }`
    RegionEscapes {
        /// The region that escaped
        region: Region,
    },

    /// Attempted to drop a variable while it has active borrows
    ///
    /// Example: Dropping a value while references to it exist
    DropWhileBorrowed {
        /// The variable being dropped
        var: VarId,
        /// Active loans on the variable
        loans: Vec<LoanId>,
    },

    /// Attempted to drop/free a variable that was already dropped
    ///
    /// Example: Calling drop() twice on the same value
    DoubleFree {
        /// The variable that was freed twice
        var: VarId,
    },

    /// Linear variable was not consumed (exactly-once semantics)
    ///
    /// Example: A `One`-moded variable going out of scope unused
    LinearNotConsumed {
        /// The linear variable
        var: VarId,
    },

    /// Relevant variable was not used (at-least-once semantics)
    ///
    /// Example: A `One` or `Affine`-moded variable going unused
    RelevantNotUsed {
        /// The relevant variable
        var: VarId,
    },

    /// Affine variable was used multiple times (at-most-once semantics)
    ///
    /// Example: Using an `Affine`-moded variable twice
    AffineUsedMultiple {
        /// The affine variable
        var: VarId,
        /// Number of times it was used
        count: u32,
    },

    /// Variable not found in the environment
    ///
    /// Internal error: variable lookup failed
    VariableNotFound {
        /// The missing variable
        var: VarId,
    },

    /// Loan not found in the borrow state
    ///
    /// Internal error: loan lookup or end failed
    LoanNotFound {
        /// The missing loan
        loan: LoanId,
    },

    /// Internal error in the borrow checker
    ///
    /// Should not occur in correct implementations
    InternalError {
        /// Description of the error
        msg: String,
    },
}

impl OwnershipError {
    /// Extract the primary variable involved in this error, if any
    ///
    /// Returns `Some(var)` for errors related to a specific variable,
    /// `None` for errors like `RegionEscapes` or `InternalError`.
    pub fn primary_var(&self) -> Option<VarId> {
        match self {
            Self::UseAfterMove { var }
            | Self::MoveWhileBorrowed { var, .. }
            | Self::DoubleMove { var }
            | Self::BorrowWhileMoved { var }
            | Self::MutBorrowWhileBorrowed { var, .. }
            | Self::BorrowWhileMutBorrowed { var, .. }
            | Self::MultipleMutBorrows { var, .. }
            | Self::BorrowOutlivesValue { var, .. }
            | Self::DanglingReference { var }
            | Self::DropWhileBorrowed { var, .. }
            | Self::DoubleFree { var }
            | Self::LinearNotConsumed { var }
            | Self::RelevantNotUsed { var }
            | Self::AffineUsedMultiple { var, .. }
            | Self::VariableNotFound { var } => Some(*var),
            Self::RegionEscapes { .. } | Self::LoanNotFound { .. } | Self::InternalError { .. } => {
                None
            }
        }
    }

    /// Extract the primary loan involved in this error, if any
    ///
    /// Returns `Some(loan)` for errors with a single primary loan,
    /// `None` for errors with multiple loans or no loans.
    pub fn primary_loan(&self) -> Option<LoanId> {
        match self {
            Self::MoveWhileBorrowed { loan, .. }
            | Self::BorrowWhileMutBorrowed { loan, .. }
            | Self::BorrowOutlivesValue { loan, .. }
            | Self::LoanNotFound { loan } => Some(*loan),
            _ => None,
        }
    }

    /// Extract all loans involved in this error
    ///
    /// Returns a slice of loan IDs for errors with multiple loans,
    /// or a single-element vec for errors with one loan.
    pub fn loans(&self) -> Vec<LoanId> {
        match self {
            Self::MoveWhileBorrowed { loan, .. }
            | Self::BorrowWhileMutBorrowed { loan, .. }
            | Self::BorrowOutlivesValue { loan, .. }
            | Self::LoanNotFound { loan } => vec![*loan],
            Self::MutBorrowWhileBorrowed { loans, .. }
            | Self::MultipleMutBorrows { loans, .. }
            | Self::DropWhileBorrowed { loans, .. } => loans.clone(),
            _ => vec![],
        }
    }

    /// Get the region involved in this error, if any
    pub fn region(&self) -> Option<Region> {
        match self {
            Self::RegionEscapes { region } => Some(*region),
            _ => None,
        }
    }

    /// Check if this is an internal/unexpected error
    pub fn is_internal(&self) -> bool {
        matches!(
            self,
            Self::InternalError { .. } | Self::VariableNotFound { .. } | Self::LoanNotFound { .. }
        )
    }

    /// Get a short error code for categorization
    pub fn code(&self) -> &'static str {
        match self {
            Self::UseAfterMove { .. } => "E0001",
            Self::MoveWhileBorrowed { .. } => "E0002",
            Self::DoubleMove { .. } => "E0003",
            Self::BorrowWhileMoved { .. } => "E0004",
            Self::MutBorrowWhileBorrowed { .. } => "E0005",
            Self::BorrowWhileMutBorrowed { .. } => "E0006",
            Self::MultipleMutBorrows { .. } => "E0007",
            Self::BorrowOutlivesValue { .. } => "E0008",
            Self::DanglingReference { .. } => "E0009",
            Self::RegionEscapes { .. } => "E0010",
            Self::DropWhileBorrowed { .. } => "E0011",
            Self::DoubleFree { .. } => "E0012",
            Self::LinearNotConsumed { .. } => "E0013",
            Self::RelevantNotUsed { .. } => "E0014",
            Self::AffineUsedMultiple { .. } => "E0015",
            Self::VariableNotFound { .. } => "E0016",
            Self::LoanNotFound { .. } => "E0017",
            Self::InternalError { .. } => "E0018",
        }
    }
}

impl std::fmt::Display for OwnershipError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UseAfterMove { var } => {
                write!(f, "use of moved value: variable {:?}", var)
            }
            Self::MoveWhileBorrowed { var, loan } => {
                write!(
                    f,
                    "cannot move variable {:?} because it is borrowed by {}",
                    var, loan
                )
            }
            Self::DoubleMove { var } => {
                write!(f, "value {:?} moved here after previous move", var)
            }
            Self::BorrowWhileMoved { var } => {
                write!(f, "cannot borrow {:?} because it was moved", var)
            }
            Self::MutBorrowWhileBorrowed { var, loans } => {
                write!(
                    f,
                    "cannot borrow {:?} as mutable because it is already borrowed as immutable ({} active loans)",
                    var, loans.len()
                )
            }
            Self::BorrowWhileMutBorrowed { var, loan } => {
                write!(
                    f,
                    "cannot borrow {:?} as immutable because it is already mutably borrowed ({})",
                    var, loan
                )
            }
            Self::MultipleMutBorrows { var, loans } => {
                write!(
                    f,
                    "cannot borrow {:?} as mutable more than once ({} existing mutable loans)",
                    var,
                    loans.len()
                )
            }
            Self::BorrowOutlivesValue { var, loan } => {
                write!(f, "borrow {} of {:?} does not live long enough", loan, var)
            }
            Self::DanglingReference { var } => {
                write!(f, "dangling reference to {:?}", var)
            }
            Self::RegionEscapes { region } => {
                write!(f, "region {} escapes its scope", region.format())
            }
            Self::DropWhileBorrowed { var, loans } => {
                write!(
                    f,
                    "cannot drop {:?} while {} borrows are active",
                    var,
                    loans.len()
                )
            }
            Self::DoubleFree { var } => {
                write!(f, "double free detected for {:?}", var)
            }
            Self::LinearNotConsumed { var } => {
                write!(f, "linear variable {:?} must be consumed exactly once", var)
            }
            Self::RelevantNotUsed { var } => {
                write!(f, "relevant variable {:?} must be used at least once", var)
            }
            Self::AffineUsedMultiple { var, count } => {
                write!(
                    f,
                    "affine variable {:?} used {} times (allowed at most once)",
                    var, count
                )
            }
            Self::VariableNotFound { var } => {
                write!(f, "variable {:?} not found in environment", var)
            }
            Self::LoanNotFound { loan } => {
                write!(f, "loan {} not found in borrow state", loan)
            }
            Self::InternalError { msg } => {
                write!(f, "internal borrow checker error: {}", msg)
            }
        }
    }
}

impl std::error::Error for OwnershipError {}

/// Result type for borrow checking operations
///
/// Maps to F* BorrowChecker.fst lines 127-129:
/// ```fstar
/// type borrow_result (a: Type) =
///   | BrOk   : value:a -> borrow_result a
///   | BrErr  : error:ownership_error -> borrow_result a
/// ```
pub type BorrowResult<T> = Result<T, OwnershipError>;

/// Helper to extract location information from an error
///
/// Returns a tuple of (variable, loan, region) where each is optional.
/// This is useful for error reporting and diagnostics.
///
/// # Example
///
/// ```ignore
/// let err = OwnershipError::MoveWhileBorrowed { var, loan };
/// let (var_opt, loan_opt, region_opt) = error_location(&err);
/// ```
pub fn error_location(err: &OwnershipError) -> (Option<VarId>, Option<LoanId>, Option<Region>) {
    (err.primary_var(), err.primary_loan(), err.region())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Key;

    fn make_var(n: usize) -> VarId {
        lasso::Spur::try_from_usize(n).unwrap()
    }

    #[test]
    fn test_use_after_move() {
        let var = make_var(1);
        let err = OwnershipError::UseAfterMove { var };

        assert_eq!(err.primary_var(), Some(var));
        assert_eq!(err.primary_loan(), None);
        assert!(!err.is_internal());
        assert_eq!(err.code(), "E0001");

        let msg = format!("{}", err);
        assert!(msg.contains("moved value"));
    }

    #[test]
    fn test_move_while_borrowed() {
        let var = make_var(1);
        let loan = LoanId::new(42);
        let err = OwnershipError::MoveWhileBorrowed { var, loan };

        assert_eq!(err.primary_var(), Some(var));
        assert_eq!(err.primary_loan(), Some(loan));
        assert_eq!(err.loans(), vec![loan]);
        assert_eq!(err.code(), "E0002");

        let msg = format!("{}", err);
        assert!(msg.contains("cannot move"));
        assert!(msg.contains("borrowed"));
    }

    #[test]
    fn test_mut_borrow_while_borrowed() {
        let var = make_var(1);
        let loans = vec![LoanId::new(1), LoanId::new(2), LoanId::new(3)];
        let err = OwnershipError::MutBorrowWhileBorrowed {
            var,
            loans: loans.clone(),
        };

        assert_eq!(err.primary_var(), Some(var));
        assert_eq!(err.primary_loan(), None); // Multiple loans
        assert_eq!(err.loans(), loans);
        assert_eq!(err.code(), "E0005");

        let msg = format!("{}", err);
        assert!(msg.contains("mutable"));
        assert!(msg.contains("3 active loans"));
    }

    #[test]
    fn test_region_escapes() {
        let region = Region::Fresh(42);
        let err = OwnershipError::RegionEscapes { region };

        assert_eq!(err.primary_var(), None);
        assert_eq!(err.primary_loan(), None);
        assert_eq!(err.region(), Some(region));
        assert_eq!(err.code(), "E0010");

        let msg = format!("{}", err);
        assert!(msg.contains("escapes"));
    }

    #[test]
    fn test_linear_not_consumed() {
        let var = make_var(5);
        let err = OwnershipError::LinearNotConsumed { var };

        assert_eq!(err.code(), "E0013");
        let msg = format!("{}", err);
        assert!(msg.contains("linear"));
        assert!(msg.contains("exactly once"));
    }

    #[test]
    fn test_affine_used_multiple() {
        let var = make_var(10);
        let err = OwnershipError::AffineUsedMultiple { var, count: 3 };

        assert_eq!(err.code(), "E0015");
        let msg = format!("{}", err);
        assert!(msg.contains("affine"));
        assert!(msg.contains("3 times"));
    }

    #[test]
    fn test_internal_errors() {
        let var = make_var(1);
        let loan = LoanId::new(99);

        assert!(OwnershipError::VariableNotFound { var }.is_internal());
        assert!(OwnershipError::LoanNotFound { loan }.is_internal());
        assert!(OwnershipError::InternalError { msg: "test".into() }.is_internal());

        // Regular errors are not internal
        assert!(!OwnershipError::UseAfterMove { var }.is_internal());
    }

    #[test]
    fn test_error_location() {
        let var = make_var(1);
        let loan = LoanId::new(42);
        let region = Region::Scope(3);

        // Test with var and loan
        let err = OwnershipError::MoveWhileBorrowed { var, loan };
        let (v, l, r) = error_location(&err);
        assert_eq!(v, Some(var));
        assert_eq!(l, Some(loan));
        assert_eq!(r, None);

        // Test with region only
        let err = OwnershipError::RegionEscapes { region };
        let (v, l, r) = error_location(&err);
        assert_eq!(v, None);
        assert_eq!(l, None);
        assert_eq!(r, Some(region));
    }

    #[test]
    fn test_borrow_result_ok() {
        let result: BorrowResult<i32> = Ok(42);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 42);
    }

    #[test]
    fn test_borrow_result_err() {
        let var = make_var(1);
        let result: BorrowResult<i32> = Err(OwnershipError::UseAfterMove { var });
        assert!(result.is_err());

        let err = result.unwrap_err();
        assert_eq!(err.code(), "E0001");
    }

    #[test]
    fn test_error_is_send_sync() {
        fn assert_send<T: Send>() {}
        fn assert_sync<T: Sync>() {}

        assert_send::<OwnershipError>();
        assert_sync::<OwnershipError>();
    }

    #[test]
    fn test_all_error_codes_unique() {
        let var = make_var(1);
        let loan = LoanId::new(1);
        let region = Region::Static;

        let errors: Vec<OwnershipError> = vec![
            OwnershipError::UseAfterMove { var },
            OwnershipError::MoveWhileBorrowed { var, loan },
            OwnershipError::DoubleMove { var },
            OwnershipError::BorrowWhileMoved { var },
            OwnershipError::MutBorrowWhileBorrowed {
                var,
                loans: vec![loan],
            },
            OwnershipError::BorrowWhileMutBorrowed { var, loan },
            OwnershipError::MultipleMutBorrows {
                var,
                loans: vec![loan],
            },
            OwnershipError::BorrowOutlivesValue { var, loan },
            OwnershipError::DanglingReference { var },
            OwnershipError::RegionEscapes { region },
            OwnershipError::DropWhileBorrowed {
                var,
                loans: vec![loan],
            },
            OwnershipError::DoubleFree { var },
            OwnershipError::LinearNotConsumed { var },
            OwnershipError::RelevantNotUsed { var },
            OwnershipError::AffineUsedMultiple { var, count: 2 },
            OwnershipError::VariableNotFound { var },
            OwnershipError::LoanNotFound { loan },
            OwnershipError::InternalError { msg: "test".into() },
        ];

        let codes: Vec<_> = errors.iter().map(|e| e.code()).collect();
        let mut unique_codes = codes.clone();
        unique_codes.sort();
        unique_codes.dedup();

        assert_eq!(
            codes.len(),
            unique_codes.len(),
            "All error codes must be unique"
        );
    }
}
