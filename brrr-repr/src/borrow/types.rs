//! Core borrow checking types
//!
//! Mirrors F* BorrowChecker.fst:
//! - `loan_id` (line 182)
//! - `borrow_kind` (lines 186-189)
//! - `loan` (lines 191-199)
//! - `ref_box_diamond` (lines 56-60)
//!
//! # Overview
//!
//! This module provides the fundamental types for borrow tracking:
//!
//! - [`LoanId`] - Unique identifier for each borrow operation
//! - [`BorrowKind`] - Shared vs exclusive borrow
//! - [`Loan`] - Active borrow record with metadata
//! - [`LoanCounter`] - Monotonic generator for loan IDs

use lasso::Spur;
use serde::{Deserialize, Serialize};

use crate::types::Region;

/// Variable identifier (interned string)
///
/// Re-exported from verification module for convenience.
pub type VarId = Spur;

// ============================================================================
// Loan Identifier
// ============================================================================

/// Unique identifier for a borrow/loan
///
/// Maps to F* BorrowChecker.fst line 182:
/// ```fstar
/// type loan_id = nat
/// ```
///
/// Each borrow operation generates a unique loan ID that tracks
/// the lifetime of the borrow until it ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LoanId(u32);

impl LoanId {
    /// Create a new loan ID
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw ID value
    pub const fn raw(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for LoanId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "L{}", self.0)
    }
}

// ============================================================================
// Loan Counter
// ============================================================================

/// Monotonic counter for generating fresh loan IDs
///
/// Maps to F* BorrowChecker.fst lines 204-207:
/// ```fstar
/// type loan_counter = nat
/// val fresh_loan : loan_counter -> loan_id * loan_counter
/// ```
#[derive(Debug, Clone, Default)]
pub struct LoanCounter(u32);

impl LoanCounter {
    /// Create a new counter starting at zero
    pub const fn new() -> Self {
        Self(0)
    }

    /// Generate a fresh loan ID and advance the counter
    pub fn fresh(&mut self) -> LoanId {
        let id = LoanId::new(self.0);
        self.0 = self.0.saturating_add(1);
        id
    }

    /// Get current counter value (next ID that will be generated)
    pub const fn current(&self) -> u32 {
        self.0
    }
}

// ============================================================================
// Borrow Kind
// ============================================================================

/// Kind of borrow - shared (immutable) or exclusive (mutable)
///
/// Maps to F* BorrowChecker.fst lines 186-189:
/// ```fstar
/// type borrow_kind =
///   | BkShared    : borrow_kind
///   | BkExclusive : borrow_kind
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BorrowKind {
    /// Shared/immutable borrow (`&T`)
    ///
    /// Multiple shared borrows can coexist.
    Shared,

    /// Exclusive/mutable borrow (`&mut T`)
    ///
    /// Only one exclusive borrow can exist at a time.
    Exclusive,
}

impl BorrowKind {
    /// Is this a shared borrow?
    pub const fn is_shared(self) -> bool {
        matches!(self, Self::Shared)
    }

    /// Is this an exclusive borrow?
    pub const fn is_exclusive(self) -> bool {
        matches!(self, Self::Exclusive)
    }

    /// Format as text
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Shared => "shared",
            Self::Exclusive => "exclusive",
        }
    }

    /// Format as Rust syntax
    pub const fn as_rust(self) -> &'static str {
        match self {
            Self::Shared => "&",
            Self::Exclusive => "&mut",
        }
    }
}

impl std::fmt::Display for BorrowKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

// ============================================================================
// Loan
// ============================================================================

/// An active borrow/loan record
///
/// Maps to F* BorrowChecker.fst lines 191-199:
/// ```fstar
/// noeq type loan = {
///   loan_id     : loan_id;
///   loan_var    : var_id;
///   loan_kind   : borrow_kind;
///   loan_depth  : nat;
///   loan_region : option region
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Loan {
    /// Unique identifier for this loan
    pub id: LoanId,

    /// The variable being borrowed
    pub var: VarId,

    /// Kind of borrow (shared or exclusive)
    pub kind: BorrowKind,

    /// Scope depth where the borrow was created
    ///
    /// Used for determining when the borrow goes out of scope.
    pub depth: u32,

    /// Optional region annotation for the borrow
    ///
    /// If `Some(region)`, the borrow is valid for that region's lifetime.
    /// If `None`, the borrow has no explicit region constraint.
    pub region: Option<Region>,
}

impl Loan {
    /// Create a new loan with explicit depth
    pub fn new(id: LoanId, var: VarId, kind: BorrowKind, depth: u32) -> Self {
        Self {
            id,
            var,
            kind,
            depth,
            region: None,
        }
    }

    /// Create a loan at the top level (depth 0)
    pub fn top_level(id: LoanId, var: VarId, kind: BorrowKind) -> Self {
        Self::new(id, var, kind, 0)
    }

    /// Create a loan with a region annotation
    pub fn with_region(id: LoanId, var: VarId, kind: BorrowKind, depth: u32, region: Region) -> Self {
        Self {
            id,
            var,
            kind,
            depth,
            region: Some(region),
        }
    }

    /// Check if this is a shared borrow
    pub const fn is_shared(&self) -> bool {
        self.kind.is_shared()
    }

    /// Check if this is an exclusive borrow
    pub const fn is_exclusive(&self) -> bool {
        self.kind.is_exclusive()
    }

    /// Check if this loan is for a specific variable
    pub fn is_for_var(&self, var: VarId) -> bool {
        self.var == var
    }

    /// Check if this loan is at or above a given depth
    ///
    /// Used for scope exit: loans at depth >= exit_depth are invalidated.
    pub const fn is_at_depth(&self, depth: u32) -> bool {
        self.depth >= depth
    }
}

impl std::fmt::Display for Loan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({}, {})", self.id, self.kind, self.depth)?;
        if let Some(region) = &self.region {
            write!(f, " @ {}", region.format())?;
        }
        Ok(())
    }
}

// ============================================================================
// Ref Box Diamond (Modal Types)
// ============================================================================

/// Modal reference types for region-based borrow tracking
///
/// Maps to F* BorrowChecker.fst lines 56-60:
/// ```fstar
/// type ref_box_diamond =
///   | RbdRef : region -> ref_box_diamond    (* &'r T *)
///   | RbdBox : ref_box_diamond              (* Box<T> *)
///   | RbdDiamond : region -> ref_box_diamond (* diamond type *)
/// ```
///
/// This type represents the "modal" aspect of references:
/// - `Ref` is a borrowed reference with a region
/// - `Box` is an owned heap allocation
/// - `Diamond` is the "possibly uninitialized" modality
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RefBoxDiamond {
    /// Reference with lifetime region: `&'r T`
    Ref(Region),

    /// Owned heap allocation: `Box<T>`
    Box,

    /// Diamond modality for region: `◇'r T`
    ///
    /// Represents a value that may or may not be initialized,
    /// typically used in letregion constructs.
    Diamond(Region),
}

impl RefBoxDiamond {
    /// Create a reference with static lifetime
    pub const fn static_ref() -> Self {
        Self::Ref(Region::Static)
    }

    /// Get the region if this is a Ref or Diamond
    pub const fn region(&self) -> Option<Region> {
        match self {
            Self::Ref(r) | Self::Diamond(r) => Some(*r),
            Self::Box => None,
        }
    }

    /// Is this a reference (not box or diamond)?
    pub const fn is_ref(&self) -> bool {
        matches!(self, Self::Ref(_))
    }

    /// Is this a box?
    pub const fn is_box(&self) -> bool {
        matches!(self, Self::Box)
    }

    /// Is this a diamond modality?
    pub const fn is_diamond(&self) -> bool {
        matches!(self, Self::Diamond(_))
    }
}

impl std::fmt::Display for RefBoxDiamond {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ref(r) => write!(f, "&{}", r.format()),
            Self::Box => write!(f, "Box"),
            Self::Diamond(r) => write!(f, "◇{}", r.format()),
        }
    }
}

// ============================================================================
// Loan Conflict Checking
// ============================================================================

/// Check if two loans conflict
///
/// Loans conflict if:
/// - They are for the same variable, AND
/// - At least one is exclusive
///
/// # Arguments
/// * `a` - First loan
/// * `b` - Second loan
///
/// # Returns
/// `true` if the loans conflict and cannot coexist
pub fn loan_conflicts(a: &Loan, b: &Loan) -> bool {
    if a.var != b.var {
        return false;
    }

    // Two shared borrows of the same variable don't conflict
    if a.kind.is_shared() && b.kind.is_shared() {
        return false;
    }

    // Any exclusive borrow conflicts with any other borrow of the same var
    true
}

// ============================================================================
// Borrow Operations
// ============================================================================

/// Begin a shared borrow
///
/// Creates a new loan for a shared borrow of the given variable.
///
/// # Arguments
/// * `counter` - Loan counter for generating fresh ID
/// * `var` - Variable to borrow
/// * `depth` - Current scope depth
///
/// # Returns
/// The new loan representing the shared borrow
pub fn begin_shared_borrow(counter: &mut LoanCounter, var: VarId, depth: u32) -> Loan {
    Loan::new(counter.fresh(), var, BorrowKind::Shared, depth)
}

/// Begin an exclusive borrow
///
/// Creates a new loan for an exclusive borrow of the given variable.
///
/// # Arguments
/// * `counter` - Loan counter for generating fresh ID
/// * `var` - Variable to borrow
/// * `depth` - Current scope depth
///
/// # Returns
/// The new loan representing the exclusive borrow
pub fn begin_exclusive_borrow(counter: &mut LoanCounter, var: VarId, depth: u32) -> Loan {
    Loan::new(counter.fresh(), var, BorrowKind::Exclusive, depth)
}

/// End a borrow by removing the loan from a list
///
/// # Arguments
/// * `loans` - List of active loans
/// * `loan_id` - ID of the loan to end
///
/// # Returns
/// `true` if the loan was found and removed
pub fn end_borrow(loans: &mut Vec<Loan>, loan_id: LoanId) -> bool {
    let original_len = loans.len();
    loans.retain(|l| l.id != loan_id);
    loans.len() < original_len
}

// ============================================================================
// Variable State (VarState)
// ============================================================================

use crate::modes::Mode;
use crate::types::BrrrType;

/// Variable ownership state
///
/// Maps to F* BorrowChecker.fst lines 296-306:
/// ```fstar
/// type var_state =
///   | VsOwned       : var_state
///   | VsMoved       : var_state
///   | VsBorrowed    : list loan_id -> var_state
///   | VsBorrowedMut : loan_id -> var_state
///   | VsShared      : ref_count:nat -> var_state
///   | VsDropped     : var_state
/// ```
///
/// # State Semantics
///
/// - **Owned**: Full ownership - can move, borrow shared, or borrow mut
/// - **Moved**: Consumed - use-after-move error for any operation
/// - **Borrowed**: Active shared borrows - can borrow shared, cannot move or mut borrow
/// - **BorrowedMut**: Active mutable borrow - no operations until borrow ends
/// - **Shared**: Reference-counted (Rc/Arc) - can clone, cannot move
/// - **Dropped**: Explicitly dropped - no operations permitted
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum VarState {
    /// Full ownership - can move, borrow shared, or borrow mut
    Owned,

    /// Value has been moved out - use-after-move error for any operation
    Moved,

    /// Active shared (immutable) borrows
    ///
    /// Contains list of loan IDs for all active shared borrows.
    /// Multiple shared borrows can coexist.
    Borrowed(Vec<LoanId>),

    /// Active mutable (exclusive) borrow
    ///
    /// Contains the single loan ID for the exclusive borrow.
    /// No other borrows or operations permitted until this ends.
    BorrowedMut(LoanId),

    /// Reference-counted ownership (Rc/Arc)
    ///
    /// Tracks the number of active references.
    /// Value is dropped when count reaches zero.
    Shared {
        /// Number of active references (always >= 1 while alive)
        ref_count: u32,
    },

    /// Explicitly dropped - no operations permitted
    Dropped,
}

impl Default for VarState {
    fn default() -> Self {
        Self::Owned
    }
}

impl VarState {
    /// Create a new owned state
    #[must_use]
    pub const fn owned() -> Self {
        Self::Owned
    }

    /// Create a new shared (Rc/Arc) state with initial ref count of 1
    #[must_use]
    pub const fn shared() -> Self {
        Self::Shared { ref_count: 1 }
    }

    /// Create a borrowed state with a single loan
    #[must_use]
    pub fn borrowed(loan: LoanId) -> Self {
        Self::Borrowed(vec![loan])
    }

    /// Create a mutably borrowed state
    #[must_use]
    pub const fn borrowed_mut(loan: LoanId) -> Self {
        Self::BorrowedMut(loan)
    }
}

impl std::fmt::Display for VarState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Owned => write!(f, "owned"),
            Self::Moved => write!(f, "moved"),
            Self::Borrowed(loans) => write!(f, "borrowed({} loans)", loans.len()),
            Self::BorrowedMut(loan) => write!(f, "borrowed_mut(loan={})", loan),
            Self::Shared { ref_count } => write!(f, "shared(rc={})", ref_count),
            Self::Dropped => write!(f, "dropped"),
        }
    }
}

// ============================================================================
// VarState Predicates
// ============================================================================

/// Check if variable is available for use (not moved/dropped)
///
/// Maps to F*: `val is_available : var_state -> bool`
///
/// A variable is available if it hasn't been moved or dropped.
/// Note: BorrowedMut is technically "available" but with restricted operations.
#[must_use]
pub fn is_available(state: &VarState) -> bool {
    !matches!(state, VarState::Moved | VarState::Dropped)
}

/// Check if variable can be moved (ownership transfer)
///
/// Maps to F*: `val can_move_state : var_state -> bool`
///
/// Only `Owned` state permits moving - all other states either:
/// - Already moved/dropped
/// - Have active borrows that would be invalidated
/// - Are reference-counted (move semantics don't apply)
#[must_use]
pub fn can_move(state: &VarState) -> bool {
    matches!(state, VarState::Owned)
}

/// Check if variable can be borrowed as shared (immutable)
///
/// Maps to F*: `val can_borrow_shared : var_state -> bool`
///
/// Shared borrows are allowed from:
/// - `Owned` - creates first borrow
/// - `Borrowed` - adds another shared borrow (multiple readers OK)
///
/// Not allowed from:
/// - `Moved`/`Dropped` - value doesn't exist
/// - `BorrowedMut` - exclusive borrow active
/// - `Shared` - use clone instead
#[must_use]
pub fn can_borrow_shared(state: &VarState) -> bool {
    matches!(state, VarState::Owned | VarState::Borrowed(_))
}

/// Check if variable can be borrowed as mutable (exclusive)
///
/// Maps to F*: `val can_borrow_mut : var_state -> bool`
///
/// Exclusive borrows are only allowed from `Owned` state.
/// Any existing borrows (shared or mut) prevent new mut borrows.
#[must_use]
pub fn can_borrow_mut(state: &VarState) -> bool {
    matches!(state, VarState::Owned)
}

/// Check if variable uses reference counting (Rc/Arc)
#[must_use]
pub fn is_ref_counted(state: &VarState) -> bool {
    matches!(state, VarState::Shared { .. })
}

// ============================================================================
// VarState Transitions
// ============================================================================

/// Clone a shared (Rc/Arc) reference, incrementing ref count
///
/// Returns `Some(new_state)` with incremented count if state is `Shared`,
/// otherwise returns `None`.
///
/// # Overflow Safety
/// Returns `None` if ref count would overflow u32.
#[must_use]
pub fn clone_shared(state: &VarState) -> Option<VarState> {
    match state {
        VarState::Shared { ref_count } => {
            ref_count.checked_add(1).map(|new_count| VarState::Shared {
                ref_count: new_count,
            })
        }
        _ => None,
    }
}

/// Drop a shared reference, decrementing ref count
///
/// Returns:
/// - `Some(Shared { ref_count: n-1 })` if count > 1 (still alive)
/// - `Some(Dropped)` if count reaches 0 (value deallocated)
/// - `None` if not a `Shared` state
#[must_use]
pub fn drop_shared_ref(state: &VarState) -> Option<VarState> {
    match state {
        VarState::Shared { ref_count } => {
            if *ref_count <= 1 {
                Some(VarState::Dropped)
            } else {
                Some(VarState::Shared {
                    ref_count: ref_count - 1,
                })
            }
        }
        _ => None,
    }
}

/// Add a shared borrow to the state
///
/// Returns the new state with the loan added, or `None` if borrowing
/// is not permitted in the current state.
#[must_use]
pub fn add_shared_borrow(state: &VarState, loan: LoanId) -> Option<VarState> {
    match state {
        VarState::Owned => Some(VarState::Borrowed(vec![loan])),
        VarState::Borrowed(loans) => {
            let mut new_loans = loans.clone();
            new_loans.push(loan);
            Some(VarState::Borrowed(new_loans))
        }
        _ => None,
    }
}

/// Remove a shared borrow from the state
///
/// Returns the new state with the loan removed. If this was the last
/// loan, returns `Owned` state.
#[must_use]
pub fn end_shared_borrow(state: &VarState, loan: LoanId) -> Option<VarState> {
    match state {
        VarState::Borrowed(loans) => {
            let new_loans: Vec<_> = loans.iter().copied().filter(|&l| l != loan).collect();
            if new_loans.is_empty() {
                Some(VarState::Owned)
            } else {
                Some(VarState::Borrowed(new_loans))
            }
        }
        _ => None,
    }
}

/// End a mutable borrow, returning to owned state
///
/// Returns `Some(Owned)` if the loan matches, `None` otherwise.
#[must_use]
pub fn end_mut_borrow(state: &VarState, loan: LoanId) -> Option<VarState> {
    match state {
        VarState::BorrowedMut(active_loan) if *active_loan == loan => Some(VarState::Owned),
        _ => None,
    }
}

// ============================================================================
// VarEntry - Variable Table Entry
// ============================================================================

/// Entry in the variable tracking table
///
/// Combines variable identifier, type, usage mode, and ownership state.
/// Used by the borrow checker to track all variables in scope.
///
/// Maps to F* BorrowChecker.fst lines 380-386:
/// ```fstar
/// noeq type var_entry = {
///   ve_var   : var_id;
///   ve_ty    : brrr_type;
///   ve_mode  : mode;
///   ve_state : var_state
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct VarEntry {
    /// Variable identifier (interned string)
    pub var: VarId,

    /// Static type of the variable
    pub ty: BrrrType,

    /// Usage mode (linear/affine/unrestricted)
    pub mode: Mode,

    /// Current ownership state
    pub state: VarState,
}

impl VarEntry {
    /// Create a new owned variable entry
    pub fn new(var: VarId, ty: BrrrType, mode: Mode) -> Self {
        Self {
            var,
            ty,
            mode,
            state: VarState::Owned,
        }
    }

    /// Create a new shared (Rc/Arc) variable entry
    pub fn new_shared(var: VarId, ty: BrrrType, mode: Mode) -> Self {
        Self {
            var,
            ty,
            mode,
            state: VarState::Shared { ref_count: 1 },
        }
    }

    /// Check if this variable is available for use
    pub fn is_available(&self) -> bool {
        is_available(&self.state)
    }

    /// Check if this variable can be moved
    pub fn can_move(&self) -> bool {
        can_move(&self.state)
    }

    /// Check if this variable can be borrowed as shared
    pub fn can_borrow_shared(&self) -> bool {
        can_borrow_shared(&self.state)
    }

    /// Check if this variable can be borrowed as mutable
    pub fn can_borrow_mut(&self) -> bool {
        can_borrow_mut(&self.state)
    }

    /// Transition to moved state (consume the variable)
    ///
    /// Returns `true` if the move was successful, `false` if not permitted.
    pub fn do_move(&mut self) -> bool {
        if self.can_move() {
            self.state = VarState::Moved;
            true
        } else {
            false
        }
    }

    /// Add a shared borrow
    ///
    /// Returns `true` if successful, `false` if not permitted.
    pub fn add_borrow(&mut self, loan: LoanId) -> bool {
        if let Some(new_state) = add_shared_borrow(&self.state, loan) {
            self.state = new_state;
            true
        } else {
            false
        }
    }

    /// Add a mutable borrow
    ///
    /// Returns `true` if successful, `false` if not permitted.
    pub fn add_mut_borrow(&mut self, loan: LoanId) -> bool {
        if self.can_borrow_mut() {
            self.state = VarState::BorrowedMut(loan);
            true
        } else {
            false
        }
    }

    /// End a shared borrow
    pub fn end_borrow(&mut self, loan: LoanId) -> bool {
        if let Some(new_state) = end_shared_borrow(&self.state, loan) {
            self.state = new_state;
            true
        } else {
            false
        }
    }

    /// End a mutable borrow
    pub fn end_mut_borrow(&mut self, loan: LoanId) -> bool {
        if let Some(new_state) = end_mut_borrow(&self.state, loan) {
            self.state = new_state;
            true
        } else {
            false
        }
    }

    /// Drop the variable
    pub fn drop(&mut self) {
        self.state = VarState::Dropped;
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Key;

    fn make_var(n: usize) -> VarId {
        Spur::try_from_usize(n).unwrap()
    }

    #[test]
    fn test_loan_id() {
        let id = LoanId::new(42);
        assert_eq!(id.raw(), 42);
        assert_eq!(format!("{}", id), "L42");
    }

    #[test]
    fn test_loan_counter() {
        let mut counter = LoanCounter::new();
        assert_eq!(counter.current(), 0);

        let id1 = counter.fresh();
        assert_eq!(id1.raw(), 0);
        assert_eq!(counter.current(), 1);

        let id2 = counter.fresh();
        assert_eq!(id2.raw(), 1);
        assert_eq!(counter.current(), 2);
    }

    #[test]
    fn test_borrow_kind() {
        assert!(BorrowKind::Shared.is_shared());
        assert!(!BorrowKind::Shared.is_exclusive());
        assert!(!BorrowKind::Exclusive.is_shared());
        assert!(BorrowKind::Exclusive.is_exclusive());

        assert_eq!(BorrowKind::Shared.as_str(), "shared");
        assert_eq!(BorrowKind::Exclusive.as_rust(), "&mut");
    }

    #[test]
    fn test_loan_creation() {
        let var = make_var(1);
        let loan = Loan::new(LoanId::new(0), var, BorrowKind::Shared, 2);

        assert_eq!(loan.id.raw(), 0);
        assert_eq!(loan.var, var);
        assert!(loan.is_shared());
        assert!(!loan.is_exclusive());
        assert_eq!(loan.depth, 2);
        assert!(loan.region.is_none());
    }

    #[test]
    fn test_loan_top_level() {
        let var = make_var(1);
        let loan = Loan::top_level(LoanId::new(0), var, BorrowKind::Exclusive);

        assert_eq!(loan.depth, 0);
        assert!(loan.is_exclusive());
    }

    #[test]
    fn test_loan_with_region() {
        let var = make_var(1);
        let region = Region::Static;
        let loan = Loan::with_region(LoanId::new(0), var, BorrowKind::Shared, 1, region);

        assert_eq!(loan.region, Some(Region::Static));
    }

    #[test]
    fn test_loan_is_at_depth() {
        let var = make_var(1);
        let loan = Loan::new(LoanId::new(0), var, BorrowKind::Shared, 2);

        assert!(loan.is_at_depth(0));
        assert!(loan.is_at_depth(1));
        assert!(loan.is_at_depth(2));
        assert!(!loan.is_at_depth(3));
    }

    #[test]
    fn test_loan_conflicts() {
        let var1 = make_var(1);
        let var2 = make_var(2);

        let shared1 = Loan::top_level(LoanId::new(0), var1, BorrowKind::Shared);
        let shared2 = Loan::top_level(LoanId::new(1), var1, BorrowKind::Shared);
        let excl1 = Loan::top_level(LoanId::new(2), var1, BorrowKind::Exclusive);
        let excl_other = Loan::top_level(LoanId::new(3), var2, BorrowKind::Exclusive);

        // Two shared borrows of same var don't conflict
        assert!(!loan_conflicts(&shared1, &shared2));

        // Exclusive + shared of same var conflict
        assert!(loan_conflicts(&shared1, &excl1));
        assert!(loan_conflicts(&excl1, &shared1));

        // Two exclusive of same var conflict
        let excl1b = Loan::top_level(LoanId::new(4), var1, BorrowKind::Exclusive);
        assert!(loan_conflicts(&excl1, &excl1b));

        // Different variables don't conflict
        assert!(!loan_conflicts(&excl1, &excl_other));
        assert!(!loan_conflicts(&shared1, &excl_other));
    }

    #[test]
    fn test_begin_borrow() {
        let mut counter = LoanCounter::new();
        let var = make_var(1);

        let loan1 = begin_shared_borrow(&mut counter, var, 0);
        assert!(loan1.is_shared());
        assert_eq!(loan1.id.raw(), 0);

        let loan2 = begin_exclusive_borrow(&mut counter, var, 1);
        assert!(loan2.is_exclusive());
        assert_eq!(loan2.id.raw(), 1);
    }

    #[test]
    fn test_end_borrow() {
        let mut counter = LoanCounter::new();
        let var = make_var(1);

        let loan1 = begin_shared_borrow(&mut counter, var, 0);
        let loan2 = begin_shared_borrow(&mut counter, var, 0);

        let mut loans = vec![loan1.clone(), loan2.clone()];

        assert!(end_borrow(&mut loans, loan1.id));
        assert_eq!(loans.len(), 1);
        assert_eq!(loans[0].id, loan2.id);

        assert!(!end_borrow(&mut loans, loan1.id)); // Already removed
        assert_eq!(loans.len(), 1);
    }

    #[test]
    fn test_ref_box_diamond() {
        let rbd_ref = RefBoxDiamond::Ref(Region::Static);
        assert!(rbd_ref.is_ref());
        assert!(!rbd_ref.is_box());
        assert_eq!(rbd_ref.region(), Some(Region::Static));

        let rbd_box = RefBoxDiamond::Box;
        assert!(rbd_box.is_box());
        assert!(rbd_box.region().is_none());

        let rbd_diamond = RefBoxDiamond::Diamond(Region::Fresh(0));
        assert!(rbd_diamond.is_diamond());
        assert_eq!(rbd_diamond.region(), Some(Region::Fresh(0)));
    }

    // =========================================================================
    // VarState Tests
    // =========================================================================

    #[test]
    fn test_var_state_default() {
        assert_eq!(VarState::default(), VarState::Owned);
    }

    #[test]
    fn test_var_state_constructors() {
        assert_eq!(VarState::owned(), VarState::Owned);
        assert_eq!(VarState::shared(), VarState::Shared { ref_count: 1 });
        assert_eq!(VarState::borrowed(LoanId::new(42)), VarState::Borrowed(vec![LoanId::new(42)]));
        assert_eq!(VarState::borrowed_mut(LoanId::new(99)), VarState::BorrowedMut(LoanId::new(99)));
    }

    #[test]
    fn test_is_available() {
        assert!(is_available(&VarState::Owned));
        assert!(!is_available(&VarState::Moved));
        assert!(is_available(&VarState::Borrowed(vec![LoanId::new(1)])));
        assert!(is_available(&VarState::BorrowedMut(LoanId::new(1))));
        assert!(is_available(&VarState::Shared { ref_count: 1 }));
        assert!(!is_available(&VarState::Dropped));
    }

    #[test]
    fn test_can_move() {
        // Only Owned can be moved
        assert!(can_move(&VarState::Owned));

        // All other states cannot be moved
        assert!(!can_move(&VarState::Moved));
        assert!(!can_move(&VarState::Borrowed(vec![LoanId::new(1)])));
        assert!(!can_move(&VarState::BorrowedMut(LoanId::new(1))));
        assert!(!can_move(&VarState::Shared { ref_count: 1 }));
        assert!(!can_move(&VarState::Dropped));
    }

    #[test]
    fn test_can_borrow_shared() {
        // Owned and Borrowed can borrow shared
        assert!(can_borrow_shared(&VarState::Owned));
        assert!(can_borrow_shared(&VarState::Borrowed(vec![LoanId::new(1)])));

        // Other states cannot borrow shared
        assert!(!can_borrow_shared(&VarState::Moved));
        assert!(!can_borrow_shared(&VarState::BorrowedMut(LoanId::new(1))));
        assert!(!can_borrow_shared(&VarState::Shared { ref_count: 1 }));
        assert!(!can_borrow_shared(&VarState::Dropped));
    }

    #[test]
    fn test_can_borrow_mut() {
        // Only Owned can borrow mut
        assert!(can_borrow_mut(&VarState::Owned));

        // All other states cannot borrow mut
        assert!(!can_borrow_mut(&VarState::Moved));
        assert!(!can_borrow_mut(&VarState::Borrowed(vec![LoanId::new(1)])));
        assert!(!can_borrow_mut(&VarState::BorrowedMut(LoanId::new(1))));
        assert!(!can_borrow_mut(&VarState::Shared { ref_count: 1 }));
        assert!(!can_borrow_mut(&VarState::Dropped));
    }

    #[test]
    fn test_is_ref_counted() {
        assert!(is_ref_counted(&VarState::Shared { ref_count: 1 }));
        assert!(is_ref_counted(&VarState::Shared { ref_count: 100 }));

        assert!(!is_ref_counted(&VarState::Owned));
        assert!(!is_ref_counted(&VarState::Moved));
        assert!(!is_ref_counted(&VarState::Borrowed(vec![LoanId::new(1)])));
        assert!(!is_ref_counted(&VarState::BorrowedMut(LoanId::new(1))));
        assert!(!is_ref_counted(&VarState::Dropped));
    }

    #[test]
    fn test_clone_shared() {
        // Cloning shared increments ref count
        let state = VarState::Shared { ref_count: 1 };
        assert_eq!(clone_shared(&state), Some(VarState::Shared { ref_count: 2 }));

        let state = VarState::Shared { ref_count: 5 };
        assert_eq!(clone_shared(&state), Some(VarState::Shared { ref_count: 6 }));

        // Non-shared states return None
        assert_eq!(clone_shared(&VarState::Owned), None);
        assert_eq!(clone_shared(&VarState::Moved), None);
        assert_eq!(clone_shared(&VarState::Borrowed(vec![LoanId::new(1)])), None);
        assert_eq!(clone_shared(&VarState::BorrowedMut(LoanId::new(1))), None);
        assert_eq!(clone_shared(&VarState::Dropped), None);
    }

    #[test]
    fn test_clone_shared_overflow() {
        let state = VarState::Shared { ref_count: u32::MAX };
        assert_eq!(clone_shared(&state), None);
    }

    #[test]
    fn test_drop_shared_ref() {
        // Dropping with ref_count > 1 decrements
        let state = VarState::Shared { ref_count: 3 };
        assert_eq!(drop_shared_ref(&state), Some(VarState::Shared { ref_count: 2 }));

        // Dropping with ref_count == 1 drops the value
        let state = VarState::Shared { ref_count: 1 };
        assert_eq!(drop_shared_ref(&state), Some(VarState::Dropped));

        // ref_count == 0 edge case
        let state = VarState::Shared { ref_count: 0 };
        assert_eq!(drop_shared_ref(&state), Some(VarState::Dropped));

        // Non-shared states return None
        assert_eq!(drop_shared_ref(&VarState::Owned), None);
        assert_eq!(drop_shared_ref(&VarState::Moved), None);
    }

    #[test]
    fn test_add_shared_borrow() {
        // Owned -> Borrowed
        let state = VarState::Owned;
        assert_eq!(add_shared_borrow(&state, LoanId::new(1)), Some(VarState::Borrowed(vec![LoanId::new(1)])));

        // Borrowed -> Borrowed (add more)
        let state = VarState::Borrowed(vec![LoanId::new(1)]);
        assert_eq!(add_shared_borrow(&state, LoanId::new(2)), Some(VarState::Borrowed(vec![LoanId::new(1), LoanId::new(2)])));

        // Other states cannot add borrow
        assert_eq!(add_shared_borrow(&VarState::Moved, LoanId::new(1)), None);
        assert_eq!(add_shared_borrow(&VarState::BorrowedMut(LoanId::new(1)), LoanId::new(2)), None);
        assert_eq!(add_shared_borrow(&VarState::Shared { ref_count: 1 }, LoanId::new(1)), None);
    }

    #[test]
    fn test_end_shared_borrow() {
        // Ending last borrow returns to Owned
        let state = VarState::Borrowed(vec![LoanId::new(1)]);
        assert_eq!(end_shared_borrow(&state, LoanId::new(1)), Some(VarState::Owned));

        // Ending one of many borrows
        let state = VarState::Borrowed(vec![LoanId::new(1), LoanId::new(2), LoanId::new(3)]);
        assert_eq!(end_shared_borrow(&state, LoanId::new(2)), Some(VarState::Borrowed(vec![LoanId::new(1), LoanId::new(3)])));

        // Non-borrowed states return None
        assert_eq!(end_shared_borrow(&VarState::Owned, LoanId::new(1)), None);
    }

    #[test]
    fn test_end_mut_borrow() {
        // Correct loan returns to Owned
        let state = VarState::BorrowedMut(LoanId::new(42));
        assert_eq!(end_mut_borrow(&state, LoanId::new(42)), Some(VarState::Owned));

        // Wrong loan returns None
        let state = VarState::BorrowedMut(LoanId::new(42));
        assert_eq!(end_mut_borrow(&state, LoanId::new(99)), None);

        // Non-BorrowedMut states return None
        assert_eq!(end_mut_borrow(&VarState::Owned, LoanId::new(1)), None);
        assert_eq!(end_mut_borrow(&VarState::Borrowed(vec![LoanId::new(1)]), LoanId::new(1)), None);
    }

    #[test]
    fn test_var_entry_new() {
        let var = make_var(1);
        let entry = VarEntry::new(var, BrrrType::BOOL, Mode::One);

        assert_eq!(entry.var, var);
        assert_eq!(entry.ty, BrrrType::BOOL);
        assert_eq!(entry.mode, Mode::One);
        assert_eq!(entry.state, VarState::Owned);
    }

    #[test]
    fn test_var_entry_new_shared() {
        let var = make_var(1);
        let entry = VarEntry::new_shared(var, BrrrType::STRING, Mode::Omega);

        assert_eq!(entry.state, VarState::Shared { ref_count: 1 });
    }

    #[test]
    fn test_var_entry_move() {
        let var = make_var(1);
        let mut entry = VarEntry::new(var, BrrrType::BOOL, Mode::One);

        assert!(entry.can_move());
        assert!(entry.do_move());
        assert_eq!(entry.state, VarState::Moved);

        // Cannot move again
        assert!(!entry.can_move());
        assert!(!entry.do_move());
    }

    #[test]
    fn test_var_entry_borrow_shared() {
        let var = make_var(1);
        let mut entry = VarEntry::new(var, BrrrType::BOOL, Mode::One);

        // Add first borrow
        assert!(entry.can_borrow_shared());
        assert!(entry.add_borrow(LoanId::new(1)));
        assert_eq!(entry.state, VarState::Borrowed(vec![LoanId::new(1)]));

        // Add second borrow
        assert!(entry.can_borrow_shared());
        assert!(entry.add_borrow(LoanId::new(2)));
        assert_eq!(entry.state, VarState::Borrowed(vec![LoanId::new(1), LoanId::new(2)]));

        // Cannot move while borrowed
        assert!(!entry.can_move());

        // End borrows
        assert!(entry.end_borrow(LoanId::new(1)));
        assert!(entry.end_borrow(LoanId::new(2)));
        assert_eq!(entry.state, VarState::Owned);

        // Can move again
        assert!(entry.can_move());
    }

    #[test]
    fn test_var_entry_borrow_mut() {
        let var = make_var(1);
        let mut entry = VarEntry::new(var, BrrrType::BOOL, Mode::One);

        // Add mut borrow
        assert!(entry.can_borrow_mut());
        assert!(entry.add_mut_borrow(LoanId::new(1)));
        assert_eq!(entry.state, VarState::BorrowedMut(LoanId::new(1)));

        // Cannot borrow again while mut borrowed
        assert!(!entry.can_borrow_mut());
        assert!(!entry.can_borrow_shared());
        assert!(!entry.can_move());

        // End mut borrow
        assert!(entry.end_mut_borrow(LoanId::new(1)));
        assert_eq!(entry.state, VarState::Owned);

        // Can operate again
        assert!(entry.can_borrow_mut());
        assert!(entry.can_borrow_shared());
        assert!(entry.can_move());
    }

    #[test]
    fn test_var_entry_drop() {
        let var = make_var(1);
        let mut entry = VarEntry::new(var, BrrrType::BOOL, Mode::One);

        entry.drop();
        assert_eq!(entry.state, VarState::Dropped);
        assert!(!entry.is_available());
        assert!(!entry.can_move());
        assert!(!entry.can_borrow_shared());
        assert!(!entry.can_borrow_mut());
    }

    #[test]
    fn test_var_state_display() {
        assert_eq!(format!("{}", VarState::Owned), "owned");
        assert_eq!(format!("{}", VarState::Moved), "moved");
        assert_eq!(format!("{}", VarState::Borrowed(vec![LoanId::new(1), LoanId::new(2)])), "borrowed(2 loans)");
        assert_eq!(format!("{}", VarState::BorrowedMut(LoanId::new(42))), "borrowed_mut(loan=L42)");
        assert_eq!(format!("{}", VarState::Shared { ref_count: 5 }), "shared(rc=5)");
        assert_eq!(format!("{}", VarState::Dropped), "dropped");
    }

    #[test]
    fn test_owned_semantics() {
        // Owned can: move, borrow shared, borrow mut
        let state = VarState::Owned;
        assert!(is_available(&state));
        assert!(can_move(&state));
        assert!(can_borrow_shared(&state));
        assert!(can_borrow_mut(&state));
    }

    #[test]
    fn test_moved_semantics() {
        // Moved cannot do anything
        let state = VarState::Moved;
        assert!(!is_available(&state));
        assert!(!can_move(&state));
        assert!(!can_borrow_shared(&state));
        assert!(!can_borrow_mut(&state));
    }

    #[test]
    fn test_borrowed_semantics() {
        // Borrowed can borrow shared but not move
        let state = VarState::Borrowed(vec![LoanId::new(1)]);
        assert!(is_available(&state));
        assert!(!can_move(&state));
        assert!(can_borrow_shared(&state));
        assert!(!can_borrow_mut(&state));
    }

    #[test]
    fn test_borrowed_mut_semantics() {
        // BorrowedMut cannot do anything until borrow ends
        let state = VarState::BorrowedMut(LoanId::new(1));
        assert!(is_available(&state)); // Technically available, just restricted
        assert!(!can_move(&state));
        assert!(!can_borrow_shared(&state));
        assert!(!can_borrow_mut(&state));
    }
}
