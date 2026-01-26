//! Borrow state tracking for ownership and lifetime analysis
//!
//! Mirrors F* BorrowChecker.fst:
//! - `borrow_state` (lines 388-394)
//! - `extended_borrow_state` (lines 1668-1675)
//! - State lookup and update operations (lines 405-468)
//!
//! # Overview
//!
//! This module provides the core data structures for tracking borrow checker state:
//!
//! - [`BorrowKind`] - Shared (`&T`) vs exclusive (`&mut T`) borrows
//! - [`Loan`] - Active borrow with variable, kind, and depth
//! - [`LoanCounter`] - Monotonic counter for fresh loan IDs
//! - [`BorrowState`] - Complete borrow checker state with variables and loans
//! - [`RegionCap`] - Region capability for lifetime tracking
//! - [`ExtendedBorrowState`] - Full state with region tracking
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::borrow::{BorrowState, BorrowKind, Loan};
//! use brrr_repr::types::BrrrType;
//! use brrr_repr::modes::Mode;
//!
//! let mut state = BorrowState::new();
//!
//! // Add a variable
//! state.add_var(var_id, BrrrType::BOOL, Mode::One);
//!
//! // Create a loan and enter scope
//! let state = state.enter_scope();
//! let loan = Loan::new(state.fresh_loan_id(), var_id, BorrowKind::Shared, state.depth);
//! let state = state.add_loan(loan);
//!
//! // Exit scope
//! let state = state.exit_scope();
//! ```

use serde::{Deserialize, Serialize};

use super::types::{LoanId, VarEntry, VarState};
use crate::modes::{ExtendedMode, Mode};
use crate::types::{BrrrType, Region};
use crate::verification::VarId;

// ============================================================================
// Borrow Kind
// ============================================================================

/// Kind of borrow: shared or exclusive
///
/// Maps to F* BorrowChecker.fst:
/// ```fstar
/// type borrow_kind =
///   | BorrowShared    : borrow_kind   (* &T *)
///   | BorrowExclusive : borrow_kind   (* &mut T *)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[repr(u8)]
pub enum BorrowKind {
    /// Shared/immutable borrow (`&T`)
    #[default]
    Shared = 0,

    /// Exclusive/mutable borrow (`&mut T`)
    Exclusive = 1,
}

impl BorrowKind {
    /// Check if this is a shared borrow
    pub const fn is_shared(self) -> bool {
        matches!(self, Self::Shared)
    }

    /// Check if this is an exclusive borrow
    pub const fn is_exclusive(self) -> bool {
        matches!(self, Self::Exclusive)
    }

    /// Check if two borrow kinds conflict
    pub const fn conflicts_with(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::Exclusive, _) | (_, Self::Exclusive)
        )
    }
}

// ============================================================================
// Loan Counter
// ============================================================================

/// Monotonic counter for generating fresh loan IDs
#[derive(Debug, Clone, Default)]
pub struct LoanCounter(u32);

impl LoanCounter {
    /// Create a new counter starting at zero
    pub const fn new() -> Self {
        Self(0)
    }

    /// Generate a fresh loan ID and increment counter
    pub fn fresh(&mut self) -> LoanId {
        let id = LoanId::new(self.0);
        self.0 = self.0.saturating_add(1);
        id
    }

    /// Get current counter value
    pub const fn current(&self) -> u32 {
        self.0
    }
}

// ============================================================================
// Loan
// ============================================================================

/// An active loan (borrow) of a variable
///
/// Maps to F* BorrowChecker.fst lines 207-213:
/// ```fstar
/// noeq type loan = {
///   loan_id      : loan_id;
///   loan_var     : var_id;
///   loan_kind    : borrow_kind;
///   loan_depth   : nat
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Loan {
    /// Unique identifier for this loan
    pub id: LoanId,
    /// Variable being borrowed
    pub var: VarId,
    /// Kind of borrow (shared or exclusive)
    pub kind: BorrowKind,
    /// Nesting depth (0 for top-level)
    pub depth: u32,
}

impl Loan {
    /// Create a new loan
    pub const fn new(id: LoanId, var: VarId, kind: BorrowKind, depth: u32) -> Self {
        Self { id, var, kind, depth }
    }

    /// Create a top-level loan (depth 0)
    pub const fn top_level(id: LoanId, var: VarId, kind: BorrowKind) -> Self {
        Self::new(id, var, kind, 0)
    }

    /// Check if this is a shared loan
    pub const fn is_shared(&self) -> bool {
        self.kind.is_shared()
    }

    /// Check if this is an exclusive loan
    pub const fn is_exclusive(&self) -> bool {
        self.kind.is_exclusive()
    }
}

/// Check if two loans conflict (same variable, at least one exclusive)
pub fn loan_conflicts(l1: &Loan, l2: &Loan) -> bool {
    l1.var == l2.var && l1.kind.conflicts_with(l2.kind)
}

// ============================================================================
// Region Capability
// ============================================================================

/// Region capability for lifetime tracking
///
/// Maps to F* BorrowChecker.fst lines 40-44:
/// ```fstar
/// type region_cap = {
///   rc_region : region;
///   rc_valid  : bool
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RegionCap {
    /// The region this capability refers to
    pub region: Region,
    /// Whether the capability is still valid
    pub valid: bool,
}

impl RegionCap {
    /// Create a new valid region capability
    pub const fn new(region: Region) -> Self {
        Self { region, valid: true }
    }

    /// Invalidate this capability
    pub fn invalidate(&mut self) {
        self.valid = false;
    }
}

/// Region context - tracks available region capabilities
pub type RegionCtx = Vec<RegionCap>;

/// Check if region has valid capability in context
pub fn has_region_cap(region: Region, ctx: &RegionCtx) -> bool {
    ctx.iter().any(|rc| rc.region == region && rc.valid)
}

/// Add region capability to context
pub fn add_region_cap(region: Region, ctx: &mut RegionCtx) {
    ctx.push(RegionCap::new(region));
}

/// Invalidate region capability
pub fn invalidate_region(region: Region, ctx: &mut RegionCtx) {
    for cap in ctx.iter_mut() {
        if cap.region == region {
            cap.valid = false;
        }
    }
}

// ============================================================================
// Region Counter
// ============================================================================

/// Monotonic counter for generating fresh region IDs
#[derive(Debug, Clone, Default)]
pub struct RegionCounter(u32);

impl RegionCounter {
    /// Create a new counter starting at zero
    pub const fn new() -> Self {
        Self(0)
    }

    /// Generate a fresh region
    pub fn fresh(&mut self) -> Region {
        let region = Region::Fresh(self.0);
        self.0 = self.0.saturating_add(1);
        region
    }

    /// Get current counter value
    pub const fn current(&self) -> u32 {
        self.0
    }
}

// ============================================================================
// Borrow State
// ============================================================================

/// Borrow checker state
///
/// Maps to F* BorrowChecker.fst lines 388-394:
/// ```fstar
/// noeq type borrow_state = {
///   bs_vars      : list var_entry;
///   bs_loans     : list loan;
///   bs_counter   : loan_counter;
///   bs_depth     : nat
/// }
/// ```
#[derive(Debug, Clone, Default)]
pub struct BorrowState {
    /// Variable states
    pub vars: Vec<VarEntry>,
    /// Active loans
    pub loans: Vec<Loan>,
    /// Loan ID generator
    pub counter: LoanCounter,
    /// Current scope depth
    pub depth: u32,
}

impl BorrowState {
    /// Create an empty borrow state
    pub fn new() -> Self {
        Self::default()
    }

    /// Create with initial depth
    pub fn with_depth(depth: u32) -> Self {
        Self {
            depth,
            ..Self::default()
        }
    }

    // -------------------------------------------------------------------------
    // Variable lookup and update
    // -------------------------------------------------------------------------

    /// Look up a variable entry by ID
    ///
    /// Maps to F* `find_var : var_id -> borrow_state -> option var_entry`
    pub fn lookup_var(&self, var: VarId) -> Option<&VarEntry> {
        self.vars.iter().find(|entry| entry.var == var)
    }

    /// Look up a variable entry mutably
    pub fn lookup_var_mut(&mut self, var: VarId) -> Option<&mut VarEntry> {
        self.vars.iter_mut().find(|entry| entry.var == var)
    }

    /// Update the state of a variable (functional style)
    ///
    /// Returns a new BorrowState with the updated variable.
    pub fn update_var_state(mut self, var: VarId, new_state: VarState) -> Self {
        if let Some(entry) = self.vars.iter_mut().find(|e| e.var == var) {
            entry.state = new_state;
        }
        self
    }

    /// Update the state of a variable in place
    ///
    /// Returns true if the variable was found and updated.
    pub fn update_var_state_mut(&mut self, var: VarId, new_state: VarState) -> bool {
        if let Some(entry) = self.vars.iter_mut().find(|e| e.var == var) {
            entry.state = new_state;
            true
        } else {
            false
        }
    }

    /// Add a new variable to the state
    pub fn add_var(&mut self, var: VarId, ty: BrrrType, mode: Mode) {
        self.vars.push(VarEntry::new(var, ty, mode));
    }

    // -------------------------------------------------------------------------
    // Loan management
    // -------------------------------------------------------------------------

    /// Add a new loan (functional style)
    pub fn add_loan(mut self, loan: Loan) -> Self {
        self.loans.push(loan);
        self
    }

    /// Add a loan in place
    pub fn add_loan_mut(&mut self, loan: Loan) {
        self.loans.push(loan);
    }

    /// Remove a loan by ID (functional style)
    ///
    /// Returns `Some(new_state)` if loan was found, `None` otherwise.
    pub fn remove_loan(mut self, loan_id: LoanId) -> Option<Self> {
        let original_len = self.loans.len();
        self.loans.retain(|l| l.id != loan_id);

        if self.loans.len() < original_len {
            Some(self)
        } else {
            None
        }
    }

    /// Remove a loan in place
    ///
    /// Returns true if the loan was found and removed.
    pub fn remove_loan_mut(&mut self, loan_id: LoanId) -> bool {
        let original_len = self.loans.len();
        self.loans.retain(|l| l.id != loan_id);
        self.loans.len() < original_len
    }

    /// Find a loan by ID
    pub fn find_loan(&self, loan_id: LoanId) -> Option<&Loan> {
        self.loans.iter().find(|l| l.id == loan_id)
    }

    /// Get all loans for a specific variable
    pub fn loans_for_var(&self, var: VarId) -> Vec<&Loan> {
        self.loans.iter().filter(|l| l.var == var).collect()
    }

    // -------------------------------------------------------------------------
    // Scope management
    // -------------------------------------------------------------------------

    /// Enter a new scope (functional style)
    ///
    /// Increments depth counter.
    pub fn enter_scope(mut self) -> Self {
        self.depth = self.depth.saturating_add(1);
        self
    }

    /// Enter a new scope in place
    pub fn enter_scope_mut(&mut self) {
        self.depth = self.depth.saturating_add(1);
    }

    /// Exit the current scope (functional style)
    ///
    /// Decrements depth and removes all loans at or beyond current depth.
    pub fn exit_scope(mut self) -> Self {
        let current_depth = self.depth;

        // Remove all loans at or beyond current depth
        self.loans.retain(|l| l.depth < current_depth);

        // Decrement depth
        if self.depth > 0 {
            self.depth -= 1;
        }

        self
    }

    /// Exit the current scope in place
    pub fn exit_scope_mut(&mut self) {
        let current_depth = self.depth;
        self.loans.retain(|l| l.depth < current_depth);

        if self.depth > 0 {
            self.depth -= 1;
        }
    }

    /// Get the current scope depth
    pub fn current_depth(&self) -> u32 {
        self.depth
    }

    /// Generate a fresh loan ID
    pub fn fresh_loan_id(&mut self) -> LoanId {
        self.counter.fresh()
    }
}

// ============================================================================
// Extended Variable Entry
// ============================================================================

/// Variable entry with extended mode tracking
///
/// Maps to F* BorrowChecker.fst lines 1658-1665:
/// ```fstar
/// noeq type extended_var_entry = {
///   eve_var    : var_id;
///   eve_ty     : brrr_type;
///   eve_mode   : mode;
///   eve_ext    : extended_mode;
///   eve_state  : var_state;
///   eve_region : option region
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExtendedVarEntry {
    /// Variable identifier
    pub var: VarId,
    /// Variable type
    pub ty: BrrrType,
    /// Base usage mode
    pub mode: Mode,
    /// Extended mode (Linear, Affine, Relevant, Unrestricted)
    pub extended_mode: ExtendedMode,
    /// Current ownership state
    pub state: VarState,
    /// Optional region annotation
    pub region: Option<Region>,
}

impl ExtendedVarEntry {
    /// Create a new extended variable entry with default unrestricted mode
    pub fn new(var: VarId, ty: BrrrType, mode: Mode) -> Self {
        Self {
            var,
            ty,
            mode,
            extended_mode: ExtendedMode::Unrestricted,
            state: VarState::Owned,
            region: None,
        }
    }

    /// Create with explicit extended mode
    pub fn with_extended(
        var: VarId,
        ty: BrrrType,
        mode: Mode,
        ext: ExtendedMode,
        region: Option<Region>,
    ) -> Self {
        Self {
            var,
            ty,
            mode,
            extended_mode: ext,
            state: VarState::Owned,
            region,
        }
    }

    /// Convert to basic VarEntry
    pub fn to_var_entry(&self) -> VarEntry {
        VarEntry {
            var: self.var,
            ty: self.ty.clone(),
            mode: self.mode,
            state: self.state.clone(),
        }
    }

    /// Create from basic VarEntry
    pub fn from_var_entry(entry: &VarEntry) -> Self {
        Self {
            var: entry.var,
            ty: entry.ty.clone(),
            mode: entry.mode,
            extended_mode: ExtendedMode::Unrestricted,
            state: entry.state.clone(),
            region: None,
        }
    }
}

// ============================================================================
// Extended Borrow State
// ============================================================================

/// Extended borrow state with region tracking
///
/// Maps to F* BorrowChecker.fst lines 1668-1675:
/// ```fstar
/// noeq type extended_borrow_state = {
///   ebs_vars    : list extended_var_entry;
///   ebs_loans   : list loan;
///   ebs_counter : loan_counter;
///   ebs_depth   : nat;
///   ebs_regions : region_ctx;
///   ebs_region_counter : region_counter
/// }
/// ```
#[derive(Debug, Clone, Default)]
pub struct ExtendedBorrowState {
    /// Variable states with extended mode tracking
    pub vars: Vec<ExtendedVarEntry>,
    /// Active loans
    pub loans: Vec<Loan>,
    /// Loan ID generator
    pub counter: LoanCounter,
    /// Current scope depth
    pub depth: u32,
    /// Active region capabilities
    pub regions: RegionCtx,
    /// Fresh region generator
    pub region_counter: RegionCounter,
}

impl ExtendedBorrowState {
    /// Create an empty extended borrow state
    pub fn new() -> Self {
        Self::default()
    }

    // -------------------------------------------------------------------------
    // Variable operations
    // -------------------------------------------------------------------------

    /// Look up a variable entry by ID
    pub fn lookup_var(&self, var: VarId) -> Option<&ExtendedVarEntry> {
        self.vars.iter().find(|entry| entry.var == var)
    }

    /// Look up a variable entry mutably
    pub fn lookup_var_mut(&mut self, var: VarId) -> Option<&mut ExtendedVarEntry> {
        self.vars.iter_mut().find(|entry| entry.var == var)
    }

    /// Update the state of a variable (functional style)
    pub fn update_var_state(mut self, var: VarId, new_state: VarState) -> Self {
        if let Some(entry) = self.vars.iter_mut().find(|e| e.var == var) {
            entry.state = new_state;
        }
        self
    }

    /// Add a variable with extended mode
    pub fn add_var(
        &mut self,
        var: VarId,
        ty: BrrrType,
        mode: Mode,
        ext: ExtendedMode,
        region: Option<Region>,
    ) {
        self.vars.push(ExtendedVarEntry::with_extended(var, ty, mode, ext, region));
    }

    // -------------------------------------------------------------------------
    // Loan operations
    // -------------------------------------------------------------------------

    /// Add a loan (functional style)
    pub fn add_loan(mut self, loan: Loan) -> Self {
        self.loans.push(loan);
        self
    }

    /// Remove a loan by ID (functional style)
    pub fn remove_loan(mut self, loan_id: LoanId) -> Option<Self> {
        let original_len = self.loans.len();
        self.loans.retain(|l| l.id != loan_id);

        if self.loans.len() < original_len {
            Some(self)
        } else {
            None
        }
    }

    /// Find a loan by ID
    pub fn find_loan(&self, loan_id: LoanId) -> Option<&Loan> {
        self.loans.iter().find(|l| l.id == loan_id)
    }

    // -------------------------------------------------------------------------
    // Scope operations
    // -------------------------------------------------------------------------

    /// Enter a new scope (functional style)
    pub fn enter_scope(mut self) -> Self {
        self.depth = self.depth.saturating_add(1);
        self
    }

    /// Exit the current scope (functional style)
    pub fn exit_scope(mut self) -> Self {
        let current_depth = self.depth;
        self.loans.retain(|l| l.depth < current_depth);

        if self.depth > 0 {
            self.depth -= 1;
        }
        self
    }

    // -------------------------------------------------------------------------
    // Region operations
    // -------------------------------------------------------------------------

    /// Enter letregion scope: introduce fresh region
    ///
    /// Returns (fresh_region, new_state)
    pub fn enter_letregion(mut self) -> (Region, Self) {
        let region = self.region_counter.fresh();
        add_region_cap(region, &mut self.regions);
        self.depth = self.depth.saturating_add(1);
        (region, self)
    }

    /// Exit letregion scope: invalidate region
    pub fn exit_letregion(mut self, region: Region) -> Self {
        invalidate_region(region, &mut self.regions);

        if self.depth > 0 {
            self.depth -= 1;
        }
        self
    }

    /// Check if a region has valid capability
    pub fn has_region(&self, region: Region) -> bool {
        has_region_cap(region, &self.regions)
    }

    /// Generate a fresh loan ID
    pub fn fresh_loan_id(&mut self) -> LoanId {
        self.counter.fresh()
    }

    // -------------------------------------------------------------------------
    // Conversion
    // -------------------------------------------------------------------------

    /// Convert to basic BorrowState
    pub fn to_borrow_state(&self) -> BorrowState {
        BorrowState {
            vars: self.vars.iter().map(|e| e.to_var_entry()).collect(),
            loans: self.loans.clone(),
            counter: self.counter.clone(),
            depth: self.depth,
        }
    }

    /// Create from basic BorrowState
    pub fn from_borrow_state(state: &BorrowState) -> Self {
        Self {
            vars: state.vars.iter().map(ExtendedVarEntry::from_var_entry).collect(),
            loans: state.loans.clone(),
            counter: state.counter.clone(),
            depth: state.depth,
            regions: Vec::new(),
            region_counter: RegionCounter::new(),
        }
    }
}

// ============================================================================
// Borrow State Merging for Control Flow
// ============================================================================
//
// Maps to F* BorrowChecker.fst lines 519-663:
// - `merge_var_state` - Merge variable states taking most restrictive
// - `merge_var_entry` - Merge variable entries
// - `merge_loans` - Union of active loans
// - `merge_borrow_states` - Merge complete borrow states
//
// Key insight: Merge takes MOST RESTRICTIVE state. If a variable is moved
// in either control flow branch, the merged result is moved.

/// Merge two variable states, taking the most restrictive state
///
/// Maps to F* BorrowChecker.fst:
/// ```fstar
/// let merge_var_state (s1 s2: var_state) : var_state =
///   match s1, s2 with
///   | VsOwned, VsOwned -> VsOwned
///   | VsMoved, _ | _, VsMoved -> VsMoved  (* Most restrictive *)
///   | VsDropped, _ | _, VsDropped -> VsDropped
///   | VsBorrowed l1, VsBorrowed l2 -> VsBorrowed (l1 @ l2)
///   | VsBorrowedMut l, _ | _, VsBorrowedMut l -> VsBorrowedMut l
///   | VsShared n1, VsShared n2 -> VsShared (max n1 n2)
///   | VsOwned, VsBorrowed l | VsBorrowed l, VsOwned -> VsBorrowed l
///   | VsOwned, VsShared n | VsShared n, VsOwned -> VsShared n
/// ```
///
/// # Restrictiveness Ordering
///
/// From most restrictive to least:
/// 1. Moved - value consumed, use-after-move error
/// 2. Dropped - value explicitly dropped
/// 3. BorrowedMut - exclusive borrow active
/// 4. Borrowed - shared borrows active
/// 5. Shared - reference-counted
/// 6. Owned - full ownership
///
/// # Example
///
/// ```ignore
/// use brrr_repr::borrow::{VarState, merge_var_state};
///
/// // If one branch moved, result is moved
/// let s1 = VarState::Owned;
/// let s2 = VarState::Moved;
/// assert_eq!(merge_var_state(&s1, &s2), VarState::Moved);
///
/// // Borrows are combined
/// let s1 = VarState::Borrowed(vec![LoanId::new(1)]);
/// let s2 = VarState::Borrowed(vec![LoanId::new(2)]);
/// let merged = merge_var_state(&s1, &s2);
/// // merged has both loans
/// ```
pub fn merge_var_state(s1: &VarState, s2: &VarState) -> VarState {
    use VarState::*;

    match (s1, s2) {
        // Both owned: stay owned
        (Owned, Owned) => Owned,

        // Moved is most restrictive - if either branch moved, result is moved
        (Moved, _) | (_, Moved) => Moved,

        // Dropped is very restrictive
        (Dropped, _) | (_, Dropped) => Dropped,

        // BorrowedMut is exclusive - take the loan from whichever branch has it
        (BorrowedMut(loan), _) | (_, BorrowedMut(loan)) => BorrowedMut(*loan),

        // Both have shared borrows: combine the loan lists
        (Borrowed(l1), Borrowed(l2)) => {
            let mut combined = l1.clone();
            // Add loans from l2 that aren't already present
            for loan in l2 {
                if !combined.contains(loan) {
                    combined.push(*loan);
                }
            }
            Borrowed(combined)
        }

        // Owned + Borrowed: take the borrowed state (more restrictive)
        (Owned, Borrowed(loans)) | (Borrowed(loans), Owned) => Borrowed(loans.clone()),

        // Both shared: take max ref count (more restrictive assumption)
        (Shared { ref_count: n1 }, Shared { ref_count: n2 }) => Shared {
            ref_count: (*n1).max(*n2),
        },

        // Owned + Shared: take the shared state
        (Owned, Shared { ref_count }) | (Shared { ref_count }, Owned) => Shared {
            ref_count: *ref_count,
        },

        // Borrowed + Shared: Borrowed is more restrictive
        (Borrowed(loans), Shared { .. }) | (Shared { .. }, Borrowed(loans)) => {
            Borrowed(loans.clone())
        }
    }
}

/// Merge two variable entries
///
/// Maps to F* BorrowChecker.fst:
/// ```fstar
/// let merge_var_entry (e1 e2: var_entry) : var_entry = {
///   ve_var = e1.ve_var;
///   ve_type = e1.ve_type;
///   ve_mode = mode_meet e1.ve_mode e2.ve_mode;
///   ve_state = merge_var_state e1.ve_state e2.ve_state
/// }
/// ```
///
/// # Panics
///
/// Panics if the two entries are for different variables.
/// This should never happen in well-formed control flow merge.
pub fn merge_var_entry(e1: &VarEntry, e2: &VarEntry) -> VarEntry {
    debug_assert_eq!(
        e1.var, e2.var,
        "merge_var_entry: variable mismatch - {:?} vs {:?}",
        e1.var, e2.var
    );

    VarEntry {
        var: e1.var,
        ty: e1.ty.clone(),
        // Mode meet: take the more restrictive mode
        mode: e1.mode.meet(e2.mode),
        // Merge states taking most restrictive
        state: merge_var_state(&e1.state, &e2.state),
    }
}

/// Merge two variable lists from control flow branches
///
/// Assumes both lists have the same variables in the same order.
/// For each variable, merges the entries using `merge_var_entry`.
///
/// # Panics
///
/// Panics if the lists have different lengths or mismatched variables.
pub fn merge_var_lists(l1: &[VarEntry], l2: &[VarEntry]) -> Vec<VarEntry> {
    debug_assert_eq!(
        l1.len(),
        l2.len(),
        "merge_var_lists: length mismatch - {} vs {}",
        l1.len(),
        l2.len()
    );

    l1.iter()
        .zip(l2.iter())
        .map(|(e1, e2)| merge_var_entry(e1, e2))
        .collect()
}

/// Merge two loan lists (union of active loans)
///
/// Maps to F* BorrowChecker.fst:
/// ```fstar
/// let merge_loans (l1 l2: list loan) : list loan =
///   l1 @ l2  (* Union of active loans *)
/// ```
///
/// Active loans from either branch remain active after merge.
/// Deduplication is performed by loan ID.
pub fn merge_loans(l1: &[Loan], l2: &[Loan]) -> Vec<Loan> {
    let mut result = l1.to_vec();

    for loan in l2 {
        if !result.iter().any(|existing| existing.id == loan.id) {
            result.push(loan.clone());
        }
    }

    result
}

/// Merge two borrow states from control flow branches
///
/// Maps to F* BorrowChecker.fst:
/// ```fstar
/// let merge_borrow_states (s1 s2: borrow_state) : borrow_state = {
///   bs_vars = merge_var_lists s1.bs_vars s2.bs_vars;
///   bs_loans = merge_loans s1.bs_loans s2.bs_loans;
///   bs_counter = max s1.bs_counter s2.bs_counter;
///   bs_depth = s1.bs_depth  (* Should be same *)
/// }
/// ```
///
/// This is used after if/else, match, or other control flow constructs
/// to reconcile the borrow state from multiple execution paths.
///
/// # Example
///
/// ```ignore
/// use brrr_repr::borrow::{BorrowState, merge_borrow_states};
///
/// let before = BorrowState::new();
/// // ... add variables ...
///
/// // Simulate if-else
/// let then_branch = before.clone();
/// let else_branch = before.clone();
///
/// // ... execute branches, possibly moving/borrowing ...
///
/// let after = merge_borrow_states(&then_branch, &else_branch);
/// // 'after' has the most restrictive view of each variable
/// ```
///
/// # Panics
///
/// Debug-asserts that both states have the same depth (should always be true
/// after well-formed control flow).
pub fn merge_borrow_states(s1: &BorrowState, s2: &BorrowState) -> BorrowState {
    debug_assert_eq!(
        s1.depth, s2.depth,
        "merge_borrow_states: depth mismatch - {} vs {}",
        s1.depth, s2.depth
    );

    BorrowState {
        vars: merge_var_lists(&s1.vars, &s2.vars),
        loans: merge_loans(&s1.loans, &s2.loans),
        // Take the maximum counter to avoid ID collisions
        counter: LoanCounter(s1.counter.current().max(s2.counter.current())),
        // Depth should be the same (verified by debug_assert above)
        depth: s1.depth,
    }
}

impl BorrowState {
    /// Merge with another borrow state (method form of `merge_borrow_states`)
    ///
    /// See [`merge_borrow_states`] for details.
    #[must_use]
    pub fn merge(&self, other: &Self) -> Self {
        merge_borrow_states(self, other)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::{Key, Spur};

    fn make_var(n: usize) -> VarId {
        Spur::try_from_usize(n).unwrap()
    }

    fn make_loan_id(n: u32) -> LoanId {
        LoanId::new(n)
    }

    // -------------------------------------------------------------------------
    // BorrowKind tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_borrow_kind_conflicts() {
        // Shared + Shared = OK
        assert!(!BorrowKind::Shared.conflicts_with(BorrowKind::Shared));

        // Shared + Exclusive = CONFLICT
        assert!(BorrowKind::Shared.conflicts_with(BorrowKind::Exclusive));

        // Exclusive + Shared = CONFLICT
        assert!(BorrowKind::Exclusive.conflicts_with(BorrowKind::Shared));

        // Exclusive + Exclusive = CONFLICT
        assert!(BorrowKind::Exclusive.conflicts_with(BorrowKind::Exclusive));
    }

    // -------------------------------------------------------------------------
    // Loan tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_loan_creation() {
        let var = make_var(1);
        let loan = Loan::top_level(make_loan_id(0), var, BorrowKind::Shared);

        assert_eq!(loan.id, make_loan_id(0));
        assert_eq!(loan.var, var);
        assert!(loan.is_shared());
        assert_eq!(loan.depth, 0);
    }

    #[test]
    fn test_loan_conflicts() {
        let var = make_var(1);
        let shared1 = Loan::top_level(make_loan_id(0), var, BorrowKind::Shared);
        let shared2 = Loan::top_level(make_loan_id(1), var, BorrowKind::Shared);
        let excl = Loan::top_level(make_loan_id(2), var, BorrowKind::Exclusive);

        // Same var, both shared = OK
        assert!(!loan_conflicts(&shared1, &shared2));

        // Same var, one exclusive = CONFLICT
        assert!(loan_conflicts(&shared1, &excl));

        // Different vars = OK
        let other_var = make_var(2);
        let other_excl = Loan::top_level(make_loan_id(3), other_var, BorrowKind::Exclusive);
        assert!(!loan_conflicts(&excl, &other_excl));
    }

    // -------------------------------------------------------------------------
    // BorrowState tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_borrow_state_basic() {
        let mut state = BorrowState::new();
        let var = make_var(1);

        state.add_var(var, BrrrType::BOOL, Mode::One);

        assert!(state.lookup_var(var).is_some());
        assert!(state.lookup_var(make_var(2)).is_none());
    }

    #[test]
    fn test_borrow_state_update_var() {
        let mut state = BorrowState::new();
        let var = make_var(1);

        state.add_var(var, BrrrType::BOOL, Mode::One);

        let state = state.update_var_state(var, VarState::Moved);
        assert_eq!(state.lookup_var(var).unwrap().state, VarState::Moved);
    }

    #[test]
    fn test_borrow_state_loans() {
        let mut state = BorrowState::new();
        let var = make_var(1);
        let loan_id = state.fresh_loan_id();

        let loan = Loan::top_level(loan_id, var, BorrowKind::Shared);
        state = state.add_loan(loan);

        assert!(state.find_loan(loan_id).is_some());
        assert_eq!(state.loans_for_var(var).len(), 1);

        let state = state.remove_loan(loan_id);
        assert!(state.is_some());
        assert!(state.unwrap().find_loan(loan_id).is_none());
    }

    #[test]
    fn test_borrow_state_scope() {
        let state = BorrowState::new();
        assert_eq!(state.current_depth(), 0);

        let state = state.enter_scope();
        assert_eq!(state.current_depth(), 1);

        let state = state.enter_scope();
        assert_eq!(state.current_depth(), 2);

        let state = state.exit_scope();
        assert_eq!(state.current_depth(), 1);

        let state = state.exit_scope();
        assert_eq!(state.current_depth(), 0);
    }

    #[test]
    fn test_borrow_state_exit_scope_clears_loans() {
        let mut state = BorrowState::with_depth(2);
        let var = make_var(1);

        // Add loans at different depths
        let loan1 = Loan::new(state.fresh_loan_id(), var, BorrowKind::Shared, 1);
        let loan2 = Loan::new(state.fresh_loan_id(), var, BorrowKind::Shared, 2);

        state.add_loan_mut(loan1.clone());
        state.add_loan_mut(loan2.clone());

        assert_eq!(state.loans.len(), 2);

        let state = state.exit_scope();
        // Only loan at depth 1 should remain (depth 2 was cleared)
        assert_eq!(state.loans.len(), 1);
        assert!(state.find_loan(loan1.id).is_some());
        assert!(state.find_loan(loan2.id).is_none());
    }

    // -------------------------------------------------------------------------
    // Region tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_region_capability() {
        let mut ctx: RegionCtx = Vec::new();
        let region = Region::Fresh(0);

        assert!(!has_region_cap(region, &ctx));

        add_region_cap(region, &mut ctx);
        assert!(has_region_cap(region, &ctx));

        invalidate_region(region, &mut ctx);
        assert!(!has_region_cap(region, &ctx));
    }

    #[test]
    fn test_extended_borrow_state_letregion() {
        let state = ExtendedBorrowState::new();

        let (region, state) = state.enter_letregion();
        assert!(state.has_region(region));
        assert_eq!(state.depth, 1);

        let state = state.exit_letregion(region);
        assert!(!state.has_region(region));
        assert_eq!(state.depth, 0);
    }

    #[test]
    fn test_extended_var_entry_conversion() {
        let var = make_var(1);
        let entry = VarEntry::new(var, BrrrType::BOOL, Mode::One);

        let extended = ExtendedVarEntry::from_var_entry(&entry);
        assert_eq!(extended.var, var);
        assert_eq!(extended.extended_mode, ExtendedMode::Unrestricted);
        assert!(extended.region.is_none());

        let back = extended.to_var_entry();
        assert_eq!(back.var, entry.var);
        assert_eq!(back.mode, entry.mode);
    }

    #[test]
    fn test_region_counter() {
        let mut counter = RegionCounter::new();

        let r1 = counter.fresh();
        assert!(matches!(r1, Region::Fresh(0)));

        let r2 = counter.fresh();
        assert!(matches!(r2, Region::Fresh(1)));

        assert_eq!(counter.current(), 2);
    }

    // -------------------------------------------------------------------------
    // Merge tests (control flow merging)
    // -------------------------------------------------------------------------

    #[test]
    fn test_merge_var_state_owned_owned() {
        // Both owned: stay owned
        let s1 = VarState::Owned;
        let s2 = VarState::Owned;
        assert_eq!(merge_var_state(&s1, &s2), VarState::Owned);
    }

    #[test]
    fn test_merge_var_state_moved_is_most_restrictive() {
        // Moved absorbs all other states
        let moved = VarState::Moved;
        let owned = VarState::Owned;
        let borrowed = VarState::Borrowed(vec![make_loan_id(1)]);
        let shared = VarState::Shared { ref_count: 1 };
        let dropped = VarState::Dropped;

        assert_eq!(merge_var_state(&moved, &owned), VarState::Moved);
        assert_eq!(merge_var_state(&owned, &moved), VarState::Moved);
        assert_eq!(merge_var_state(&moved, &borrowed), VarState::Moved);
        assert_eq!(merge_var_state(&moved, &shared), VarState::Moved);
        assert_eq!(merge_var_state(&moved, &dropped), VarState::Moved);
    }

    #[test]
    fn test_merge_var_state_dropped() {
        // Dropped is second most restrictive (after moved)
        let dropped = VarState::Dropped;
        let owned = VarState::Owned;
        let borrowed = VarState::Borrowed(vec![make_loan_id(1)]);

        assert_eq!(merge_var_state(&dropped, &owned), VarState::Dropped);
        assert_eq!(merge_var_state(&owned, &dropped), VarState::Dropped);
        assert_eq!(merge_var_state(&dropped, &borrowed), VarState::Dropped);
    }

    #[test]
    fn test_merge_var_state_borrowed_mut() {
        // BorrowedMut takes the loan from whichever branch has it
        let borrowed_mut = VarState::BorrowedMut(make_loan_id(42));
        let owned = VarState::Owned;
        let borrowed = VarState::Borrowed(vec![make_loan_id(1)]);

        assert_eq!(
            merge_var_state(&borrowed_mut, &owned),
            VarState::BorrowedMut(make_loan_id(42))
        );
        assert_eq!(
            merge_var_state(&owned, &borrowed_mut),
            VarState::BorrowedMut(make_loan_id(42))
        );
        assert_eq!(
            merge_var_state(&borrowed_mut, &borrowed),
            VarState::BorrowedMut(make_loan_id(42))
        );
    }

    #[test]
    fn test_merge_var_state_borrowed_combines_loans() {
        // Borrowed + Borrowed: combine loan lists
        let b1 = VarState::Borrowed(vec![make_loan_id(1), make_loan_id(2)]);
        let b2 = VarState::Borrowed(vec![make_loan_id(2), make_loan_id(3)]);

        match merge_var_state(&b1, &b2) {
            VarState::Borrowed(loans) => {
                assert_eq!(loans.len(), 3); // 1, 2, 3 (deduped)
                assert!(loans.contains(&make_loan_id(1)));
                assert!(loans.contains(&make_loan_id(2)));
                assert!(loans.contains(&make_loan_id(3)));
            }
            _ => panic!("Expected Borrowed state"),
        }
    }

    #[test]
    fn test_merge_var_state_owned_borrowed() {
        // Owned + Borrowed: take Borrowed (more restrictive)
        let owned = VarState::Owned;
        let borrowed = VarState::Borrowed(vec![make_loan_id(1)]);

        assert_eq!(
            merge_var_state(&owned, &borrowed),
            VarState::Borrowed(vec![make_loan_id(1)])
        );
        assert_eq!(
            merge_var_state(&borrowed, &owned),
            VarState::Borrowed(vec![make_loan_id(1)])
        );
    }

    #[test]
    fn test_merge_var_state_shared() {
        // Shared + Shared: take max ref_count
        let s1 = VarState::Shared { ref_count: 3 };
        let s2 = VarState::Shared { ref_count: 5 };

        assert_eq!(
            merge_var_state(&s1, &s2),
            VarState::Shared { ref_count: 5 }
        );
        assert_eq!(
            merge_var_state(&s2, &s1),
            VarState::Shared { ref_count: 5 }
        );
    }

    #[test]
    fn test_merge_var_state_owned_shared() {
        // Owned + Shared: take Shared
        let owned = VarState::Owned;
        let shared = VarState::Shared { ref_count: 2 };

        assert_eq!(
            merge_var_state(&owned, &shared),
            VarState::Shared { ref_count: 2 }
        );
        assert_eq!(
            merge_var_state(&shared, &owned),
            VarState::Shared { ref_count: 2 }
        );
    }

    #[test]
    fn test_merge_var_state_borrowed_shared() {
        // Borrowed + Shared: Borrowed is more restrictive
        let borrowed = VarState::Borrowed(vec![make_loan_id(1)]);
        let shared = VarState::Shared { ref_count: 2 };

        assert_eq!(
            merge_var_state(&borrowed, &shared),
            VarState::Borrowed(vec![make_loan_id(1)])
        );
        assert_eq!(
            merge_var_state(&shared, &borrowed),
            VarState::Borrowed(vec![make_loan_id(1)])
        );
    }

    #[test]
    fn test_merge_var_entry() {
        let var = make_var(1);
        let e1 = VarEntry {
            var,
            ty: BrrrType::BOOL,
            mode: Mode::One,
            state: VarState::Owned,
        };
        let e2 = VarEntry {
            var,
            ty: BrrrType::BOOL,
            mode: Mode::Omega,
            state: VarState::Moved,
        };

        let merged = merge_var_entry(&e1, &e2);

        assert_eq!(merged.var, var);
        assert_eq!(merged.ty, BrrrType::BOOL);
        // Mode::One.meet(Mode::Omega) = Mode::One (greatest lower bound)
        assert_eq!(merged.mode, Mode::One);
        // Moved is more restrictive than Owned
        assert_eq!(merged.state, VarState::Moved);
    }

    #[test]
    fn test_merge_var_lists() {
        let var1 = make_var(1);
        let var2 = make_var(2);

        let l1 = vec![
            VarEntry::new(var1, BrrrType::BOOL, Mode::One),
            VarEntry::new(var2, BrrrType::STRING, Mode::Omega),
        ];

        let mut l2 = vec![
            VarEntry::new(var1, BrrrType::BOOL, Mode::One),
            VarEntry::new(var2, BrrrType::STRING, Mode::Omega),
        ];
        // Modify var1 in l2 to be moved
        l2[0].state = VarState::Moved;

        let merged = merge_var_lists(&l1, &l2);

        assert_eq!(merged.len(), 2);
        // var1 was Owned in l1, Moved in l2 -> Moved
        assert_eq!(merged[0].state, VarState::Moved);
        // var2 was Owned in both -> Owned
        assert_eq!(merged[1].state, VarState::Owned);
    }

    #[test]
    fn test_merge_loans_deduplicates() {
        let var = make_var(1);
        let loan1 = Loan::top_level(make_loan_id(1), var, BorrowKind::Shared);
        let loan2 = Loan::top_level(make_loan_id(2), var, BorrowKind::Shared);
        let loan3 = Loan::top_level(make_loan_id(3), var, BorrowKind::Shared);

        let l1 = vec![loan1.clone(), loan2.clone()];
        let l2 = vec![loan2.clone(), loan3.clone()];

        let merged = merge_loans(&l1, &l2);

        // Should have 3 unique loans (deduped by ID)
        assert_eq!(merged.len(), 3);
        assert!(merged.iter().any(|l| l.id == make_loan_id(1)));
        assert!(merged.iter().any(|l| l.id == make_loan_id(2)));
        assert!(merged.iter().any(|l| l.id == make_loan_id(3)));
    }

    #[test]
    fn test_merge_loans_empty() {
        let l1: Vec<Loan> = vec![];
        let l2: Vec<Loan> = vec![];

        let merged = merge_loans(&l1, &l2);
        assert!(merged.is_empty());
    }

    #[test]
    fn test_merge_borrow_states() {
        let var1 = make_var(1);
        let var2 = make_var(2);

        let mut s1 = BorrowState::with_depth(1);
        s1.add_var(var1, BrrrType::BOOL, Mode::One);
        s1.add_var(var2, BrrrType::STRING, Mode::Omega);
        // Use explicit loan IDs to avoid counter overlap
        let loan1_id = make_loan_id(10);
        let loan1 = Loan::new(loan1_id, var1, BorrowKind::Shared, 1);
        s1.add_loan_mut(loan1);

        let mut s2 = BorrowState::with_depth(1);
        s2.add_var(var1, BrrrType::BOOL, Mode::One);
        s2.add_var(var2, BrrrType::STRING, Mode::Omega);
        // Move var1 in s2
        s2.update_var_state_mut(var1, VarState::Moved);
        let loan2_id = make_loan_id(20);
        let loan2 = Loan::new(loan2_id, var2, BorrowKind::Exclusive, 1);
        s2.add_loan_mut(loan2);

        let merged = merge_borrow_states(&s1, &s2);

        // Depth should be same
        assert_eq!(merged.depth, 1);

        // var1: Owned in s1, Moved in s2 -> Moved
        let var1_entry = merged.lookup_var(var1).unwrap();
        assert_eq!(var1_entry.state, VarState::Moved);

        // var2: Owned in both -> Owned
        let var2_entry = merged.lookup_var(var2).unwrap();
        assert_eq!(var2_entry.state, VarState::Owned);

        // Loans: union of both (loan1 from s1, loan2 from s2)
        assert_eq!(merged.loans.len(), 2);
        assert!(merged.find_loan(loan1_id).is_some());
        assert!(merged.find_loan(loan2_id).is_some());

        // Counter: max of both
        assert!(merged.counter.current() >= s1.counter.current());
        assert!(merged.counter.current() >= s2.counter.current());
    }

    #[test]
    fn test_borrow_state_merge_method() {
        let var = make_var(1);

        let mut s1 = BorrowState::new();
        s1.add_var(var, BrrrType::BOOL, Mode::One);

        let mut s2 = s1.clone();
        s2.update_var_state_mut(var, VarState::Dropped);

        let merged = s1.merge(&s2);

        // Dropped is more restrictive than Owned
        assert_eq!(merged.lookup_var(var).unwrap().state, VarState::Dropped);
    }

    #[test]
    fn test_merge_if_else_scenario() {
        // Simulate: if cond { move x } else { /* keep x */ }
        let x = make_var(1);

        let mut before = BorrowState::new();
        before.add_var(x, BrrrType::BOOL, Mode::One);

        // Then branch: move x
        let mut then_branch = before.clone();
        then_branch.update_var_state_mut(x, VarState::Moved);

        // Else branch: keep x
        let else_branch = before.clone();

        // After merge: x is moved (most restrictive)
        let after = merge_borrow_states(&then_branch, &else_branch);
        assert_eq!(after.lookup_var(x).unwrap().state, VarState::Moved);
    }

    #[test]
    fn test_merge_both_branches_borrow() {
        // Simulate: if cond { &x } else { &x }
        let x = make_var(1);

        let mut before = BorrowState::new();
        before.add_var(x, BrrrType::BOOL, Mode::One);

        // Then branch: borrow x (loan 1)
        let mut then_branch = before.clone();
        let loan1 = make_loan_id(1);
        then_branch.update_var_state_mut(x, VarState::Borrowed(vec![loan1]));
        then_branch.add_loan_mut(Loan::top_level(loan1, x, BorrowKind::Shared));

        // Else branch: borrow x (loan 2)
        let mut else_branch = before.clone();
        let loan2 = make_loan_id(2);
        else_branch.update_var_state_mut(x, VarState::Borrowed(vec![loan2]));
        else_branch.add_loan_mut(Loan::top_level(loan2, x, BorrowKind::Shared));

        // After merge: x has both loans
        let after = merge_borrow_states(&then_branch, &else_branch);
        match &after.lookup_var(x).unwrap().state {
            VarState::Borrowed(loans) => {
                assert_eq!(loans.len(), 2);
                assert!(loans.contains(&loan1));
                assert!(loans.contains(&loan2));
            }
            _ => panic!("Expected Borrowed state"),
        }

        // Both loans should be in the merged loan list
        assert!(after.find_loan(loan1).is_some());
        assert!(after.find_loan(loan2).is_some());
    }
}
