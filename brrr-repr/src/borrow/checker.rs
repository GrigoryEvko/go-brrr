//! Expression-level borrow checking
//!
//! Mirrors F* BorrowChecker.fst lines 837-1214:
//! ```fstar
//! let rec borrow_check_expr (fuel: nat) (state: borrow_state) (e: expr)
//!     : Tot (borrow_result borrow_state) (decreases fuel) = ...
//! ```
//!
//! # Overview
//!
//! This module provides the core borrow checking algorithm for expressions.
//! It tracks ownership state transitions as expressions are evaluated:
//!
//! - Variable use: checks the variable is not moved/dropped
//! - Move: transfers ownership, marks variable as moved
//! - Borrow: creates a loan, checks no conflicting borrows exist
//! - Drop: ends ownership, checks no active borrows
//!
//! # Fuel-Based Recursion
//!
//! The checker uses explicit fuel to ensure termination (matching F* spec).
//! Fuel decreases with each recursive call; exhaustion returns an error.
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::borrow::{BorrowState, borrow_check_expr};
//! use brrr_repr::expr::Expr;
//!
//! let mut state = BorrowState::new();
//! state.add_var(x, BrrrType::BOOL, Mode::One);
//!
//! let result = borrow_check_expr(&state, &expr, 1000);
//! match result {
//!     Ok(new_state) => { /* expression valid */ }
//!     Err(e) => { /* borrow error: e */ }
//! }
//! ```

use super::error::{BorrowResult, OwnershipError};
use super::state::{
    merge_borrow_states as state_merge_borrow_states, BorrowKind, BorrowState, Loan,
};
use super::types::{
    add_shared_borrow, can_borrow_mut, can_borrow_shared, can_move, end_mut_borrow,
    end_shared_borrow, is_available, LoanId, VarState,
};
use crate::expr::{Expr, Expr_};
use crate::modes::Mode;
use crate::types::BrrrType;

/// Default fuel for borrow checking
///
/// This should be sufficient for most reasonable expression depths.
/// Extremely deep or recursive structures may need more.
pub const DEFAULT_FUEL: usize = 10_000;

// ============================================================================
// Core Check Functions
// ============================================================================

/// Check if a variable can be used (read)
///
/// Maps to F* BorrowChecker.fst `check_var_use`:
/// ```fstar
/// let check_var_use (state: borrow_state) (x: var_id)
///     : borrow_result borrow_state = ...
/// ```
///
/// A variable can be used if:
/// - It exists in the state
/// - It is not moved or dropped
///
/// Note: Reading does NOT consume the variable (unlike move).
///
/// # Errors
/// - `VariableNotFound` if variable is not in state
/// - `UseAfterMove` if variable was moved
pub fn check_var_use(state: &BorrowState, var: lasso::Spur) -> BorrowResult<BorrowState> {
    let entry = state
        .lookup_var(var)
        .ok_or(OwnershipError::VariableNotFound { var })?;

    if !is_available(&entry.state) {
        return Err(OwnershipError::UseAfterMove { var });
    }

    // Variable use does not modify state for owned/borrowed variables
    // (only unrestricted/Copy types can be freely used)
    Ok(state.clone())
}

/// Check if a variable can be moved (ownership transfer)
///
/// Maps to F* BorrowChecker.fst `check_move`:
/// ```fstar
/// let check_move (state: borrow_state) (x: var_id)
///     : borrow_result borrow_state = ...
/// ```
///
/// A variable can be moved if:
/// - It exists and is in `Owned` state
/// - It has no active borrows
///
/// After move, the variable transitions to `Moved` state.
///
/// # Errors
/// - `VariableNotFound` if variable is not in state
/// - `UseAfterMove` if already moved
/// - `DoubleMove` if already moved
/// - `MoveWhileBorrowed` if variable has active borrows
pub fn check_move(state: &BorrowState, var: lasso::Spur) -> BorrowResult<BorrowState> {
    let entry = state
        .lookup_var(var)
        .ok_or(OwnershipError::VariableNotFound { var })?;

    // Check for use-after-move
    if matches!(entry.state, VarState::Moved) {
        return Err(OwnershipError::DoubleMove { var });
    }

    if matches!(entry.state, VarState::Dropped) {
        return Err(OwnershipError::UseAfterMove { var });
    }

    // Check for move while borrowed
    if let VarState::Borrowed(ref loans) = entry.state {
        if let Some(&loan) = loans.first() {
            return Err(OwnershipError::MoveWhileBorrowed { var, loan });
        }
    }

    if let VarState::BorrowedMut(loan) = entry.state {
        return Err(OwnershipError::MoveWhileBorrowed { var, loan });
    }

    // Check can_move (must be Owned)
    if !can_move(&entry.state) {
        return Err(OwnershipError::UseAfterMove { var });
    }

    // Transition to Moved state
    Ok(state.clone().update_var_state(var, VarState::Moved))
}

/// Check if a variable can be borrowed as shared (immutable)
///
/// Maps to F* BorrowChecker.fst `check_borrow_shared`:
/// ```fstar
/// let check_borrow_shared (state: borrow_state) (x: var_id)
///     : borrow_result borrow_state = ...
/// ```
///
/// A variable can be borrowed shared if:
/// - It exists and is available (not moved/dropped)
/// - It is in `Owned` or `Borrowed` state (not `BorrowedMut`)
///
/// After borrow, creates a new shared loan.
///
/// # Errors
/// - `VariableNotFound` if variable is not in state
/// - `BorrowWhileMoved` if variable was moved
/// - `BorrowWhileMutBorrowed` if variable has exclusive borrow
pub fn check_borrow_shared(state: &BorrowState, var: lasso::Spur) -> BorrowResult<BorrowState> {
    let entry = state
        .lookup_var(var)
        .ok_or(OwnershipError::VariableNotFound { var })?;

    // Check for borrow of moved/dropped variable
    if matches!(entry.state, VarState::Moved | VarState::Dropped) {
        return Err(OwnershipError::BorrowWhileMoved { var });
    }

    // Check for shared borrow while mutably borrowed
    if let VarState::BorrowedMut(loan) = entry.state {
        return Err(OwnershipError::BorrowWhileMutBorrowed { var, loan });
    }

    // Check can_borrow_shared
    if !can_borrow_shared(&entry.state) {
        return Err(OwnershipError::BorrowWhileMoved { var });
    }

    // Create new loan and update state
    let mut new_state = state.clone();
    let loan_id = new_state.fresh_loan_id();
    let loan = Loan::new(loan_id, var, BorrowKind::Shared, new_state.depth);
    new_state.add_loan_mut(loan);

    // Update variable state to include the new borrow
    let new_var_state = add_shared_borrow(&entry.state, loan_id)
        .ok_or(OwnershipError::BorrowWhileMoved { var })?;
    new_state.update_var_state_mut(var, new_var_state);

    Ok(new_state)
}

/// Check if a variable can be borrowed as exclusive (mutable)
///
/// Maps to F* BorrowChecker.fst `check_borrow_exclusive`:
/// ```fstar
/// let check_borrow_exclusive (state: borrow_state) (x: var_id)
///     : borrow_result borrow_state = ...
/// ```
///
/// A variable can be borrowed exclusively if:
/// - It exists and is in `Owned` state
/// - It has no active borrows (shared or exclusive)
///
/// After borrow, creates a new exclusive loan.
///
/// # Errors
/// - `VariableNotFound` if variable is not in state
/// - `BorrowWhileMoved` if variable was moved
/// - `MutBorrowWhileBorrowed` if variable has shared borrows
/// - `MultipleMutBorrows` if variable already has exclusive borrow
pub fn check_borrow_exclusive(state: &BorrowState, var: lasso::Spur) -> BorrowResult<BorrowState> {
    let entry = state
        .lookup_var(var)
        .ok_or(OwnershipError::VariableNotFound { var })?;

    // Check for borrow of moved/dropped variable
    if matches!(entry.state, VarState::Moved | VarState::Dropped) {
        return Err(OwnershipError::BorrowWhileMoved { var });
    }

    // Check for mut borrow while already borrowed
    if let VarState::Borrowed(ref loans) = entry.state {
        return Err(OwnershipError::MutBorrowWhileBorrowed {
            var,
            loans: loans.clone(),
        });
    }

    // Check for multiple mut borrows
    if let VarState::BorrowedMut(existing) = entry.state {
        return Err(OwnershipError::MultipleMutBorrows {
            var,
            loans: vec![existing],
        });
    }

    // Check can_borrow_mut (must be Owned)
    if !can_borrow_mut(&entry.state) {
        return Err(OwnershipError::BorrowWhileMoved { var });
    }

    // Create new loan and update state
    let mut new_state = state.clone();
    let loan_id = new_state.fresh_loan_id();
    let loan = Loan::new(loan_id, var, BorrowKind::Exclusive, new_state.depth);
    new_state.add_loan_mut(loan);

    // Update variable state to BorrowedMut
    new_state.update_var_state_mut(var, VarState::BorrowedMut(loan_id));

    Ok(new_state)
}

/// Check if a variable can be dropped
///
/// Maps to F* BorrowChecker.fst `check_drop`:
/// ```fstar
/// let check_drop (state: borrow_state) (x: var_id)
///     : borrow_result borrow_state = ...
/// ```
///
/// A variable can be dropped if:
/// - It exists and is available
/// - It has no active borrows
///
/// After drop, the variable transitions to `Dropped` state.
///
/// # Errors
/// - `VariableNotFound` if variable is not in state
/// - `DoubleFree` if already dropped
/// - `DropWhileBorrowed` if variable has active borrows
pub fn check_drop(state: &BorrowState, var: lasso::Spur) -> BorrowResult<BorrowState> {
    let entry = state
        .lookup_var(var)
        .ok_or(OwnershipError::VariableNotFound { var })?;

    // Check for double-free
    if matches!(entry.state, VarState::Dropped) {
        return Err(OwnershipError::DoubleFree { var });
    }

    // Check for drop while borrowed
    if let VarState::Borrowed(ref loans) = entry.state {
        return Err(OwnershipError::DropWhileBorrowed {
            var,
            loans: loans.clone(),
        });
    }

    if let VarState::BorrowedMut(loan) = entry.state {
        return Err(OwnershipError::DropWhileBorrowed {
            var,
            loans: vec![loan],
        });
    }

    // Transition to Dropped state
    Ok(state.clone().update_var_state(var, VarState::Dropped))
}

// ============================================================================
// State Management Helpers
// ============================================================================

/// Extend state with a new variable
///
/// Maps to F* BorrowChecker.fst `extend_var`:
/// ```fstar
/// let extend_var (state: borrow_state) (x: var_id) (ty: brrr_type) (mode: mode)
///     : borrow_state = ...
/// ```
///
/// Adds a new variable in `Owned` state.
pub fn extend_var(
    state: &BorrowState,
    var: lasso::Spur,
    ty: BrrrType,
    mode: Mode,
) -> BorrowState {
    let mut new_state = state.clone();
    new_state.add_var(var, ty, mode);
    new_state
}

/// Extend state with variables bound by a pattern
///
/// Adds all variables bound in the pattern to the state.
fn extend_pattern_vars(
    state: &BorrowState,
    pattern: &crate::expr::Pattern,
    ty: &BrrrType,
    mode: Mode,
) -> BorrowState {
    let bound_vars = pattern.value.bound_vars();
    let mut new_state = state.clone();
    for var in bound_vars {
        // In a real implementation, we would compute the type for each binding
        // For now, use the overall type (simplification)
        new_state.add_var(var, ty.clone(), mode);
    }
    new_state
}

/// Merge borrow states after conditional branches
///
/// Maps to F* BorrowChecker.fst `merge_borrow_states`:
/// ```fstar
/// let merge_borrow_states (s1: borrow_state) (s2: borrow_state)
///     : borrow_result borrow_state = ...
/// ```
///
/// Takes the most conservative (restrictive) view:
/// - Variable is moved if moved in EITHER branch
/// - Variable is dropped if dropped in EITHER branch
/// - Borrows are unioned (all loans from both branches)
///
/// This is sound because:
/// - If moved in one branch, it might be moved at runtime
/// - If dropped in one branch, it might be dropped at runtime
///
/// This is a thin wrapper around `super::state::merge_borrow_states` that
/// returns a `BorrowResult` for consistency with other checker functions.
pub fn merge_borrow_states(left: BorrowState, right: BorrowState) -> BorrowResult<BorrowState> {
    Ok(state_merge_borrow_states(&left, &right))
}

/// End a borrow and update state
///
/// Called when a reference goes out of scope.
pub fn end_borrow_in_state(state: &BorrowState, loan_id: LoanId) -> BorrowResult<BorrowState> {
    let mut new_state = state.clone();

    // Find the loan to get the variable
    let loan = state
        .find_loan(loan_id)
        .ok_or(OwnershipError::LoanNotFound { loan: loan_id })?;

    let var = loan.var;
    let is_exclusive = loan.kind.is_exclusive();

    // Remove the loan
    new_state.remove_loan_mut(loan_id);

    // Update variable state
    if let Some(entry) = new_state.lookup_var(var) {
        let new_var_state = if is_exclusive {
            end_mut_borrow(&entry.state, loan_id).unwrap_or(entry.state.clone())
        } else {
            end_shared_borrow(&entry.state, loan_id).unwrap_or(entry.state.clone())
        };
        new_state.update_var_state_mut(var, new_var_state);
    }

    Ok(new_state)
}

// ============================================================================
// Expression Borrow Checking
// ============================================================================

/// Extract variable ID from a simple expression
///
/// For expressions like `Move(Var(x))`, `Borrow(Var(x))`, etc.,
/// extracts the underlying variable ID.
///
/// Returns `None` for complex expressions (field access, indexing, etc.)
fn extract_var_id(expr: &Expr) -> Option<lasso::Spur> {
    match &expr.value {
        Expr_::Var(var) => Some(*var),
        _ => None,
    }
}

/// Main expression borrow checker
///
/// Maps to F* BorrowChecker.fst lines 837-1214:
/// ```fstar
/// let rec borrow_check_expr (fuel: nat) (state: borrow_state) (e: expr)
///     : Tot (borrow_result borrow_state) (decreases fuel) = ...
/// ```
///
/// Recursively checks an expression, threading borrow state through.
/// Uses explicit fuel for termination (matching F* spec).
///
/// # Arguments
/// * `state` - Current borrow state
/// * `expr` - Expression to check
/// * `fuel` - Recursion fuel (decreases each call)
///
/// # Returns
/// Updated borrow state after expression, or ownership error.
///
/// # Errors
/// - `InternalError` if fuel exhausted
/// - Various ownership errors based on expression semantics
pub fn borrow_check_expr(
    state: &BorrowState,
    expr: &Expr,
    fuel: usize,
) -> BorrowResult<BorrowState> {
    if fuel == 0 {
        return Err(OwnershipError::InternalError {
            msg: "fuel exhausted in borrow_check_expr".to_string(),
        });
    }

    match &expr.value {
        // === Literals and Variables ===
        Expr_::Lit(_) => {
            // Literals don't affect borrow state
            Ok(state.clone())
        }

        Expr_::Var(var) => {
            // Variable use: check it's available
            check_var_use(state, *var)
        }

        Expr_::Global(_) => {
            // Global references don't affect local borrow state
            Ok(state.clone())
        }

        // === Memory Operations ===
        Expr_::Move(inner) => {
            // First check the inner expression
            let state1 = borrow_check_expr(state, inner, fuel - 1)?;

            // Then check the move operation
            if let Some(var) = extract_var_id(inner) {
                check_move(&state1, var)
            } else {
                // Complex expression move - for now, just pass through
                // A full implementation would track moved places
                Ok(state1)
            }
        }

        Expr_::Borrow(inner) => {
            // First check the inner expression
            let state1 = borrow_check_expr(state, inner, fuel - 1)?;

            // Then check the borrow operation
            if let Some(var) = extract_var_id(inner) {
                check_borrow_shared(&state1, var)
            } else {
                // Complex expression borrow - for now, just pass through
                Ok(state1)
            }
        }

        Expr_::BorrowMut(inner) => {
            // First check the inner expression
            let state1 = borrow_check_expr(state, inner, fuel - 1)?;

            // Then check the exclusive borrow operation
            if let Some(var) = extract_var_id(inner) {
                check_borrow_exclusive(&state1, var)
            } else {
                // Complex expression borrow - for now, just pass through
                Ok(state1)
            }
        }

        Expr_::Drop(inner) => {
            // First check the inner expression
            let state1 = borrow_check_expr(state, inner, fuel - 1)?;

            // Then check the drop operation
            if let Some(var) = extract_var_id(inner) {
                check_drop(&state1, var)
            } else {
                // Complex expression drop - for now, just pass through
                Ok(state1)
            }
        }

        Expr_::Deref(inner) => {
            // Dereference: check the reference expression
            borrow_check_expr(state, inner, fuel - 1)
        }

        Expr_::Box(inner) => {
            // Box allocation: check the inner expression
            borrow_check_expr(state, inner, fuel - 1)
        }

        // === Bindings ===
        Expr_::Let { pattern, ty, init, body } => {
            // Check the initializer expression
            let state1 = borrow_check_expr(state, init, fuel - 1)?;

            // Extend state with bound variables
            let ty = ty.clone().unwrap_or(BrrrType::UNIT);
            let state2 = extend_pattern_vars(&state1, pattern, &ty, Mode::One);

            // Check the body with extended state
            borrow_check_expr(&state2, body, fuel - 1)
        }

        Expr_::LetMut { var, ty, init, body } => {
            // Check the initializer expression
            let state1 = borrow_check_expr(state, init, fuel - 1)?;

            // Extend state with the mutable variable
            let ty = ty.clone().unwrap_or(BrrrType::UNIT);
            let state2 = extend_var(&state1, *var, ty, Mode::One);

            // Check the body with extended state
            borrow_check_expr(&state2, body, fuel - 1)
        }

        // === Control Flow ===
        Expr_::If(cond, then_branch, else_branch) => {
            // Check condition
            let state1 = borrow_check_expr(state, cond, fuel - 1)?;

            // Check both branches
            let state_then = borrow_check_expr(&state1, then_branch, fuel - 1)?;
            let state_else = borrow_check_expr(&state1, else_branch, fuel - 1)?;

            // Merge states (conservative)
            merge_borrow_states(state_then, state_else)
        }

        Expr_::Match(scrutinee, arms) => {
            // Check the scrutinee
            let state1 = borrow_check_expr(state, scrutinee, fuel - 1)?;

            if arms.is_empty() {
                return Ok(state1);
            }

            // Check each arm and merge states
            let mut merged_state: Option<BorrowState> = None;

            for arm in arms {
                // Check guard if present
                let state_with_guard = if let Some(ref guard) = arm.guard {
                    borrow_check_expr(&state1, guard, fuel - 1)?
                } else {
                    state1.clone()
                };

                // Extend with pattern bindings
                // For now, use UNIT type - real impl would infer from scrutinee
                let state_extended =
                    extend_pattern_vars(&state_with_guard, &arm.pattern, &BrrrType::UNIT, Mode::One);

                // Check the arm body
                let arm_state = borrow_check_expr(&state_extended, &arm.body, fuel - 1)?;

                // Merge with previous arms
                merged_state = Some(match merged_state {
                    None => arm_state,
                    Some(prev) => merge_borrow_states(prev, arm_state)?,
                });
            }

            Ok(merged_state.unwrap_or(state1))
        }

        // === Blocks and Sequences ===
        Expr_::Block(exprs) => {
            // Check expressions in sequence, threading state
            let mut current_state = state.clone();

            // Enter new scope
            current_state.enter_scope_mut();

            for e in exprs {
                current_state = borrow_check_expr(&current_state, e, fuel - 1)?;
            }

            // Exit scope (ends loans at this depth)
            current_state.exit_scope_mut();

            Ok(current_state)
        }

        Expr_::Seq(first, second) => {
            // Check first, then second
            let state1 = borrow_check_expr(state, first, fuel - 1)?;
            borrow_check_expr(&state1, second, fuel - 1)
        }

        // === Operations ===
        Expr_::Unary(_, operand) => {
            borrow_check_expr(state, operand, fuel - 1)
        }

        Expr_::Binary(_, left, right) => {
            // Check left, then right
            let state1 = borrow_check_expr(state, left, fuel - 1)?;
            borrow_check_expr(&state1, right, fuel - 1)
        }

        Expr_::Call(func, args) => {
            // Check function expression
            let mut current = borrow_check_expr(state, func, fuel - 1)?;

            // Check each argument
            for arg in args {
                current = borrow_check_expr(&current, arg, fuel - 1)?;
            }

            Ok(current)
        }

        Expr_::MethodCall(receiver, _, args) => {
            // Check receiver
            let mut current = borrow_check_expr(state, receiver, fuel - 1)?;

            // Check each argument
            for arg in args {
                current = borrow_check_expr(&current, arg, fuel - 1)?;
            }

            Ok(current)
        }

        // === Data Construction ===
        Expr_::Tuple(elems) => {
            let mut current = state.clone();
            for elem in elems {
                current = borrow_check_expr(&current, elem, fuel - 1)?;
            }
            Ok(current)
        }

        Expr_::Array(elems) => {
            let mut current = state.clone();
            for elem in elems {
                current = borrow_check_expr(&current, elem, fuel - 1)?;
            }
            Ok(current)
        }

        Expr_::Struct { fields, .. } => {
            let mut current = state.clone();
            for (_, field_expr) in fields {
                current = borrow_check_expr(&current, field_expr, fuel - 1)?;
            }
            Ok(current)
        }

        Expr_::Variant { fields, .. } => {
            let mut current = state.clone();
            for field_expr in fields {
                current = borrow_check_expr(&current, field_expr, fuel - 1)?;
            }
            Ok(current)
        }

        // === Data Access ===
        Expr_::Field(base, _) => {
            borrow_check_expr(state, base, fuel - 1)
        }

        Expr_::Index(base, index) => {
            let state1 = borrow_check_expr(state, base, fuel - 1)?;
            borrow_check_expr(&state1, index, fuel - 1)
        }

        Expr_::TupleProj(base, _) => {
            borrow_check_expr(state, base, fuel - 1)
        }

        // === Assignment ===
        Expr_::Assign(lhs, rhs) => {
            // Check RHS first
            let state1 = borrow_check_expr(state, rhs, fuel - 1)?;
            // Check LHS (place expression)
            borrow_check_expr(&state1, lhs, fuel - 1)
        }

        // === Loops ===
        Expr_::Loop { body, .. } => {
            // For loops, we check the body once
            // A more sophisticated analysis would iterate to fixpoint
            borrow_check_expr(state, body, fuel - 1)
        }

        Expr_::While { cond, body, .. } => {
            let state1 = borrow_check_expr(state, cond, fuel - 1)?;
            borrow_check_expr(&state1, body, fuel - 1)
        }

        Expr_::For { iter, body, var, .. } => {
            let state1 = borrow_check_expr(state, iter, fuel - 1)?;
            // Extend with loop variable
            let state2 = extend_var(&state1, *var, BrrrType::UNIT, Mode::One);
            borrow_check_expr(&state2, body, fuel - 1)
        }

        // === Control Flow (jumps) ===
        Expr_::Break { value, .. } => {
            if let Some(v) = value {
                borrow_check_expr(state, v, fuel - 1)
            } else {
                Ok(state.clone())
            }
        }

        Expr_::Continue { .. } => {
            Ok(state.clone())
        }

        Expr_::Return(value) => {
            if let Some(v) = value {
                borrow_check_expr(state, v, fuel - 1)
            } else {
                Ok(state.clone())
            }
        }

        // === Functions ===
        Expr_::Lambda { params, body } => {
            // Add lambda parameters to state
            let mut inner_state = state.clone();
            for (var, ty) in params {
                inner_state.add_var(*var, ty.clone(), Mode::One);
            }
            borrow_check_expr(&inner_state, body, fuel - 1)
        }

        Expr_::Closure { params, captures, body } => {
            // Check captures are available
            for capture in captures {
                check_var_use(state, *capture)?;
            }

            // Add parameters to state
            let mut inner_state = state.clone();
            for (var, ty) in params {
                inner_state.add_var(*var, ty.clone(), Mode::One);
            }
            borrow_check_expr(&inner_state, body, fuel - 1)
        }

        // === Async/Effects ===
        Expr_::Async(inner) | Expr_::Await(inner) | Expr_::Yield(inner) | Expr_::Spawn(inner) => {
            borrow_check_expr(state, inner, fuel - 1)
        }

        Expr_::Handle(body, _handler) => {
            borrow_check_expr(state, body, fuel - 1)
        }

        Expr_::Perform(_, args) => {
            let mut current = state.clone();
            for arg in args {
                current = borrow_check_expr(&current, arg, fuel - 1)?;
            }
            Ok(current)
        }

        Expr_::Resume { value, .. } => {
            borrow_check_expr(state, value, fuel - 1)
        }

        // === Delimited Continuations ===
        Expr_::Reset { body, .. } => {
            borrow_check_expr(state, body, fuel - 1)
        }

        Expr_::Shift { body, var, .. } => {
            let inner_state = extend_var(state, *var, BrrrType::UNIT, Mode::One);
            borrow_check_expr(&inner_state, body, fuel - 1)
        }

        // === Exceptions ===
        Expr_::Throw(inner) => {
            borrow_check_expr(state, inner, fuel - 1)
        }

        Expr_::Try { body, catches, finally } => {
            let state1 = borrow_check_expr(state, body, fuel - 1)?;

            let mut merged = state1.clone();
            for catch in catches {
                let catch_state = extend_pattern_vars(&state1, &catch.pattern, &catch.exception_type, Mode::One);
                let catch_result = borrow_check_expr(&catch_state, &catch.body, fuel - 1)?;
                merged = merge_borrow_states(merged, catch_result)?;
            }

            if let Some(finally_block) = finally {
                merged = borrow_check_expr(&merged, finally_block, fuel - 1)?;
            }

            Ok(merged)
        }

        // === Type Operations ===
        Expr_::As(inner, _) | Expr_::Is(inner, _) => {
            borrow_check_expr(state, inner, fuel - 1)
        }

        Expr_::Sizeof(_) | Expr_::Alignof(_) => {
            Ok(state.clone())
        }

        // === Special ===
        Expr_::Unsafe(inner) => {
            borrow_check_expr(state, inner, fuel - 1)
        }

        Expr_::Hole | Expr_::Error(_) => {
            Ok(state.clone())
        }

        // === Gradual Typing ===
        Expr_::GradualCast { expr, .. } => {
            // Check the inner expression
            borrow_check_expr(state, expr, fuel - 1)
        }

        // === Control Flow Labels ===
        Expr_::Goto { .. } => {
            // Goto is a jump - doesn't affect borrow state directly
            Ok(state.clone())
        }
        Expr_::Labeled { body, .. } => {
            // Labeled wraps body expression
            borrow_check_expr(state, body, fuel - 1)
        }
    }
}

/// Convenience wrapper with default fuel
pub fn check_expr(state: &BorrowState, expr: &Expr) -> BorrowResult<BorrowState> {
    borrow_check_expr(state, expr, DEFAULT_FUEL)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::WithLoc;
    use crate::expr::Literal;
    use lasso::{Key, Spur};

    fn make_var(n: usize) -> Spur {
        Spur::try_from_usize(n).unwrap()
    }

    fn var_expr(var: Spur) -> Expr {
        WithLoc::synthetic(Expr_::Var(var))
    }

    fn lit_expr(lit: Literal) -> Expr {
        WithLoc::synthetic(Expr_::Lit(lit))
    }

    fn move_expr(inner: Expr) -> Expr {
        WithLoc::synthetic(Expr_::Move(Box::new(inner)))
    }

    fn borrow_expr(inner: Expr) -> Expr {
        WithLoc::synthetic(Expr_::Borrow(Box::new(inner)))
    }

    fn borrow_mut_expr(inner: Expr) -> Expr {
        WithLoc::synthetic(Expr_::BorrowMut(Box::new(inner)))
    }

    fn drop_expr(inner: Expr) -> Expr {
        WithLoc::synthetic(Expr_::Drop(Box::new(inner)))
    }

    fn seq_expr(first: Expr, second: Expr) -> Expr {
        WithLoc::synthetic(Expr_::Seq(Box::new(first), Box::new(second)))
    }

    fn block_expr(exprs: Vec<Expr>) -> Expr {
        WithLoc::synthetic(Expr_::Block(exprs))
    }

    fn if_expr(cond: Expr, then_: Expr, else_: Expr) -> Expr {
        WithLoc::synthetic(Expr_::If(Box::new(cond), Box::new(then_), Box::new(else_)))
    }

    // -------------------------------------------------------------------------
    // check_var_use tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_check_var_use_owned() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let result = check_var_use(&state, x);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_var_use_not_found() {
        let state = BorrowState::new();
        let x = make_var(1);

        let result = check_var_use(&state, x);
        assert!(matches!(
            result,
            Err(OwnershipError::VariableNotFound { .. })
        ));
    }

    #[test]
    fn test_check_var_use_after_move() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);
        state.update_var_state_mut(x, VarState::Moved);

        let result = check_var_use(&state, x);
        assert!(matches!(result, Err(OwnershipError::UseAfterMove { .. })));
    }

    // -------------------------------------------------------------------------
    // check_move tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_check_move_owned() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let result = check_move(&state, x);
        assert!(result.is_ok());

        let new_state = result.unwrap();
        assert!(matches!(
            new_state.lookup_var(x).unwrap().state,
            VarState::Moved
        ));
    }

    #[test]
    fn test_check_move_double_move() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);
        state.update_var_state_mut(x, VarState::Moved);

        let result = check_move(&state, x);
        assert!(matches!(result, Err(OwnershipError::DoubleMove { .. })));
    }

    #[test]
    fn test_check_move_while_borrowed() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        // Borrow first
        let state = check_borrow_shared(&state, x).unwrap();

        // Try to move - should fail
        let result = check_move(&state, x);
        assert!(matches!(
            result,
            Err(OwnershipError::MoveWhileBorrowed { .. })
        ));
    }

    // -------------------------------------------------------------------------
    // check_borrow_shared tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_check_borrow_shared_owned() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let result = check_borrow_shared(&state, x);
        assert!(result.is_ok());

        let new_state = result.unwrap();
        assert!(matches!(
            new_state.lookup_var(x).unwrap().state,
            VarState::Borrowed(_)
        ));
        assert_eq!(new_state.loans.len(), 1);
    }

    #[test]
    fn test_check_borrow_shared_multiple() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        // First borrow
        let state1 = check_borrow_shared(&state, x).unwrap();

        // Second borrow should succeed (multiple shared allowed)
        let result = check_borrow_shared(&state1, x);
        assert!(result.is_ok());

        let state2 = result.unwrap();
        assert_eq!(state2.loans.len(), 2);

        if let VarState::Borrowed(loans) = &state2.lookup_var(x).unwrap().state {
            assert_eq!(loans.len(), 2);
        } else {
            panic!("Expected Borrowed state");
        }
    }

    #[test]
    fn test_check_borrow_shared_while_mut_borrowed() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        // Exclusive borrow first
        let state1 = check_borrow_exclusive(&state, x).unwrap();

        // Shared borrow should fail
        let result = check_borrow_shared(&state1, x);
        assert!(matches!(
            result,
            Err(OwnershipError::BorrowWhileMutBorrowed { .. })
        ));
    }

    // -------------------------------------------------------------------------
    // check_borrow_exclusive tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_check_borrow_exclusive_owned() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let result = check_borrow_exclusive(&state, x);
        assert!(result.is_ok());

        let new_state = result.unwrap();
        assert!(matches!(
            new_state.lookup_var(x).unwrap().state,
            VarState::BorrowedMut(_)
        ));
    }

    #[test]
    fn test_check_borrow_exclusive_while_shared() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        // Shared borrow first
        let state1 = check_borrow_shared(&state, x).unwrap();

        // Exclusive borrow should fail
        let result = check_borrow_exclusive(&state1, x);
        assert!(matches!(
            result,
            Err(OwnershipError::MutBorrowWhileBorrowed { .. })
        ));
    }

    #[test]
    fn test_check_borrow_exclusive_multiple() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        // First exclusive borrow
        let state1 = check_borrow_exclusive(&state, x).unwrap();

        // Second exclusive borrow should fail
        let result = check_borrow_exclusive(&state1, x);
        assert!(matches!(
            result,
            Err(OwnershipError::MultipleMutBorrows { .. })
        ));
    }

    // -------------------------------------------------------------------------
    // check_drop tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_check_drop_owned() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let result = check_drop(&state, x);
        assert!(result.is_ok());

        let new_state = result.unwrap();
        assert!(matches!(
            new_state.lookup_var(x).unwrap().state,
            VarState::Dropped
        ));
    }

    #[test]
    fn test_check_drop_double_free() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);
        state.update_var_state_mut(x, VarState::Dropped);

        let result = check_drop(&state, x);
        assert!(matches!(result, Err(OwnershipError::DoubleFree { .. })));
    }

    #[test]
    fn test_check_drop_while_borrowed() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        // Borrow first
        let state1 = check_borrow_shared(&state, x).unwrap();

        // Drop should fail
        let result = check_drop(&state1, x);
        assert!(matches!(
            result,
            Err(OwnershipError::DropWhileBorrowed { .. })
        ));
    }

    // -------------------------------------------------------------------------
    // borrow_check_expr tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_borrow_check_literal() {
        let state = BorrowState::new();
        let expr = lit_expr(Literal::i32(42));

        let result = check_expr(&state, &expr);
        assert!(result.is_ok());
    }

    #[test]
    fn test_borrow_check_var() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let expr = var_expr(x);
        let result = check_expr(&state, &expr);
        assert!(result.is_ok());
    }

    #[test]
    fn test_borrow_check_move() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let expr = move_expr(var_expr(x));
        let result = check_expr(&state, &expr);
        assert!(result.is_ok());

        let new_state = result.unwrap();
        assert!(matches!(
            new_state.lookup_var(x).unwrap().state,
            VarState::Moved
        ));
    }

    #[test]
    fn test_borrow_check_move_use_after_move() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        // Move then use
        let expr = seq_expr(move_expr(var_expr(x)), var_expr(x));

        let result = check_expr(&state, &expr);
        assert!(matches!(result, Err(OwnershipError::UseAfterMove { .. })));
    }

    #[test]
    fn test_borrow_check_borrow() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let expr = borrow_expr(var_expr(x));
        let result = check_expr(&state, &expr);
        assert!(result.is_ok());
    }

    #[test]
    fn test_borrow_check_borrow_mut() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let expr = borrow_mut_expr(var_expr(x));
        let result = check_expr(&state, &expr);
        assert!(result.is_ok());
    }

    #[test]
    fn test_borrow_check_drop() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let expr = drop_expr(var_expr(x));
        let result = check_expr(&state, &expr);
        assert!(result.is_ok());

        let new_state = result.unwrap();
        assert!(matches!(
            new_state.lookup_var(x).unwrap().state,
            VarState::Dropped
        ));
    }

    #[test]
    fn test_borrow_check_block() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        state.add_var(x, BrrrType::BOOL, Mode::One);

        let expr = block_expr(vec![var_expr(x), lit_expr(Literal::i32(1))]);

        let result = check_expr(&state, &expr);
        assert!(result.is_ok());
    }

    #[test]
    fn test_borrow_check_if_merge_moved() {
        let mut state = BorrowState::new();
        let x = make_var(1);
        let cond = make_var(2);
        state.add_var(x, BrrrType::BOOL, Mode::One);
        state.add_var(cond, BrrrType::BOOL, Mode::Omega);

        // if cond { move(x) } else { x }
        // After merge, x should be Moved (conservative)
        let expr = if_expr(
            var_expr(cond),
            move_expr(var_expr(x)),
            var_expr(x),
        );

        let result = check_expr(&state, &expr);
        assert!(result.is_ok());

        let new_state = result.unwrap();
        // Conservative merge: if moved in one branch, considered moved
        assert!(matches!(
            new_state.lookup_var(x).unwrap().state,
            VarState::Moved
        ));
    }

    #[test]
    fn test_borrow_check_fuel_exhaustion() {
        let state = BorrowState::new();
        let expr = lit_expr(Literal::Unit);

        let result = borrow_check_expr(&state, &expr, 0);
        assert!(matches!(result, Err(OwnershipError::InternalError { .. })));
    }

    #[test]
    fn test_merge_borrow_states() {
        let mut left = BorrowState::new();
        let mut right = BorrowState::new();
        let x = make_var(1);
        let y = make_var(2);

        left.add_var(x, BrrrType::BOOL, Mode::One);
        left.add_var(y, BrrrType::BOOL, Mode::One);
        right.add_var(x, BrrrType::BOOL, Mode::One);
        right.add_var(y, BrrrType::BOOL, Mode::One);

        // x moved in left, owned in right
        left.update_var_state_mut(x, VarState::Moved);
        // y owned in left, dropped in right
        right.update_var_state_mut(y, VarState::Dropped);

        let merged = merge_borrow_states(left, right).unwrap();

        // x should be Moved (dominates Owned)
        assert!(matches!(
            merged.lookup_var(x).unwrap().state,
            VarState::Moved
        ));
        // y should be Dropped (dominates Owned)
        assert!(matches!(
            merged.lookup_var(y).unwrap().state,
            VarState::Dropped
        ));
    }

    #[test]
    fn test_extend_var() {
        let state = BorrowState::new();
        let x = make_var(1);

        let new_state = extend_var(&state, x, BrrrType::BOOL, Mode::One);

        assert!(new_state.lookup_var(x).is_some());
        assert!(matches!(
            new_state.lookup_var(x).unwrap().state,
            VarState::Owned
        ));
    }
}
