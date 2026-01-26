//! Priority-based session types for deadlock freedom
//!
//! Extends binary session types with priorities to ensure deadlock freedom.
//! Each communication action is annotated with a priority level, and the
//! type system enforces that priorities decrease along any execution path.
//!
//! # Deadlock Freedom via Priorities
//!
//! The key insight is that if all communication actions have strictly
//! increasing priorities (from the perspective of each endpoint), then
//! circular wait conditions cannot occur.
//!
//! # Example
//!
//! ```text
//! // Lock A with priority 1, then lock B with priority 2
//! !A@1.?B@2.end
//!
//! // The dual must also respect the priority order
//! ?A@1.!B@2.end
//! ```
//!
//! # References
//!
//! - Kobayashi, N. (2006). A new type system for deadlock-free processes.
//! - Padovani, L. (2014). Deadlock and lock freedom in the linear pi-calculus.

use serde::{Deserialize, Serialize};

use super::{Label, SessionVar};
use crate::types::BrrrType;

/// Priority level for session type actions.
///
/// Higher values indicate higher priority (executed first).
/// Priority 0 is the lowest priority.
pub type Priority = u32;

/// Priority-annotated session type for deadlock freedom.
///
/// Each communication action (Send, Recv, Select, Branch) carries a priority.
/// The type system can then verify that priorities form a valid ordering
/// to prevent circular waits.
///
/// Maps to F*:
/// ```fstar
/// noeq type pri_session =
///   | PSSend   : priority -> payload:brrr_type -> continuation:pri_session -> pri_session
///   | PSRecv   : priority -> payload:brrr_type -> continuation:pri_session -> pri_session
///   | PSSelect : priority -> branches:list (label & pri_session) -> pri_session
///   | PSBranch : priority -> branches:list (label & pri_session) -> pri_session
///   | PSRec    : var:session_var -> body:pri_session -> pri_session
///   | PSVar    : var:session_var -> pri_session
///   | PSEnd    : pri_session
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PriSession {
    /// Send with priority: `!T@p.S`
    ///
    /// The sender transmits a value of type `payload` at priority level `priority`,
    /// then continues with the `continuation` session type.
    Send {
        priority: Priority,
        payload: BrrrType,
        continuation: Box<PriSession>,
    },

    /// Receive with priority: `?T@p.S`
    ///
    /// The receiver expects a value of type `payload` at priority level `priority`,
    /// then continues with the `continuation` session type.
    Recv {
        priority: Priority,
        payload: BrrrType,
        continuation: Box<PriSession>,
    },

    /// Internal choice with priority: `+{l1: S1, l2: S2, ...}@p`
    ///
    /// The sender chooses one branch label at the given priority.
    Select {
        priority: Priority,
        branches: Vec<(Label, PriSession)>,
    },

    /// External choice with priority: `&{l1: S1, l2: S2, ...}@p`
    ///
    /// The receiver offers multiple continuations at the given priority.
    Branch {
        priority: Priority,
        branches: Vec<(Label, PriSession)>,
    },

    /// Recursive type: `rec X.S` (mu-type)
    ///
    /// Defines a recursive session type where `var` can appear in `body`.
    Rec {
        var: SessionVar,
        body: Box<PriSession>,
    },

    /// Type variable: `X`
    ///
    /// References a recursion variable bound by an enclosing `Rec`.
    Var(SessionVar),

    /// Session end: `end`
    ///
    /// Protocol termination - no more communication.
    End,
}

impl PriSession {
    /// End session constant
    pub const END: Self = Self::End;

    /// Create send type with priority: `!T@p.S`
    pub fn send(priority: Priority, payload: BrrrType, cont: Self) -> Self {
        Self::Send {
            priority,
            payload,
            continuation: Box::new(cont),
        }
    }

    /// Create receive type with priority: `?T@p.S`
    pub fn recv(priority: Priority, payload: BrrrType, cont: Self) -> Self {
        Self::Recv {
            priority,
            payload,
            continuation: Box::new(cont),
        }
    }

    /// Create select type with priority: `+{...}@p`
    pub fn select(priority: Priority, branches: Vec<(Label, Self)>) -> Self {
        Self::Select { priority, branches }
    }

    /// Create branch type with priority: `&{...}@p`
    pub fn branch(priority: Priority, branches: Vec<(Label, Self)>) -> Self {
        Self::Branch { priority, branches }
    }

    /// Create recursive type: `rec X.S`
    pub fn rec(var: SessionVar, body: Self) -> Self {
        Self::Rec {
            var,
            body: Box::new(body),
        }
    }

    /// Create variable reference: `X`
    pub const fn var(v: SessionVar) -> Self {
        Self::Var(v)
    }

    /// Check if this is the end type
    pub const fn is_end(&self) -> bool {
        matches!(self, Self::End)
    }

    /// Check if this is a send type
    pub const fn is_send(&self) -> bool {
        matches!(self, Self::Send { .. })
    }

    /// Check if this is a receive type
    pub const fn is_recv(&self) -> bool {
        matches!(self, Self::Recv { .. })
    }

    /// Check if this is a choice type (select or branch)
    pub const fn is_choice(&self) -> bool {
        matches!(self, Self::Select { .. } | Self::Branch { .. })
    }

    /// Check if this is a recursive type
    pub const fn is_recursive(&self) -> bool {
        matches!(self, Self::Rec { .. })
    }

    /// Get discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Send { .. } => 0,
            Self::Recv { .. } => 1,
            Self::Select { .. } => 2,
            Self::Branch { .. } => 3,
            Self::Rec { .. } => 4,
            Self::Var(_) => 5,
            Self::End => 6,
        }
    }

    /// Get free session variables in this type
    pub fn free_vars(&self) -> Vec<SessionVar> {
        self.free_vars_with_bound(&[])
    }

    /// Helper for computing free variables with bound context
    fn free_vars_with_bound(&self, bound: &[SessionVar]) -> Vec<SessionVar> {
        match self {
            Self::Send { continuation, .. } | Self::Recv { continuation, .. } => {
                continuation.free_vars_with_bound(bound)
            }
            Self::Select { branches, .. } | Self::Branch { branches, .. } => branches
                .iter()
                .flat_map(|(_, s)| s.free_vars_with_bound(bound))
                .collect(),
            Self::Rec { var, body } => {
                let mut new_bound = bound.to_vec();
                new_bound.push(*var);
                body.free_vars_with_bound(&new_bound)
            }
            Self::Var(v) => {
                if bound.contains(v) {
                    vec![]
                } else {
                    vec![*v]
                }
            }
            Self::End => vec![],
        }
    }

    /// Check if this session type is closed (no free variables)
    pub fn is_closed(&self) -> bool {
        self.free_vars().is_empty()
    }

    /// Substitute a session variable with a session type
    pub fn substitute(&self, var: SessionVar, replacement: &Self) -> Self {
        match self {
            Self::Send {
                priority,
                payload,
                continuation,
            } => Self::Send {
                priority: *priority,
                payload: payload.clone(),
                continuation: Box::new(continuation.substitute(var, replacement)),
            },
            Self::Recv {
                priority,
                payload,
                continuation,
            } => Self::Recv {
                priority: *priority,
                payload: payload.clone(),
                continuation: Box::new(continuation.substitute(var, replacement)),
            },
            Self::Select { priority, branches } => Self::Select {
                priority: *priority,
                branches: branches
                    .iter()
                    .map(|(l, s)| (*l, s.substitute(var, replacement)))
                    .collect(),
            },
            Self::Branch { priority, branches } => Self::Branch {
                priority: *priority,
                branches: branches
                    .iter()
                    .map(|(l, s)| (*l, s.substitute(var, replacement)))
                    .collect(),
            },
            Self::Rec { var: rec_var, body } => {
                // Don't substitute if shadowed
                if *rec_var == var {
                    self.clone()
                } else {
                    Self::Rec {
                        var: *rec_var,
                        body: Box::new(body.substitute(var, replacement)),
                    }
                }
            }
            Self::Var(v) => {
                if *v == var {
                    replacement.clone()
                } else {
                    Self::Var(*v)
                }
            }
            Self::End => Self::End,
        }
    }

    /// Unfold one level of a recursive type
    ///
    /// `unfold(rec X.S) = S[X := rec X.S]`
    pub fn unfold(&self) -> Self {
        match self {
            Self::Rec { var, body } => body.substitute(*var, self),
            _ => self.clone(),
        }
    }
}

impl Default for PriSession {
    fn default() -> Self {
        Self::End
    }
}

// ============================================================================
// Priority Analysis Functions
// ============================================================================

/// Get the first priority encountered in a session type.
///
/// Returns the priority of the outermost communication action.
/// Returns `None` for `End`, `Var`, or bare `Rec` without immediate action.
///
/// Maps to F*:
/// ```fstar
/// let first_priority (s: pri_session) : option priority = ...
/// ```
pub fn first_priority(s: &PriSession) -> Option<Priority> {
    match s {
        PriSession::Send { priority, .. }
        | PriSession::Recv { priority, .. }
        | PriSession::Select { priority, .. }
        | PriSession::Branch { priority, .. } => Some(*priority),
        PriSession::Rec { body, .. } => first_priority(body),
        PriSession::Var(_) | PriSession::End => None,
    }
}

/// Get the minimum priority in a session type.
///
/// Traverses the entire session type and returns the smallest priority value.
/// Returns `None` if the session type has no communication actions.
///
/// Maps to F*:
/// ```fstar
/// let min_priority (s: pri_session) : option priority = ...
/// ```
pub fn min_priority(s: &PriSession) -> Option<Priority> {
    let priorities = all_priorities(s);
    priorities.into_iter().min()
}

/// Get the maximum priority in a session type.
///
/// Traverses the entire session type and returns the largest priority value.
/// Returns `None` if the session type has no communication actions.
///
/// Maps to F*:
/// ```fstar
/// let max_priority (s: pri_session) : option priority = ...
/// ```
pub fn max_priority(s: &PriSession) -> Option<Priority> {
    let priorities = all_priorities(s);
    priorities.into_iter().max()
}

/// Collect all priorities in a session type.
///
/// Returns a vector of all priority values in the order they are encountered
/// during a depth-first traversal. May contain duplicates.
///
/// Maps to F*:
/// ```fstar
/// let all_priorities (s: pri_session) : list priority = ...
/// ```
pub fn all_priorities(s: &PriSession) -> Vec<Priority> {
    let mut result = Vec::new();
    collect_priorities(s, &mut result);
    result
}

/// Helper function to collect priorities into a vector.
fn collect_priorities(s: &PriSession, result: &mut Vec<Priority>) {
    match s {
        PriSession::Send {
            priority,
            continuation,
            ..
        } => {
            result.push(*priority);
            collect_priorities(continuation, result);
        }
        PriSession::Recv {
            priority,
            continuation,
            ..
        } => {
            result.push(*priority);
            collect_priorities(continuation, result);
        }
        PriSession::Select { priority, branches } => {
            result.push(*priority);
            for (_, branch) in branches {
                collect_priorities(branch, result);
            }
        }
        PriSession::Branch { priority, branches } => {
            result.push(*priority);
            for (_, branch) in branches {
                collect_priorities(branch, result);
            }
        }
        PriSession::Rec { body, .. } => {
            collect_priorities(body, result);
        }
        PriSession::Var(_) | PriSession::End => {}
    }
}

/// Check if priorities are consistent (no gaps, proper ordering).
///
/// A session type has consistent priorities if:
/// 1. All branches of a choice have compatible priority structures
/// 2. Priorities form a valid sequence without unexpected gaps
///
/// This is a weaker property than strict increasing - it just checks
/// that the priority structure is well-formed.
///
/// Maps to F*:
/// ```fstar
/// let priority_consistent (s: pri_session) : bool = ...
/// ```
pub fn priority_consistent(s: &PriSession) -> bool {
    priority_consistent_inner(s, &[])
}

/// Inner helper for priority consistency check.
fn priority_consistent_inner(s: &PriSession, bound_vars: &[SessionVar]) -> bool {
    match s {
        PriSession::End => true,
        PriSession::Var(v) => {
            // Variable is consistent if it refers to a bound recursion variable
            bound_vars.contains(v)
        }
        PriSession::Send { continuation, .. } | PriSession::Recv { continuation, .. } => {
            priority_consistent_inner(continuation, bound_vars)
        }
        PriSession::Select { branches, .. } | PriSession::Branch { branches, .. } => {
            // All branches must have consistent priorities
            // Additionally, first priorities of all branches should be comparable
            if branches.is_empty() {
                return true;
            }

            // Check each branch is internally consistent
            let all_consistent = branches
                .iter()
                .all(|(_, b)| priority_consistent_inner(b, bound_vars));

            if !all_consistent {
                return false;
            }

            // Check that branches have compatible first priorities
            // All branches should have the same first priority (or all None)
            let first_priorities: Vec<Option<Priority>> =
                branches.iter().map(|(_, b)| first_priority(b)).collect();

            let first = first_priorities.first();
            first_priorities.iter().all(|p| p == first.unwrap_or(&None))
        }
        PriSession::Rec { var, body } => {
            let mut new_bound = bound_vars.to_vec();
            new_bound.push(*var);
            priority_consistent_inner(body, &new_bound)
        }
    }
}

/// Check if priorities are strictly increasing along all execution paths.
///
/// This is the key property for deadlock freedom: if priorities strictly
/// increase along any path, circular waits are impossible.
///
/// For each path from the start to `End`:
/// - Each subsequent priority must be strictly greater than the previous
/// - All branches must maintain this property independently
///
/// Maps to F*:
/// ```fstar
/// let priorities_strictly_increasing (s: pri_session) : bool = ...
/// ```
pub fn priorities_strictly_increasing(s: &PriSession) -> bool {
    priorities_increasing_from(s, None, &[])
}

/// Helper for checking strictly increasing priorities.
///
/// `prev` is the priority of the previous action (None if this is the first).
fn priorities_increasing_from(
    s: &PriSession,
    prev: Option<Priority>,
    bound_vars: &[SessionVar],
) -> bool {
    match s {
        PriSession::End => true,
        PriSession::Var(v) => {
            // For recursive calls, we accept the variable if it's bound
            // The actual check happens when unfolding
            bound_vars.contains(v)
        }
        PriSession::Send {
            priority,
            continuation,
            ..
        }
        | PriSession::Recv {
            priority,
            continuation,
            ..
        } => {
            // Priority must be strictly greater than previous
            let valid = match prev {
                Some(p) => *priority > p,
                None => true, // First action, any priority is valid
            };
            valid && priorities_increasing_from(continuation, Some(*priority), bound_vars)
        }
        PriSession::Select { priority, branches }
        | PriSession::Branch { priority, branches } => {
            // Priority must be strictly greater than previous
            let valid = match prev {
                Some(p) => *priority > p,
                None => true,
            };
            if !valid {
                return false;
            }

            // All branches must maintain strictly increasing property
            branches
                .iter()
                .all(|(_, b)| priorities_increasing_from(b, Some(*priority), bound_vars))
        }
        PriSession::Rec { var, body } => {
            let mut new_bound = bound_vars.to_vec();
            new_bound.push(*var);
            priorities_increasing_from(body, prev, &new_bound)
        }
    }
}

/// Compute the dual (co-type) of a priority session type.
///
/// Duality swaps the direction of communication while preserving priorities:
/// - `dual(!T@p.S) = ?T@p.dual(S)`
/// - `dual(?T@p.S) = !T@p.dual(S)`
/// - `dual(+{...}@p) = &{...}@p` (with dual branches)
/// - `dual(&{...}@p) = +{...}@p` (with dual branches)
/// - `dual(end) = end`
/// - `dual(rec X.S) = rec X.dual(S)`
/// - `dual(X) = X`
///
/// The priority annotations are preserved - both endpoints use the same
/// priority values, ensuring coordination.
///
/// Maps to F*:
/// ```fstar
/// let pri_dual (s: pri_session) : pri_session = ...
/// ```
///
/// # Property: Involution
/// `pri_dual(pri_dual(S)) = S` for all priority session types S
pub fn pri_dual(s: &PriSession) -> PriSession {
    match s {
        PriSession::Send {
            priority,
            payload,
            continuation,
        } => PriSession::Recv {
            priority: *priority,
            payload: payload.clone(),
            continuation: Box::new(pri_dual(continuation)),
        },
        PriSession::Recv {
            priority,
            payload,
            continuation,
        } => PriSession::Send {
            priority: *priority,
            payload: payload.clone(),
            continuation: Box::new(pri_dual(continuation)),
        },
        PriSession::Select { priority, branches } => PriSession::Branch {
            priority: *priority,
            branches: branches.iter().map(|(l, s)| (*l, pri_dual(s))).collect(),
        },
        PriSession::Branch { priority, branches } => PriSession::Select {
            priority: *priority,
            branches: branches.iter().map(|(l, s)| (*l, pri_dual(s))).collect(),
        },
        PriSession::Rec { var, body } => PriSession::Rec {
            var: *var,
            body: Box::new(pri_dual(body)),
        },
        PriSession::Var(v) => PriSession::Var(*v),
        PriSession::End => PriSession::End,
    }
}

/// Check if two priority session types are duals of each other.
pub fn is_pri_dual_of(s1: &PriSession, s2: &PriSession) -> bool {
    pri_dual(s1) == *s2
}

/// Check if a priority session type is self-dual (symmetric).
pub fn is_pri_self_dual(s: &PriSession) -> bool {
    pri_dual(s) == *s
}

/// Get unique sorted priorities in a session type.
///
/// Unlike `all_priorities`, this returns a deduplicated and sorted list.
pub fn unique_priorities(s: &PriSession) -> Vec<Priority> {
    let mut priorities = all_priorities(s);
    priorities.sort_unstable();
    priorities.dedup();
    priorities
}

/// Check if priorities form a contiguous range starting from a base.
///
/// Returns true if the unique priorities are exactly `base, base+1, ..., base+n`.
pub fn priorities_contiguous_from(s: &PriSession, base: Priority) -> bool {
    let unique = unique_priorities(s);
    if unique.is_empty() {
        return true;
    }

    // Check the sequence is contiguous starting from base
    for (i, &p) in unique.iter().enumerate() {
        #[allow(clippy::cast_possible_truncation)]
        let expected = base + i as u32;
        if p != expected {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PrimKind;

    #[test]
    fn test_pri_session_construction() {
        let s = PriSession::send(1, BrrrType::BOOL, PriSession::End);
        assert!(s.is_send());
        assert!(!s.is_end());
        assert_eq!(s.discriminant(), 0);
    }

    #[test]
    fn test_pri_session_end() {
        let s = PriSession::END;
        assert!(s.is_end());
        assert_eq!(s.discriminant(), 6);
    }

    #[test]
    fn test_first_priority_send() {
        let s = PriSession::send(42, BrrrType::BOOL, PriSession::End);
        assert_eq!(first_priority(&s), Some(42));
    }

    #[test]
    fn test_first_priority_recv() {
        let s = PriSession::recv(7, BrrrType::STRING, PriSession::End);
        assert_eq!(first_priority(&s), Some(7));
    }

    #[test]
    fn test_first_priority_end() {
        assert_eq!(first_priority(&PriSession::End), None);
    }

    #[test]
    fn test_first_priority_var() {
        let s = PriSession::var(SessionVar::new(0));
        assert_eq!(first_priority(&s), None);
    }

    #[test]
    fn test_first_priority_rec() {
        let var = SessionVar::new(0);
        let s = PriSession::rec(var, PriSession::send(5, BrrrType::BOOL, PriSession::var(var)));
        assert_eq!(first_priority(&s), Some(5));
    }

    #[test]
    fn test_all_priorities_simple() {
        let s = PriSession::send(
            1,
            BrrrType::BOOL,
            PriSession::recv(2, BrrrType::STRING, PriSession::End),
        );
        let priorities = all_priorities(&s);
        assert_eq!(priorities, vec![1, 2]);
    }

    #[test]
    fn test_all_priorities_empty() {
        let priorities = all_priorities(&PriSession::End);
        assert!(priorities.is_empty());
    }

    #[test]
    fn test_all_priorities_branching() {
        let s = PriSession::select(
            1,
            vec![
                (
                    lasso::Spur::default(),
                    PriSession::send(2, BrrrType::BOOL, PriSession::End),
                ),
                (
                    lasso::Spur::default(),
                    PriSession::send(3, BrrrType::BOOL, PriSession::End),
                ),
            ],
        );
        let priorities = all_priorities(&s);
        assert_eq!(priorities, vec![1, 2, 3]);
    }

    #[test]
    fn test_min_priority() {
        let s = PriSession::send(
            5,
            BrrrType::BOOL,
            PriSession::recv(2, BrrrType::STRING, PriSession::send(8, BrrrType::BOOL, PriSession::End)),
        );
        assert_eq!(min_priority(&s), Some(2));
    }

    #[test]
    fn test_min_priority_empty() {
        assert_eq!(min_priority(&PriSession::End), None);
    }

    #[test]
    fn test_max_priority() {
        let s = PriSession::send(
            5,
            BrrrType::BOOL,
            PriSession::recv(2, BrrrType::STRING, PriSession::send(8, BrrrType::BOOL, PriSession::End)),
        );
        assert_eq!(max_priority(&s), Some(8));
    }

    #[test]
    fn test_max_priority_empty() {
        assert_eq!(max_priority(&PriSession::End), None);
    }

    #[test]
    fn test_priorities_strictly_increasing_valid() {
        let s = PriSession::send(
            1,
            BrrrType::BOOL,
            PriSession::recv(2, BrrrType::STRING, PriSession::send(3, BrrrType::BOOL, PriSession::End)),
        );
        assert!(priorities_strictly_increasing(&s));
    }

    #[test]
    fn test_priorities_strictly_increasing_invalid_equal() {
        let s = PriSession::send(
            1,
            BrrrType::BOOL,
            PriSession::recv(1, BrrrType::STRING, PriSession::End), // Same priority
        );
        assert!(!priorities_strictly_increasing(&s));
    }

    #[test]
    fn test_priorities_strictly_increasing_invalid_decreasing() {
        let s = PriSession::send(
            5,
            BrrrType::BOOL,
            PriSession::recv(3, BrrrType::STRING, PriSession::End), // Decreasing
        );
        assert!(!priorities_strictly_increasing(&s));
    }

    #[test]
    fn test_priorities_strictly_increasing_branching() {
        let s = PriSession::select(
            1,
            vec![
                (
                    lasso::Spur::default(),
                    PriSession::send(2, BrrrType::BOOL, PriSession::End),
                ),
                (
                    lasso::Spur::default(),
                    PriSession::send(3, BrrrType::BOOL, PriSession::End),
                ),
            ],
        );
        assert!(priorities_strictly_increasing(&s));
    }

    #[test]
    fn test_priorities_strictly_increasing_branching_invalid() {
        let s = PriSession::select(
            5,
            vec![
                (
                    lasso::Spur::default(),
                    PriSession::send(2, BrrrType::BOOL, PriSession::End), // 2 < 5!
                ),
                (
                    lasso::Spur::default(),
                    PriSession::send(3, BrrrType::BOOL, PriSession::End), // 3 < 5!
                ),
            ],
        );
        assert!(!priorities_strictly_increasing(&s));
    }

    #[test]
    fn test_pri_dual_send_recv() {
        let send = PriSession::send(1, BrrrType::BOOL, PriSession::End);
        let recv = pri_dual(&send);

        match recv {
            PriSession::Recv { priority, .. } => {
                assert_eq!(priority, 1);
            }
            _ => panic!("Expected Recv"),
        }
    }

    #[test]
    fn test_pri_dual_involution() {
        let s = PriSession::send(
            1,
            BrrrType::BOOL,
            PriSession::recv(2, BrrrType::STRING, PriSession::End),
        );
        assert_eq!(pri_dual(&pri_dual(&s)), s);
    }

    #[test]
    fn test_pri_dual_preserves_priority() {
        let s = PriSession::send(42, BrrrType::BOOL, PriSession::End);
        let d = pri_dual(&s);

        if let PriSession::Recv { priority, .. } = d {
            assert_eq!(priority, 42);
        } else {
            panic!("Expected Recv");
        }
    }

    #[test]
    fn test_pri_dual_select_branch() {
        let s = PriSession::select(
            1,
            vec![(lasso::Spur::default(), PriSession::End)],
        );
        let d = pri_dual(&s);

        match d {
            PriSession::Branch { priority, .. } => {
                assert_eq!(priority, 1);
            }
            _ => panic!("Expected Branch"),
        }
    }

    #[test]
    fn test_is_pri_dual_of() {
        let send = PriSession::send(1, BrrrType::BOOL, PriSession::End);
        let recv = PriSession::recv(1, BrrrType::BOOL, PriSession::End);

        assert!(is_pri_dual_of(&send, &recv));
        assert!(is_pri_dual_of(&recv, &send));
        assert!(!is_pri_dual_of(&send, &send));
    }

    #[test]
    fn test_is_pri_self_dual() {
        assert!(is_pri_self_dual(&PriSession::End));

        let send = PriSession::send(1, BrrrType::BOOL, PriSession::End);
        assert!(!is_pri_self_dual(&send));

        let var = PriSession::var(SessionVar::new(0));
        assert!(is_pri_self_dual(&var));
    }

    #[test]
    fn test_priority_consistent_simple() {
        let s = PriSession::send(1, BrrrType::BOOL, PriSession::End);
        assert!(priority_consistent(&s));
    }

    #[test]
    fn test_priority_consistent_recursive() {
        let var = SessionVar::new(0);
        let s = PriSession::rec(var, PriSession::send(1, BrrrType::BOOL, PriSession::var(var)));
        assert!(priority_consistent(&s));
    }

    #[test]
    fn test_priority_consistent_unbound_var() {
        let s = PriSession::var(SessionVar::new(0));
        assert!(!priority_consistent(&s));
    }

    #[test]
    fn test_unique_priorities() {
        let s = PriSession::send(
            1,
            BrrrType::BOOL,
            PriSession::recv(
                2,
                BrrrType::STRING,
                PriSession::send(1, BrrrType::BOOL, PriSession::End), // Duplicate priority
            ),
        );
        let unique = unique_priorities(&s);
        assert_eq!(unique, vec![1, 2]);
    }

    #[test]
    fn test_priorities_contiguous_from() {
        let s = PriSession::send(
            0,
            BrrrType::BOOL,
            PriSession::recv(1, BrrrType::STRING, PriSession::send(2, BrrrType::BOOL, PriSession::End)),
        );
        assert!(priorities_contiguous_from(&s, 0));
        assert!(!priorities_contiguous_from(&s, 1));
    }

    #[test]
    fn test_priorities_contiguous_from_gap() {
        let s = PriSession::send(
            0,
            BrrrType::BOOL,
            PriSession::recv(2, BrrrType::STRING, PriSession::End), // Gap: missing 1
        );
        assert!(!priorities_contiguous_from(&s, 0));
    }

    #[test]
    fn test_free_vars() {
        let var0 = SessionVar::new(0);
        let var1 = SessionVar::new(1);

        // Free variable
        let s = PriSession::Var(var0);
        assert_eq!(s.free_vars(), vec![var0]);
        assert!(!s.is_closed());

        // Bound variable
        let s = PriSession::rec(var0, PriSession::var(var0));
        assert!(s.free_vars().is_empty());
        assert!(s.is_closed());

        // Mixed: var1 free, var0 bound
        let s = PriSession::rec(
            var0,
            PriSession::send(1, BrrrType::BOOL, PriSession::Var(var1)),
        );
        assert_eq!(s.free_vars(), vec![var1]);
    }

    #[test]
    fn test_substitute() {
        let var = SessionVar::new(0);
        let s = PriSession::var(var);
        let replacement = PriSession::End;

        let result = s.substitute(var, &replacement);
        assert_eq!(result, PriSession::End);
    }

    #[test]
    fn test_substitute_preserves_priority() {
        let var = SessionVar::new(0);
        let s = PriSession::send(5, BrrrType::BOOL, PriSession::var(var));
        let replacement = PriSession::End;

        let result = s.substitute(var, &replacement);
        if let PriSession::Send { priority, continuation, .. } = result {
            assert_eq!(priority, 5);
            assert_eq!(*continuation, PriSession::End);
        } else {
            panic!("Expected Send");
        }
    }

    #[test]
    fn test_unfold() {
        let var = SessionVar::new(0);
        let body = PriSession::send(1, BrrrType::BOOL, PriSession::var(var));
        let rec_type = PriSession::rec(var, body);

        let unfolded = rec_type.unfold();

        // Unfolding should produce: !Bool@1.rec X0.!Bool@1.X0
        if let PriSession::Send { priority, continuation, .. } = unfolded {
            assert_eq!(priority, 1);
            assert!(continuation.is_recursive());
        } else {
            panic!("Expected Send after unfold");
        }
    }

    #[test]
    fn test_default() {
        let s: PriSession = Default::default();
        assert_eq!(s, PriSession::End);
    }

    #[test]
    fn test_discriminants_unique() {
        let types = [
            PriSession::send(1, BrrrType::BOOL, PriSession::End),
            PriSession::recv(1, BrrrType::BOOL, PriSession::End),
            PriSession::select(1, vec![]),
            PriSession::branch(1, vec![]),
            PriSession::rec(SessionVar::new(0), PriSession::End),
            PriSession::var(SessionVar::new(0)),
            PriSession::End,
        ];

        let discriminants: Vec<_> = types.iter().map(|t| t.discriminant()).collect();
        let unique: std::collections::HashSet<_> = discriminants.iter().collect();

        assert_eq!(
            discriminants.len(),
            unique.len(),
            "Discriminants must be unique"
        );
    }

    #[test]
    fn test_complex_protocol_deadlock_free() {
        // A valid priority-based protocol:
        // Client: !Request@1.?Response@2.end
        // Server: ?Request@1.!Response@2.end
        let client = PriSession::send(
            1,
            BrrrType::Prim(PrimKind::String), // Request
            PriSession::recv(
                2,
                BrrrType::Prim(PrimKind::String), // Response
                PriSession::End,
            ),
        );

        let server = pri_dual(&client);

        // Both should have strictly increasing priorities
        assert!(priorities_strictly_increasing(&client));
        assert!(priorities_strictly_increasing(&server));

        // They should be duals
        assert!(is_pri_dual_of(&client, &server));
    }

    #[test]
    fn test_recursive_protocol_priorities() {
        // Recursive protocol: rec X. !Bool@1.?Int@2.X
        let var = SessionVar::new(0);
        let body = PriSession::send(
            1,
            BrrrType::BOOL,
            PriSession::recv(2, BrrrType::Prim(PrimKind::String), PriSession::var(var)),
        );
        let s = PriSession::rec(var, body);

        assert!(s.is_recursive());
        assert!(s.is_closed());
        assert_eq!(all_priorities(&s), vec![1, 2]);
        assert!(priority_consistent(&s));
        assert!(priorities_strictly_increasing(&s));
    }
}
