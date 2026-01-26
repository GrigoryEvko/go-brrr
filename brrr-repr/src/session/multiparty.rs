//! Multiparty session types (N-party communication)
//!
//! Mirrors F* MultipartySession.fst for typed multiparty protocols.
//!
//! # Overview
//!
//! Multiparty session types extend binary session types to N participants.
//! A global type describes the complete protocol from a bird's eye view,
//! while local types describe each participant's view after projection.
//!
//! # Global Types
//!
//! Global types describe interactions between named participants:
//! - `A -> B: T. G` - A sends T to B, continue with G
//! - `A -> B: {l1: G1, l2: G2}` - A sends choice to B
//! - `rec X. G` - Recursive protocol
//! - `end` - Protocol termination
//!
//! # Projection
//!
//! For each participant p in a global type G, we can project to get p's
//! local view: `project(G, p) = L`. The projection must be defined
//! (consistent) for all participants.
//!
//! # References
//!
//! - Honda, Yoshida, Carbone (2008). Multiparty asynchronous session types.
//! - Scalas, Yoshida (2019). Less is more: Multiparty session types revisited.

use std::collections::{HashMap, HashSet};

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::{Label, SessionVar};
use crate::types::BrrrType;

/// Participant identifier (interned string)
///
/// Represents a named role in a multiparty protocol (e.g., "Client", "Server", "Bank").
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Participant(pub Spur);

impl Participant {
    /// Create a new participant from an interned string
    pub const fn new(name: Spur) -> Self {
        Self(name)
    }
}

/// Global recursion variable
///
/// Used in `rec X. G` for recursive global types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GlobalVar(pub u32);

impl GlobalVar {
    /// Create a new global variable with the given index
    pub const fn new(idx: u32) -> Self {
        Self(idx)
    }

    /// Get the variable index
    pub const fn index(self) -> u32 {
        self.0
    }
}

impl From<u32> for GlobalVar {
    fn from(idx: u32) -> Self {
        Self(idx)
    }
}

/// Type alias for F* compatibility (gtype_var in MultipartySession.fst)
pub type GTypeVar = GlobalVar;

/// Global type - describes complete multiparty protocol
///
/// Maps to F*:
/// ```fstar
/// noeq type global_type =
///   | GEnd     : global_type
///   | GVar     : global_var -> global_type
///   | GRec     : var:global_var -> body:global_type -> global_type
///   | GMsg     : sender:participant -> receiver:participant ->
///                payload:brrr_type -> continuation:global_type -> global_type
///   | GChoice  : sender:participant -> receiver:participant ->
///                branches:list (label & global_type) -> global_type
///   | GParallel: global_type -> global_type -> global_type
///   | GDelegation: delegator:participant -> receiver:participant ->
///                  delegated:global_type -> continuation:global_type -> global_type
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum GlobalType {
    /// Protocol termination
    End,

    /// Recursion variable reference
    Var(GlobalVar),

    /// Recursive protocol: `rec X. G`
    Rec {
        var: GlobalVar,
        body: Box<GlobalType>,
    },

    /// Message exchange: `A -> B: T. G`
    ///
    /// Sender transmits a value of type payload to receiver,
    /// then protocol continues with continuation.
    Message {
        sender: Participant,
        receiver: Participant,
        payload: BrrrType,
        continuation: Box<GlobalType>,
    },

    /// Choice/branching: `A -> B: {l1: G1, l2: G2, ...}`
    ///
    /// Sender selects a branch label and informs receiver,
    /// then protocol continues with the selected branch.
    Choice {
        sender: Participant,
        receiver: Participant,
        branches: Vec<(Label, GlobalType)>,
    },

    /// Parallel composition: `G1 | G2`
    ///
    /// Two independent subprotocols running concurrently.
    /// Participants in G1 and G2 should be disjoint.
    Parallel(Box<GlobalType>, Box<GlobalType>),

    /// Session delegation: `A delegates S to B in G`
    ///
    /// Delegator transfers a session (represented by delegated type)
    /// to receiver, then continues with continuation.
    Delegation {
        delegator: Participant,
        receiver: Participant,
        delegated: Box<GlobalType>,
        continuation: Box<GlobalType>,
    },
}

/// Local type - participant's view of the protocol
///
/// Maps to F*:
/// ```fstar
/// noeq type local_type =
///   | LEnd    : local_type
///   | LVar    : session_var -> local_type
///   | LRec    : var:session_var -> body:local_type -> local_type
///   | LSend   : target:participant -> payload:brrr_type -> continuation:local_type -> local_type
///   | LRecv   : source:participant -> payload:brrr_type -> continuation:local_type -> local_type
///   | LSelect : target:participant -> branches:list (label & local_type) -> local_type
///   | LBranch : source:participant -> branches:list (label & local_type) -> local_type
///   | LThrow  : target:participant -> delegated:local_type -> continuation:local_type -> local_type
///   | LCatch  : source:participant -> delegated:local_type -> continuation:local_type -> local_type
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum LocalType {
    /// Protocol termination
    End,

    /// Recursion variable reference
    Var(SessionVar),

    /// Recursive local type: `rec X. L`
    Rec {
        var: SessionVar,
        body: Box<LocalType>,
    },

    /// Send message: `target!T. L`
    Send {
        target: Participant,
        payload: BrrrType,
        continuation: Box<LocalType>,
    },

    /// Receive message: `source?T. L`
    Recv {
        source: Participant,
        payload: BrrrType,
        continuation: Box<LocalType>,
    },

    /// Internal choice (select): `target +{l1: L1, l2: L2, ...}`
    Select {
        target: Participant,
        branches: Vec<(Label, LocalType)>,
    },

    /// External choice (branch): `source &{l1: L1, l2: L2, ...}`
    Branch {
        source: Participant,
        branches: Vec<(Label, LocalType)>,
    },

    /// Delegation send (throw): `target!![S]. L`
    ///
    /// Send a session endpoint to target.
    Throw {
        target: Participant,
        delegated: Box<LocalType>,
        continuation: Box<LocalType>,
    },

    /// Delegation receive (catch): `source??[S]. L`
    ///
    /// Receive a session endpoint from source.
    Catch {
        source: Participant,
        delegated: Box<LocalType>,
        continuation: Box<LocalType>,
    },
}

// ============================================================================
// GlobalType Constructors and Methods
// ============================================================================

impl GlobalType {
    /// End constant
    pub const END: Self = Self::End;

    /// Create a message exchange: `sender -> receiver: T. G`
    pub fn message(
        sender: Participant,
        receiver: Participant,
        payload: BrrrType,
        continuation: Self,
    ) -> Self {
        Self::Message {
            sender,
            receiver,
            payload,
            continuation: Box::new(continuation),
        }
    }

    /// Create a choice: `sender -> receiver: {branches}`
    pub fn choice(
        sender: Participant,
        receiver: Participant,
        branches: Vec<(Label, Self)>,
    ) -> Self {
        Self::Choice {
            sender,
            receiver,
            branches,
        }
    }

    /// Create a recursive type: `rec X. G`
    pub fn rec(var: GlobalVar, body: Self) -> Self {
        Self::Rec {
            var,
            body: Box::new(body),
        }
    }

    /// Create a variable reference
    pub const fn var(v: GlobalVar) -> Self {
        Self::Var(v)
    }

    /// Create parallel composition: `G1 | G2`
    pub fn parallel(g1: Self, g2: Self) -> Self {
        Self::Parallel(Box::new(g1), Box::new(g2))
    }

    /// Create delegation: `delegator delegates S to receiver in G`
    pub fn delegation(
        delegator: Participant,
        receiver: Participant,
        delegated: Self,
        continuation: Self,
    ) -> Self {
        Self::Delegation {
            delegator,
            receiver,
            delegated: Box::new(delegated),
            continuation: Box::new(continuation),
        }
    }

    /// Check if this is the end type
    pub const fn is_end(&self) -> bool {
        matches!(self, Self::End)
    }

    /// Check if this is a recursive type
    pub const fn is_recursive(&self) -> bool {
        matches!(self, Self::Rec { .. })
    }

    /// Check if this is a message type
    pub const fn is_message(&self) -> bool {
        matches!(self, Self::Message { .. })
    }

    /// Check if this is a choice type
    pub const fn is_choice(&self) -> bool {
        matches!(self, Self::Choice { .. })
    }

    /// Check if this is a parallel composition
    pub const fn is_parallel(&self) -> bool {
        matches!(self, Self::Parallel(_, _))
    }

    /// Check if this is a delegation
    pub const fn is_delegation(&self) -> bool {
        matches!(self, Self::Delegation { .. })
    }

    /// Get discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Message { .. } => 0,
            Self::Choice { .. } => 1,
            Self::Parallel(_, _) => 2,
            Self::Delegation { .. } => 3,
            Self::Rec { .. } => 4,
            Self::Var(_) => 5,
            Self::End => 6,
        }
    }

    /// Get all participants mentioned in this global type
    pub fn participants(&self) -> Vec<Participant> {
        let mut result = Vec::new();
        self.collect_participants(&mut result);
        result.sort_by_key(|p| p.0);
        result.dedup_by_key(|p| p.0);
        result
    }

    fn collect_participants(&self, result: &mut Vec<Participant>) {
        match self {
            Self::End | Self::Var(_) => {}
            Self::Rec { body, .. } => body.collect_participants(result),
            Self::Message {
                sender,
                receiver,
                continuation,
                ..
            } => {
                result.push(*sender);
                result.push(*receiver);
                continuation.collect_participants(result);
            }
            Self::Choice {
                sender,
                receiver,
                branches,
            } => {
                result.push(*sender);
                result.push(*receiver);
                for (_, g) in branches {
                    g.collect_participants(result);
                }
            }
            Self::Parallel(g1, g2) => {
                g1.collect_participants(result);
                g2.collect_participants(result);
            }
            Self::Delegation {
                delegator,
                receiver,
                delegated,
                continuation,
            } => {
                result.push(*delegator);
                result.push(*receiver);
                delegated.collect_participants(result);
                continuation.collect_participants(result);
            }
        }
    }

    /// Get free global variables in this type
    pub fn free_vars(&self) -> Vec<GlobalVar> {
        self.free_vars_with_bound(&[])
    }

    /// Helper for computing free variables with bound context
    fn free_vars_with_bound(&self, bound: &[GlobalVar]) -> Vec<GlobalVar> {
        match self {
            Self::End => vec![],
            Self::Var(v) => {
                if bound.contains(v) {
                    vec![]
                } else {
                    vec![*v]
                }
            }
            Self::Rec { var, body } => {
                let mut new_bound = bound.to_vec();
                new_bound.push(*var);
                body.free_vars_with_bound(&new_bound)
            }
            Self::Message { continuation, .. } => continuation.free_vars_with_bound(bound),
            Self::Choice { branches, .. } => branches
                .iter()
                .flat_map(|(_, g)| g.free_vars_with_bound(bound))
                .collect(),
            Self::Parallel(g1, g2) => {
                let mut vars = g1.free_vars_with_bound(bound);
                vars.extend(g2.free_vars_with_bound(bound));
                vars
            }
            Self::Delegation {
                delegated,
                continuation,
                ..
            } => {
                let mut vars = delegated.free_vars_with_bound(bound);
                vars.extend(continuation.free_vars_with_bound(bound));
                vars
            }
        }
    }

    /// Check if this global type is closed (no free variables)
    pub fn is_closed(&self) -> bool {
        self.free_vars().is_empty()
    }

    /// Check well-formedness: sender and receiver must be different
    ///
    /// Returns None if well-formed, or Some error message if not.
    pub fn check_distinct_endpoints(&self) -> Option<&'static str> {
        match self {
            Self::End | Self::Var(_) => None,
            Self::Rec { body, .. } => body.check_distinct_endpoints(),
            Self::Message {
                sender,
                receiver,
                continuation,
                ..
            } => {
                if sender == receiver {
                    return Some("Message sender and receiver must be different");
                }
                continuation.check_distinct_endpoints()
            }
            Self::Choice {
                sender,
                receiver,
                branches,
            } => {
                if sender == receiver {
                    return Some("Choice sender and receiver must be different");
                }
                for (_, g) in branches {
                    if let Some(err) = g.check_distinct_endpoints() {
                        return Some(err);
                    }
                }
                None
            }
            Self::Parallel(g1, g2) => g1
                .check_distinct_endpoints()
                .or_else(|| g2.check_distinct_endpoints()),
            Self::Delegation {
                delegator,
                receiver,
                delegated,
                continuation,
            } => {
                if delegator == receiver {
                    return Some("Delegation delegator and receiver must be different");
                }
                delegated
                    .check_distinct_endpoints()
                    .or_else(|| continuation.check_distinct_endpoints())
            }
        }
    }

    /// Project global type to local type for a participant
    ///
    /// Returns None if the projection fails (e.g., inconsistent branches
    /// for participants not involved in a choice).
    ///
    /// # Algorithm
    ///
    /// For each global type constructor:
    /// - `End` projects to `End`
    /// - `Var X` projects to `Var X` (variable mapping)
    /// - `rec X. G` projects to `rec X. project(G, p)`
    /// - `A -> B: T. G`:
    ///   - If p = A: `B!T. project(G, p)`
    ///   - If p = B: `A?T. project(G, p)`
    ///   - Otherwise: `project(G, p)` (not involved)
    /// - `A -> B: {branches}`:
    ///   - If p = A: `B+{project each branch}`
    ///   - If p = B: `A&{project each branch}`
    ///   - Otherwise: merge projections (must be identical)
    pub fn project(&self, p: Participant) -> Option<LocalType> {
        self.project_inner(p, &mut HashMap::new())
    }

    fn project_inner(
        &self,
        p: Participant,
        var_map: &mut HashMap<GlobalVar, SessionVar>,
    ) -> Option<LocalType> {
        match self {
            Self::End => Some(LocalType::End),

            Self::Var(v) => {
                // Map global var to local var (preserving index if not mapped)
                let local_var = var_map.get(v).copied().unwrap_or(SessionVar(v.0));
                Some(LocalType::Var(local_var))
            }

            Self::Rec { var, body } => {
                let local_var = SessionVar(var.0);
                var_map.insert(*var, local_var);
                let projected_body = body.project_inner(p, var_map)?;
                Some(LocalType::Rec {
                    var: local_var,
                    body: Box::new(projected_body),
                })
            }

            Self::Message {
                sender,
                receiver,
                payload,
                continuation,
            } => {
                let cont = continuation.project_inner(p, var_map)?;

                if p == *sender {
                    Some(LocalType::Send {
                        target: *receiver,
                        payload: payload.clone(),
                        continuation: Box::new(cont),
                    })
                } else if p == *receiver {
                    Some(LocalType::Recv {
                        source: *sender,
                        payload: payload.clone(),
                        continuation: Box::new(cont),
                    })
                } else {
                    // Participant not involved in this message
                    Some(cont)
                }
            }

            Self::Choice {
                sender,
                receiver,
                branches,
            } => {
                // Project each branch
                let projected_branches: Option<Vec<_>> = branches
                    .iter()
                    .map(|(label, g)| {
                        // Clone var_map for each branch to avoid interference
                        let mut branch_var_map = var_map.clone();
                        g.project_inner(p, &mut branch_var_map)
                            .map(|l| (*label, l))
                    })
                    .collect();
                let branches = projected_branches?;

                if p == *sender {
                    Some(LocalType::Select {
                        target: *receiver,
                        branches,
                    })
                } else if p == *receiver {
                    Some(LocalType::Branch {
                        source: *sender,
                        branches,
                    })
                } else {
                    // Not sender or receiver - merge branches
                    // All branches must project to the same local type
                    Self::merge_projections(branches)
                }
            }

            Self::Parallel(g1, g2) => {
                let l1 = g1.project_inner(p, var_map)?;
                let l2 = g2.project_inner(p, var_map)?;

                // Simple parallel handling: if one side is End, take the other
                if l1.is_end() {
                    Some(l2)
                } else if l2.is_end() {
                    Some(l1)
                } else {
                    // Complex parallel composition requires interleaving semantics
                    // This is a limitation - full interleaving not supported
                    None
                }
            }

            Self::Delegation {
                delegator,
                receiver,
                delegated,
                continuation,
            } => {
                let cont = continuation.project_inner(p, var_map)?;
                let del = delegated.project_inner(p, var_map)?;

                if p == *delegator {
                    Some(LocalType::Throw {
                        target: *receiver,
                        delegated: Box::new(del),
                        continuation: Box::new(cont),
                    })
                } else if p == *receiver {
                    Some(LocalType::Catch {
                        source: *delegator,
                        delegated: Box::new(del),
                        continuation: Box::new(cont),
                    })
                } else {
                    // Not involved in delegation
                    Some(cont)
                }
            }
        }
    }

    /// Merge projections from different branches
    ///
    /// For a participant not involved in a choice, all branches must
    /// project to the same local type. This ensures consistency.
    fn merge_projections(branches: Vec<(Label, LocalType)>) -> Option<LocalType> {
        if branches.is_empty() {
            return Some(LocalType::End);
        }

        let first = &branches[0].1;

        // All branches must project to the same type for uninvolved participants
        if branches.iter().all(|(_, l)| l == first) {
            Some(first.clone())
        } else {
            // Inconsistent projections - not well-formed for this participant
            None
        }
    }
}

impl Default for GlobalType {
    fn default() -> Self {
        Self::End
    }
}

// ============================================================================
// Standalone Functions (F* compatible API)
// ============================================================================

/// Get all participants mentioned in a global type as a HashSet
///
/// Maps to F*:
/// ```fstar
/// val get_participants: global_type -> HashSet participant
/// ```
///
/// Returns the set of all participant identifiers that appear in the global type.
/// This includes senders and receivers in messages, choices, and delegations.
pub fn get_participants(g: &GlobalType) -> HashSet<Participant> {
    let mut result = HashSet::new();
    collect_participants_into(g, &mut result);
    result
}

/// Helper function to collect participants into a HashSet
fn collect_participants_into(g: &GlobalType, result: &mut HashSet<Participant>) {
    match g {
        GlobalType::End | GlobalType::Var(_) => {}
        GlobalType::Rec { body, .. } => collect_participants_into(body, result),
        GlobalType::Message {
            sender,
            receiver,
            continuation,
            ..
        } => {
            result.insert(*sender);
            result.insert(*receiver);
            collect_participants_into(continuation, result);
        }
        GlobalType::Choice {
            sender,
            receiver,
            branches,
        } => {
            result.insert(*sender);
            result.insert(*receiver);
            for (_, branch) in branches {
                collect_participants_into(branch, result);
            }
        }
        GlobalType::Parallel(g1, g2) => {
            collect_participants_into(g1, result);
            collect_participants_into(g2, result);
        }
        GlobalType::Delegation {
            delegator,
            receiver,
            delegated,
            continuation,
        } => {
            result.insert(*delegator);
            result.insert(*receiver);
            collect_participants_into(delegated, result);
            collect_participants_into(continuation, result);
        }
    }
}

/// Check if a global type is well-formed
///
/// Maps to F*:
/// ```fstar
/// val is_well_formed: global_type -> bool
/// ```
///
/// A global type is well-formed if:
/// 1. Sender and receiver are always different in messages, choices, and delegations
/// 2. Choice branches are non-empty (optional - currently not enforced)
/// 3. Recursion is guarded (contains at least one communication before recursion variable)
///
/// Returns true if the global type is well-formed, false otherwise.
pub fn is_well_formed(g: &GlobalType) -> bool {
    check_well_formed_inner(g, &[])
}

/// Inner well-formedness check with bound variable tracking
fn check_well_formed_inner(g: &GlobalType, bound_vars: &[GlobalVar]) -> bool {
    match g {
        GlobalType::End => true,

        GlobalType::Var(v) => {
            // Variable must be bound by an enclosing Rec
            bound_vars.contains(v)
        }

        GlobalType::Rec { var, body } => {
            // Add variable to bound set and check body
            let mut new_bound = bound_vars.to_vec();
            new_bound.push(*var);
            // Check that body is well-formed
            // Note: Guardedness (body must have communication before Var) is not enforced here
            check_well_formed_inner(body, &new_bound)
        }

        GlobalType::Message {
            sender,
            receiver,
            continuation,
            ..
        } => {
            // Sender and receiver must be different
            if sender == receiver {
                return false;
            }
            check_well_formed_inner(continuation, bound_vars)
        }

        GlobalType::Choice {
            sender,
            receiver,
            branches,
        } => {
            // Sender and receiver must be different
            if sender == receiver {
                return false;
            }
            // All branches must be well-formed
            branches
                .iter()
                .all(|(_, branch)| check_well_formed_inner(branch, bound_vars))
        }

        GlobalType::Parallel(g1, g2) => {
            // Both branches must be well-formed
            // Note: We don't check for disjoint participants here
            check_well_formed_inner(g1, bound_vars) && check_well_formed_inner(g2, bound_vars)
        }

        GlobalType::Delegation {
            delegator,
            receiver,
            delegated,
            continuation,
        } => {
            // Delegator and receiver must be different
            if delegator == receiver {
                return false;
            }
            check_well_formed_inner(delegated, bound_vars)
                && check_well_formed_inner(continuation, bound_vars)
        }
    }
}

// ============================================================================
// LocalType Methods
// ============================================================================

impl LocalType {
    /// End constant
    pub const END: Self = Self::End;

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
            Self::Throw { .. } => 4,
            Self::Catch { .. } => 5,
            Self::Rec { .. } => 6,
            Self::Var(_) => 7,
            Self::End => 8,
        }
    }

    /// Get free session variables in this type
    pub fn free_vars(&self) -> Vec<SessionVar> {
        self.free_vars_with_bound(&[])
    }

    /// Helper for computing free variables with bound context
    fn free_vars_with_bound(&self, bound: &[SessionVar]) -> Vec<SessionVar> {
        match self {
            Self::End => vec![],
            Self::Var(v) => {
                if bound.contains(v) {
                    vec![]
                } else {
                    vec![*v]
                }
            }
            Self::Rec { var, body } => {
                let mut new_bound = bound.to_vec();
                new_bound.push(*var);
                body.free_vars_with_bound(&new_bound)
            }
            Self::Send { continuation, .. } | Self::Recv { continuation, .. } => {
                continuation.free_vars_with_bound(bound)
            }
            Self::Select { branches, .. } | Self::Branch { branches, .. } => branches
                .iter()
                .flat_map(|(_, l)| l.free_vars_with_bound(bound))
                .collect(),
            Self::Throw {
                delegated,
                continuation,
                ..
            }
            | Self::Catch {
                delegated,
                continuation,
                ..
            } => {
                let mut vars = delegated.free_vars_with_bound(bound);
                vars.extend(continuation.free_vars_with_bound(bound));
                vars
            }
        }
    }

    /// Check if this local type is closed (no free variables)
    pub fn is_closed(&self) -> bool {
        self.free_vars().is_empty()
    }

    /// Create send type: `target!T. L`
    pub fn send(target: Participant, payload: BrrrType, cont: Self) -> Self {
        Self::Send {
            target,
            payload,
            continuation: Box::new(cont),
        }
    }

    /// Create receive type: `source?T. L`
    pub fn recv(source: Participant, payload: BrrrType, cont: Self) -> Self {
        Self::Recv {
            source,
            payload,
            continuation: Box::new(cont),
        }
    }

    /// Create select type: `target+{branches}`
    pub fn select(target: Participant, branches: Vec<(Label, Self)>) -> Self {
        Self::Select { target, branches }
    }

    /// Create branch type: `source&{branches}`
    pub fn branch(source: Participant, branches: Vec<(Label, Self)>) -> Self {
        Self::Branch { source, branches }
    }

    /// Create recursive type: `rec X. L`
    pub fn rec(var: SessionVar, body: Self) -> Self {
        Self::Rec {
            var,
            body: Box::new(body),
        }
    }

    /// Create variable reference
    pub const fn var(v: SessionVar) -> Self {
        Self::Var(v)
    }
}

impl Default for LocalType {
    fn default() -> Self {
        Self::End
    }
}

// ============================================================================
// Local Type Merging (for parallel composition)
// ============================================================================

/// Merge two local types for parallel composition.
///
/// When projecting `G1 | G2` to participant p, we need to merge p's local
/// views from both subprotocols. This is only defined when the local types
/// are compatible.
///
/// # Merging Rules
///
/// - `merge(End, L) = L` (identity left)
/// - `merge(L, End) = L` (identity right)
/// - `merge(L, L) = L` (idempotent)
/// - `merge(rec X.L1, rec X.L2) = rec X.merge(L1, L2)` (if vars match)
/// - `merge(Var X, Var X) = Var X`
/// - Otherwise: None (incompatible)
///
/// Maps to F*:
/// ```fstar
/// val merge_local: local_type -> local_type -> option local_type
/// ```
///
/// # Arguments
///
/// * `l1` - First local type to merge
/// * `l2` - Second local type to merge
///
/// # Returns
///
/// `Some(merged)` if types can be merged, `None` if incompatible.
pub fn merge_local(l1: &LocalType, l2: &LocalType) -> Option<LocalType> {
    // Optimization: if they're equal, return clone directly
    if l1 == l2 {
        return Some(l1.clone());
    }

    match (l1, l2) {
        // Identity: End is neutral element for merge
        (LocalType::End, other) => Some(other.clone()),
        (other, LocalType::End) => Some(other.clone()),

        // Variable merge: must be same variable
        (LocalType::Var(v1), LocalType::Var(v2)) if v1 == v2 => Some(LocalType::Var(*v1)),

        // Recursive type merge: merge bodies if variables match
        (
            LocalType::Rec { var: v1, body: b1 },
            LocalType::Rec { var: v2, body: b2 },
        ) if v1 == v2 => {
            let merged_body = merge_local(b1, b2)?;
            Some(LocalType::Rec {
                var: *v1,
                body: Box::new(merged_body),
            })
        }

        // Send merge: same target and payload, merge continuations
        (
            LocalType::Send {
                target: t1,
                payload: p1,
                continuation: c1,
            },
            LocalType::Send {
                target: t2,
                payload: p2,
                continuation: c2,
            },
        ) if t1 == t2 && p1 == p2 => {
            let merged_cont = merge_local(c1, c2)?;
            Some(LocalType::Send {
                target: *t1,
                payload: p1.clone(),
                continuation: Box::new(merged_cont),
            })
        }

        // Recv merge: same source and payload, merge continuations
        (
            LocalType::Recv {
                source: s1,
                payload: p1,
                continuation: c1,
            },
            LocalType::Recv {
                source: s2,
                payload: p2,
                continuation: c2,
            },
        ) if s1 == s2 && p1 == p2 => {
            let merged_cont = merge_local(c1, c2)?;
            Some(LocalType::Recv {
                source: *s1,
                payload: p1.clone(),
                continuation: Box::new(merged_cont),
            })
        }

        // Select merge: same target, merge branches
        (
            LocalType::Select {
                target: t1,
                branches: b1,
            },
            LocalType::Select {
                target: t2,
                branches: b2,
            },
        ) if t1 == t2 => {
            let merged_branches = merge_local_branches(b1, b2)?;
            Some(LocalType::Select {
                target: *t1,
                branches: merged_branches,
            })
        }

        // Branch merge: same source, merge branches
        (
            LocalType::Branch {
                source: s1,
                branches: b1,
            },
            LocalType::Branch {
                source: s2,
                branches: b2,
            },
        ) if s1 == s2 => {
            let merged_branches = merge_local_branches(b1, b2)?;
            Some(LocalType::Branch {
                source: *s1,
                branches: merged_branches,
            })
        }

        // Throw merge: same target, merge delegated and continuation
        (
            LocalType::Throw {
                target: t1,
                delegated: d1,
                continuation: c1,
            },
            LocalType::Throw {
                target: t2,
                delegated: d2,
                continuation: c2,
            },
        ) if t1 == t2 => {
            let merged_del = merge_local(d1, d2)?;
            let merged_cont = merge_local(c1, c2)?;
            Some(LocalType::Throw {
                target: *t1,
                delegated: Box::new(merged_del),
                continuation: Box::new(merged_cont),
            })
        }

        // Catch merge: same source, merge delegated and continuation
        (
            LocalType::Catch {
                source: s1,
                delegated: d1,
                continuation: c1,
            },
            LocalType::Catch {
                source: s2,
                delegated: d2,
                continuation: c2,
            },
        ) if s1 == s2 => {
            let merged_del = merge_local(d1, d2)?;
            let merged_cont = merge_local(c1, c2)?;
            Some(LocalType::Catch {
                source: *s1,
                delegated: Box::new(merged_del),
                continuation: Box::new(merged_cont),
            })
        }

        // All other combinations are incompatible
        _ => None,
    }
}

/// Merge two sets of local type branches.
///
/// Both sets must have exactly the same labels, and each pair of branches
/// with the same label must be mergeable.
fn merge_local_branches(
    b1: &[(Label, LocalType)],
    b2: &[(Label, LocalType)],
) -> Option<Vec<(Label, LocalType)>> {
    // Must have same number of branches
    if b1.len() != b2.len() {
        return None;
    }

    // Build a map from b2 for lookup
    let b2_map: HashMap<Label, &LocalType> = b2.iter().map(|(l, t)| (*l, t)).collect();

    // Merge each branch from b1 with corresponding branch from b2
    let mut result = Vec::with_capacity(b1.len());
    for (label, l1_type) in b1 {
        let l2_type = b2_map.get(label)?;
        let merged = merge_local(l1_type, l2_type)?;
        result.push((*label, merged));
    }

    // Verify b2 has no extra labels
    if b2.iter().any(|(l, _)| !b1.iter().any(|(l1, _)| l1 == l)) {
        return None;
    }

    Some(result)
}

// ============================================================================
// Projection Helpers
// ============================================================================

impl GlobalType {
    /// Project all branches of a choice and return the projected branches.
    ///
    /// This is a helper for projecting `GChoice` to a participant.
    /// Returns `None` if any branch fails to project.
    ///
    /// Maps to F*:
    /// ```fstar
    /// val project_branches: list (label & global_type) -> participant -> option (list (label & local_type))
    /// ```
    pub fn project_branches(
        branches: &[(Label, GlobalType)],
        p: Participant,
    ) -> Option<Vec<(Label, LocalType)>> {
        branches
            .iter()
            .map(|(label, g)| g.project(p).map(|l| (*label, l)))
            .collect()
    }

    /// Check if projection is defined for a participant without building the result.
    ///
    /// This is more efficient than calling `project()` when you only need to know
    /// if projection succeeds, not what the result is.
    ///
    /// Maps to F*:
    /// ```fstar
    /// val is_projectable: global_type -> participant -> bool
    /// ```
    ///
    /// # Arguments
    ///
    /// * `p` - The participant to check projection for
    ///
    /// # Returns
    ///
    /// `true` if `project(self, p)` would return `Some(_)`, `false` otherwise.
    pub fn is_projectable(&self, p: Participant) -> bool {
        self.is_projectable_inner(p, &mut HashMap::new())
    }

    fn is_projectable_inner(
        &self,
        p: Participant,
        var_map: &mut HashMap<GlobalVar, SessionVar>,
    ) -> bool {
        match self {
            Self::End => true,
            Self::Var(_) => true, // Variables are always projectable

            Self::Rec { var, body } => {
                let local_var = SessionVar(var.0);
                var_map.insert(*var, local_var);
                body.is_projectable_inner(p, var_map)
            }

            Self::Message { continuation, .. } => continuation.is_projectable_inner(p, var_map),

            Self::Choice {
                sender,
                receiver,
                branches,
            } => {
                // All branches must be projectable
                let all_projectable = branches.iter().all(|(_, g)| {
                    let mut branch_var_map = var_map.clone();
                    g.is_projectable_inner(p, &mut branch_var_map)
                });

                if !all_projectable {
                    return false;
                }

                // If participant is sender or receiver, projection is always defined
                if p == *sender || p == *receiver {
                    return true;
                }

                // For uninvolved participants, all branch projections must be equal
                // We need to actually project to check this
                let projected: Option<Vec<LocalType>> = branches
                    .iter()
                    .map(|(_, g)| {
                        let mut branch_var_map = var_map.clone();
                        g.project_inner(p, &mut branch_var_map)
                    })
                    .collect();

                match projected {
                    None => false,
                    Some(projections) => {
                        if projections.is_empty() {
                            true
                        } else {
                            let first = &projections[0];
                            projections.iter().all(|proj| proj == first)
                        }
                    }
                }
            }

            Self::Parallel(g1, g2) => {
                let l1_projectable = g1.is_projectable_inner(p, var_map);
                let l2_projectable = g2.is_projectable_inner(p, var_map);

                if !l1_projectable || !l2_projectable {
                    return false;
                }

                // Need to check if merge would succeed
                let l1 = g1.project_inner(p, var_map);
                let l2 = g2.project_inner(p, var_map);

                match (l1, l2) {
                    (Some(l1), Some(l2)) => {
                        l1.is_end() || l2.is_end() || merge_local(&l1, &l2).is_some()
                    }
                    _ => false,
                }
            }

            Self::Delegation {
                delegated,
                continuation,
                ..
            } => {
                delegated.is_projectable_inner(p, var_map)
                    && continuation.is_projectable_inner(p, var_map)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        get_participants, is_well_formed, merge_local, GTypeVar, GlobalType, GlobalVar, LocalType,
        Participant, SessionVar,
    };
    use crate::types::{BrrrType, PrimKind};
    use lasso::Rodeo;

    fn make_participants(rodeo: &mut Rodeo) -> (Participant, Participant, Participant) {
        let alice = Participant(rodeo.get_or_intern("Alice"));
        let bob = Participant(rodeo.get_or_intern("Bob"));
        let carol = Participant(rodeo.get_or_intern("Carol"));
        (alice, bob, carol)
    }

    #[test]
    fn test_global_type_construction() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let g = GlobalType::message(
            alice,
            bob,
            BrrrType::Prim(PrimKind::Bool),
            GlobalType::End,
        );

        assert!(!g.is_end());
        assert!(!g.is_recursive());
    }

    #[test]
    fn test_global_type_participants() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let g = GlobalType::message(
            alice,
            bob,
            BrrrType::BOOL,
            GlobalType::message(bob, carol, BrrrType::STRING, GlobalType::End),
        );

        let participants = g.participants();
        assert_eq!(participants.len(), 3);
    }

    #[test]
    fn test_projection_sender() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let g = GlobalType::message(
            alice,
            bob,
            BrrrType::Prim(PrimKind::Bool),
            GlobalType::End,
        );

        let alice_local = g.project(alice).expect("projection should succeed");
        match alice_local {
            LocalType::Send { target, .. } => {
                assert_eq!(target, bob);
            }
            _ => panic!("Expected Send for sender, got {:?}", alice_local),
        }
    }

    #[test]
    fn test_projection_receiver() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let g = GlobalType::message(
            alice,
            bob,
            BrrrType::Prim(PrimKind::Bool),
            GlobalType::End,
        );

        let bob_local = g.project(bob).expect("projection should succeed");
        match bob_local {
            LocalType::Recv { source, .. } => {
                assert_eq!(source, alice);
            }
            _ => panic!("Expected Recv for receiver, got {:?}", bob_local),
        }
    }

    #[test]
    fn test_projection_uninvolved() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        // Carol is not involved in Alice -> Bob message
        let g = GlobalType::message(
            alice,
            bob,
            BrrrType::Prim(PrimKind::Bool),
            GlobalType::End,
        );

        let carol_local = g.project(carol).expect("projection should succeed");
        assert!(carol_local.is_end(), "Uninvolved participant should get End");
    }

    #[test]
    fn test_projection_chain() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        // Protocol: Alice -> Bob: Bool. Bob -> Carol: Int. end
        let g = GlobalType::message(
            alice,
            bob,
            BrrrType::BOOL,
            GlobalType::message(
                bob,
                carol,
                BrrrType::STRING,
                GlobalType::End,
            ),
        );

        // Alice: Send to Bob, then End
        let alice_local = g.project(alice).expect("alice projection");
        match &alice_local {
            LocalType::Send { target, continuation, .. } => {
                assert_eq!(*target, bob);
                assert!(continuation.is_end());
            }
            _ => panic!("Expected Send for Alice"),
        }

        // Bob: Recv from Alice, then Send to Carol
        let bob_local = g.project(bob).expect("bob projection");
        match &bob_local {
            LocalType::Recv { source, continuation, .. } => {
                assert_eq!(*source, alice);
                match continuation.as_ref() {
                    LocalType::Send { target, .. } => assert_eq!(*target, carol),
                    _ => panic!("Expected Send continuation for Bob"),
                }
            }
            _ => panic!("Expected Recv for Bob"),
        }

        // Carol: Recv from Bob
        let carol_local = g.project(carol).expect("carol projection");
        match &carol_local {
            LocalType::Recv { source, continuation, .. } => {
                assert_eq!(*source, bob);
                assert!(continuation.is_end());
            }
            _ => panic!("Expected Recv for Carol"),
        }
    }

    #[test]
    fn test_projection_choice_sender() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        let g = GlobalType::choice(
            alice,
            bob,
            vec![
                (label_ok, GlobalType::End),
                (label_err, GlobalType::End),
            ],
        );

        let alice_local = g.project(alice).expect("alice projection");
        match alice_local {
            LocalType::Select { target, branches } => {
                assert_eq!(target, bob);
                assert_eq!(branches.len(), 2);
            }
            _ => panic!("Expected Select for sender"),
        }
    }

    #[test]
    fn test_projection_choice_receiver() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        let g = GlobalType::choice(
            alice,
            bob,
            vec![
                (label_ok, GlobalType::End),
                (label_err, GlobalType::End),
            ],
        );

        let bob_local = g.project(bob).expect("bob projection");
        match bob_local {
            LocalType::Branch { source, branches } => {
                assert_eq!(source, alice);
                assert_eq!(branches.len(), 2);
            }
            _ => panic!("Expected Branch for receiver"),
        }
    }

    #[test]
    fn test_projection_choice_uninvolved_consistent() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        // Both branches lead to same continuation for Carol
        let g = GlobalType::choice(
            alice,
            bob,
            vec![
                (label_ok, GlobalType::End),
                (label_err, GlobalType::End),
            ],
        );

        // Carol is not involved, both branches project to End
        let carol_local = g.project(carol).expect("carol projection should succeed");
        assert!(carol_local.is_end());
    }

    #[test]
    fn test_projection_choice_uninvolved_inconsistent() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        // Branches have DIFFERENT continuations for Carol (inconsistent)
        let g = GlobalType::choice(
            alice,
            bob,
            vec![
                // In "ok" branch, Carol receives from Bob
                (label_ok, GlobalType::message(bob, carol, BrrrType::BOOL, GlobalType::End)),
                // In "err" branch, Carol does nothing
                (label_err, GlobalType::End),
            ],
        );

        // Carol's projection should FAIL because branches are inconsistent
        let result = g.project(carol);
        assert!(result.is_none(), "Inconsistent branches should fail projection");
    }

    #[test]
    fn test_projection_recursive() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let var = GlobalVar::new(0);
        let g = GlobalType::rec(
            var,
            GlobalType::message(
                alice,
                bob,
                BrrrType::BOOL,
                GlobalType::var(var),
            ),
        );

        let alice_local = g.project(alice).expect("alice projection");
        match &alice_local {
            LocalType::Rec { var: local_var, body } => {
                assert_eq!(local_var.0, 0);
                match body.as_ref() {
                    LocalType::Send { continuation, .. } => {
                        match continuation.as_ref() {
                            LocalType::Var(v) => assert_eq!(v.0, 0),
                            _ => panic!("Expected Var in continuation"),
                        }
                    }
                    _ => panic!("Expected Send in recursive body"),
                }
            }
            _ => panic!("Expected Rec for recursive protocol"),
        }
    }

    #[test]
    fn test_projection_delegation_delegator() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        // Alice delegates a session (Alice-Carol protocol) to Bob
        let delegated = GlobalType::message(alice, carol, BrrrType::BOOL, GlobalType::End);

        let g = GlobalType::delegation(alice, bob, delegated, GlobalType::End);

        let alice_local = g.project(alice).expect("alice projection");
        match alice_local {
            LocalType::Throw { target, .. } => {
                assert_eq!(target, bob);
            }
            _ => panic!("Expected Throw for delegator"),
        }
    }

    #[test]
    fn test_projection_delegation_receiver() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let delegated = GlobalType::message(alice, carol, BrrrType::BOOL, GlobalType::End);

        let g = GlobalType::delegation(alice, bob, delegated, GlobalType::End);

        let bob_local = g.project(bob).expect("bob projection");
        match bob_local {
            LocalType::Catch { source, .. } => {
                assert_eq!(source, alice);
            }
            _ => panic!("Expected Catch for delegation receiver"),
        }
    }

    #[test]
    fn test_local_type_predicates() {
        assert!(LocalType::End.is_end());
        assert!(!LocalType::End.is_send());

        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        let send = LocalType::send(p, BrrrType::BOOL, LocalType::End);
        assert!(send.is_send());
        assert!(!send.is_recv());
        assert!(!send.is_end());

        let recv = LocalType::recv(p, BrrrType::BOOL, LocalType::End);
        assert!(recv.is_recv());
        assert!(!recv.is_send());
    }

    #[test]
    fn test_global_type_default() {
        let g: GlobalType = Default::default();
        assert!(g.is_end());
    }

    #[test]
    fn test_local_type_default() {
        let l: LocalType = Default::default();
        assert!(l.is_end());
    }

    #[test]
    fn test_global_type_discriminant() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let types = [
            GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End),
            GlobalType::choice(alice, bob, vec![]),
            GlobalType::parallel(GlobalType::End, GlobalType::End),
            GlobalType::delegation(alice, bob, GlobalType::End, GlobalType::End),
            GlobalType::rec(GlobalVar::new(0), GlobalType::End),
            GlobalType::var(GlobalVar::new(0)),
            GlobalType::End,
        ];

        let discriminants: Vec<u8> = types.iter().map(|t| t.discriminant()).collect();
        let unique: std::collections::HashSet<u8> = discriminants.iter().copied().collect();
        assert_eq!(discriminants.len(), unique.len(), "Global discriminants must be unique");

        // Verify specific values
        assert_eq!(GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End).discriminant(), 0);
        assert_eq!(GlobalType::End.discriminant(), 6);
    }

    #[test]
    fn test_local_type_discriminant() {
        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        let types = [
            LocalType::send(p, BrrrType::BOOL, LocalType::End),
            LocalType::recv(p, BrrrType::BOOL, LocalType::End),
            LocalType::select(p, vec![]),
            LocalType::branch(p, vec![]),
            LocalType::Throw { target: p, delegated: Box::new(LocalType::End), continuation: Box::new(LocalType::End) },
            LocalType::Catch { source: p, delegated: Box::new(LocalType::End), continuation: Box::new(LocalType::End) },
            LocalType::rec(SessionVar(0), LocalType::End),
            LocalType::var(SessionVar(0)),
            LocalType::End,
        ];

        let discriminants: Vec<u8> = types.iter().map(|t| t.discriminant()).collect();
        let unique: std::collections::HashSet<u8> = discriminants.iter().copied().collect();
        assert_eq!(discriminants.len(), unique.len(), "Local discriminants must be unique");

        // Verify specific values
        assert_eq!(LocalType::send(p, BrrrType::BOOL, LocalType::End).discriminant(), 0);
        assert_eq!(LocalType::End.discriminant(), 8);
    }

    #[test]
    fn test_global_type_free_vars() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let var0 = GlobalVar::new(0);
        let var1 = GlobalVar::new(1);

        // End has no free vars
        assert!(GlobalType::End.free_vars().is_empty());

        // Free variable
        let g = GlobalType::Var(var0);
        assert_eq!(g.free_vars(), vec![var0]);
        assert!(!g.is_closed());

        // Bound variable
        let g = GlobalType::rec(var0, GlobalType::Var(var0));
        assert!(g.free_vars().is_empty());
        assert!(g.is_closed());

        // Mixed: var1 free, var0 bound
        let g = GlobalType::rec(
            var0,
            GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::Var(var1)),
        );
        assert_eq!(g.free_vars(), vec![var1]);
        assert!(!g.is_closed());
    }

    #[test]
    fn test_local_type_free_vars() {
        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        let var0 = SessionVar(0);
        let var1 = SessionVar(1);

        // End has no free vars
        assert!(LocalType::End.free_vars().is_empty());

        // Free variable
        let l = LocalType::Var(var0);
        assert_eq!(l.free_vars(), vec![var0]);
        assert!(!l.is_closed());

        // Bound variable
        let l = LocalType::rec(var0, LocalType::Var(var0));
        assert!(l.free_vars().is_empty());
        assert!(l.is_closed());

        // Mixed
        let l = LocalType::rec(
            var0,
            LocalType::send(p, BrrrType::BOOL, LocalType::Var(var1)),
        );
        assert_eq!(l.free_vars(), vec![var1]);
        assert!(!l.is_closed());
    }

    #[test]
    fn test_check_distinct_endpoints() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        // Valid: sender != receiver
        let valid = GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End);
        assert!(valid.check_distinct_endpoints().is_none());

        // Invalid: sender == receiver in message
        let invalid = GlobalType::message(alice, alice, BrrrType::BOOL, GlobalType::End);
        assert!(invalid.check_distinct_endpoints().is_some());

        // Invalid: sender == receiver in choice
        let label = rodeo.get_or_intern("ok");
        let invalid_choice = GlobalType::choice(
            bob,
            bob,
            vec![(label, GlobalType::End)],
        );
        assert!(invalid_choice.check_distinct_endpoints().is_some());

        // Invalid: delegator == receiver
        let invalid_deleg = GlobalType::delegation(
            alice,
            alice,
            GlobalType::End,
            GlobalType::End,
        );
        assert!(invalid_deleg.check_distinct_endpoints().is_some());

        // Valid parallel
        let valid_par = GlobalType::parallel(
            GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End),
            GlobalType::End,
        );
        assert!(valid_par.check_distinct_endpoints().is_none());
    }

    #[test]
    fn test_global_type_predicates() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let msg = GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End);
        assert!(msg.is_message());
        assert!(!msg.is_end());
        assert!(!msg.is_choice());

        let choice = GlobalType::choice(alice, bob, vec![]);
        assert!(choice.is_choice());
        assert!(!choice.is_message());

        let par = GlobalType::parallel(GlobalType::End, GlobalType::End);
        assert!(par.is_parallel());

        let deleg = GlobalType::delegation(alice, bob, GlobalType::End, GlobalType::End);
        assert!(deleg.is_delegation());
    }

    // ========================================================================
    // Tests for standalone functions
    // ========================================================================

    #[test]
    fn test_get_participants_empty() {
        let participants = get_participants(&GlobalType::End);
        assert!(participants.is_empty());
    }

    #[test]
    fn test_get_participants_message() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let g = GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End);
        let participants = get_participants(&g);

        assert_eq!(participants.len(), 2);
        assert!(participants.contains(&alice));
        assert!(participants.contains(&bob));
    }

    #[test]
    fn test_get_participants_chain() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let g = GlobalType::message(
            alice,
            bob,
            BrrrType::BOOL,
            GlobalType::message(bob, carol, BrrrType::STRING, GlobalType::End),
        );
        let participants = get_participants(&g);

        assert_eq!(participants.len(), 3);
        assert!(participants.contains(&alice));
        assert!(participants.contains(&bob));
        assert!(participants.contains(&carol));
    }

    #[test]
    fn test_get_participants_choice() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        let g = GlobalType::choice(
            alice,
            bob,
            vec![
                (label_ok, GlobalType::message(bob, carol, BrrrType::BOOL, GlobalType::End)),
                (label_err, GlobalType::End),
            ],
        );
        let participants = get_participants(&g);

        assert_eq!(participants.len(), 3);
        assert!(participants.contains(&alice));
        assert!(participants.contains(&bob));
        assert!(participants.contains(&carol));
    }

    #[test]
    fn test_get_participants_parallel() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let g = GlobalType::parallel(
            GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End),
            GlobalType::message(bob, carol, BrrrType::STRING, GlobalType::End),
        );
        let participants = get_participants(&g);

        assert_eq!(participants.len(), 3);
    }

    #[test]
    fn test_get_participants_delegation() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let g = GlobalType::delegation(
            alice,
            bob,
            GlobalType::message(alice, carol, BrrrType::BOOL, GlobalType::End),
            GlobalType::End,
        );
        let participants = get_participants(&g);

        assert_eq!(participants.len(), 3);
        assert!(participants.contains(&alice));
        assert!(participants.contains(&bob));
        assert!(participants.contains(&carol));
    }

    #[test]
    fn test_get_participants_recursive() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let var = GlobalVar::new(0);
        let g = GlobalType::rec(
            var,
            GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::var(var)),
        );
        let participants = get_participants(&g);

        assert_eq!(participants.len(), 2);
        assert!(participants.contains(&alice));
        assert!(participants.contains(&bob));
    }

    #[test]
    fn test_is_well_formed_end() {
        assert!(is_well_formed(&GlobalType::End));
    }

    #[test]
    fn test_is_well_formed_valid_message() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let g = GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End);
        assert!(is_well_formed(&g));
    }

    #[test]
    fn test_is_well_formed_invalid_self_message() {
        let mut rodeo = Rodeo::default();
        let alice = Participant(rodeo.get_or_intern("Alice"));

        // Sending to self is not allowed
        let g = GlobalType::message(alice, alice, BrrrType::BOOL, GlobalType::End);
        assert!(!is_well_formed(&g));
    }

    #[test]
    fn test_is_well_formed_invalid_self_choice() {
        let mut rodeo = Rodeo::default();
        let alice = Participant(rodeo.get_or_intern("Alice"));
        let label = rodeo.get_or_intern("ok");

        // Choice sender == receiver is not allowed
        let g = GlobalType::choice(alice, alice, vec![(label, GlobalType::End)]);
        assert!(!is_well_formed(&g));
    }

    #[test]
    fn test_is_well_formed_invalid_self_delegation() {
        let mut rodeo = Rodeo::default();
        let alice = Participant(rodeo.get_or_intern("Alice"));

        // Delegating to self is not allowed
        let g = GlobalType::delegation(alice, alice, GlobalType::End, GlobalType::End);
        assert!(!is_well_formed(&g));
    }

    #[test]
    fn test_is_well_formed_recursive_valid() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let var = GlobalVar::new(0);
        let g = GlobalType::rec(
            var,
            GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::var(var)),
        );
        assert!(is_well_formed(&g));
    }

    #[test]
    fn test_is_well_formed_unbound_var() {
        // Variable without enclosing Rec is not well-formed
        let g = GlobalType::var(GlobalVar::new(0));
        assert!(!is_well_formed(&g));
    }

    #[test]
    fn test_is_well_formed_nested_invalid() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        // Valid outer, but contains invalid inner (self-message)
        let g = GlobalType::message(
            alice,
            bob,
            BrrrType::BOOL,
            GlobalType::message(bob, bob, BrrrType::STRING, GlobalType::End), // Invalid!
        );
        assert!(!is_well_formed(&g));
    }

    #[test]
    fn test_is_well_formed_parallel_both_valid() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let g = GlobalType::parallel(
            GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End),
            GlobalType::message(bob, carol, BrrrType::STRING, GlobalType::End),
        );
        assert!(is_well_formed(&g));
    }

    #[test]
    fn test_is_well_formed_parallel_one_invalid() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let g = GlobalType::parallel(
            GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End),
            GlobalType::message(bob, bob, BrrrType::STRING, GlobalType::End), // Invalid!
        );
        assert!(!is_well_formed(&g));
    }

    #[test]
    fn test_is_well_formed_choice_all_branches() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        let g = GlobalType::choice(
            alice,
            bob,
            vec![
                (label_ok, GlobalType::message(bob, alice, BrrrType::BOOL, GlobalType::End)),
                (label_err, GlobalType::End),
            ],
        );
        assert!(is_well_formed(&g));
    }

    #[test]
    fn test_is_well_formed_choice_invalid_branch() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        let g = GlobalType::choice(
            alice,
            bob,
            vec![
                (label_ok, GlobalType::End),
                (label_err, GlobalType::message(bob, bob, BrrrType::BOOL, GlobalType::End)), // Invalid!
            ],
        );
        assert!(!is_well_formed(&g));
    }

    #[test]
    fn test_gtype_var_alias() {
        // Verify that GTypeVar is an alias for GlobalVar
        let v1: GTypeVar = GlobalVar::new(42);
        let v2: GlobalVar = GTypeVar::new(42);
        assert_eq!(v1, v2);
        assert_eq!(v1.index(), 42);
    }

    // ========================================================================
    // Tests for merge_local
    // ========================================================================

    #[test]
    fn test_merge_local_identity_end() {
        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        let l = LocalType::send(p, BrrrType::BOOL, LocalType::End);

        // merge(End, L) = L
        let merged = merge_local(&LocalType::End, &l).expect("should merge");
        assert_eq!(merged, l);

        // merge(L, End) = L
        let merged = merge_local(&l, &LocalType::End).expect("should merge");
        assert_eq!(merged, l);
    }

    #[test]
    fn test_merge_local_idempotent() {
        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        let l = LocalType::send(p, BrrrType::BOOL, LocalType::End);

        // merge(L, L) = L
        let merged = merge_local(&l, &l).expect("should merge");
        assert_eq!(merged, l);
    }

    #[test]
    fn test_merge_local_var_same() {
        let v = SessionVar(0);
        let l1 = LocalType::Var(v);
        let l2 = LocalType::Var(v);

        let merged = merge_local(&l1, &l2).expect("should merge");
        assert_eq!(merged, LocalType::Var(v));
    }

    #[test]
    fn test_merge_local_var_different() {
        let l1 = LocalType::Var(SessionVar(0));
        let l2 = LocalType::Var(SessionVar(1));

        // Different variables cannot be merged
        let result = merge_local(&l1, &l2);
        assert!(result.is_none());
    }

    #[test]
    fn test_merge_local_rec_same_var() {
        let v = SessionVar(0);
        let body = LocalType::Var(v);
        let l1 = LocalType::rec(v, body.clone());
        let l2 = LocalType::rec(v, body);

        let merged = merge_local(&l1, &l2).expect("should merge");
        assert!(matches!(merged, LocalType::Rec { var, .. } if var == v));
    }

    #[test]
    fn test_merge_local_rec_different_var() {
        let v1 = SessionVar(0);
        let v2 = SessionVar(1);
        let l1 = LocalType::rec(v1, LocalType::Var(v1));
        let l2 = LocalType::rec(v2, LocalType::Var(v2));

        // Different variables cannot be merged
        let result = merge_local(&l1, &l2);
        assert!(result.is_none());
    }

    #[test]
    fn test_merge_local_send_compatible() {
        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        // Same target and payload, End continuations
        let l1 = LocalType::send(p, BrrrType::BOOL, LocalType::End);
        let l2 = LocalType::send(p, BrrrType::BOOL, LocalType::End);

        let merged = merge_local(&l1, &l2).expect("should merge");
        match merged {
            LocalType::Send { target, payload, .. } => {
                assert_eq!(target, p);
                assert_eq!(payload, BrrrType::BOOL);
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_merge_local_send_incompatible_target() {
        let mut rodeo = Rodeo::default();
        let p1 = Participant(rodeo.get_or_intern("P1"));
        let p2 = Participant(rodeo.get_or_intern("P2"));

        let l1 = LocalType::send(p1, BrrrType::BOOL, LocalType::End);
        let l2 = LocalType::send(p2, BrrrType::BOOL, LocalType::End);

        // Different targets cannot be merged
        let result = merge_local(&l1, &l2);
        assert!(result.is_none());
    }

    #[test]
    fn test_merge_local_send_incompatible_payload() {
        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        let l1 = LocalType::send(p, BrrrType::BOOL, LocalType::End);
        let l2 = LocalType::send(p, BrrrType::STRING, LocalType::End);

        // Different payloads cannot be merged
        let result = merge_local(&l1, &l2);
        assert!(result.is_none());
    }

    #[test]
    fn test_merge_local_incompatible_types() {
        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        let l1 = LocalType::send(p, BrrrType::BOOL, LocalType::End);
        let l2 = LocalType::recv(p, BrrrType::BOOL, LocalType::End);

        // Send and Recv cannot be merged
        let result = merge_local(&l1, &l2);
        assert!(result.is_none());
    }

    // ========================================================================
    // Tests for project_branches
    // ========================================================================

    #[test]
    fn test_project_branches_empty() {
        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        let branches: Vec<(lasso::Spur, GlobalType)> = vec![];
        let projected = GlobalType::project_branches(&branches, p).expect("should project");
        assert!(projected.is_empty());
    }

    #[test]
    fn test_project_branches_simple() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);
        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        let branches = vec![
            (label_ok, GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End)),
            (label_err, GlobalType::End),
        ];

        // Project for Alice (sender in ok branch)
        let projected = GlobalType::project_branches(&branches, alice).expect("should project");
        assert_eq!(projected.len(), 2);

        // Check ok branch projects to Send
        let (ok_label, ok_local) = &projected[0];
        assert_eq!(*ok_label, label_ok);
        assert!(matches!(ok_local, LocalType::Send { .. }));

        // Check err branch projects to End
        let (err_label, err_local) = &projected[1];
        assert_eq!(*err_label, label_err);
        assert!(err_local.is_end());
    }

    // ========================================================================
    // Tests for is_projectable
    // ========================================================================

    #[test]
    fn test_is_projectable_end() {
        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        assert!(GlobalType::End.is_projectable(p));
    }

    #[test]
    fn test_is_projectable_var() {
        let mut rodeo = Rodeo::default();
        let p = Participant(rodeo.get_or_intern("P"));

        assert!(GlobalType::var(GlobalVar::new(0)).is_projectable(p));
    }

    #[test]
    fn test_is_projectable_message() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let g = GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End);

        // All participants can project
        assert!(g.is_projectable(alice));
        assert!(g.is_projectable(bob));
        assert!(g.is_projectable(carol));
    }

    #[test]
    fn test_is_projectable_choice_consistent() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        // Both branches are consistent for Carol (both End)
        let g = GlobalType::choice(
            alice,
            bob,
            vec![
                (label_ok, GlobalType::End),
                (label_err, GlobalType::End),
            ],
        );

        assert!(g.is_projectable(alice));
        assert!(g.is_projectable(bob));
        assert!(g.is_projectable(carol));
    }

    #[test]
    fn test_is_projectable_choice_inconsistent() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        // Branches are inconsistent for Carol
        let g = GlobalType::choice(
            alice,
            bob,
            vec![
                (label_ok, GlobalType::message(bob, carol, BrrrType::BOOL, GlobalType::End)),
                (label_err, GlobalType::End),
            ],
        );

        // Alice and Bob can project (they're sender/receiver)
        assert!(g.is_projectable(alice));
        assert!(g.is_projectable(bob));
        // Carol cannot project (inconsistent branches)
        assert!(!g.is_projectable(carol));
    }

    #[test]
    fn test_is_projectable_parallel_one_end() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        // Alice only appears in g1
        let g = GlobalType::parallel(
            GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::End),
            GlobalType::End,
        );

        assert!(g.is_projectable(alice));
        assert!(g.is_projectable(bob));
    }

    #[test]
    fn test_is_projectable_recursive() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, _) = make_participants(&mut rodeo);

        let var = GlobalVar::new(0);
        let g = GlobalType::rec(
            var,
            GlobalType::message(alice, bob, BrrrType::BOOL, GlobalType::var(var)),
        );

        assert!(g.is_projectable(alice));
        assert!(g.is_projectable(bob));
    }

    #[test]
    fn test_is_projectable_delegation() {
        let mut rodeo = Rodeo::default();
        let (alice, bob, carol) = make_participants(&mut rodeo);

        let delegated = GlobalType::message(alice, carol, BrrrType::BOOL, GlobalType::End);
        let g = GlobalType::delegation(alice, bob, delegated, GlobalType::End);

        assert!(g.is_projectable(alice));
        assert!(g.is_projectable(bob));
        assert!(g.is_projectable(carol));
    }
}
