//! Binary session types (two-party communication)
//!
//! Mirrors F* SessionTypes.fsti for typed communication protocols.
//!
//! Session types ensure that:
//! - When one party sends, the other must receive
//! - Select/branch choices are compatible
//! - Recursive protocols are well-formed
//! - Communication terminates correctly
//!
//! # Notation
//! - `!T.S` - Send type T then continue with S
//! - `?T.S` - Receive type T then continue with S
//! - `+{l1: S1, l2: S2}` - Internal choice (select)
//! - `&{l1: S1, l2: S2}` - External choice (branch/offer)
//! - `end` - Session termination
//! - `rec X.S` - Recursive session type

use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};

use lasso::Spur;
use serde::{Deserialize, Serialize};

use crate::types::BrrrType;

/// Session type variable identifier (for recursive types)
///
/// Used in `rec X.S` and `X` constructs for mu-types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SessionVar(pub u32);

impl SessionVar {
    /// Create a new session variable with the given index
    pub const fn new(idx: u32) -> Self {
        Self(idx)
    }

    /// Get the variable index
    pub const fn index(self) -> u32 {
        self.0
    }
}

impl From<u32> for SessionVar {
    fn from(idx: u32) -> Self {
        Self(idx)
    }
}

/// Label for select/branch operations
///
/// Interned string for efficient comparison.
pub type Label = Spur;

/// Binary session type - typed two-party communication protocol
///
/// Maps to F*:
/// ```fstar
/// noeq type session_type =
///   | SSend   : payload:brrr_type -> continuation:session_type -> session_type
///   | SRecv   : payload:brrr_type -> continuation:session_type -> session_type
///   | SSelect : branches:list (label & session_type) -> session_type
///   | SBranch : branches:list (label & session_type) -> session_type
///   | SRec    : var:session_var -> body:session_type -> session_type
///   | SVar    : var:session_var -> session_type
///   | SEnd    : session_type
/// ```
///
/// # Duality
/// Session types come in dual pairs:
/// - `Send` is dual to `Recv`
/// - `Select` is dual to `Branch`
/// - `End` is self-dual
/// - Recursive types maintain duality through the body
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum SessionType {
    /// Send payload then continue: `!T.S`
    ///
    /// The sender transmits a value of type `payload`, then continues
    /// with the `continuation` session type.
    Send {
        payload: BrrrType,
        continuation: Box<SessionType>,
    },

    /// Receive payload then continue: `?T.S`
    ///
    /// The receiver expects a value of type `payload`, then continues
    /// with the `continuation` session type.
    Recv {
        payload: BrrrType,
        continuation: Box<SessionType>,
    },

    /// Internal choice (select): `+{l1: S1, l2: S2, ...}`
    ///
    /// The sender chooses one branch label and continues with that session.
    /// The receiver must handle all possible choices (via `Branch`).
    Select(Vec<(Label, SessionType)>),

    /// External choice (branch/offer): `&{l1: S1, l2: S2, ...}`
    ///
    /// The receiver offers multiple continuations, and the sender picks one.
    /// All branches must be handled.
    Branch(Vec<(Label, SessionType)>),

    /// Recursive type: `rec X.S` (mu-type)
    ///
    /// Defines a recursive session type where `var` can appear in `body`.
    /// Enables infinite/looping protocols.
    Rec {
        var: SessionVar,
        body: Box<SessionType>,
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

impl SessionType {
    /// End session constant
    pub const END: Self = Self::End;

    /// Create send type: `!T.S`
    pub fn send(payload: BrrrType, cont: Self) -> Self {
        Self::Send {
            payload,
            continuation: Box::new(cont),
        }
    }

    /// Create receive type: `?T.S`
    pub fn recv(payload: BrrrType, cont: Self) -> Self {
        Self::Recv {
            payload,
            continuation: Box::new(cont),
        }
    }

    /// Create select type: `+{l1: S1, l2: S2, ...}`
    pub fn select(branches: Vec<(Label, Self)>) -> Self {
        Self::Select(branches)
    }

    /// Create branch type: `&{l1: S1, l2: S2, ...}`
    pub fn branch(branches: Vec<(Label, Self)>) -> Self {
        Self::Branch(branches)
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
        matches!(self, Self::Select(_) | Self::Branch(_))
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
            Self::Select(_) => 2,
            Self::Branch(_) => 3,
            Self::Rec { .. } => 4,
            Self::Var(_) => 5,
            Self::End => 6,
        }
    }

    /// Compute the dual (co-type) of a session type
    ///
    /// Duality swaps the direction of communication:
    /// - `dual(!T.S) = ?T.dual(S)`
    /// - `dual(?T.S) = !T.dual(S)`
    /// - `dual(+{...}) = &{...}` (with dual branches)
    /// - `dual(&{...}) = +{...}` (with dual branches)
    /// - `dual(end) = end`
    /// - `dual(rec X.S) = rec X.dual(S)`
    /// - `dual(X) = X`
    ///
    /// This is CRITICAL for type-safe channel pairing.
    ///
    /// # Examples
    /// - `dual(!Int.end) = ?Int.end`
    /// - `dual(+{ok: S1, err: S2}) = &{ok: dual(S1), err: dual(S2)}`
    ///
    /// # Property: Involution
    /// `dual(dual(S)) = S` for all session types S
    pub fn dual(&self) -> Self {
        match self {
            Self::Send { payload, continuation } => Self::Recv {
                payload: payload.clone(),
                continuation: Box::new(continuation.dual()),
            },
            Self::Recv { payload, continuation } => Self::Send {
                payload: payload.clone(),
                continuation: Box::new(continuation.dual()),
            },
            Self::Select(branches) => {
                Self::Branch(branches.iter().map(|(l, s)| (*l, s.dual())).collect())
            }
            Self::Branch(branches) => {
                Self::Select(branches.iter().map(|(l, s)| (*l, s.dual())).collect())
            }
            Self::Rec { var, body } => Self::Rec {
                var: *var,
                body: Box::new(body.dual()),
            },
            Self::Var(v) => Self::Var(*v),
            Self::End => Self::End,
        }
    }

    /// Check if two session types are duals of each other
    ///
    /// Two session types are dual when one is the `dual()` of the other.
    /// This is the key property for safe channel endpoint pairing.
    pub fn is_dual_of(&self, other: &Self) -> bool {
        self.dual() == *other
    }

    /// Check if this session type is self-dual (symmetric)
    ///
    /// A session type is self-dual if `dual(S) = S`.
    /// Only `End` and certain recursive types can be self-dual.
    pub fn is_self_dual(&self) -> bool {
        self.dual() == *self
    }

    /// Check if this session type is closed (no free variables)
    pub fn is_closed(&self) -> bool {
        self.free_vars().is_empty()
    }

    /// Compute the size of a session type (for termination metrics)
    ///
    /// Returns the total number of nodes in the session type tree.
    /// Useful as a termination measure for recursive functions over session types.
    ///
    /// - `End` has size 1
    /// - `Var(x)` has size 1
    /// - `Send/Recv` has size 1 + size(continuation)
    /// - `Select/Branch` has size 1 + sum of branch sizes
    /// - `Rec` has size 1 + size(body)
    pub fn session_size(&self) -> usize {
        match self {
            Self::End | Self::Var(_) => 1,
            Self::Send { continuation, .. } | Self::Recv { continuation, .. } => {
                1 + continuation.session_size()
            }
            Self::Select(branches) | Self::Branch(branches) => {
                1 + branches.iter().map(|(_, s)| s.session_size()).sum::<usize>()
            }
            Self::Rec { body, .. } => 1 + body.session_size(),
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
            Self::Select(branches) | Self::Branch(branches) => branches
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

    /// Substitute a session variable with a session type
    pub fn substitute(&self, var: SessionVar, replacement: &Self) -> Self {
        match self {
            Self::Send { payload, continuation } => Self::Send {
                payload: payload.clone(),
                continuation: Box::new(continuation.substitute(var, replacement)),
            },
            Self::Recv { payload, continuation } => Self::Recv {
                payload: payload.clone(),
                continuation: Box::new(continuation.substitute(var, replacement)),
            },
            Self::Select(branches) => Self::Select(
                branches
                    .iter()
                    .map(|(l, s)| (*l, s.substitute(var, replacement)))
                    .collect(),
            ),
            Self::Branch(branches) => Self::Branch(
                branches
                    .iter()
                    .map(|(l, s)| (*l, s.substitute(var, replacement)))
                    .collect(),
            ),
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

    /// Check if a session variable is guarded in this type.
    ///
    /// A variable is "guarded" if it does not appear at the top level of the
    /// session type - meaning every occurrence is protected by at least one
    /// Send or Recv operation.
    ///
    /// This is essential for contractivity: `rec X.S` is contractive only if
    /// `X` is guarded in `S`, preventing infinite loops without communication.
    ///
    /// # Semantics
    /// - `End`: variable cannot appear, vacuously guarded
    /// - `Var(x)`: NOT guarded if `x == var` (appears directly at top level)
    /// - `Send/Recv`: guards all variables in continuation (the key property!)
    /// - `Select/Branch`: check all branches (choice itself doesn't guard)
    /// - `Rec`: shadowing makes it vacuously guarded, otherwise check body
    ///
    /// # Examples
    /// - In `!T.X`, `X` is guarded (protected by Send)
    /// - In `?T.X`, `X` is guarded (protected by Recv)
    /// - In `X`, `X` is NOT guarded (appears directly)
    /// - In `+{l: X}`, `X` is NOT guarded (Select doesn't protect)
    /// - In `+{l: !T.X}`, `X` is guarded (Send protects it)
    pub fn is_guarded(&self, var: SessionVar) -> bool {
        match self {
            // End: variable cannot appear, vacuously guarded
            Self::End => true,

            // Variable: NOT guarded if it's the one we're looking for
            Self::Var(x) => *x != var,

            // Send/Recv: these act as guards - variable is protected
            // This is the KEY property: I/O operations guard recursive variables
            Self::Send { .. } | Self::Recv { .. } => true,

            // Select/Branch: check all branches (choice itself doesn't guard)
            Self::Select(branches) | Self::Branch(branches) => {
                branches.iter().all(|(_, s)| s.is_guarded(var))
            }

            // Rec: shadowing makes it vacuously guarded, otherwise check body
            Self::Rec { var: rec_var, body } => {
                if *rec_var == var {
                    true // Inner binding shadows the variable
                } else {
                    body.is_guarded(var)
                }
            }
        }
    }

    /// Check if this session type is contractive.
    ///
    /// A session type is contractive if every recursive type `rec X.S` has
    /// `X` guarded in `S` (protected by at least one Send or Recv).
    ///
    /// Contractivity ensures that recursive protocols make progress - they
    /// must perform at least one I/O operation before recursing. Without
    /// contractivity, a type like `rec X.X` would unfold infinitely without
    /// ever doing any communication.
    ///
    /// # Examples
    /// - `rec X.!T.X` is contractive (X guarded by Send)
    /// - `rec X.?T.X` is contractive (X guarded by Recv)
    /// - `rec X.X` is NOT contractive (X unguarded -> infinite loop)
    /// - `rec X.+{l: X}` is NOT contractive (X unguarded in branch)
    /// - `rec X.+{l: !T.X, r: end}` is contractive (X guarded by Send)
    /// - `rec X.rec Y.!T.X` is contractive (X guarded, Y doesn't appear)
    pub fn is_contractive(&self) -> bool {
        match self {
            // Base cases: always contractive
            Self::End | Self::Var(_) => true,

            // Check continuation
            Self::Send { continuation, .. } | Self::Recv { continuation, .. } => {
                continuation.is_contractive()
            }

            // All branches must be contractive
            Self::Select(branches) | Self::Branch(branches) => {
                branches.iter().all(|(_, s)| s.is_contractive())
            }

            // Recursive type: bound variable must be guarded AND body must be contractive
            Self::Rec { var, body } => body.is_guarded(*var) && body.is_contractive(),
        }
    }

    /// Check if this session type is well-formed.
    ///
    /// A session type is well-formed if it is both:
    /// 1. **Closed**: no free variables (all variables bound by enclosing `Rec`)
    /// 2. **Contractive**: all recursive types make progress (guard their variables)
    ///
    /// Well-formed session types are safe to use in typed channels - they
    /// won't have dangling references and won't loop forever without communication.
    ///
    /// # Examples
    /// - `!Int.end` is well-formed (closed, no recursion)
    /// - `rec X.!Int.X` is well-formed (closed, X is guarded)
    /// - `X` is NOT well-formed (free variable)
    /// - `rec X.X` is NOT well-formed (not contractive)
    pub fn is_wellformed(&self) -> bool {
        self.is_closed() && self.is_contractive()
    }

    // ========================================================================
    // Coinductive Session Subtyping
    // ========================================================================

    /// Compute a structural hash for cycle detection in coinductive subtyping
    ///
    /// Used to detect when we've encountered the same pair of types during
    /// recursive subtyping checks, enabling the coinductive (greatest fixpoint)
    /// semantics for recursive session types.
    fn content_hash(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.hash_content(&mut hasher);
        hasher.finish()
    }

    /// Recursively hash the structural content of this session type
    fn hash_content<H: Hasher>(&self, state: &mut H) {
        // Hash discriminant to distinguish variants
        self.discriminant().hash(state);

        match self {
            Self::End => {}
            Self::Var(v) => v.0.hash(state),
            Self::Send { payload, continuation } => {
                // Hash payload by discriminant (simplified; full hash would require
                // BrrrType to implement Hash)
                payload.discriminant().hash(state);
                continuation.hash_content(state);
            }
            Self::Recv { payload, continuation } => {
                payload.discriminant().hash(state);
                continuation.hash_content(state);
            }
            Self::Select(branches) | Self::Branch(branches) => {
                branches.len().hash(state);
                for (label, session) in branches {
                    label.hash(state);
                    session.hash_content(state);
                }
            }
            Self::Rec { var, body } => {
                var.0.hash(state);
                body.hash_content(state);
            }
        }
    }

    /// Check if payload type t1 is a subtype of t2
    ///
    /// Currently uses structural equality. Can be extended for proper
    /// subtyping (e.g., numeric widening, variance in type constructors).
    fn type_subtype(t1: &BrrrType, t2: &BrrrType) -> bool {
        t1 == t2
    }

    /// Coinductive session subtyping implementation
    ///
    /// Uses a visited set to detect cycles. If we encounter the same (s1, s2)
    /// pair during recursion, we return true (greatest fixpoint semantics).
    ///
    /// This implements the F* specification from SessionTypes.fst:
    /// ```fstar
    /// let rec session_subtype_co (visited: list (session_type & session_type))
    ///     (s1 s2: session_type) : Tot bool = ...
    /// ```
    fn session_subtype_co(&self, other: &SessionType, visited: &mut HashSet<(u64, u64)>) -> bool {
        let key = (self.content_hash(), other.content_hash());

        // Coinductive: if we've seen this pair, assume true (greatest fixpoint)
        if visited.contains(&key) {
            return true;
        }

        visited.insert(key);

        match (self, other) {
            // End <: End
            (Self::End, Self::End) => true,

            // Var(x) <: Var(y) iff x == y
            (Self::Var(x), Self::Var(y)) => x == y,

            // Send: contravariant in payload, covariant in continuation
            // !T1.S1 <: !T2.S2 iff T2 <: T1 and S1 <: S2
            (
                Self::Send {
                    payload: t1,
                    continuation: c1,
                },
                Self::Send {
                    payload: t2,
                    continuation: c2,
                },
            ) => Self::type_subtype(t2, t1) && c1.session_subtype_co(c2, visited),

            // Recv: covariant in payload, covariant in continuation
            // ?T1.S1 <: ?T2.S2 iff T1 <: T2 and S1 <: S2
            (
                Self::Recv {
                    payload: t1,
                    continuation: c1,
                },
                Self::Recv {
                    payload: t2,
                    continuation: c2,
                },
            ) => Self::type_subtype(t1, t2) && c1.session_subtype_co(c2, visited),

            // Select: s1 can select fewer labels than s2
            // All labels in s1 must exist in s2 with subtype continuations
            (Self::Select(bs1), Self::Select(bs2)) => bs1.iter().all(|(label, s1_cont)| {
                bs2.iter()
                    .find(|(l2, _)| label == l2)
                    .map(|(_, s2_cont)| s1_cont.session_subtype_co(s2_cont, visited))
                    .unwrap_or(false)
            }),

            // Branch: s1 must handle all labels that s2 handles
            // All labels in s2 must exist in s1 with subtype continuations
            (Self::Branch(bs1), Self::Branch(bs2)) => bs2.iter().all(|(label, s2_cont)| {
                bs1.iter()
                    .find(|(l1, _)| label == l1)
                    .map(|(_, s1_cont)| s1_cont.session_subtype_co(s2_cont, visited))
                    .unwrap_or(false)
            }),

            // Rec: unfold both and compare
            (Self::Rec { .. }, Self::Rec { .. }) => {
                self.unfold().session_subtype_co(&other.unfold(), visited)
            }

            // All other combinations are not subtypes
            _ => false,
        }
    }

    /// Check if this session type is a subtype of another
    ///
    /// Uses coinductive reasoning (greatest fixpoint semantics) to correctly
    /// handle recursive session types. For recursive types, if we encounter
    /// the same comparison during recursion, we assume it holds.
    ///
    /// # Subtyping Rules
    ///
    /// - `End <: End`
    /// - `Var(x) <: Var(y)` iff `x == y`
    /// - `!T1.S1 <: !T2.S2` iff `T2 <: T1` (contravariant) and `S1 <: S2`
    /// - `?T1.S1 <: ?T2.S2` iff `T1 <: T2` (covariant) and `S1 <: S2`
    /// - `+{...} <: +{...}` - s1 can select fewer labels than s2
    /// - `&{...} <: &{...}` - s1 must handle all labels in s2
    /// - `rec X.S1 <: rec Y.S2` - unfold both and compare
    ///
    /// # Variance Intuition
    ///
    /// - **Send is contravariant** in payload: If I promise to send an Int,
    ///   I can substitute with a sender of a more specific type.
    /// - **Recv is covariant** in payload: If I expect to receive an Int,
    ///   I can substitute with a receiver that accepts a more general type.
    /// - **Select** (internal choice): A client that selects from fewer options
    ///   can replace one that might select from more.
    /// - **Branch** (external choice): A server that handles more options
    ///   can replace one that handles fewer.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Recursive ping-pong protocol
    /// let ping = SessionType::rec(
    ///     SessionVar::new(0),
    ///     SessionType::send(BrrrType::BOOL, SessionType::var(SessionVar::new(0)))
    /// );
    /// assert!(ping.is_subtype_of(&ping)); // reflexive
    /// ```
    pub fn is_subtype_of(&self, other: &SessionType) -> bool {
        let mut visited = HashSet::new();
        self.session_subtype_co(other, &mut visited)
    }

    /// Format as UTF-8 symbol for .brrrx output
    pub fn as_symbol(&self, interner: &impl LabelInterner) -> String {
        match self {
            Self::Send { payload, continuation } => {
                format!("!{:?}.{}", payload, continuation.as_symbol(interner))
            }
            Self::Recv { payload, continuation } => {
                format!("?{:?}.{}", payload, continuation.as_symbol(interner))
            }
            Self::Select(branches) => {
                let bs: Vec<_> = branches
                    .iter()
                    .map(|(l, s)| format!("{}: {}", interner.resolve(*l), s.as_symbol(interner)))
                    .collect();
                format!("+{{{}}}", bs.join(", "))
            }
            Self::Branch(branches) => {
                let bs: Vec<_> = branches
                    .iter()
                    .map(|(l, s)| format!("{}: {}", interner.resolve(*l), s.as_symbol(interner)))
                    .collect();
                format!("&{{{}}}", bs.join(", "))
            }
            Self::Rec { var, body } => {
                format!("rec X{}.{}", var.0, body.as_symbol(interner))
            }
            Self::Var(v) => format!("X{}", v.0),
            Self::End => "end".to_string(),
        }
    }
}

impl Default for SessionType {
    fn default() -> Self {
        Self::End
    }
}

// ============================================================================
// Channel Endpoints
// ============================================================================

use crate::effects::ChanId;

/// Channel endpoint - session type with channel ID
///
/// Represents one end of a bidirectional typed channel.
/// Each channel has two endpoints with dual session types.
///
/// # Invariant
/// For a channel pair (ep1, ep2): `ep1.session.is_dual_of(&ep2.session)`
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ChannelEndpoint {
    /// Channel identifier (shared between both endpoints)
    pub channel: ChanId,
    /// Current session state (advances after each operation)
    pub session: SessionType,
}

impl ChannelEndpoint {
    /// Create a new channel endpoint
    pub const fn new(channel: ChanId, session: SessionType) -> Self {
        Self { channel, session }
    }

    /// Advance after send (must be Send type)
    ///
    /// Returns the continuation endpoint if this is a Send type,
    /// or None if the current state is not a Send.
    pub fn advance_send(&self) -> Option<Self> {
        match &self.session {
            SessionType::Send { continuation, .. } => Some(Self {
                channel: self.channel,
                session: (**continuation).clone(),
            }),
            _ => None,
        }
    }

    /// Advance after recv (must be Recv type)
    ///
    /// Returns the continuation endpoint if this is a Recv type,
    /// or None if the current state is not a Recv.
    pub fn advance_recv(&self) -> Option<Self> {
        match &self.session {
            SessionType::Recv { continuation, .. } => Some(Self {
                channel: self.channel,
                session: (**continuation).clone(),
            }),
            _ => None,
        }
    }

    /// Select a branch (must be Select type)
    ///
    /// Returns the continuation for the selected label, or None if:
    /// - The current state is not a Select
    /// - The label is not found in the available branches
    pub fn select_branch(&self, label: Label) -> Option<Self> {
        match &self.session {
            SessionType::Select(branches) => branches
                .iter()
                .find(|(l, _)| *l == label)
                .map(|(_, ty)| Self {
                    channel: self.channel,
                    session: ty.clone(),
                }),
            _ => None,
        }
    }

    /// Offer a branch (must be Branch type)
    ///
    /// Returns the continuation for the offered label, or None if:
    /// - The current state is not a Branch
    /// - The label is not found in the available branches
    pub fn offer_branch(&self, label: Label) -> Option<Self> {
        match &self.session {
            SessionType::Branch(branches) => branches
                .iter()
                .find(|(l, _)| *l == label)
                .map(|(_, ty)| Self {
                    channel: self.channel,
                    session: ty.clone(),
                }),
            _ => None,
        }
    }

    /// Check if session is complete (reached End)
    pub fn is_end(&self) -> bool {
        self.session.is_end()
    }

    /// Get the expected payload type for send operation
    pub fn send_payload(&self) -> Option<&BrrrType> {
        match &self.session {
            SessionType::Send { payload, .. } => Some(payload),
            _ => None,
        }
    }

    /// Get the expected payload type for recv operation
    pub fn recv_payload(&self) -> Option<&BrrrType> {
        match &self.session {
            SessionType::Recv { payload, .. } => Some(payload),
            _ => None,
        }
    }

    /// Get available branch labels (for Select or Branch types)
    pub fn available_labels(&self) -> Option<Vec<Label>> {
        match &self.session {
            SessionType::Select(branches) | SessionType::Branch(branches) => {
                Some(branches.iter().map(|(l, _)| *l).collect())
            }
            _ => None,
        }
    }
}

/// Create a pair of dual channel endpoints
///
/// This is the primary way to create a typed channel.
/// The two endpoints have dual session types, ensuring type-safe communication.
///
/// # Arguments
/// * `chan1` - Channel ID for the first endpoint
/// * `chan2` - Channel ID for the second endpoint (typically chan1 for same channel)
/// * `session` - Session type for the first endpoint (second gets dual)
///
/// # Returns
/// A tuple of (endpoint1, endpoint2) where endpoint2.session = dual(endpoint1.session)
pub fn make_channel_pair(
    chan1: ChanId,
    chan2: ChanId,
    session: SessionType,
) -> (ChannelEndpoint, ChannelEndpoint) {
    (
        ChannelEndpoint::new(chan1, session.clone()),
        ChannelEndpoint::new(chan2, session.dual()),
    )
}

/// Create a channel pair with the same channel ID
///
/// Convenience function for the common case where both endpoints
/// share the same channel identifier.
pub fn make_channel(channel: ChanId, session: SessionType) -> (ChannelEndpoint, ChannelEndpoint) {
    make_channel_pair(channel, channel, session)
}

/// Trait for resolving interned labels
///
/// Abstracts over lasso::Rodeo and similar interners.
pub trait LabelInterner {
    /// Resolve a label to its string representation
    fn resolve(&self, label: Label) -> &str;
}

/// Dummy interner for testing (shows raw Spur key)
pub struct DebugInterner;

impl LabelInterner for DebugInterner {
    fn resolve(&self, label: Label) -> &str {
        // In tests, we just show the raw key
        // Real usage would use a proper Rodeo
        Box::leak(format!("L{:?}", label).into_boxed_str())
    }
}

// ============================================================================
// Session Context - Channel Tracking
// ============================================================================

/// Session context - tracks active channels and their session types
///
/// Maps to F*:
/// ```fstar
/// type session_ctx = list (chan_id & session_type)
/// ```
///
/// Provides functional-style operations for channel management during
/// session type checking. Implemented as a list to match F* semantics
/// where order may be significant for proofs.
///
/// # Invariant
/// Each channel ID appears at most once in the context (enforced by update_channel).
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct SessionCtx {
    /// Channel bindings in order of insertion (most recent first after update)
    channels: Vec<(ChanId, SessionType)>,
}

impl SessionCtx {
    /// Create an empty session context
    ///
    /// Maps to F*: `let empty_session_ctx : session_ctx = []`
    #[inline]
    pub const fn empty() -> Self {
        Self {
            channels: Vec::new(),
        }
    }

    /// Create a session context with a single channel binding
    pub fn singleton(ch: ChanId, session: SessionType) -> Self {
        Self {
            channels: vec![(ch, session)],
        }
    }

    /// Create a session context from an iterator of channel bindings
    ///
    /// Note: If duplicate channel IDs are provided, earlier bindings are kept
    /// (consistent with list semantics where first match wins in lookup).
    pub fn from_iter(iter: impl IntoIterator<Item = (ChanId, SessionType)>) -> Self {
        let mut ctx = Self::empty();
        for (ch, session) in iter {
            if !ctx.has_channel(ch) {
                ctx.channels.push((ch, session));
            }
        }
        ctx
    }

    /// Lookup a channel in the context
    ///
    /// Maps to F*:
    /// ```fstar
    /// let lookup_channel (ch: chan_id) (ctx: session_ctx) : option session_type =
    ///   List.Tot.assoc ch ctx
    /// ```
    ///
    /// Returns None if the channel is not in the context.
    pub fn lookup_channel(&self, ch: ChanId) -> Option<&SessionType> {
        self.channels
            .iter()
            .find(|(c, _)| *c == ch)
            .map(|(_, s)| s)
    }

    /// Check if a channel exists in the context
    ///
    /// Maps to F*:
    /// ```fstar
    /// let has_channel (ch: chan_id) (ctx: session_ctx) : bool =
    ///   Some? (lookup_channel ch ctx)
    /// ```
    #[inline]
    pub fn has_channel(&self, ch: ChanId) -> bool {
        self.lookup_channel(ch).is_some()
    }

    /// Remove a channel from the context
    ///
    /// Maps to F*:
    /// ```fstar
    /// let remove_channel (ch: chan_id) (ctx: session_ctx) : session_ctx =
    ///   List.Tot.filter (fun (c, _) -> c <> ch) ctx
    /// ```
    ///
    /// Returns a new context without the specified channel.
    /// If the channel is not present, returns an equivalent context.
    pub fn remove_channel(&self, ch: ChanId) -> Self {
        Self {
            channels: self
                .channels
                .iter()
                .filter(|(c, _)| *c != ch)
                .cloned()
                .collect(),
        }
    }

    /// Update a channel in the context (insert or replace)
    ///
    /// Maps to F*:
    /// ```fstar
    /// let update_channel (ch: chan_id) (s: session_type) (ctx: session_ctx) : session_ctx =
    ///   (ch, s) :: remove_channel ch ctx
    /// ```
    ///
    /// Returns a new context with the channel bound to the given session type.
    /// If the channel already exists, the old binding is replaced.
    /// The new binding is placed at the front (most recent).
    pub fn update_channel(&self, ch: ChanId, session: SessionType) -> Self {
        let mut new_ctx = self.remove_channel(ch);
        new_ctx.channels.insert(0, (ch, session));
        new_ctx
    }

    /// Check if two contexts are disjoint (no overlapping channel IDs)
    ///
    /// Maps to F*:
    /// ```fstar
    /// let disjoint_ctx (ctx1 ctx2: session_ctx) : bool =
    ///   List.for_all (fun (ch, _) -> not (has_channel ch ctx2)) ctx1
    /// ```
    pub fn disjoint_ctx(&self, other: &Self) -> bool {
        self.channels
            .iter()
            .all(|(ch, _)| !other.has_channel(*ch))
    }

    /// Merge two contexts if they are disjoint
    ///
    /// Maps to F*:
    /// ```fstar
    /// let merge_ctx (ctx1 ctx2: session_ctx) : option session_ctx =
    ///   if disjoint_ctx ctx1 ctx2 then Some (ctx1 @ ctx2) else None
    /// ```
    ///
    /// Returns None if the contexts have overlapping channel IDs.
    pub fn merge_ctx(&self, other: &Self) -> Option<Self> {
        if self.disjoint_ctx(other) {
            let mut merged = self.channels.clone();
            merged.extend(other.channels.iter().cloned());
            Some(Self { channels: merged })
        } else {
            None
        }
    }

    /// Check if all channels in the context have ended
    ///
    /// Maps to F*:
    /// ```fstar
    /// let all_ended (ctx: session_ctx) : bool =
    ///   List.for_all (fun (_, s) -> s = SEnd) ctx
    /// ```
    ///
    /// Returns true if all channel session types are End.
    /// Also returns true for an empty context.
    pub fn all_ended(&self) -> bool {
        self.channels.iter().all(|(_, s)| *s == SessionType::End)
    }

    /// Get the number of channels in the context
    #[inline]
    pub fn len(&self) -> usize {
        self.channels.len()
    }

    /// Check if the context is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.channels.is_empty()
    }

    /// Iterate over all channel bindings
    pub fn iter(&self) -> impl Iterator<Item = &(ChanId, SessionType)> {
        self.channels.iter()
    }

    /// Get all channel IDs in the context
    pub fn channel_ids(&self) -> impl Iterator<Item = ChanId> + '_ {
        self.channels.iter().map(|(ch, _)| *ch)
    }

    /// Advance a channel after a send operation
    ///
    /// Returns a new context with the channel's session type advanced,
    /// or None if the channel doesn't exist or isn't in a Send state.
    pub fn advance_send(&self, ch: ChanId) -> Option<Self> {
        let session = self.lookup_channel(ch)?;
        match session {
            SessionType::Send { continuation, .. } => {
                Some(self.update_channel(ch, (**continuation).clone()))
            }
            _ => None,
        }
    }

    /// Advance a channel after a recv operation
    ///
    /// Returns a new context with the channel's session type advanced,
    /// or None if the channel doesn't exist or isn't in a Recv state.
    pub fn advance_recv(&self, ch: ChanId) -> Option<Self> {
        let session = self.lookup_channel(ch)?;
        match session {
            SessionType::Recv { continuation, .. } => {
                Some(self.update_channel(ch, (**continuation).clone()))
            }
            _ => None,
        }
    }

    /// Select a branch on a channel
    ///
    /// Returns a new context with the channel's session type set to the
    /// selected branch, or None if the channel doesn't exist, isn't a
    /// Select type, or the label isn't found.
    pub fn select_branch(&self, ch: ChanId, label: Label) -> Option<Self> {
        let session = self.lookup_channel(ch)?;
        match session {
            SessionType::Select(branches) => branches
                .iter()
                .find(|(l, _)| *l == label)
                .map(|(_, ty)| self.update_channel(ch, ty.clone())),
            _ => None,
        }
    }

    /// Offer a branch on a channel
    ///
    /// Returns a new context with the channel's session type set to the
    /// offered branch, or None if the channel doesn't exist, isn't a
    /// Branch type, or the label isn't found.
    pub fn offer_branch(&self, ch: ChanId, label: Label) -> Option<Self> {
        let session = self.lookup_channel(ch)?;
        match session {
            SessionType::Branch(branches) => branches
                .iter()
                .find(|(l, _)| *l == label)
                .map(|(_, ty)| self.update_channel(ch, ty.clone())),
            _ => None,
        }
    }

    /// Close a channel by checking it has ended and removing it
    ///
    /// Returns a new context without the channel if the channel's session
    /// type is End. Returns None if the channel doesn't exist or hasn't ended.
    pub fn close_channel(&self, ch: ChanId) -> Option<Self> {
        let session = self.lookup_channel(ch)?;
        if session.is_end() {
            Some(self.remove_channel(ch))
        } else {
            None
        }
    }

    /// Split the context into two parts for parallel composition
    ///
    /// Distributes channels between two sub-contexts based on a predicate.
    /// Returns (matching, non-matching) contexts.
    pub fn split<F>(&self, predicate: F) -> (Self, Self)
    where
        F: Fn(ChanId) -> bool,
    {
        let (left, right): (Vec<_>, Vec<_>) =
            self.channels.iter().cloned().partition(|(ch, _)| predicate(*ch));
        (Self { channels: left }, Self { channels: right })
    }
}

/// Free function: Create an empty session context
///
/// Convenience function matching F* naming.
#[inline]
pub fn empty_session_ctx() -> SessionCtx {
    SessionCtx::empty()
}

/// Free function: Lookup a channel in the context
///
/// Matches F* signature: `lookup_channel : chan_id -> session_ctx -> option session_type`
#[inline]
pub fn lookup_channel(ch: ChanId, ctx: &SessionCtx) -> Option<&SessionType> {
    ctx.lookup_channel(ch)
}

/// Free function: Check if a channel exists in the context
///
/// Matches F* signature: `has_channel : chan_id -> session_ctx -> bool`
#[inline]
pub fn has_channel(ch: ChanId, ctx: &SessionCtx) -> bool {
    ctx.has_channel(ch)
}

/// Free function: Remove a channel from the context
///
/// Matches F* signature: `remove_channel : chan_id -> session_ctx -> session_ctx`
#[inline]
pub fn remove_channel(ch: ChanId, ctx: &SessionCtx) -> SessionCtx {
    ctx.remove_channel(ch)
}

/// Free function: Update a channel in the context
///
/// Matches F* signature: `update_channel : chan_id -> session_type -> session_ctx -> session_ctx`
#[inline]
pub fn update_channel(ch: ChanId, session: SessionType, ctx: &SessionCtx) -> SessionCtx {
    ctx.update_channel(ch, session)
}

/// Free function: Check if two contexts are disjoint
///
/// Matches F* signature: `disjoint_ctx : session_ctx -> session_ctx -> bool`
#[inline]
pub fn disjoint_ctx(ctx1: &SessionCtx, ctx2: &SessionCtx) -> bool {
    ctx1.disjoint_ctx(ctx2)
}

/// Free function: Merge two contexts if disjoint
///
/// Matches F* signature: `merge_ctx : session_ctx -> session_ctx -> option session_ctx`
#[inline]
pub fn merge_ctx(ctx1: &SessionCtx, ctx2: &SessionCtx) -> Option<SessionCtx> {
    ctx1.merge_ctx(ctx2)
}

/// Free function: Check if all channels have ended
///
/// Matches F* signature: `all_ended : session_ctx -> bool`
#[inline]
pub fn all_ended(ctx: &SessionCtx) -> bool {
    ctx.all_ended()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{IntType, NumericType, PrimKind};

    #[test]
    fn test_session_type_construction() {
        let int_ty = BrrrType::Prim(PrimKind::Bool);
        let s = SessionType::send(
            int_ty.clone(),
            SessionType::recv(int_ty, SessionType::End),
        );
        assert_eq!(s.discriminant(), 0);
        assert!(s.is_send());
        assert!(!s.is_end());
    }

    #[test]
    fn test_session_type_end() {
        let s = SessionType::END;
        assert!(s.is_end());
        assert_eq!(s.discriminant(), 6);
    }

    #[test]
    fn test_dual_send_recv() {
        let payload = BrrrType::BOOL;
        let send = SessionType::send(payload.clone(), SessionType::End);
        let recv = send.dual();

        assert!(send.is_send());
        assert!(recv.is_recv());

        // Double dual should be original
        assert_eq!(send, recv.dual());
    }

    #[test]
    fn test_dual_end() {
        let end = SessionType::End;
        assert_eq!(end.dual(), SessionType::End);
    }

    #[test]
    fn test_recursive_type() {
        let var = SessionVar::new(0);
        let body = SessionType::send(
            BrrrType::BOOL,
            SessionType::var(var),
        );
        let rec_type = SessionType::rec(var, body);

        assert!(rec_type.is_recursive());
        assert!(rec_type.is_closed());
    }

    #[test]
    fn test_free_vars() {
        let var0 = SessionVar::new(0);
        let var1 = SessionVar::new(1);

        // Free variable
        let s = SessionType::Var(var0);
        assert_eq!(s.free_vars(), vec![var0]);
        assert!(!s.is_closed());

        // Bound variable
        let s = SessionType::rec(var0, SessionType::var(var0));
        assert!(s.free_vars().is_empty());
        assert!(s.is_closed());

        // Mixed: var1 free, var0 bound
        let s = SessionType::rec(
            var0,
            SessionType::send(
                BrrrType::BOOL,
                SessionType::Var(var1),
            ),
        );
        assert_eq!(s.free_vars(), vec![var1]);
    }

    #[test]
    fn test_substitute() {
        let var = SessionVar::new(0);
        let s = SessionType::var(var);
        let replacement = SessionType::End;

        let result = s.substitute(var, &replacement);
        assert_eq!(result, SessionType::End);
    }

    #[test]
    fn test_unfold() {
        let var = SessionVar::new(0);
        let body = SessionType::send(
            BrrrType::BOOL,
            SessionType::var(var),
        );
        let rec_type = SessionType::rec(var, body);

        let unfolded = rec_type.unfold();

        // Unfolding should produce: !Bool.rec X0.!Bool.X0
        if let SessionType::Send { continuation, .. } = unfolded {
            assert!(continuation.is_recursive());
        } else {
            panic!("Expected Send after unfold");
        }
    }

    #[test]
    fn test_discriminants_unique() {
        let types = [
            SessionType::send(BrrrType::BOOL, SessionType::End),
            SessionType::recv(BrrrType::BOOL, SessionType::End),
            SessionType::select(vec![]),
            SessionType::branch(vec![]),
            SessionType::rec(SessionVar::new(0), SessionType::End),
            SessionType::var(SessionVar::new(0)),
            SessionType::End,
        ];

        let discriminants: Vec<_> = types.iter().map(|t| t.discriminant()).collect();
        let unique: std::collections::HashSet<_> = discriminants.iter().collect();

        assert_eq!(discriminants.len(), unique.len(), "Discriminants must be unique");
    }

    #[test]
    fn test_default() {
        let s: SessionType = Default::default();
        assert_eq!(s, SessionType::End);
    }

    #[test]
    fn test_session_size() {
        // End has size 1
        assert_eq!(SessionType::End.session_size(), 1);

        // Var has size 1
        assert_eq!(SessionType::var(SessionVar::new(0)).session_size(), 1);

        // Send/Recv: 1 + continuation
        let send = SessionType::send(BrrrType::BOOL, SessionType::End);
        assert_eq!(send.session_size(), 2); // 1 (send) + 1 (end)

        let nested = SessionType::send(
            BrrrType::BOOL,
            SessionType::recv(BrrrType::BOOL, SessionType::End),
        );
        assert_eq!(nested.session_size(), 3); // 1 (send) + 1 (recv) + 1 (end)

        // Rec: 1 + body
        // rec X0. !Bool.X0 = 1 (rec) + (1 (send) + 1 (var)) = 3
        let var = SessionVar::new(0);
        let rec = SessionType::rec(var, SessionType::send(BrrrType::BOOL, SessionType::var(var)));
        assert_eq!(rec.session_size(), 3);

        // Select/Branch with empty branches: size 1
        assert_eq!(SessionType::select(vec![]).session_size(), 1);
        assert_eq!(SessionType::branch(vec![]).session_size(), 1);
    }

    #[test]
    fn test_dual_involutive() {
        // Property: dual(dual(S)) == S for all S
        let s = SessionType::send(BrrrType::Prim(PrimKind::Bool), SessionType::End);
        assert_eq!(s.dual().dual(), s);

        // Test with nested types
        let nested = SessionType::send(
            BrrrType::BOOL,
            SessionType::recv(BrrrType::Numeric(NumericType::Int(IntType::I32)), SessionType::End),
        );
        assert_eq!(nested.dual().dual(), nested);

        // Test with recursive type
        let var = SessionVar::new(0);
        let rec = SessionType::rec(var, SessionType::send(BrrrType::BOOL, SessionType::var(var)));
        assert_eq!(rec.dual().dual(), rec);
    }

    #[test]
    fn test_dual_swap() {
        let s = SessionType::send(BrrrType::Prim(PrimKind::Bool), SessionType::End);
        match s.dual() {
            SessionType::Recv { .. } => {}
            _ => panic!("dual of send should be recv"),
        }

        let r = SessionType::recv(BrrrType::BOOL, SessionType::End);
        match r.dual() {
            SessionType::Send { .. } => {}
            _ => panic!("dual of recv should be send"),
        }
    }

    #[test]
    fn test_is_dual_of() {
        let send = SessionType::send(BrrrType::BOOL, SessionType::End);
        let recv = SessionType::recv(BrrrType::BOOL, SessionType::End);

        assert!(send.is_dual_of(&recv));
        assert!(recv.is_dual_of(&send));
        assert!(!send.is_dual_of(&send));
    }

    #[test]
    fn test_is_self_dual() {
        // End is self-dual
        assert!(SessionType::End.is_self_dual());

        // Send/Recv are not self-dual
        let send = SessionType::send(BrrrType::BOOL, SessionType::End);
        assert!(!send.is_self_dual());

        // Variable is self-dual
        let var = SessionType::var(SessionVar::new(0));
        assert!(var.is_self_dual());
    }

    #[test]
    fn test_channel_endpoint_send() {
        let session = SessionType::send(BrrrType::BOOL, SessionType::End);
        let ep = ChannelEndpoint::new(0, session);

        assert!(!ep.is_end());
        assert!(ep.send_payload().is_some());
        assert!(ep.recv_payload().is_none());

        let advanced = ep.advance_send().expect("should advance");
        assert!(advanced.is_end());
    }

    #[test]
    fn test_channel_endpoint_recv() {
        let session = SessionType::recv(BrrrType::BOOL, SessionType::End);
        let ep = ChannelEndpoint::new(0, session);

        assert!(ep.recv_payload().is_some());
        assert!(ep.send_payload().is_none());

        let advanced = ep.advance_recv().expect("should advance");
        assert!(advanced.is_end());
    }

    #[test]
    fn test_channel_endpoint_wrong_operation() {
        let send_session = SessionType::send(BrrrType::BOOL, SessionType::End);
        let ep = ChannelEndpoint::new(0, send_session);

        // Trying to recv on a send endpoint should fail
        assert!(ep.advance_recv().is_none());
    }

    #[test]
    fn test_make_channel_pair() {
        let session = SessionType::send(BrrrType::BOOL, SessionType::End);
        let (ep1, ep2) = make_channel_pair(1, 2, session.clone());

        assert_eq!(ep1.channel, 1);
        assert_eq!(ep2.channel, 2);
        assert_eq!(ep1.session, session);
        assert!(ep1.session.is_dual_of(&ep2.session));
    }

    #[test]
    fn test_make_channel() {
        let session = SessionType::send(BrrrType::BOOL, SessionType::End);
        let (ep1, ep2) = make_channel(42, session.clone());

        assert_eq!(ep1.channel, 42);
        assert_eq!(ep2.channel, 42);
        assert!(ep1.session.is_dual_of(&ep2.session));
    }

    #[test]
    fn test_channel_pair_protocol() {
        // Simulate a simple request-response protocol
        // Endpoint 1: !Req.?Resp.end (send request, receive response)
        // Endpoint 2: ?Req.!Resp.end (receive request, send response)

        let req_type = BrrrType::BOOL;
        let resp_type = BrrrType::Numeric(NumericType::Int(IntType::I32));

        let client_session = SessionType::send(
            req_type.clone(),
            SessionType::recv(resp_type.clone(), SessionType::End),
        );

        let (client, server) = make_channel(0, client_session);

        // Verify duality
        assert!(client.session.is_dual_of(&server.session));

        // Simulate protocol execution
        // 1. Client sends request
        let client = client.advance_send().expect("client should send");
        // 2. Server receives request
        let server = server.advance_recv().expect("server should recv");

        // Still dual after first step
        assert!(client.session.is_dual_of(&server.session));

        // 3. Server sends response
        let server = server.advance_send().expect("server should send");
        // 4. Client receives response
        let client = client.advance_recv().expect("client should recv");

        // Both should be at end
        assert!(client.is_end());
        assert!(server.is_end());
    }

    // ========================================================================
    // SessionCtx tests
    // ========================================================================

    #[test]
    fn test_session_ctx_empty() {
        let ctx = SessionCtx::empty();
        assert!(ctx.is_empty());
        assert_eq!(ctx.len(), 0);
        assert!(ctx.all_ended()); // Empty context has all channels ended (vacuously true)
    }

    #[test]
    fn test_session_ctx_singleton() {
        let session = SessionType::send(BrrrType::BOOL, SessionType::End);
        let ctx = SessionCtx::singleton(1, session.clone());

        assert_eq!(ctx.len(), 1);
        assert!(!ctx.is_empty());
        assert!(ctx.has_channel(1));
        assert!(!ctx.has_channel(2));
        assert_eq!(ctx.lookup_channel(1), Some(&session));
        assert_eq!(ctx.lookup_channel(2), None);
    }

    #[test]
    fn test_session_ctx_lookup_channel() {
        let s1 = SessionType::send(BrrrType::BOOL, SessionType::End);
        let s2 = SessionType::recv(BrrrType::BOOL, SessionType::End);
        let ctx = SessionCtx::from_iter(vec![(1, s1.clone()), (2, s2.clone())]);

        assert_eq!(lookup_channel(1, &ctx), Some(&s1));
        assert_eq!(lookup_channel(2, &ctx), Some(&s2));
        assert_eq!(lookup_channel(3, &ctx), None);
    }

    #[test]
    fn test_session_ctx_has_channel() {
        let ctx = SessionCtx::singleton(42, SessionType::End);

        assert!(has_channel(42, &ctx));
        assert!(!has_channel(0, &ctx));
    }

    #[test]
    fn test_session_ctx_remove_channel() {
        let s1 = SessionType::send(BrrrType::BOOL, SessionType::End);
        let s2 = SessionType::recv(BrrrType::BOOL, SessionType::End);
        let ctx = SessionCtx::from_iter(vec![(1, s1.clone()), (2, s2.clone())]);

        let ctx2 = remove_channel(1, &ctx);
        assert!(!ctx2.has_channel(1));
        assert!(ctx2.has_channel(2));
        assert_eq!(ctx2.len(), 1);

        // Removing non-existent channel returns equivalent context
        let ctx3 = remove_channel(99, &ctx);
        assert_eq!(ctx3.len(), 2);
    }

    #[test]
    fn test_session_ctx_update_channel() {
        let s1 = SessionType::send(BrrrType::BOOL, SessionType::End);
        let s2 = SessionType::End;
        let ctx = SessionCtx::singleton(1, s1);

        // Update existing channel
        let ctx2 = update_channel(1, s2.clone(), &ctx);
        assert_eq!(ctx2.lookup_channel(1), Some(&s2));
        assert_eq!(ctx2.len(), 1);

        // Add new channel
        let s3 = SessionType::recv(BrrrType::BOOL, SessionType::End);
        let ctx3 = update_channel(2, s3.clone(), &ctx2);
        assert_eq!(ctx3.lookup_channel(1), Some(&s2));
        assert_eq!(ctx3.lookup_channel(2), Some(&s3));
        assert_eq!(ctx3.len(), 2);
    }

    #[test]
    fn test_session_ctx_disjoint() {
        let ctx1 = SessionCtx::from_iter(vec![
            (1, SessionType::End),
            (2, SessionType::End),
        ]);
        let ctx2 = SessionCtx::from_iter(vec![
            (3, SessionType::End),
            (4, SessionType::End),
        ]);
        let ctx3 = SessionCtx::from_iter(vec![
            (2, SessionType::End),
            (5, SessionType::End),
        ]);

        assert!(disjoint_ctx(&ctx1, &ctx2));
        assert!(disjoint_ctx(&ctx2, &ctx1));
        assert!(!disjoint_ctx(&ctx1, &ctx3)); // 2 is in both
        assert!(!disjoint_ctx(&ctx3, &ctx1));

        // Empty context is disjoint with everything
        let empty = SessionCtx::empty();
        assert!(disjoint_ctx(&empty, &ctx1));
        assert!(disjoint_ctx(&ctx1, &empty));
    }

    #[test]
    fn test_session_ctx_merge() {
        let s1 = SessionType::send(BrrrType::BOOL, SessionType::End);
        let s2 = SessionType::recv(BrrrType::BOOL, SessionType::End);

        let ctx1 = SessionCtx::singleton(1, s1.clone());
        let ctx2 = SessionCtx::singleton(2, s2.clone());

        // Disjoint merge succeeds
        let merged = merge_ctx(&ctx1, &ctx2).expect("should merge");
        assert_eq!(merged.len(), 2);
        assert_eq!(merged.lookup_channel(1), Some(&s1));
        assert_eq!(merged.lookup_channel(2), Some(&s2));

        // Overlapping merge fails
        let ctx3 = SessionCtx::singleton(1, SessionType::End);
        assert!(merge_ctx(&ctx1, &ctx3).is_none());
    }

    #[test]
    fn test_session_ctx_all_ended() {
        // Empty context - vacuously true
        assert!(all_ended(&SessionCtx::empty()));

        // All ended
        let ctx1 = SessionCtx::from_iter(vec![
            (1, SessionType::End),
            (2, SessionType::End),
        ]);
        assert!(all_ended(&ctx1));

        // Not all ended
        let ctx2 = SessionCtx::from_iter(vec![
            (1, SessionType::End),
            (2, SessionType::send(BrrrType::BOOL, SessionType::End)),
        ]);
        assert!(!all_ended(&ctx2));
    }

    #[test]
    fn test_session_ctx_advance_send() {
        let session = SessionType::send(
            BrrrType::BOOL,
            SessionType::recv(BrrrType::BOOL, SessionType::End),
        );
        let ctx = SessionCtx::singleton(1, session);

        let ctx2 = ctx.advance_send(1).expect("should advance");
        assert!(ctx2.lookup_channel(1).unwrap().is_recv());

        // Wrong operation fails
        assert!(ctx2.advance_send(1).is_none());

        // Non-existent channel fails
        assert!(ctx.advance_send(99).is_none());
    }

    #[test]
    fn test_session_ctx_advance_recv() {
        let session = SessionType::recv(BrrrType::BOOL, SessionType::End);
        let ctx = SessionCtx::singleton(1, session);

        let ctx2 = ctx.advance_recv(1).expect("should advance");
        assert!(ctx2.lookup_channel(1).unwrap().is_end());

        // Wrong operation fails
        assert!(ctx.advance_send(1).is_none());
    }

    #[test]
    fn test_session_ctx_close_channel() {
        let ctx = SessionCtx::from_iter(vec![
            (1, SessionType::End),
            (2, SessionType::send(BrrrType::BOOL, SessionType::End)),
        ]);

        // Can close ended channel
        let ctx2 = ctx.close_channel(1).expect("should close");
        assert!(!ctx2.has_channel(1));
        assert!(ctx2.has_channel(2));

        // Cannot close non-ended channel
        assert!(ctx.close_channel(2).is_none());

        // Cannot close non-existent channel
        assert!(ctx.close_channel(99).is_none());
    }

    #[test]
    fn test_session_ctx_split() {
        let ctx = SessionCtx::from_iter(vec![
            (1, SessionType::End),
            (2, SessionType::End),
            (3, SessionType::End),
            (4, SessionType::End),
        ]);

        let (even, odd) = ctx.split(|ch| ch % 2 == 0);

        assert_eq!(even.len(), 2);
        assert!(even.has_channel(2));
        assert!(even.has_channel(4));

        assert_eq!(odd.len(), 2);
        assert!(odd.has_channel(1));
        assert!(odd.has_channel(3));
    }

    #[test]
    fn test_session_ctx_iter() {
        let ctx = SessionCtx::from_iter(vec![
            (1, SessionType::End),
            (2, SessionType::End),
        ]);

        let channel_ids: Vec<_> = ctx.channel_ids().collect();
        assert!(channel_ids.contains(&1));
        assert!(channel_ids.contains(&2));
        assert_eq!(channel_ids.len(), 2);
    }

    #[test]
    fn test_session_ctx_from_iter_dedup() {
        // from_iter should keep first occurrence for duplicates
        let s1 = SessionType::send(BrrrType::BOOL, SessionType::End);
        let s2 = SessionType::recv(BrrrType::BOOL, SessionType::End);

        let ctx = SessionCtx::from_iter(vec![
            (1, s1.clone()),
            (1, s2.clone()), // duplicate, should be ignored
        ]);

        assert_eq!(ctx.len(), 1);
        assert_eq!(ctx.lookup_channel(1), Some(&s1));
    }

    #[test]
    fn test_session_ctx_default() {
        let ctx: SessionCtx = Default::default();
        assert!(ctx.is_empty());
    }

    #[test]
    fn test_free_functions_match_methods() {
        let s1 = SessionType::send(BrrrType::BOOL, SessionType::End);
        let ctx = SessionCtx::singleton(1, s1.clone());

        // Verify free functions delegate to methods correctly
        assert_eq!(empty_session_ctx(), SessionCtx::empty());
        assert_eq!(lookup_channel(1, &ctx), ctx.lookup_channel(1));
        assert_eq!(has_channel(1, &ctx), ctx.has_channel(1));
        assert_eq!(remove_channel(1, &ctx), ctx.remove_channel(1));
        assert_eq!(
            update_channel(2, SessionType::End, &ctx),
            ctx.update_channel(2, SessionType::End)
        );
        assert_eq!(all_ended(&ctx), ctx.all_ended());

        let ctx2 = SessionCtx::singleton(2, SessionType::End);
        assert_eq!(disjoint_ctx(&ctx, &ctx2), ctx.disjoint_ctx(&ctx2));
        assert_eq!(merge_ctx(&ctx, &ctx2), ctx.merge_ctx(&ctx2));
    }

    #[test]
    fn test_session_ctx_protocol_simulation() {
        // Simulate a multi-channel protocol
        // Channel 1: client sends request
        // Channel 2: server receives request
        let req_session = SessionType::send(BrrrType::BOOL, SessionType::End);
        let resp_session = SessionType::recv(BrrrType::BOOL, SessionType::End);

        let ctx = SessionCtx::from_iter(vec![
            (1, req_session),
            (2, resp_session),
        ]);

        // Advance channel 1 (send)
        let ctx = ctx.advance_send(1).expect("channel 1 send");
        assert!(ctx.lookup_channel(1).unwrap().is_end());

        // Advance channel 2 (recv)
        let ctx = ctx.advance_recv(2).expect("channel 2 recv");
        assert!(ctx.lookup_channel(2).unwrap().is_end());

        // Now all channels are ended
        assert!(ctx.all_ended());

        // Close both channels
        let ctx = ctx.close_channel(1).expect("close 1");
        let ctx = ctx.close_channel(2).expect("close 2");
        assert!(ctx.is_empty());
    }

    // ========================================================================
    // Contractivity and Well-formedness tests
    // ========================================================================

    #[test]
    fn test_is_guarded_end() {
        let var = SessionVar::new(0);
        // End: variable vacuously guarded (can't appear)
        assert!(SessionType::End.is_guarded(var));
    }

    #[test]
    fn test_is_guarded_var() {
        let var0 = SessionVar::new(0);
        let var1 = SessionVar::new(1);

        // Var(X): NOT guarded if checking for X
        assert!(!SessionType::var(var0).is_guarded(var0));
        // Var(Y): guarded if checking for X (different variable)
        assert!(SessionType::var(var1).is_guarded(var0));
    }

    #[test]
    fn test_is_guarded_send_recv() {
        let var = SessionVar::new(0);

        // !T.X: X is guarded (Send protects it)
        let send_with_var = SessionType::send(BrrrType::BOOL, SessionType::var(var));
        assert!(send_with_var.is_guarded(var));

        // ?T.X: X is guarded (Recv protects it)
        let recv_with_var = SessionType::recv(BrrrType::BOOL, SessionType::var(var));
        assert!(recv_with_var.is_guarded(var));

        // !T.end: X is guarded (can't appear)
        let send_end = SessionType::send(BrrrType::BOOL, SessionType::End);
        assert!(send_end.is_guarded(var));
    }

    #[test]
    fn test_is_guarded_select_branch() {
        let var = SessionVar::new(0);

        // For select/branch with empty branches
        assert!(SessionType::select(vec![]).is_guarded(var));
        assert!(SessionType::branch(vec![]).is_guarded(var));
    }

    #[test]
    fn test_is_guarded_rec_shadowing() {
        let var0 = SessionVar::new(0);
        let var1 = SessionVar::new(1);

        // rec X.X: checking if X is guarded - inner binding shadows, so vacuously true
        let rec_self = SessionType::rec(var0, SessionType::var(var0));
        assert!(rec_self.is_guarded(var0));

        // rec Y.X: checking if X is guarded - Y doesn't shadow X, so check body
        // body is X, which is NOT guarded
        let rec_other = SessionType::rec(var1, SessionType::var(var0));
        assert!(!rec_other.is_guarded(var0));

        // rec Y.!T.X: checking if X is guarded - Y doesn't shadow, but Send guards
        let rec_guarded = SessionType::rec(
            var1,
            SessionType::send(BrrrType::BOOL, SessionType::var(var0)),
        );
        assert!(rec_guarded.is_guarded(var0));
    }

    #[test]
    fn test_is_contractive_simple() {
        // End is contractive
        assert!(SessionType::End.is_contractive());

        // Var is contractive (it's not a recursive type itself)
        assert!(SessionType::var(SessionVar::new(0)).is_contractive());

        // !T.end is contractive
        let send = SessionType::send(BrrrType::BOOL, SessionType::End);
        assert!(send.is_contractive());

        // ?T.end is contractive
        let recv = SessionType::recv(BrrrType::BOOL, SessionType::End);
        assert!(recv.is_contractive());
    }

    #[test]
    fn test_is_contractive_recursive_guarded() {
        let var = SessionVar::new(0);

        // rec X.!T.X is contractive (X guarded by Send)
        let contractive = SessionType::rec(
            var,
            SessionType::send(BrrrType::BOOL, SessionType::var(var)),
        );
        assert!(contractive.is_contractive());

        // rec X.?T.X is contractive (X guarded by Recv)
        let contractive_recv = SessionType::rec(
            var,
            SessionType::recv(BrrrType::BOOL, SessionType::var(var)),
        );
        assert!(contractive_recv.is_contractive());

        // rec X.end is contractive (X doesn't appear, vacuously guarded)
        let rec_end = SessionType::rec(var, SessionType::End);
        assert!(rec_end.is_contractive());
    }

    #[test]
    fn test_is_contractive_recursive_unguarded() {
        let var = SessionVar::new(0);

        // rec X.X is NOT contractive (X unguarded - infinite loop)
        let non_contractive = SessionType::rec(var, SessionType::var(var));
        assert!(!non_contractive.is_contractive());
    }

    #[test]
    fn test_is_contractive_nested_rec() {
        let var0 = SessionVar::new(0);
        let var1 = SessionVar::new(1);

        // rec X.rec Y.!T.X is contractive
        let nested_contractive = SessionType::rec(
            var0,
            SessionType::rec(
                var1,
                SessionType::send(BrrrType::BOOL, SessionType::var(var0)),
            ),
        );
        assert!(nested_contractive.is_contractive());

        // rec X.rec Y.X is NOT contractive
        let nested_non_contractive = SessionType::rec(
            var0,
            SessionType::rec(var1, SessionType::var(var0)),
        );
        assert!(!nested_non_contractive.is_contractive());
    }

    #[test]
    fn test_is_wellformed_closed_and_contractive() {
        let var = SessionVar::new(0);

        // !Int.end is well-formed (closed, no recursion)
        let simple = SessionType::send(BrrrType::BOOL, SessionType::End);
        assert!(simple.is_wellformed());

        // rec X.!Int.X is well-formed (closed, X is guarded)
        let rec_wellformed = SessionType::rec(
            var,
            SessionType::send(BrrrType::BOOL, SessionType::var(var)),
        );
        assert!(rec_wellformed.is_wellformed());

        // end is well-formed
        assert!(SessionType::End.is_wellformed());
    }

    #[test]
    fn test_is_wellformed_not_closed() {
        let var = SessionVar::new(0);

        // X is NOT well-formed (free variable)
        let free_var = SessionType::var(var);
        assert!(!free_var.is_wellformed());
        assert!(!free_var.is_closed());
        assert!(free_var.is_contractive()); // It's contractive, just not closed
    }

    #[test]
    fn test_is_wellformed_not_contractive() {
        let var = SessionVar::new(0);

        // rec X.X is NOT well-formed (not contractive)
        let non_contractive = SessionType::rec(var, SessionType::var(var));
        assert!(!non_contractive.is_wellformed());
        assert!(non_contractive.is_closed()); // It IS closed
        assert!(!non_contractive.is_contractive()); // But not contractive
    }

    #[test]
    fn test_is_wellformed_complex() {
        let var = SessionVar::new(0);

        // rec X.!Bool.?Int.X is well-formed (request-response loop)
        let protocol = SessionType::rec(
            var,
            SessionType::send(
                BrrrType::BOOL,
                SessionType::recv(
                    BrrrType::Numeric(NumericType::Int(IntType::I32)),
                    SessionType::var(var),
                ),
            ),
        );
        assert!(protocol.is_wellformed());

        // The dual should also be well-formed
        assert!(protocol.dual().is_wellformed());
    }

    // ========================================================================
    // Coinductive Session Subtyping Tests
    // ========================================================================

    #[test]
    fn test_subtype_reflexive() {
        // End <: End
        assert!(SessionType::End.is_subtype_of(&SessionType::End));

        // Var <: Var (same variable)
        let var = SessionVar::new(0);
        assert!(SessionType::var(var).is_subtype_of(&SessionType::var(var)));

        // Send <: Send (same types)
        let send = SessionType::send(BrrrType::BOOL, SessionType::End);
        assert!(send.is_subtype_of(&send));

        // Recv <: Recv (same types)
        let recv = SessionType::recv(BrrrType::BOOL, SessionType::End);
        assert!(recv.is_subtype_of(&recv));
    }

    #[test]
    fn test_subtype_var_different() {
        // Different variables are not subtypes
        let var0 = SessionVar::new(0);
        let var1 = SessionVar::new(1);
        assert!(!SessionType::var(var0).is_subtype_of(&SessionType::var(var1)));
    }

    #[test]
    fn test_subtype_send_continuation() {
        // !Bool.end <: !Bool.end
        let s1 = SessionType::send(BrrrType::BOOL, SessionType::End);
        let s2 = SessionType::send(BrrrType::BOOL, SessionType::End);
        assert!(s1.is_subtype_of(&s2));

        // !Bool.!Bool.end <: !Bool.!Bool.end
        let s3 = SessionType::send(
            BrrrType::BOOL,
            SessionType::send(BrrrType::BOOL, SessionType::End),
        );
        assert!(s3.is_subtype_of(&s3));
    }

    #[test]
    fn test_subtype_recv_continuation() {
        // ?Bool.end <: ?Bool.end
        let r1 = SessionType::recv(BrrrType::BOOL, SessionType::End);
        let r2 = SessionType::recv(BrrrType::BOOL, SessionType::End);
        assert!(r1.is_subtype_of(&r2));
    }

    #[test]
    fn test_subtype_send_recv_not_compatible() {
        // Send and Recv are not subtypes of each other
        let send = SessionType::send(BrrrType::BOOL, SessionType::End);
        let recv = SessionType::recv(BrrrType::BOOL, SessionType::End);
        assert!(!send.is_subtype_of(&recv));
        assert!(!recv.is_subtype_of(&send));
    }

    #[test]
    fn test_subtype_different_payload() {
        // Different payload types -> not subtypes (using structural equality)
        let s1 = SessionType::send(BrrrType::BOOL, SessionType::End);
        let s2 = SessionType::send(BrrrType::STRING, SessionType::End);
        assert!(!s1.is_subtype_of(&s2));
        assert!(!s2.is_subtype_of(&s1));
    }

    #[test]
    fn test_subtype_select_fewer_labels() {
        use lasso::Rodeo;

        let mut rodeo = Rodeo::default();
        let l_ok = rodeo.get_or_intern("ok");
        let l_err = rodeo.get_or_intern("err");

        // +{ok: end} <: +{ok: end, err: end}
        // A selector that only selects 'ok' is a subtype of one that could select 'ok' or 'err'
        let s1 = SessionType::select(vec![(l_ok, SessionType::End)]);
        let s2 = SessionType::select(vec![
            (l_ok, SessionType::End),
            (l_err, SessionType::End),
        ]);
        assert!(s1.is_subtype_of(&s2));

        // But not the reverse: +{ok: end, err: end} is NOT <: +{ok: end}
        // because s2 might select 'err' which s1 doesn't have
        assert!(!s2.is_subtype_of(&s1));
    }

    #[test]
    fn test_subtype_branch_more_labels() {
        use lasso::Rodeo;

        let mut rodeo = Rodeo::default();
        let l_ok = rodeo.get_or_intern("ok");
        let l_err = rodeo.get_or_intern("err");

        // &{ok: end, err: end} <: &{ok: end}
        // A handler that handles both 'ok' and 'err' is a subtype of one that only needs 'ok'
        let b1 = SessionType::branch(vec![
            (l_ok, SessionType::End),
            (l_err, SessionType::End),
        ]);
        let b2 = SessionType::branch(vec![(l_ok, SessionType::End)]);
        assert!(b1.is_subtype_of(&b2));

        // But not the reverse: &{ok: end} is NOT <: &{ok: end, err: end}
        // because b2 might receive 'err' which b1 doesn't handle
        assert!(!b2.is_subtype_of(&b1));
    }

    #[test]
    fn test_subtype_recursive_reflexive() {
        // rec X.!Bool.X <: rec X.!Bool.X (coinductive reflexivity)
        let var = SessionVar::new(0);
        let rec = SessionType::rec(var, SessionType::send(BrrrType::BOOL, SessionType::var(var)));
        assert!(rec.is_subtype_of(&rec));
    }

    #[test]
    fn test_subtype_recursive_coinductive() {
        // Tests the coinductive aspect: the recursion terminates because we track visited pairs
        let var = SessionVar::new(0);

        // rec X.!Bool.?Bool.X - a protocol that alternates send and receive
        let body = SessionType::send(
            BrrrType::BOOL,
            SessionType::recv(BrrrType::BOOL, SessionType::var(var)),
        );
        let rec = SessionType::rec(var, body);

        // Should not hang due to coinductive termination
        assert!(rec.is_subtype_of(&rec));
    }

    #[test]
    fn test_subtype_nested_send_recv() {
        // !Bool.?Bool.end <: !Bool.?Bool.end
        let s = SessionType::send(
            BrrrType::BOOL,
            SessionType::recv(BrrrType::BOOL, SessionType::End),
        );
        assert!(s.is_subtype_of(&s));

        // Different payload in continuation -> not subtype
        let s1 = SessionType::send(
            BrrrType::BOOL,
            SessionType::recv(BrrrType::BOOL, SessionType::End),
        );
        let s2 = SessionType::send(
            BrrrType::BOOL,
            SessionType::recv(BrrrType::STRING, SessionType::End),
        );
        assert!(!s1.is_subtype_of(&s2));
    }

    #[test]
    fn test_subtype_empty_select_branch() {
        // Empty select/branch
        let empty_select = SessionType::select(vec![]);
        let empty_branch = SessionType::branch(vec![]);

        // Empty select <: empty select
        assert!(empty_select.is_subtype_of(&empty_select));

        // Empty branch <: empty branch
        assert!(empty_branch.is_subtype_of(&empty_branch));

        // Empty select <: any select (trivially - no labels to check)
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let l = rodeo.get_or_intern("x");
        let non_empty_select = SessionType::select(vec![(l, SessionType::End)]);
        assert!(empty_select.is_subtype_of(&non_empty_select));

        // Any branch <: empty branch (trivially - no labels required)
        let non_empty_branch = SessionType::branch(vec![(l, SessionType::End)]);
        assert!(non_empty_branch.is_subtype_of(&empty_branch));
    }

    #[test]
    fn test_subtype_end_not_subtype_of_others() {
        let send = SessionType::send(BrrrType::BOOL, SessionType::End);
        let recv = SessionType::recv(BrrrType::BOOL, SessionType::End);

        assert!(!SessionType::End.is_subtype_of(&send));
        assert!(!SessionType::End.is_subtype_of(&recv));
        assert!(!send.is_subtype_of(&SessionType::End));
        assert!(!recv.is_subtype_of(&SessionType::End));
    }
}
