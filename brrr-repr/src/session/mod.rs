//! Session type system
//!
//! Binary and multiparty session types for typed communication protocols.
//!
//! # Overview
//!
//! Session types provide static typing for communication protocols, ensuring:
//! - Protocol compliance at compile time
//! - Deadlock freedom (for well-typed programs)
//! - Type-safe message passing
//!
//! # Binary Session Types
//!
//! Two-party communication following Honda's 1998 session type theory.
//!
//! ## Notation
//! - `!T.S` - Send type T, continue with S
//! - `?T.S` - Receive type T, continue with S
//! - `+{l1: S1, l2: S2}` - Internal choice (sender selects)
//! - `&{l1: S1, l2: S2}` - External choice (receiver offers)
//! - `rec X.S` - Recursive session type
//! - `X` - Recursion variable
//! - `end` - Protocol termination
//!
//! ## Duality
//!
//! Every session type has a dual that represents the other party's view:
//! ```text
//! dual(!T.S) = ?T.dual(S)
//! dual(?T.S) = !T.dual(S)
//! dual(+{...}) = &{...}
//! dual(&{...}) = +{...}
//! dual(end) = end
//! ```
//!
//! # Multiparty Session Types
//!
//! N-party communication following Honda, Yoshida, Carbone 2008.
//!
//! ## Global Types
//! Describe the complete protocol from a bird's eye view:
//! - `A -> B: T. G` - A sends T to B
//! - `A -> B: {l1: G1, l2: G2}` - A sends choice to B
//! - `rec X. G` - Recursive protocol
//! - `end` - Protocol termination
//!
//! ## Projection
//! Each participant's local view is obtained by projecting the global type.
//!
//! # References
//!
//! - Honda, K. (1998). Session types and pi-calculus.
//! - Honda, Yoshida, Carbone (2008). Multiparty asynchronous session types.

pub mod binary;
pub mod deadlock;
pub mod multiparty;
pub mod priority;

pub use binary::{
    all_ended, disjoint_ctx, empty_session_ctx, has_channel, lookup_channel, make_channel,
    make_channel_pair, merge_ctx, remove_channel, update_channel, ChannelEndpoint, DebugInterner,
    Label, LabelInterner, SessionCtx, SessionType, SessionVar,
};
pub use multiparty::{
    get_participants, is_well_formed, GTypeVar, GlobalType, GlobalVar, LocalType, Participant,
};
pub use priority::{
    all_priorities, first_priority, is_pri_dual_of, is_pri_self_dual, max_priority, min_priority,
    pri_dual, priorities_contiguous_from, priorities_strictly_increasing, priority_consistent,
    unique_priorities, PriSession, Priority,
};
pub use deadlock::{
    analyze_deadlock, build_dep_graph, build_dep_graph_with_pairs, build_global_dep_graph,
    dfs_cycle_check, find_deadlock_cycles, has_cycle, has_cycle_from, has_global_cycle,
    is_deadlock_free, is_deadlock_free_global, is_deadlock_free_with_pairs, DeadlockAnalysis,
    DepEdge, DepGraph, GlobalDepGraph,
};
