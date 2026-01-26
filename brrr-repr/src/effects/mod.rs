//! Effect system types
//!
//! Mirrors F* Effects.fsti with 50+ effect operations.
//!
//! # Effect Rows
//!
//! Effect rows track the effects a computation may perform, with support
//! for row polymorphism via `EffectVar`.
//!
//! - `EffectRow` - Flattened representation for efficient operations
//! - `EffectRowKind` - Algebraic representation for type checking
//! - `EffectVar` - Row variable for effect polymorphism
//!
//! # Handler Infrastructure
//!
//! - `OpSig` - Signature of a single effect operation
//! - `EffectSig` - Signature of an effect (list of operations + purity)
//! - `ExtendedHandler` - Handler with depth and linearity annotations
//!
//! # Free Monad
//!
//! The `free` module provides Free monad types for effect semantics:
//!
//! - `Free` - Free monad ADT (Return | Bind)
//! - `FreeProgram` - Complete program with continuation table
//! - `FreeProgramBuilder` - Fluent builder for programs
//! - `Value` - Runtime values for effect arguments
//!
//! # Handler Semantics
//!
//! Effects are NOT deduplicated in rows. A handler consumes ONE instance
//! of an effect at a time, enabling precise tracking of nested handlers.

mod free;
mod handler;
mod locations;
mod ops;
mod row;

pub use free::{ContId, Free, FreeOp, FreeProgram, FreeProgramBuilder, Value, CONT_NONE};
pub use handler::{
    // Re-exports from expr module
    Continuation, ContinuationLinearity, EffectHandler, HandlerClause, HandlerDepth,
    // New handler infrastructure types
    EffectSig, ExtendedHandler, Linearity, OpSig,
};
pub use locations::{AbstractLoc, ChanId, IoSink, IoSource, LockId};
pub use ops::{EffectOp, EffectType};
pub use row::{EffectRow, EffectRowKind, EffectVar, RowTail, PURE};
