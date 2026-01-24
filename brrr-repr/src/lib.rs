//! .brrr Representation Engine
//!
//! This module provides serialization/deserialization for the brrr-lang IR
//! into efficient binary (.brrr) and human-readable text (.brrrx) formats.
//!
//! # UTF-8 Only
//! Uses proper mathematical Unicode symbols throughout - no ASCII fallback.
//!
//! # Format Overview
//! - `.brrr` - Binary format with columnar storage, string interning, content hashing
//! - `.brrrx` - Text format with UTF-8 math notation for debugging/inspection

pub mod types;
pub mod expr;
pub mod effects;
pub mod modes;
pub mod encoding;
mod error;
mod api;

pub use api::{BrrrDecoder, BrrrEncoder, BrrrModule, Format};
pub use error::{DecodeError, EncodeError, ReprError, ReprResult};
pub use types::{BrrrType, FuncType, NumericType, ParamType, PrimKind, WrapperKind};
pub use expr::{Expr, Expr_, Literal, Pattern, Pattern_, Pos, Range, WithLoc};
pub use effects::{AbstractLoc, EffectOp, EffectRow, IoSink, IoSource};
pub use modes::{Mode, RefKind};
