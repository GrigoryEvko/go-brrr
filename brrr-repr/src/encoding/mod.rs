//! Encoding and decoding infrastructure
//!
//! Provides binary (.brrr) and text (.brrrx) format support.

mod varint;
mod intern;
mod sections;
mod binary;
mod text;
mod hash;

pub use varint::{decode_varint, encode_varint};
pub use intern::StringInterner;
pub use sections::{SectionHeader, SectionKind};
pub use binary::{BinaryEncoder, BinaryDecoder};
pub use text::{TextEncoder, TextDecoder};
pub use hash::content_hash;
