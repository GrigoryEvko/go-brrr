//! Encoding and decoding infrastructure
//!
//! Provides binary (.brrr) and text (.brrrx) format support.
//!
//! # Modules
//! - `varint`: Variable-length integer encoding (LEB128)
//! - `intern`: Runtime string interning with lasso
//! - `interner`: Serializable string interner for binary format
//! - `sections`: Binary section headers
//! - `binary`: Binary format encoder/decoder
//! - `text`: Text format encoder/decoder
//! - `hash`: Content hashing

mod varint;
mod intern;
mod interner;
mod sections;
mod binary;
mod text;
mod hash;

pub use varint::{decode_varint, encode_varint};
pub use intern::StringInterner;
pub use interner::{
    SerializableInterner, SpurMapper,
    // Label type alias (not exported from expr module)
    Label,
    // Encoding/decoding helpers
    encode_var_id, decode_var_id,
    encode_type_var, decode_type_var,
    encode_type_name, decode_type_name,
    encode_label, decode_label,
    encode_effect_var, decode_effect_var,
    encode_option_spur, decode_option_spur,
    encode_spur, decode_spur,
};
pub use sections::{SectionHeader, SectionKind};
pub use binary::{BinaryEncoder, BinaryDecoder};
pub use text::{TextEncoder, TextDecoder};
pub use hash::content_hash;
