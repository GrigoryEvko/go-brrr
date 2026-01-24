//! Error types for the representation engine

use std::io;
use thiserror::Error;

/// Result type alias for repr operations
pub type ReprResult<T> = Result<T, ReprError>;

/// Top-level error type
#[derive(Debug, Error)]
pub enum ReprError {
    /// I/O error during read/write
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),

    /// Encoding error
    #[error("Encoding error: {0}")]
    Encode(#[from] EncodeError),

    /// Decoding error
    #[error("Decoding error: {0}")]
    Decode(#[from] DecodeError),

    /// Invalid format
    #[error("Invalid format: {0}")]
    Format(String),

    /// Version mismatch
    #[error("Version mismatch: expected {expected}, got {actual}")]
    Version { expected: u16, actual: u16 },

    /// Hash mismatch (corruption detected)
    #[error("Content hash mismatch: expected {expected}, got {actual}")]
    HashMismatch { expected: String, actual: String },
}

/// Encoding-specific errors
#[derive(Debug, Error)]
pub enum EncodeError {
    /// I/O error during encoding
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),

    /// Value too large to encode
    #[error("Value too large: {value} exceeds maximum {max}")]
    Overflow { value: u64, max: u64 },

    /// Invalid data for encoding
    #[error("Invalid data: {0}")]
    InvalidData(String),

    /// String interning failed
    #[error("String interning failed: {0}")]
    InternError(String),

    /// Section too large
    #[error("Section too large: {size} bytes exceeds limit")]
    SectionTooLarge { size: u64 },
}

/// Decoding-specific errors
#[derive(Debug, Error)]
pub enum DecodeError {
    /// I/O error during decoding
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),

    /// Invalid magic number
    #[error("Invalid magic number: expected BRRR, got {0:?}")]
    InvalidMagic([u8; 4]),

    /// Unexpected end of file
    #[error("Unexpected end of file at offset {offset}")]
    UnexpectedEof { offset: u64 },

    /// Invalid varint encoding
    #[error("Invalid varint encoding")]
    InvalidVarint,

    /// Varint overflow
    #[error("Varint overflow: value exceeds 64 bits")]
    VarintOverflow,

    /// Invalid discriminant
    #[error("Invalid discriminant {value} for {type_name}")]
    InvalidDiscriminant { value: u8, type_name: &'static str },

    /// Invalid string reference
    #[error("Invalid string reference: {index} >= {table_size}")]
    InvalidStringRef { index: u32, table_size: u32 },

    /// Invalid type reference
    #[error("Invalid type reference: {index} >= {table_size}")]
    InvalidTypeRef { index: u32, table_size: u32 },

    /// Invalid section
    #[error("Invalid section: {0}")]
    InvalidSection(String),

    /// Missing required section
    #[error("Missing required section: {0:?}")]
    MissingSection(crate::encoding::SectionKind),

    /// Parse error (for text format)
    #[error("Parse error at line {line}, column {col}: {message}")]
    ParseError {
        line: u32,
        col: u32,
        message: String,
    },

    /// Unsupported feature
    #[error("Unsupported feature: {0}")]
    Unsupported(String),
}

impl DecodeError {
    /// Create a parse error
    pub fn parse(line: u32, col: u32, message: impl Into<String>) -> Self {
        Self::ParseError {
            line,
            col,
            message: message.into(),
        }
    }

    /// Create an invalid discriminant error
    pub fn invalid_discriminant(value: u8, type_name: &'static str) -> Self {
        Self::InvalidDiscriminant { value, type_name }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_display() {
        let err = DecodeError::InvalidMagic([0x00, 0x01, 0x02, 0x03]);
        assert!(err.to_string().contains("Invalid magic"));

        let err = DecodeError::parse(10, 5, "unexpected token");
        assert!(err.to_string().contains("line 10"));
    }
}
