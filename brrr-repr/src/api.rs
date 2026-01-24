//! Public API for the representation engine
//!
//! Provides high-level encode/decode functions for .brrr and .brrrx formats.

use std::io::{Read, Write};
use std::path::Path;

use crate::encoding::{BinaryDecoder, BinaryEncoder, TextDecoder, TextEncoder};
use crate::error::ReprResult;
use crate::expr::Expr;
use crate::types::BrrrType;

/// Output format for encoding
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Format {
    /// Binary format (.brrr) - efficient, compact
    #[default]
    Binary,
    /// Text format (.brrrx) - human-readable, debuggable
    Text,
}

impl Format {
    /// Detect format from file extension
    pub fn from_extension(path: impl AsRef<Path>) -> Self {
        match path.as_ref().extension().and_then(|e| e.to_str()) {
            Some("brrrx") => Self::Text,
            _ => Self::Binary,
        }
    }

    /// Get file extension for this format
    pub const fn extension(self) -> &'static str {
        match self {
            Self::Binary => "brrr",
            Self::Text => "brrrx",
        }
    }
}

/// A complete brrr module with types, expressions, and metadata
#[derive(Debug, Clone, Default)]
pub struct BrrrModule {
    /// Module name
    pub name: String,
    /// Source files referenced
    pub files: Vec<String>,
    /// Type definitions
    pub types: Vec<BrrrType>,
    /// Top-level expressions
    pub exprs: Vec<Expr>,
    /// Module version
    pub version: u16,
}

impl BrrrModule {
    /// Create a new empty module
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            files: Vec::new(),
            types: Vec::new(),
            exprs: Vec::new(),
            version: 1,
        }
    }

    /// Add a source file
    pub fn add_file(&mut self, path: impl Into<String>) -> u32 {
        let id = self.files.len() as u32;
        self.files.push(path.into());
        id
    }

    /// Add a type definition
    pub fn add_type(&mut self, ty: BrrrType) -> u32 {
        let id = self.types.len() as u32;
        self.types.push(ty);
        id
    }

    /// Add an expression
    pub fn add_expr(&mut self, expr: Expr) -> u32 {
        let id = self.exprs.len() as u32;
        self.exprs.push(expr);
        id
    }
}

/// Main encoder for .brrr format
#[derive(Debug)]
pub struct BrrrEncoder {
    module: BrrrModule,
}

impl BrrrEncoder {
    /// Create a new encoder
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            module: BrrrModule::new(name),
        }
    }

    /// Create from an existing module
    pub fn from_module(module: BrrrModule) -> Self {
        Self { module }
    }

    /// Add a source file, returns file ID
    pub fn add_file(&mut self, path: impl Into<String>) -> u32 {
        self.module.add_file(path)
    }

    /// Add a type, returns type ID
    pub fn add_type(&mut self, ty: BrrrType) -> u32 {
        self.module.add_type(ty)
    }

    /// Add an expression, returns expression ID
    pub fn add_expr(&mut self, expr: Expr) -> u32 {
        self.module.add_expr(expr)
    }

    /// Encode to binary format
    pub fn encode_binary<W: Write>(&self, writer: W) -> ReprResult<()> {
        let encoder = BinaryEncoder::new();
        encoder.encode(&self.module, writer)
    }

    /// Encode to text format
    pub fn encode_text<W: Write>(&self, writer: W) -> ReprResult<()> {
        let encoder = TextEncoder::new();
        encoder.encode(&self.module, writer)
    }

    /// Encode to the specified format
    pub fn encode<W: Write>(&self, writer: W, format: Format) -> ReprResult<()> {
        match format {
            Format::Binary => self.encode_binary(writer),
            Format::Text => self.encode_text(writer),
        }
    }

    /// Compute content hash of the module
    pub fn content_hash(&self) -> [u8; 16] {
        crate::encoding::content_hash(&self.module)
    }
}

/// Main decoder for .brrr format
#[derive(Debug)]
pub struct BrrrDecoder {
    module: BrrrModule,
}

impl BrrrDecoder {
    /// Decode from binary format
    pub fn decode_binary<R: Read>(reader: R) -> ReprResult<Self> {
        let decoder = BinaryDecoder::new();
        let module = decoder.decode(reader)?;
        Ok(Self { module })
    }

    /// Decode from text format
    pub fn decode_text<R: Read>(reader: R) -> ReprResult<Self> {
        let decoder = TextDecoder::new();
        let module = decoder.decode(reader)?;
        Ok(Self { module })
    }

    /// Auto-detect format and decode
    pub fn decode<R: Read>(reader: R, format: Format) -> ReprResult<Self> {
        match format {
            Format::Binary => Self::decode_binary(reader),
            Format::Text => Self::decode_text(reader),
        }
    }

    /// Get the decoded module
    pub fn into_module(self) -> BrrrModule {
        self.module
    }

    /// Borrow the decoded module
    pub fn module(&self) -> &BrrrModule {
        &self.module
    }

    /// Get type by ID
    pub fn get_type(&self, id: u32) -> Option<&BrrrType> {
        self.module.types.get(id as usize)
    }

    /// Get expression by ID
    pub fn get_expr(&self, id: u32) -> Option<&Expr> {
        self.module.exprs.get(id as usize)
    }

    /// Verify content hash
    pub fn verify_hash(&self, expected: &[u8; 16]) -> bool {
        let actual = crate::encoding::content_hash(&self.module);
        actual == *expected
    }
}

// ============================================================================
// Convenience functions
// ============================================================================

/// Encode a module to a file
pub fn encode_file(path: impl AsRef<Path>, module: &BrrrModule) -> ReprResult<()> {
    let path = path.as_ref();
    let format = Format::from_extension(path);
    let file = std::fs::File::create(path)?;
    let writer = std::io::BufWriter::new(file);

    let encoder = BrrrEncoder::from_module(module.clone());
    encoder.encode(writer, format)
}

/// Decode a module from a file
pub fn decode_file(path: impl AsRef<Path>) -> ReprResult<BrrrModule> {
    let path = path.as_ref();
    let format = Format::from_extension(path);
    let file = std::fs::File::open(path)?;
    let reader = std::io::BufReader::new(file);

    let decoder = BrrrDecoder::decode(reader, format)?;
    Ok(decoder.into_module())
}

/// Convert between formats
pub fn convert(input: impl AsRef<Path>, output: impl AsRef<Path>) -> ReprResult<()> {
    let module = decode_file(input)?;
    encode_file(output, &module)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_from_extension() {
        assert_eq!(Format::from_extension("foo.brrr"), Format::Binary);
        assert_eq!(Format::from_extension("foo.brrrx"), Format::Text);
        assert_eq!(Format::from_extension("foo.txt"), Format::Binary); // Default
    }

    #[test]
    fn test_module_builder() {
        let mut encoder = BrrrEncoder::new("test");
        let file_id = encoder.add_file("main.brrr");
        assert_eq!(file_id, 0);

        let type_id = encoder.add_type(BrrrType::Prim(crate::types::PrimKind::Unit));
        assert_eq!(type_id, 0);
    }
}
