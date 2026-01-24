//! Binary format encoder/decoder (.brrr)

use std::io::{Read, Write};
use crate::api::BrrrModule;
use crate::error::ReprResult;

/// Magic number for .brrr files
const MAGIC: [u8; 4] = *b"BRRR";

/// Current format version
const VERSION: u16 = 1;

/// Binary format encoder
#[derive(Debug, Default)]
pub struct BinaryEncoder {
    _private: (),
}

impl BinaryEncoder {
    /// Create a new encoder
    pub fn new() -> Self {
        Self::default()
    }

    /// Encode a module to the writer
    pub fn encode<W: Write>(&self, module: &BrrrModule, mut writer: W) -> ReprResult<()> {
        // Write magic
        writer.write_all(&MAGIC)?;

        // Write version
        writer.write_all(&VERSION.to_le_bytes())?;

        // Write module name length and data
        let name_bytes = module.name.as_bytes();
        writer.write_all(&(name_bytes.len() as u32).to_le_bytes())?;
        writer.write_all(name_bytes)?;

        // Write file count
        writer.write_all(&(module.files.len() as u32).to_le_bytes())?;
        for file in &module.files {
            let bytes = file.as_bytes();
            writer.write_all(&(bytes.len() as u32).to_le_bytes())?;
            writer.write_all(bytes)?;
        }

        // Write type count (types serialization is placeholder)
        writer.write_all(&(module.types.len() as u32).to_le_bytes())?;

        // Write expr count (expr serialization is placeholder)
        writer.write_all(&(module.exprs.len() as u32).to_le_bytes())?;

        // Write content hash
        let hash = super::content_hash(module);
        writer.write_all(&hash)?;

        Ok(())
    }
}

/// Binary format decoder
#[derive(Debug, Default)]
pub struct BinaryDecoder {
    _private: (),
}

impl BinaryDecoder {
    /// Create a new decoder
    pub fn new() -> Self {
        Self::default()
    }

    /// Decode a module from the reader
    pub fn decode<R: Read>(&self, mut reader: R) -> ReprResult<BrrrModule> {
        use crate::error::DecodeError;

        // Read and verify magic
        let mut magic = [0u8; 4];
        reader.read_exact(&mut magic)?;
        if magic != MAGIC {
            return Err(DecodeError::InvalidMagic(magic).into());
        }

        // Read version
        let mut version_bytes = [0u8; 2];
        reader.read_exact(&mut version_bytes)?;
        let version = u16::from_le_bytes(version_bytes);

        // Read module name
        let mut len_bytes = [0u8; 4];
        reader.read_exact(&mut len_bytes)?;
        let name_len = u32::from_le_bytes(len_bytes) as usize;
        let mut name_bytes = vec![0u8; name_len];
        reader.read_exact(&mut name_bytes)?;
        let name = String::from_utf8(name_bytes)
            .map_err(|e| DecodeError::InvalidSection(e.to_string()))?;

        // Read files
        reader.read_exact(&mut len_bytes)?;
        let file_count = u32::from_le_bytes(len_bytes) as usize;
        let mut files = Vec::with_capacity(file_count);
        for _ in 0..file_count {
            reader.read_exact(&mut len_bytes)?;
            let len = u32::from_le_bytes(len_bytes) as usize;
            let mut bytes = vec![0u8; len];
            reader.read_exact(&mut bytes)?;
            let s = String::from_utf8(bytes)
                .map_err(|e| DecodeError::InvalidSection(e.to_string()))?;
            files.push(s);
        }

        // Read type count (actual types not deserialized yet)
        reader.read_exact(&mut len_bytes)?;
        let _type_count = u32::from_le_bytes(len_bytes);

        // Read expr count (actual exprs not deserialized yet)
        reader.read_exact(&mut len_bytes)?;
        let _expr_count = u32::from_le_bytes(len_bytes);

        // Read content hash (for verification)
        let mut _hash = [0u8; 16];
        reader.read_exact(&mut _hash)?;

        Ok(BrrrModule {
            name,
            files,
            types: Vec::new(),
            exprs: Vec::new(),
            version,
        })
    }
}
