//! Text format encoder/decoder (.brrrx)

use std::io::{Read, Write};
use crate::api::BrrrModule;
use crate::error::ReprResult;

/// Text format encoder
#[derive(Debug, Default)]
pub struct TextEncoder {
    _private: (),
}

impl TextEncoder {
    /// Create a new encoder
    pub fn new() -> Self {
        Self::default()
    }

    /// Encode a module to the writer
    pub fn encode<W: Write>(&self, module: &BrrrModule, mut writer: W) -> ReprResult<()> {
        // Write header
        writeln!(writer, "; brrr text format v{}", module.version)?;
        writeln!(writer, "(module \"{}\"", module.name)?;

        // Write files
        if !module.files.is_empty() {
            writeln!(writer, "  (files")?;
            for (i, file) in module.files.iter().enumerate() {
                writeln!(writer, "    ({} \"{}\")", i, file)?;
            }
            writeln!(writer, "  )")?;
        }

        // Write types placeholder
        if !module.types.is_empty() {
            writeln!(writer, "  (types")?;
            for (i, _ty) in module.types.iter().enumerate() {
                writeln!(writer, "    ({} ...)", i)?;
            }
            writeln!(writer, "  )")?;
        }

        // Write exprs placeholder
        if !module.exprs.is_empty() {
            writeln!(writer, "  (exprs")?;
            for (i, _expr) in module.exprs.iter().enumerate() {
                writeln!(writer, "    ({} ...)", i)?;
            }
            writeln!(writer, "  )")?;
        }

        writeln!(writer, ")")?;

        Ok(())
    }
}

/// Text format decoder
#[derive(Debug, Default)]
pub struct TextDecoder {
    _private: (),
}

impl TextDecoder {
    /// Create a new decoder
    pub fn new() -> Self {
        Self::default()
    }

    /// Decode a module from the reader
    pub fn decode<R: Read>(&self, mut reader: R) -> ReprResult<BrrrModule> {
        use crate::error::DecodeError;

        let mut content = String::new();
        reader.read_to_string(&mut content)?;

        // Simple parsing - find module name
        let name = if let Some(start) = content.find("(module \"") {
            let rest = &content[start + 9..];
            if let Some(end) = rest.find('"') {
                rest[..end].to_string()
            } else {
                return Err(DecodeError::parse(1, 1, "missing module name closing quote").into());
            }
        } else {
            return Err(DecodeError::parse(1, 1, "missing module declaration").into());
        };

        // Extract version from header if present
        let version = if let Some(idx) = content.find("; brrr text format v") {
            let rest = &content[idx + 20..];
            rest.lines()
                .next()
                .and_then(|l| l.trim().parse().ok())
                .unwrap_or(1)
        } else {
            1
        };

        Ok(BrrrModule {
            name,
            files: Vec::new(),
            types: Vec::new(),
            exprs: Vec::new(),
            version,
        })
    }
}
