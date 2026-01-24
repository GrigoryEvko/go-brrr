//! Section types for the binary format (.brrr)
//!
//! Binary format structure:
//! ```text
//! +------------------+
//! | Magic: "BRRR"    | 4 bytes
//! | Version: u16     | 2 bytes
//! | Flags: u16       | 2 bytes
//! +------------------+
//! | Section Count    | varint
//! | Section Directory| (kind, offset, size)*
//! +------------------+
//! | SECTION: Strings | Interned strings
//! | SECTION: Types   | Type definitions
//! | SECTION: Exprs   | Expression tree
//! | SECTION: Effects | Effect rows
//! | SECTION: Files   | Source file paths
//! | SECTION: Meta    | Metadata
//! +------------------+
//! | Content Hash     | xxh3 128-bit
//! +------------------+
//! ```

use serde::{Deserialize, Serialize};

/// Magic number for .brrr files
pub const MAGIC: [u8; 4] = *b"BRRR";

/// Current binary format version
pub const VERSION: u16 = 1;

/// Section kinds in the binary format
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum SectionKind {
    /// String table section - interned strings with lasso
    Strings = 0,
    /// Type definitions section
    Types = 1,
    /// Expression section
    Exprs = 2,
    /// Effect rows section
    Effects = 3,
    /// File table section - source file paths
    Files = 4,
    /// Metadata section - module name, version, etc.
    Meta = 5,
}

impl SectionKind {
    /// Convert from discriminant
    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            0 => Some(Self::Strings),
            1 => Some(Self::Types),
            2 => Some(Self::Exprs),
            3 => Some(Self::Effects),
            4 => Some(Self::Files),
            5 => Some(Self::Meta),
            _ => None,
        }
    }

    /// Get the name of this section
    pub const fn name(self) -> &'static str {
        match self {
            Self::Strings => "strings",
            Self::Types => "types",
            Self::Exprs => "exprs",
            Self::Effects => "effects",
            Self::Files => "files",
            Self::Meta => "meta",
        }
    }

    /// Is this section required?
    pub const fn is_required(self) -> bool {
        matches!(self, Self::Strings | Self::Meta)
    }

    /// All section kinds in canonical order
    pub const ALL: [Self; 6] = [
        Self::Strings,
        Self::Types,
        Self::Exprs,
        Self::Effects,
        Self::Files,
        Self::Meta,
    ];
}

/// Header for a section in the binary format
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct SectionHeader {
    /// Section kind
    pub kind: SectionKind,
    /// Offset from start of file (after main header)
    pub offset: u64,
    /// Size of section data in bytes
    pub size: u64,
}

impl SectionHeader {
    /// Create a new section header
    pub fn new(kind: SectionKind, offset: u64, size: u64) -> Self {
        Self { kind, offset, size }
    }

    /// Create a section header with zero offset (to be filled later)
    pub fn empty(kind: SectionKind) -> Self {
        Self {
            kind,
            offset: 0,
            size: 0,
        }
    }
}

/// File header (first 8 bytes)
#[derive(Debug, Clone, Copy)]
pub struct FileHeader {
    /// Magic number (must be "BRRR")
    pub magic: [u8; 4],
    /// Format version
    pub version: u16,
    /// Flags (reserved for future use)
    pub flags: u16,
}

impl FileHeader {
    /// Size of the file header in bytes
    pub const SIZE: usize = 8;

    /// Create a new file header with current version
    pub const fn new() -> Self {
        Self {
            magic: MAGIC,
            version: VERSION,
            flags: 0,
        }
    }

    /// Validate the magic number
    pub fn validate_magic(&self) -> bool {
        self.magic == MAGIC
    }
}

impl Default for FileHeader {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_section_kind_roundtrip() {
        for kind in SectionKind::ALL {
            let disc = kind as u8;
            let parsed = SectionKind::from_u8(disc);
            assert_eq!(parsed, Some(kind));
        }
    }

    #[test]
    fn test_file_header_magic() {
        let header = FileHeader::new();
        assert!(header.validate_magic());
        assert_eq!(header.version, VERSION);
    }

    #[test]
    fn test_section_header_size() {
        assert_eq!(FileHeader::SIZE, 8);
    }
}
