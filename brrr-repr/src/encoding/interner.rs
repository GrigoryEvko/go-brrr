//! String interner serialization for binary format
//!
//! Provides `SerializableInterner` for encoding/decoding string tables in binary format,
//! and `SpurMapper` for converting between `lasso::Spur` and serializable u32 indices.
//!
//! # Problem
//! `lasso::Spur` is an opaque 4-byte key into a thread-local interner. Binary serialization
//! needs to write/read actual strings, not Spur keys. This module bridges that gap.
//!
//! # Encoding Format
//! ```text
//! [count: varint]
//! [string1_len: varint][string1_bytes: utf8]
//! [string2_len: varint][string2_bytes: utf8]
//! ...
//! ```

use std::collections::HashMap;
use std::io::{Read, Write};

use lasso::{Rodeo, Spur, ThreadedRodeo};

use super::varint::{decode_varint32_from, encode_varint_to};
use crate::error::{DecodeError, EncodeError};

// Import Spur type aliases from the crate's public API
pub use crate::expr::VarId;
pub use crate::types::{TypeName, TypeVar};

// Note: We define our own type alias here to avoid conflict with effects::EffectVar.
// crate::types::scheme::EffectVar is a Spur alias, but effects::row::EffectVar is a struct.
// For string interning, we only care about Spur-based identifiers.
/// Effect variable for type scheme serialization (Spur alias)
pub type EffectVar = Spur;

/// Label for loops/control flow (alias of Spur)
///
/// Note: This is defined here because the expr module doesn't export Label.
/// It's the same underlying type as all other Spur-based identifiers.
pub type Label = Spur;

/// Serializable string interner for binary format.
///
/// Unlike `lasso::Rodeo` which uses opaque Spur keys, this interner uses
/// sequential u32 indices that can be serialized to binary format.
///
/// # Usage
/// ```ignore
/// let mut interner = SerializableInterner::new();
/// let idx = interner.intern("hello");  // Returns 0
/// let idx2 = interner.intern("world"); // Returns 1
/// let idx3 = interner.intern("hello"); // Returns 0 (deduplicated)
///
/// // Encode to binary
/// let mut buf = Vec::new();
/// interner.encode(&mut buf).unwrap();
///
/// // Decode from binary
/// let decoded = SerializableInterner::decode(&mut buf.as_slice()).unwrap();
/// assert_eq!(decoded.resolve(0), Some("hello"));
/// ```
#[derive(Debug, Clone)]
pub struct SerializableInterner {
    /// Indexed strings (index -> string)
    strings: Vec<String>,
    /// Reverse lookup (string -> index) for deduplication
    lookup: HashMap<String, u32>,
}

impl Default for SerializableInterner {
    fn default() -> Self {
        Self::new()
    }
}

impl SerializableInterner {
    /// Create a new empty interner.
    #[must_use]
    pub fn new() -> Self {
        Self {
            strings: Vec::new(),
            lookup: HashMap::new(),
        }
    }

    /// Create an interner with pre-allocated capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            strings: Vec::with_capacity(capacity),
            lookup: HashMap::with_capacity(capacity),
        }
    }

    /// Intern a string, returning its index.
    ///
    /// If the string was already interned, returns the existing index.
    /// Otherwise, adds the string and returns its new index.
    pub fn intern(&mut self, s: &str) -> u32 {
        if let Some(&idx) = self.lookup.get(s) {
            return idx;
        }

        let idx = self.strings.len() as u32;
        self.strings.push(s.to_owned());
        self.lookup.insert(s.to_owned(), idx);
        idx
    }

    /// Get string by index.
    ///
    /// Returns `None` if the index is out of bounds.
    #[must_use]
    pub fn resolve(&self, idx: u32) -> Option<&str> {
        self.strings.get(idx as usize).map(String::as_str)
    }

    /// Get index for a string if already interned.
    #[must_use]
    pub fn get(&self, s: &str) -> Option<u32> {
        self.lookup.get(s).copied()
    }

    /// Number of interned strings.
    #[must_use]
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Check if empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }

    /// Iterate over all (index, string) pairs.
    pub fn iter(&self) -> impl Iterator<Item = (u32, &str)> {
        self.strings
            .iter()
            .enumerate()
            .map(|(i, s)| (i as u32, s.as_str()))
    }

    /// Get all strings in order.
    #[must_use]
    pub fn strings(&self) -> &[String] {
        &self.strings
    }

    /// Write all strings to binary format.
    ///
    /// # Format
    /// ```text
    /// [count: varint]
    /// [string1_len: varint][string1_bytes: utf8]
    /// [string2_len: varint][string2_bytes: utf8]
    /// ...
    /// ```
    pub fn encode<W: Write>(&self, writer: &mut W) -> Result<(), EncodeError> {
        // Write count
        encode_varint_to(self.strings.len() as u64, writer)?;

        // Write each string
        for s in &self.strings {
            let bytes = s.as_bytes();
            encode_varint_to(bytes.len() as u64, writer)?;
            writer.write_all(bytes)?;
        }

        Ok(())
    }

    /// Read all strings from binary format.
    pub fn decode<R: Read>(reader: &mut R) -> Result<Self, DecodeError> {
        let count = decode_varint32_from(reader)? as usize;

        let mut strings = Vec::with_capacity(count);
        let mut lookup = HashMap::with_capacity(count);

        for i in 0..count {
            let len = decode_varint32_from(reader)? as usize;
            let mut bytes = vec![0u8; len];
            reader.read_exact(&mut bytes)?;

            let s = String::from_utf8(bytes)
                .map_err(|e| DecodeError::InvalidSection(format!("Invalid UTF-8 in string table: {}", e)))?;

            lookup.insert(s.clone(), i as u32);
            strings.push(s);
        }

        Ok(Self { strings, lookup })
    }
}

/// Maps between `lasso::Spur` keys and serializable u32 indices.
///
/// This is used during encoding to convert Spur keys to indices that can be
/// written to binary, and during decoding to convert indices back to Spurs.
///
/// # Usage
/// ```ignore
/// let rodeo = Rodeo::default();
/// let mut interner = SerializableInterner::new();
/// let mapper = SpurMapper::from_rodeo(&rodeo, &mut interner);
///
/// // During encoding: Spur -> index
/// let idx = mapper.spur_to_index(some_spur);
///
/// // During decoding: index -> Spur
/// let spur = mapper.index_to_spur(idx, &rodeo);
/// ```
#[derive(Debug, Clone)]
pub struct SpurMapper {
    /// Spur -> index mapping (for encoding)
    spur_to_idx: HashMap<Spur, u32>,
    /// Index -> Spur mapping (for decoding)
    idx_to_spur: HashMap<u32, Spur>,
}

impl Default for SpurMapper {
    fn default() -> Self {
        Self::new()
    }
}

impl SpurMapper {
    /// Create an empty mapper.
    #[must_use]
    pub fn new() -> Self {
        Self {
            spur_to_idx: HashMap::new(),
            idx_to_spur: HashMap::new(),
        }
    }

    /// Build from a Rodeo, populating the SerializableInterner with all strings.
    ///
    /// This iterates over all strings in the Rodeo and adds them to both
    /// the interner and the mapper.
    pub fn from_rodeo(rodeo: &Rodeo, interner: &mut SerializableInterner) -> Self {
        let mut spur_to_idx = HashMap::new();
        let mut idx_to_spur = HashMap::new();

        for (spur, s) in rodeo.iter() {
            let idx = interner.intern(s);
            spur_to_idx.insert(spur, idx);
            idx_to_spur.insert(idx, spur);
        }

        Self {
            spur_to_idx,
            idx_to_spur,
        }
    }

    /// Build from a ThreadedRodeo, populating the SerializableInterner with all strings.
    ///
    /// Similar to `from_rodeo` but works with thread-safe interners.
    pub fn from_threaded_rodeo(rodeo: &ThreadedRodeo, interner: &mut SerializableInterner) -> Self {
        let mut spur_to_idx = HashMap::new();
        let mut idx_to_spur = HashMap::new();

        for (spur, s) in rodeo.iter() {
            let idx = interner.intern(s);
            spur_to_idx.insert(spur, idx);
            idx_to_spur.insert(idx, spur);
        }

        Self {
            spur_to_idx,
            idx_to_spur,
        }
    }

    /// Register a Spur with its corresponding string, returning the index.
    ///
    /// This is useful when building the mapper incrementally during encoding.
    pub fn register(&mut self, spur: Spur, s: &str, interner: &mut SerializableInterner) -> u32 {
        if let Some(&idx) = self.spur_to_idx.get(&spur) {
            return idx;
        }

        let idx = interner.intern(s);
        self.spur_to_idx.insert(spur, idx);
        self.idx_to_spur.insert(idx, spur);
        idx
    }

    /// Convert a Spur to its serializable index.
    ///
    /// # Panics
    /// Panics if the Spur was not registered with this mapper.
    #[must_use]
    pub fn spur_to_index(&self, spur: Spur) -> u32 {
        self.spur_to_idx
            .get(&spur)
            .copied()
            .expect("Spur not found in mapper - ensure it was registered during encoding")
    }

    /// Try to convert a Spur to its serializable index.
    ///
    /// Returns `None` if the Spur was not registered.
    #[must_use]
    pub fn try_spur_to_index(&self, spur: Spur) -> Option<u32> {
        self.spur_to_idx.get(&spur).copied()
    }

    /// Convert an index back to a Spur, interning in the provided Rodeo if needed.
    ///
    /// This looks up the string in the interner and interns it in the Rodeo,
    /// returning the resulting Spur.
    pub fn index_to_spur(&mut self, idx: u32, interner: &SerializableInterner, rodeo: &mut Rodeo) -> Result<Spur, DecodeError> {
        // Check if we already have this mapping
        if let Some(&spur) = self.idx_to_spur.get(&idx) {
            return Ok(spur);
        }

        // Look up the string and intern it
        let s = interner.resolve(idx).ok_or_else(|| {
            DecodeError::InvalidSection(format!(
                "String index {} out of bounds (table size {})",
                idx,
                interner.len()
            ))
        })?;

        let spur = rodeo.get_or_intern(s);
        self.idx_to_spur.insert(idx, spur);
        self.spur_to_idx.insert(spur, idx);

        Ok(spur)
    }

    /// Number of registered mappings.
    #[must_use]
    pub fn len(&self) -> usize {
        self.spur_to_idx.len()
    }

    /// Check if empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.spur_to_idx.is_empty()
    }
}

// ============================================================================
// Helper Functions for Common Spur Types
// ============================================================================

/// Encode a VarId (variable identifier) to binary.
///
/// Uses the mapper to convert the Spur to a serializable index.
pub fn encode_var_id<W: Write>(
    var: VarId,
    mapper: &SpurMapper,
    writer: &mut W,
) -> Result<(), EncodeError> {
    let idx = mapper.spur_to_index(var);
    encode_varint_to(idx as u64, writer)?;
    Ok(())
}

/// Decode a VarId (variable identifier) from binary.
///
/// Reads an index and converts it back to a Spur.
pub fn decode_var_id<R: Read>(
    reader: &mut R,
    interner: &SerializableInterner,
    mapper: &mut SpurMapper,
    rodeo: &mut Rodeo,
) -> Result<VarId, DecodeError> {
    let idx = decode_varint32_from(reader)?;
    mapper.index_to_spur(idx, interner, rodeo)
}

/// Encode a TypeVar (type variable) to binary.
pub fn encode_type_var<W: Write>(
    var: TypeVar,
    mapper: &SpurMapper,
    writer: &mut W,
) -> Result<(), EncodeError> {
    let idx = mapper.spur_to_index(var);
    encode_varint_to(idx as u64, writer)?;
    Ok(())
}

/// Decode a TypeVar (type variable) from binary.
pub fn decode_type_var<R: Read>(
    reader: &mut R,
    interner: &SerializableInterner,
    mapper: &mut SpurMapper,
    rodeo: &mut Rodeo,
) -> Result<TypeVar, DecodeError> {
    let idx = decode_varint32_from(reader)?;
    mapper.index_to_spur(idx, interner, rodeo)
}

/// Encode a TypeName (named type reference) to binary.
pub fn encode_type_name<W: Write>(
    name: TypeName,
    mapper: &SpurMapper,
    writer: &mut W,
) -> Result<(), EncodeError> {
    let idx = mapper.spur_to_index(name);
    encode_varint_to(idx as u64, writer)?;
    Ok(())
}

/// Decode a TypeName (named type reference) from binary.
pub fn decode_type_name<R: Read>(
    reader: &mut R,
    interner: &SerializableInterner,
    mapper: &mut SpurMapper,
    rodeo: &mut Rodeo,
) -> Result<TypeName, DecodeError> {
    let idx = decode_varint32_from(reader)?;
    mapper.index_to_spur(idx, interner, rodeo)
}

/// Encode a Label (loop/control flow label) to binary.
pub fn encode_label<W: Write>(
    label: Label,
    mapper: &SpurMapper,
    writer: &mut W,
) -> Result<(), EncodeError> {
    let idx = mapper.spur_to_index(label);
    encode_varint_to(idx as u64, writer)?;
    Ok(())
}

/// Decode a Label (loop/control flow label) from binary.
pub fn decode_label<R: Read>(
    reader: &mut R,
    interner: &SerializableInterner,
    mapper: &mut SpurMapper,
    rodeo: &mut Rodeo,
) -> Result<Label, DecodeError> {
    let idx = decode_varint32_from(reader)?;
    mapper.index_to_spur(idx, interner, rodeo)
}

/// Encode an EffectVar (effect variable) to binary.
pub fn encode_effect_var<W: Write>(
    var: EffectVar,
    mapper: &SpurMapper,
    writer: &mut W,
) -> Result<(), EncodeError> {
    let idx = mapper.spur_to_index(var);
    encode_varint_to(idx as u64, writer)?;
    Ok(())
}

/// Decode an EffectVar (effect variable) from binary.
pub fn decode_effect_var<R: Read>(
    reader: &mut R,
    interner: &SerializableInterner,
    mapper: &mut SpurMapper,
    rodeo: &mut Rodeo,
) -> Result<EffectVar, DecodeError> {
    let idx = decode_varint32_from(reader)?;
    mapper.index_to_spur(idx, interner, rodeo)
}

/// Encode an optional Spur to binary.
///
/// Writes 0 for None, or 1 followed by the index for Some.
pub fn encode_option_spur<W: Write>(
    opt: Option<Spur>,
    mapper: &SpurMapper,
    writer: &mut W,
) -> Result<(), EncodeError> {
    match opt {
        None => {
            writer.write_all(&[0])?;
        }
        Some(spur) => {
            writer.write_all(&[1])?;
            let idx = mapper.spur_to_index(spur);
            encode_varint_to(idx as u64, writer)?;
        }
    }
    Ok(())
}

/// Decode an optional Spur from binary.
pub fn decode_option_spur<R: Read>(
    reader: &mut R,
    interner: &SerializableInterner,
    mapper: &mut SpurMapper,
    rodeo: &mut Rodeo,
) -> Result<Option<Spur>, DecodeError> {
    let mut has_value = [0u8; 1];
    reader.read_exact(&mut has_value)?;

    if has_value[0] == 0 {
        Ok(None)
    } else {
        let idx = decode_varint32_from(reader)?;
        let spur = mapper.index_to_spur(idx, interner, rodeo)?;
        Ok(Some(spur))
    }
}

/// Encode a generic Spur to binary.
///
/// This is a low-level function that can be used for any Spur-based type.
pub fn encode_spur<W: Write>(
    spur: Spur,
    mapper: &SpurMapper,
    writer: &mut W,
) -> Result<(), EncodeError> {
    let idx = mapper.spur_to_index(spur);
    encode_varint_to(idx as u64, writer)?;
    Ok(())
}

/// Decode a generic Spur from binary.
pub fn decode_spur<R: Read>(
    reader: &mut R,
    interner: &SerializableInterner,
    mapper: &mut SpurMapper,
    rodeo: &mut Rodeo,
) -> Result<Spur, DecodeError> {
    let idx = decode_varint32_from(reader)?;
    mapper.index_to_spur(idx, interner, rodeo)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serializable_interner_basic() {
        let mut interner = SerializableInterner::new();

        let idx1 = interner.intern("hello");
        let idx2 = interner.intern("world");
        let idx3 = interner.intern("hello"); // Duplicate

        assert_eq!(idx1, 0);
        assert_eq!(idx2, 1);
        assert_eq!(idx3, 0); // Same as idx1

        assert_eq!(interner.len(), 2);
        assert_eq!(interner.resolve(0), Some("hello"));
        assert_eq!(interner.resolve(1), Some("world"));
        assert_eq!(interner.resolve(2), None);
    }

    #[test]
    fn test_serializable_interner_roundtrip() {
        let mut interner = SerializableInterner::new();
        interner.intern("first");
        interner.intern("second");
        interner.intern("third");

        // Encode
        let mut buf = Vec::new();
        interner.encode(&mut buf).unwrap();

        // Decode
        let decoded = SerializableInterner::decode(&mut buf.as_slice()).unwrap();

        assert_eq!(decoded.len(), 3);
        assert_eq!(decoded.resolve(0), Some("first"));
        assert_eq!(decoded.resolve(1), Some("second"));
        assert_eq!(decoded.resolve(2), Some("third"));
    }

    #[test]
    fn test_spur_mapper_from_rodeo() {
        let mut rodeo = Rodeo::default();
        let spur1 = rodeo.get_or_intern("alpha");
        let spur2 = rodeo.get_or_intern("beta");

        let mut interner = SerializableInterner::new();
        let mapper = SpurMapper::from_rodeo(&rodeo, &mut interner);

        // Mapper should have both entries
        assert_eq!(mapper.len(), 2);

        // Interner should have both strings
        assert_eq!(interner.len(), 2);

        // Check mapping
        let idx1 = mapper.spur_to_index(spur1);
        let idx2 = mapper.spur_to_index(spur2);
        assert_ne!(idx1, idx2);

        // Verify string resolution
        assert!(interner.resolve(idx1) == Some("alpha") || interner.resolve(idx1) == Some("beta"));
    }

    #[test]
    fn test_spur_mapper_register() {
        let mut rodeo = Rodeo::default();
        let spur = rodeo.get_or_intern("test");

        let mut interner = SerializableInterner::new();
        let mut mapper = SpurMapper::new();

        // Register the spur
        let idx = mapper.register(spur, "test", &mut interner);

        // Should be able to convert back
        assert_eq!(mapper.spur_to_index(spur), idx);

        // Registering again should return the same index
        let idx2 = mapper.register(spur, "test", &mut interner);
        assert_eq!(idx, idx2);
    }

    #[test]
    fn test_var_id_roundtrip() {
        let mut rodeo = Rodeo::default();
        let var_id = rodeo.get_or_intern("my_variable");

        let mut interner = SerializableInterner::new();
        let mut mapper = SpurMapper::new();
        mapper.register(var_id, "my_variable", &mut interner);

        // Encode
        let mut buf = Vec::new();
        encode_var_id(var_id, &mapper, &mut buf).unwrap();

        // Decode into a new rodeo
        let mut new_rodeo = Rodeo::default();
        let mut new_mapper = SpurMapper::new();
        let decoded = decode_var_id(&mut buf.as_slice(), &interner, &mut new_mapper, &mut new_rodeo).unwrap();

        // The decoded spur should resolve to the same string
        assert_eq!(new_rodeo.resolve(&decoded), "my_variable");
    }

    #[test]
    fn test_option_spur_roundtrip() {
        let mut rodeo = Rodeo::default();
        let spur = rodeo.get_or_intern("optional_value");

        let mut interner = SerializableInterner::new();
        let mut mapper = SpurMapper::new();
        mapper.register(spur, "optional_value", &mut interner);

        // Test Some case
        let mut buf = Vec::new();
        encode_option_spur(Some(spur), &mapper, &mut buf).unwrap();

        let mut new_rodeo = Rodeo::default();
        let mut new_mapper = SpurMapper::new();
        let decoded = decode_option_spur(&mut buf.as_slice(), &interner, &mut new_mapper, &mut new_rodeo).unwrap();

        assert!(decoded.is_some());
        assert_eq!(new_rodeo.resolve(&decoded.unwrap()), "optional_value");

        // Test None case
        buf.clear();
        encode_option_spur(None, &mapper, &mut buf).unwrap();

        let decoded = decode_option_spur(&mut buf.as_slice(), &interner, &mut new_mapper, &mut new_rodeo).unwrap();
        assert!(decoded.is_none());
    }

    #[test]
    fn test_empty_interner() {
        let interner = SerializableInterner::new();

        let mut buf = Vec::new();
        interner.encode(&mut buf).unwrap();

        let decoded = SerializableInterner::decode(&mut buf.as_slice()).unwrap();
        assert!(decoded.is_empty());
    }

    #[test]
    fn test_unicode_strings() {
        let mut interner = SerializableInterner::new();
        interner.intern("hello");
        interner.intern("world");
        interner.intern("cafe");

        let mut buf = Vec::new();
        interner.encode(&mut buf).unwrap();

        let decoded = SerializableInterner::decode(&mut buf.as_slice()).unwrap();
        assert_eq!(decoded.resolve(0), Some("hello"));
        assert_eq!(decoded.resolve(1), Some("world"));
        assert_eq!(decoded.resolve(2), Some("cafe"));
    }

    #[test]
    fn test_large_interner() {
        let mut interner = SerializableInterner::new();

        // Add many strings
        for i in 0..1000 {
            let s = format!("string_{}", i);
            let idx = interner.intern(&s);
            assert_eq!(idx, i as u32);
        }

        assert_eq!(interner.len(), 1000);

        // Roundtrip
        let mut buf = Vec::new();
        interner.encode(&mut buf).unwrap();

        let decoded = SerializableInterner::decode(&mut buf.as_slice()).unwrap();
        assert_eq!(decoded.len(), 1000);

        for i in 0..1000 {
            let expected = format!("string_{}", i);
            assert_eq!(decoded.resolve(i as u32), Some(expected.as_str()));
        }
    }
}
