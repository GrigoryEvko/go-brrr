//! Content hashing for integrity verification using xxh3
//!
//! Provides 128-bit xxh3 hashing for content integrity verification.
//! The hash is appended to binary format files for corruption detection.

use xxhash_rust::xxh3::Xxh3;

use crate::api::BrrrModule;
use crate::types::BrrrType;

/// Compute content hash of a module
///
/// Returns a 128-bit xxh3 hash for integrity verification.
/// The hash includes module name, version, files, types, and expressions.
pub fn content_hash(module: &BrrrModule) -> [u8; 16] {
    let mut hasher = Xxh3::new();

    // Hash module metadata
    hash_str(&mut hasher, &module.name);
    hash_u16(&mut hasher, module.version);

    // Hash file list
    hash_u32(&mut hasher, module.files.len() as u32);
    for file in &module.files {
        hash_str(&mut hasher, file);
    }

    // Hash types (using discriminant for structure)
    hash_u32(&mut hasher, module.types.len() as u32);
    for ty in &module.types {
        hash_type(&mut hasher, ty);
    }

    // Hash expressions (using discriminant for structure)
    hash_u32(&mut hasher, module.exprs.len() as u32);
    for expr in &module.exprs {
        hash_u8(&mut hasher, expr.value.discriminant());
    }

    hasher.digest128().to_le_bytes()
}

/// Compute hash of raw bytes (128-bit).
#[inline]
pub fn hash_bytes(data: &[u8]) -> [u8; 16] {
    xxhash_rust::xxh3::xxh3_128(data).to_le_bytes()
}

/// Compute hash of raw bytes (64-bit).
#[inline]
pub fn hash_bytes_64(data: &[u8]) -> u64 {
    xxhash_rust::xxh3::xxh3_64(data)
}

/// Format a hash as hex string.
pub fn format_hash(hash: &[u8; 16]) -> String {
    let mut s = String::with_capacity(32);
    for byte in hash {
        use std::fmt::Write;
        let _ = write!(s, "{byte:02x}");
    }
    s
}

/// Parse a hex string into a hash.
pub fn parse_hash(s: &str) -> Option<[u8; 16]> {
    if s.len() != 32 {
        return None;
    }

    let mut hash = [0u8; 16];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        if i >= 16 {
            return None;
        }
        let hex_str = std::str::from_utf8(chunk).ok()?;
        hash[i] = u8::from_str_radix(hex_str, 16).ok()?;
    }
    Some(hash)
}

// ============================================================================
// Internal hashing helpers
// ============================================================================

#[inline]
fn hash_u8(hasher: &mut Xxh3, value: u8) {
    hasher.update(&[value]);
}

#[inline]
fn hash_u16(hasher: &mut Xxh3, value: u16) {
    hasher.update(&value.to_le_bytes());
}

#[inline]
fn hash_u32(hasher: &mut Xxh3, value: u32) {
    hasher.update(&value.to_le_bytes());
}

#[inline]
fn hash_str(hasher: &mut Xxh3, s: &str) {
    hash_u32(hasher, s.len() as u32);
    hasher.update(s.as_bytes());
}

fn hash_type(hasher: &mut Xxh3, ty: &BrrrType) {
    hash_u8(hasher, ty.discriminant());

    match ty {
        BrrrType::Prim(kind) => {
            hash_u8(hasher, *kind as u8);
        }
        BrrrType::Numeric(num) => {
            hash_u8(hasher, num.discriminant());
        }
        BrrrType::Wrap(kind, inner) => {
            hash_u8(hasher, *kind as u8);
            hash_type(hasher, inner);
        }
        BrrrType::Modal(kind, inner) => {
            // Hash the discriminant of modal kind
            match kind {
                crate::types::ModalKind::BoxMod(rk) => {
                    hash_u8(hasher, 0);
                    hash_u8(hasher, rk.permission);
                }
                crate::types::ModalKind::DiamondMod => {
                    hash_u8(hasher, 1);
                }
            }
            hash_type(hasher, inner);
        }
        BrrrType::Result(ok, err) => {
            hash_type(hasher, ok);
            hash_type(hasher, err);
        }
        BrrrType::Tuple(elems) => {
            hash_u32(hasher, elems.len() as u32);
            for elem in elems {
                hash_type(hasher, elem);
            }
        }
        BrrrType::Func(func) => {
            hash_u32(hasher, func.params.len() as u32);
            for param in &func.params {
                hash_type(hasher, &param.ty);
            }
            hash_type(hasher, &func.return_type);
        }
        BrrrType::Var(spur) => {
            hash_u32(hasher, spur.into_inner().get());
        }
        BrrrType::App(base, args) => {
            hash_type(hasher, base);
            hash_u32(hasher, args.len() as u32);
            for arg in args {
                hash_type(hasher, arg);
            }
        }
        BrrrType::Named(spur) => {
            hash_u32(hasher, spur.into_inner().get());
        }
        BrrrType::Struct(s) => {
            hash_u32(hasher, s.fields.len() as u32);
            for field in &s.fields {
                hash_type(hasher, &field.ty);
            }
        }
        BrrrType::Enum(e) => {
            hash_u32(hasher, e.variants.len() as u32);
            for variant in &e.variants {
                hash_u32(hasher, variant.fields.len() as u32);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_bytes() {
        let data = b"hello world";
        let hash1 = hash_bytes(data);
        let hash2 = hash_bytes(data);
        assert_eq!(hash1, hash2);

        let different = b"hello worlds";
        let hash3 = hash_bytes(different);
        assert_ne!(hash1, hash3);
    }

    #[test]
    fn test_format_parse_roundtrip() {
        let hash = hash_bytes(b"test data");
        let formatted = format_hash(&hash);
        assert_eq!(formatted.len(), 32);

        let parsed = parse_hash(&formatted).unwrap();
        assert_eq!(hash, parsed);
    }

    #[test]
    fn test_parse_hash_invalid() {
        assert!(parse_hash("").is_none());
        assert!(parse_hash("abc").is_none());
        assert!(parse_hash("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz").is_none());
    }

    #[test]
    fn test_content_hash_module() {
        let module1 = BrrrModule::new("test");
        let module2 = BrrrModule::new("test");
        let module3 = BrrrModule::new("different");

        let hash1 = content_hash(&module1);
        let hash2 = content_hash(&module2);
        let hash3 = content_hash(&module3);

        assert_eq!(hash1, hash2);
        assert_ne!(hash1, hash3);
    }
}
