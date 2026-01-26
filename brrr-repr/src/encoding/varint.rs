//! Variable-length integer encoding (LEB128)
//!
//! Uses unsigned LEB128 for compact representation of integers.
//! Small values (0-127) use 1 byte, larger values use more bytes.

use std::io::{Read, Write};

use crate::error::{DecodeError, EncodeError};

/// Maximum bytes for a 64-bit varint (ceil(64/7) = 10)
pub const MAX_VARINT_BYTES: usize = 10;

/// Encode a u64 as varint into a byte buffer.
/// Returns the number of bytes written.
///
/// # Encoding Format
/// Each byte contains 7 bits of data and 1 continuation bit (MSB).
/// - If MSB is 1, more bytes follow.
/// - If MSB is 0, this is the last byte.
pub fn encode_varint(mut value: u64, buf: &mut [u8; MAX_VARINT_BYTES]) -> usize {
    let mut i = 0;
    loop {
        let byte = (value & 0x7F) as u8;
        value >>= 7;
        if value == 0 {
            buf[i] = byte;
            return i + 1;
        }
        buf[i] = byte | 0x80;
        i += 1;
    }
}

/// Encode a u64 as varint and write to a writer.
pub fn encode_varint_to<W: Write>(mut value: u64, writer: &mut W) -> Result<usize, EncodeError> {
    let mut bytes_written = 0;
    loop {
        let byte = (value & 0x7F) as u8;
        value >>= 7;
        if value == 0 {
            writer.write_all(&[byte])?;
            return Ok(bytes_written + 1);
        }
        writer.write_all(&[byte | 0x80])?;
        bytes_written += 1;
    }
}

/// Decode a varint from a byte slice.
/// Returns (value, bytes_consumed) or error.
pub fn decode_varint(buf: &[u8]) -> Result<(u64, usize), DecodeError> {
    let mut result: u64 = 0;
    let mut shift = 0;

    for (i, &byte) in buf.iter().enumerate() {
        if i >= MAX_VARINT_BYTES {
            return Err(DecodeError::VarintOverflow);
        }

        let value = u64::from(byte & 0x7F);

        // Check for overflow before shifting
        if shift == 63 && value > 1 {
            return Err(DecodeError::VarintOverflow);
        }

        result |= value << shift;

        if byte & 0x80 == 0 {
            return Ok((result, i + 1));
        }

        shift += 7;
    }

    Err(DecodeError::InvalidVarint)
}

/// Decode a varint from a reader.
pub fn decode_varint_from<R: Read>(reader: &mut R) -> Result<u64, DecodeError> {
    let mut result: u64 = 0;
    let mut shift = 0;
    let mut buf = [0u8; 1];

    loop {
        if shift >= 64 {
            return Err(DecodeError::VarintOverflow);
        }

        reader.read_exact(&mut buf).map_err(|e| {
            if e.kind() == std::io::ErrorKind::UnexpectedEof {
                DecodeError::InvalidVarint
            } else {
                DecodeError::Io(e)
            }
        })?;

        let byte = buf[0];
        let value = u64::from(byte & 0x7F);

        // Check for overflow before shifting
        if shift == 63 && value > 1 {
            return Err(DecodeError::VarintOverflow);
        }

        result |= value << shift;

        if byte & 0x80 == 0 {
            return Ok(result);
        }

        shift += 7;
    }
}

/// Compute the number of bytes needed to encode a value.
#[inline]
#[allow(dead_code)] // API completeness - useful for pre-allocation
pub const fn varint_size(value: u64) -> usize {
    if value == 0 {
        return 1;
    }
    // Number of bytes = ceil(bits_needed / 7)
    let bits = 64 - value.leading_zeros() as usize;
    (bits + 6) / 7
}

/// Encode a u32 as varint (convenience wrapper).
#[inline]
pub fn encode_varint32(value: u32, buf: &mut [u8; MAX_VARINT_BYTES]) -> usize {
    encode_varint(u64::from(value), buf)
}

/// Decode a varint as u32, returning error if it exceeds u32::MAX.
pub fn decode_varint32(buf: &[u8]) -> Result<(u32, usize), DecodeError> {
    let (value, len) = decode_varint(buf)?;
    if value > u64::from(u32::MAX) {
        return Err(DecodeError::VarintOverflow);
    }
    Ok((value as u32, len))
}

/// Decode a varint as u32 from a reader.
pub fn decode_varint32_from<R: Read>(reader: &mut R) -> Result<u32, DecodeError> {
    let value = decode_varint_from(reader)?;
    if value > u64::from(u32::MAX) {
        return Err(DecodeError::VarintOverflow);
    }
    Ok(value as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_decode_single_byte() {
        let mut buf = [0u8; MAX_VARINT_BYTES];

        // Single byte values (0-127)
        for value in 0..=127u64 {
            let len = encode_varint(value, &mut buf);
            assert_eq!(len, 1, "value {value} should be 1 byte");
            assert_eq!(buf[0] & 0x80, 0, "continuation bit should be 0");

            let (decoded, consumed) = decode_varint(&buf[..len]).unwrap();
            assert_eq!(decoded, value);
            assert_eq!(consumed, 1);
        }
    }

    #[test]
    fn test_encode_decode_multi_byte() {
        let mut buf = [0u8; MAX_VARINT_BYTES];

        // Two byte values (128-16383)
        let value = 300u64;
        let len = encode_varint(value, &mut buf);
        assert_eq!(len, 2);

        let (decoded, consumed) = decode_varint(&buf[..len]).unwrap();
        assert_eq!(decoded, value);
        assert_eq!(consumed, 2);
    }

    #[test]
    fn test_encode_decode_large_values() {
        let mut buf = [0u8; MAX_VARINT_BYTES];

        let test_values = [
            0u64,
            1,
            127,
            128,
            255,
            256,
            16383,
            16384,
            u32::MAX as u64,
            u64::MAX,
        ];

        for value in test_values {
            let len = encode_varint(value, &mut buf);
            let (decoded, consumed) = decode_varint(&buf[..len]).unwrap();
            assert_eq!(decoded, value, "roundtrip failed for {value}");
            assert_eq!(consumed, len);
        }
    }

    #[test]
    fn test_varint_size() {
        assert_eq!(varint_size(0), 1);
        assert_eq!(varint_size(1), 1);
        assert_eq!(varint_size(127), 1);
        assert_eq!(varint_size(128), 2);
        assert_eq!(varint_size(16383), 2);
        assert_eq!(varint_size(16384), 3);
        assert_eq!(varint_size(u64::MAX), 10);
    }

    #[test]
    fn test_decode_invalid() {
        // Empty buffer
        assert!(decode_varint(&[]).is_err());

        // Truncated multi-byte (continuation bit set but no more data)
        assert!(decode_varint(&[0x80]).is_err());
    }

    #[test]
    fn test_reader_writer() {
        let mut buf = Vec::new();

        let values = [0u64, 127, 128, 300, u32::MAX as u64, u64::MAX];

        for &value in &values {
            buf.clear();
            encode_varint_to(value, &mut buf).unwrap();

            let mut reader = std::io::Cursor::new(&buf);
            let decoded = decode_varint_from(&mut reader).unwrap();
            assert_eq!(decoded, value);
        }
    }
}
