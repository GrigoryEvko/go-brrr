//! SIMD-accelerated numeric and byte operations using portable_simd.
//!
//! This module provides low-level SIMD primitives using `std::simd` for maximum
//! performance on supported platforms. Functions automatically fall back to scalar
//! operations for remainder elements that don't fill a full SIMD lane.
//!
//! # Architecture Support
//!
//! The `portable_simd` feature compiles to optimal instructions for each target:
//! - x86_64: SSE2/AVX2/AVX-512 depending on target features
//! - aarch64: NEON
//! - Other platforms: Scalar fallback with auto-vectorization hints
//!
//! # Performance Characteristics
//!
//! - `sum_f32`: ~8x speedup over scalar loop (f32x8 lanes)
//! - `dot_product`: ~8x speedup, critical for embedding similarity
//! - `count_byte`: ~32x speedup (u8x32 lanes)
//! - `all_equal`: Early exit on first difference, otherwise ~32x throughput
//! - `find_newlines`: ~32x throughput for line counting
//!
//! # Example
//!
//! ```
//! use brrr::simd::{sum_f32, dot_product, count_byte, all_equal, find_newlines};
//!
//! let floats = [1.0_f32, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0];
//! assert!((sum_f32(&floats) - 45.0).abs() < 1e-6);
//!
//! let a = [1.0_f32, 2.0, 3.0, 4.0];
//! let b = [4.0_f32, 3.0, 2.0, 1.0];
//! assert!((dot_product(&a, &b) - 20.0).abs() < 1e-6);
//!
//! let text = b"hello\nworld\n";
//! assert_eq!(count_byte(text, b'\n'), 2);
//!
//! assert!(all_equal(b"aaaaaaa"));
//! assert!(!all_equal(b"aaaaaab"));
//!
//! let positions = find_newlines(b"line1\nline2\nline3");
//! assert_eq!(positions, vec![5, 11]);
//! ```

use std::simd::prelude::*;
use std::simd::Simd;

/// SIMD lane width for f32 operations (256-bit = 8 floats).
const F32_LANES: usize = 8;

/// SIMD lane width for u8 operations (256-bit = 32 bytes).
const U8_LANES: usize = 32;

/// Type alias for f32 SIMD vector.
type F32x8 = Simd<f32, F32_LANES>;

/// Type alias for u8 SIMD vector.
type U8x32 = Simd<u8, U8_LANES>;

/// Compute the sum of all f32 values using SIMD.
///
/// Uses 8-lane SIMD (f32x8) to process 8 elements per iteration. Remaining
/// elements are summed with a scalar loop.
///
/// # Arguments
///
/// * `data` - Slice of f32 values to sum
///
/// # Returns
///
/// Sum of all elements in the slice. Returns 0.0 for empty slices.
///
/// # Performance
///
/// - Throughput: ~8 elements per cycle on AVX2
/// - Latency: O(n/8) + horizontal sum overhead
/// - Memory: Streaming access pattern, cache-friendly
///
/// # Numerical Stability
///
/// Uses simple summation. For numerically-sensitive applications requiring
/// Kahan summation or pairwise summation, use a dedicated math library.
///
/// # Example
///
/// ```
/// use brrr::simd::sum_f32;
///
/// let data = [1.0_f32, 2.0, 3.0, 4.0, 5.0];
/// assert!((sum_f32(&data) - 15.0).abs() < 1e-6);
/// ```
#[inline]
pub fn sum_f32(data: &[f32]) -> f32 {
    if data.is_empty() {
        return 0.0;
    }

    let chunks = data.chunks_exact(F32_LANES);
    let remainder = chunks.remainder();

    // SIMD accumulator for parallel summation
    let mut acc = F32x8::splat(0.0);

    for chunk in chunks {
        // SAFETY: chunks_exact guarantees exactly F32_LANES elements
        let simd_chunk = F32x8::from_slice(chunk);
        acc += simd_chunk;
    }

    // Horizontal sum of SIMD lanes
    let mut sum = acc.reduce_sum();

    // Handle remainder with scalar ops
    for &val in remainder {
        sum += val;
    }

    sum
}

/// Compute the dot product of two f32 slices using SIMD.
///
/// Uses 8-lane SIMD (f32x8) to process 8 multiplications per iteration.
/// This is the core operation for cosine similarity in embedding search.
///
/// # Arguments
///
/// * `a` - First vector
/// * `b` - Second vector
///
/// # Returns
///
/// Dot product (a . b). Returns 0.0 if either slice is empty.
///
/// # Panics
///
/// Panics in debug mode if slices have different lengths. In release mode,
/// processes only up to the minimum length (to avoid UB).
///
/// # Performance
///
/// - Throughput: ~8 multiply-adds per cycle on AVX2 with FMA
/// - Critical for embedding similarity: 1024-dim vectors process in ~128 cycles
/// - Memory: Two streaming reads, excellent prefetcher behavior
///
/// # Example
///
/// ```
/// use brrr::simd::dot_product;
///
/// let a = [1.0_f32, 2.0, 3.0];
/// let b = [4.0_f32, 5.0, 6.0];
/// // 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
/// assert!((dot_product(&a, &b) - 32.0).abs() < 1e-6);
/// ```
#[inline]
pub fn dot_product(a: &[f32], b: &[f32]) -> f32 {
    debug_assert_eq!(a.len(), b.len(), "dot_product requires equal-length slices");

    let len = a.len().min(b.len());
    if len == 0 {
        return 0.0;
    }

    let a_chunks = a[..len].chunks_exact(F32_LANES);
    let b_chunks = b[..len].chunks_exact(F32_LANES);
    let a_remainder = a_chunks.remainder();
    let b_remainder = b_chunks.remainder();

    // SIMD accumulator for FMA (fused multiply-add)
    let mut acc = F32x8::splat(0.0);

    for (chunk_a, chunk_b) in a_chunks.zip(b_chunks) {
        let simd_a = F32x8::from_slice(chunk_a);
        let simd_b = F32x8::from_slice(chunk_b);
        // acc = acc + (simd_a * simd_b) - may compile to FMA on supported hardware
        acc += simd_a * simd_b;
    }

    // Horizontal sum of SIMD lanes
    let mut sum = acc.reduce_sum();

    // Handle remainder with scalar ops
    for (&va, &vb) in a_remainder.iter().zip(b_remainder.iter()) {
        sum += va * vb;
    }

    sum
}

/// Count occurrences of a specific byte using SIMD.
///
/// Uses 32-lane SIMD (u8x32) to compare 32 bytes per iteration.
///
/// # Arguments
///
/// * `data` - Byte slice to search
/// * `byte` - Target byte to count
///
/// # Returns
///
/// Number of occurrences of `byte` in `data`.
///
/// # Performance
///
/// - Throughput: ~32 bytes per cycle on AVX2
/// - For newline counting: ~1GB/s on modern CPUs
/// - Cache-friendly streaming access pattern
///
/// # Note
///
/// For production use, consider `memchr::Memchr` which may have additional
/// optimizations. This implementation is provided for cases where you want
/// to avoid the `memchr` dependency or need consistent behavior with other
/// SIMD operations in this module.
///
/// # Example
///
/// ```
/// use brrr::simd::count_byte;
///
/// let text = b"hello world\nfoo\nbar\n";
/// assert_eq!(count_byte(text, b'\n'), 3);
/// assert_eq!(count_byte(text, b'o'), 3);
/// ```
#[inline]
pub fn count_byte(data: &[u8], byte: u8) -> usize {
    if data.is_empty() {
        return 0;
    }

    let target = U8x32::splat(byte);
    let chunks = data.chunks_exact(U8_LANES);
    let remainder = chunks.remainder();

    let mut count: usize = 0;

    for chunk in chunks {
        let simd_chunk = U8x32::from_slice(chunk);
        let matches = simd_chunk.simd_eq(target);
        // to_bitmask returns a u32 where each bit is 1 if the lane matched
        count += matches.to_bitmask().count_ones() as usize;
    }

    // Handle remainder with scalar ops
    for &b in remainder {
        if b == byte {
            count += 1;
        }
    }

    count
}

/// Check if all bytes in a slice are equal using SIMD.
///
/// Early-exits on first difference for optimal performance on non-uniform data.
/// Uses 32-lane SIMD comparison for uniform sections.
///
/// # Arguments
///
/// * `data` - Byte slice to check
///
/// # Returns
///
/// - `true` if all bytes are identical (including empty slices)
/// - `false` if any byte differs from the others
///
/// # Performance
///
/// - Best case (early mismatch): O(1)
/// - Worst case (all equal): O(n/32) with SIMD
/// - Useful for detecting padding, null regions, or corrupted data
///
/// # Example
///
/// ```
/// use brrr::simd::all_equal;
///
/// assert!(all_equal(b""));
/// assert!(all_equal(b"aaaaaa"));
/// assert!(all_equal(&[0u8; 1000]));
/// assert!(!all_equal(b"aaabaa"));
/// ```
#[inline]
pub fn all_equal(data: &[u8]) -> bool {
    if data.len() <= 1 {
        return true;
    }

    let first = data[0];
    let target = U8x32::splat(first);
    let chunks = data.chunks_exact(U8_LANES);
    let remainder = chunks.remainder();

    for chunk in chunks {
        let simd_chunk = U8x32::from_slice(chunk);
        let matches = simd_chunk.simd_eq(target);
        // If any lane doesn't match, all() returns false
        if !matches.all() {
            return false;
        }
    }

    // Handle remainder with scalar ops
    for &b in remainder {
        if b != first {
            return false;
        }
    }

    true
}

/// Find all positions of newline characters (0x0A) using SIMD.
///
/// Uses 32-lane SIMD to scan for newlines, returning positions in a Vec.
///
/// # Arguments
///
/// * `data` - Byte slice to search
///
/// # Returns
///
/// Vector of indices where `\n` (0x0A) occurs. Empty vector if no newlines.
///
/// # Performance
///
/// - Throughput: ~32 bytes per cycle for scanning
/// - Allocates output vector (consider pre-sizing if count is known)
/// - For line counting only, use `count_byte(data, b'\n')` instead
///
/// # Use Cases
///
/// - Building line index for source code navigation
/// - Splitting text without string allocation
/// - Computing line/column from byte offset
///
/// # Example
///
/// ```
/// use brrr::simd::find_newlines;
///
/// let text = b"line1\nline2\nline3";
/// let positions = find_newlines(text);
/// assert_eq!(positions, vec![5, 11]);
///
/// // Use for byte-to-line conversion
/// let byte_offset = 8;
/// let line_number = positions.iter().filter(|&&pos| pos < byte_offset).count() + 1;
/// assert_eq!(line_number, 2); // byte 8 is on line 2
/// ```
#[inline]
pub fn find_newlines(data: &[u8]) -> Vec<usize> {
    if data.is_empty() {
        return Vec::new();
    }

    // Pre-estimate capacity based on average line length assumption (~40 chars)
    let estimated_lines = (data.len() / 40).max(1);
    let mut positions = Vec::with_capacity(estimated_lines);

    let newline = U8x32::splat(b'\n');
    let chunks = data.chunks_exact(U8_LANES);
    let remainder = chunks.remainder();
    let remainder_start = data.len() - remainder.len();

    for (chunk_idx, chunk) in chunks.enumerate() {
        let simd_chunk = U8x32::from_slice(chunk);
        let matches = simd_chunk.simd_eq(newline);
        let mask = matches.to_bitmask();

        if mask != 0 {
            // Extract positions from bitmask
            let base = chunk_idx * U8_LANES;
            let mut remaining_mask = mask;
            while remaining_mask != 0 {
                let lane = remaining_mask.trailing_zeros() as usize;
                positions.push(base + lane);
                remaining_mask &= remaining_mask - 1; // Clear lowest set bit
            }
        }
    }

    // Handle remainder with scalar ops
    for (i, &b) in remainder.iter().enumerate() {
        if b == b'\n' {
            positions.push(remainder_start + i);
        }
    }

    positions
}

/// Compute the squared L2 norm (magnitude squared) of a vector using SIMD.
///
/// This is the dot product of a vector with itself: ||v||^2 = v . v
///
/// # Arguments
///
/// * `data` - Vector to compute norm of
///
/// # Returns
///
/// Sum of squared elements. Returns 0.0 for empty slices.
///
/// # Example
///
/// ```
/// use brrr::simd::squared_norm;
///
/// let v = [3.0_f32, 4.0];
/// // 3^2 + 4^2 = 9 + 16 = 25
/// assert!((squared_norm(&v) - 25.0).abs() < 1e-6);
/// ```
#[inline]
pub fn squared_norm(data: &[f32]) -> f32 {
    dot_product(data, data)
}

/// Compute cosine similarity between two vectors using SIMD.
///
/// cosine_similarity(a, b) = (a . b) / (||a|| * ||b||)
///
/// # Arguments
///
/// * `a` - First vector
/// * `b` - Second vector
///
/// # Returns
///
/// Cosine similarity in range [-1.0, 1.0]. Returns 0.0 if either vector has zero magnitude.
///
/// # Panics
///
/// Panics in debug mode if slices have different lengths.
///
/// # Example
///
/// ```
/// use brrr::simd::cosine_similarity;
///
/// let a = [1.0_f32, 0.0];
/// let b = [1.0_f32, 0.0];
/// assert!((cosine_similarity(&a, &b) - 1.0).abs() < 1e-6); // Identical vectors
///
/// let c = [1.0_f32, 0.0];
/// let d = [0.0_f32, 1.0];
/// assert!(cosine_similarity(&c, &d).abs() < 1e-6); // Orthogonal vectors
/// ```
#[inline]
pub fn cosine_similarity(a: &[f32], b: &[f32]) -> f32 {
    let dot = dot_product(a, b);
    let norm_a = squared_norm(a);
    let norm_b = squared_norm(b);

    let denominator = (norm_a * norm_b).sqrt();
    if denominator < f32::EPSILON {
        return 0.0;
    }

    dot / denominator
}

/// SIMD lane width for u32 operations (256-bit = 8 u32s).
const U32_LANES: usize = 8;

/// Type alias for u32 SIMD vector.
type U32x8 = Simd<u32, U32_LANES>;

/// Find all indices where `data[i] == target` using SIMD.
///
/// Uses 8-lane SIMD (u32x8) to compare 8 elements per iteration.
/// Critical for fast edge filtering in dataflow analysis.
///
/// # Arguments
///
/// * `data` - Slice of u32 values to search
/// * `target` - Target value to match
///
/// # Returns
///
/// Vector of indices where `data[i] == target`.
///
/// # Performance
///
/// - Throughput: ~8 comparisons per cycle on AVX2
/// - Uses bitmask extraction for efficient index collection
/// - O(n/8) iterations with SIMD, plus O(matches) for index extraction
///
/// # Example
///
/// ```
/// use brrr::simd::find_matching_u32;
///
/// let data = [1u32, 5, 3, 5, 5, 2, 7, 5, 9, 5];
/// let indices = find_matching_u32(&data, 5);
/// assert_eq!(indices, vec![1, 3, 4, 7, 9]);
/// ```
#[inline]
pub fn find_matching_u32(data: &[u32], target: u32) -> Vec<usize> {
    if data.is_empty() {
        return Vec::new();
    }

    // Pre-estimate capacity: assume ~10% match rate as reasonable default
    let estimated_matches = (data.len() / 10).max(4);
    let mut indices = Vec::with_capacity(estimated_matches);

    let target_simd = U32x8::splat(target);
    let chunks = data.chunks_exact(U32_LANES);
    let remainder = chunks.remainder();
    let remainder_start = data.len() - remainder.len();

    for (chunk_idx, chunk) in chunks.enumerate() {
        let simd_chunk = U32x8::from_slice(chunk);
        let matches = simd_chunk.simd_eq(target_simd);
        let mask = matches.to_bitmask();

        if mask != 0 {
            // Extract indices from bitmask using Brian Kernighan's bit counting trick
            let base = chunk_idx * U32_LANES;
            let mut remaining_mask = mask;
            while remaining_mask != 0 {
                let lane = remaining_mask.trailing_zeros() as usize;
                indices.push(base + lane);
                remaining_mask &= remaining_mask - 1; // Clear lowest set bit
            }
        }
    }

    // Handle remainder with scalar ops
    for (i, &val) in remainder.iter().enumerate() {
        if val == target {
            indices.push(remainder_start + i);
        }
    }

    indices
}

/// Find all indices where `data[i] == target` using SIMD, reusing output buffer.
///
/// Same as [`find_matching_u32`] but writes to a pre-allocated buffer to avoid
/// repeated allocations in hot loops.
///
/// # Arguments
///
/// * `data` - Slice of u32 values to search
/// * `target` - Target value to match
/// * `output` - Pre-allocated vector to store results (will be cleared)
///
/// # Performance
///
/// Avoids allocation overhead when called repeatedly with similar result sizes.
/// The caller should reuse the same output buffer across calls.
///
/// # Example
///
/// ```
/// use brrr::simd::find_matching_u32_into;
///
/// let data = [1u32, 5, 3, 5, 5, 2, 7, 5, 9, 5];
/// let mut buffer = Vec::new();
/// find_matching_u32_into(&data, 5, &mut buffer);
/// assert_eq!(buffer, vec![1, 3, 4, 7, 9]);
/// ```
#[inline]
pub fn find_matching_u32_into(data: &[u32], target: u32, output: &mut Vec<usize>) {
    output.clear();

    if data.is_empty() {
        return;
    }

    let target_simd = U32x8::splat(target);
    let chunks = data.chunks_exact(U32_LANES);
    let remainder = chunks.remainder();
    let remainder_start = data.len() - remainder.len();

    for (chunk_idx, chunk) in chunks.enumerate() {
        let simd_chunk = U32x8::from_slice(chunk);
        let matches = simd_chunk.simd_eq(target_simd);
        let mask = matches.to_bitmask();

        if mask != 0 {
            let base = chunk_idx * U32_LANES;
            let mut remaining_mask = mask;
            while remaining_mask != 0 {
                let lane = remaining_mask.trailing_zeros() as usize;
                output.push(base + lane);
                remaining_mask &= remaining_mask - 1;
            }
        }
    }

    // Handle remainder
    for (i, &val) in remainder.iter().enumerate() {
        if val == target {
            output.push(remainder_start + i);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sum_f32_empty() {
        assert_eq!(sum_f32(&[]), 0.0);
    }

    #[test]
    fn test_sum_f32_single() {
        assert!((sum_f32(&[42.0]) - 42.0).abs() < 1e-6);
    }

    #[test]
    fn test_sum_f32_exact_lanes() {
        let data: Vec<f32> = (1..=8).map(|x| x as f32).collect();
        // 1+2+3+4+5+6+7+8 = 36
        assert!((sum_f32(&data) - 36.0).abs() < 1e-6);
    }

    #[test]
    fn test_sum_f32_with_remainder() {
        let data: Vec<f32> = (1..=11).map(|x| x as f32).collect();
        // 1+2+...+11 = 66
        assert!((sum_f32(&data) - 66.0).abs() < 1e-6);
    }

    #[test]
    fn test_sum_f32_large() {
        let data: Vec<f32> = (1..=1000).map(|x| x as f32).collect();
        // Sum of 1..=1000 = 1000 * 1001 / 2 = 500500
        assert!((sum_f32(&data) - 500_500.0).abs() < 1e-2);
    }

    #[test]
    fn test_dot_product_empty() {
        assert_eq!(dot_product(&[], &[]), 0.0);
    }

    #[test]
    fn test_dot_product_single() {
        assert!((dot_product(&[3.0], &[4.0]) - 12.0).abs() < 1e-6);
    }

    #[test]
    fn test_dot_product_basic() {
        let a = [1.0_f32, 2.0, 3.0];
        let b = [4.0_f32, 5.0, 6.0];
        // 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
        assert!((dot_product(&a, &b) - 32.0).abs() < 1e-6);
    }

    #[test]
    fn test_dot_product_exact_lanes() {
        let a: Vec<f32> = vec![1.0; 8];
        let b: Vec<f32> = vec![2.0; 8];
        assert!((dot_product(&a, &b) - 16.0).abs() < 1e-6);
    }

    #[test]
    fn test_dot_product_with_remainder() {
        let a: Vec<f32> = vec![1.0; 11];
        let b: Vec<f32> = vec![2.0; 11];
        assert!((dot_product(&a, &b) - 22.0).abs() < 1e-6);
    }

    #[test]
    fn test_dot_product_large_embeddings() {
        // Simulate 1024-dim embedding comparison
        let a: Vec<f32> = (0..1024).map(|i| (i as f32) * 0.001).collect();
        let b: Vec<f32> = (0..1024).map(|i| (1024 - i) as f32 * 0.001).collect();
        let result = dot_product(&a, &b);
        // Just verify it produces a reasonable result
        assert!(result.is_finite());
        assert!(result > 0.0);
    }

    #[test]
    fn test_count_byte_empty() {
        assert_eq!(count_byte(&[], b'x'), 0);
    }

    #[test]
    fn test_count_byte_not_found() {
        assert_eq!(count_byte(b"hello world", b'x'), 0);
    }

    #[test]
    fn test_count_byte_found() {
        assert_eq!(count_byte(b"hello", b'l'), 2);
        assert_eq!(count_byte(b"hello", b'h'), 1);
        assert_eq!(count_byte(b"hello", b'o'), 1);
    }

    #[test]
    fn test_count_byte_newlines() {
        let text = b"line1\nline2\nline3\n";
        assert_eq!(count_byte(text, b'\n'), 3);
    }

    #[test]
    fn test_count_byte_exact_lanes() {
        let data = vec![b'a'; 32];
        assert_eq!(count_byte(&data, b'a'), 32);
        assert_eq!(count_byte(&data, b'b'), 0);
    }

    #[test]
    fn test_count_byte_with_remainder() {
        let data = vec![b'a'; 37];
        assert_eq!(count_byte(&data, b'a'), 37);
    }

    #[test]
    fn test_count_byte_large() {
        let mut data = vec![b' '; 10000];
        data[0] = b'x';
        data[5000] = b'x';
        data[9999] = b'x';
        assert_eq!(count_byte(&data, b'x'), 3);
    }

    #[test]
    fn test_all_equal_empty() {
        assert!(all_equal(&[]));
    }

    #[test]
    fn test_all_equal_single() {
        assert!(all_equal(&[b'a']));
    }

    #[test]
    fn test_all_equal_true() {
        assert!(all_equal(b"aaaaaa"));
        assert!(all_equal(&[0u8; 100]));
        assert!(all_equal(&[255u8; 100]));
    }

    #[test]
    fn test_all_equal_false_early() {
        assert!(!all_equal(b"ab"));
        assert!(!all_equal(b"ba"));
    }

    #[test]
    fn test_all_equal_false_late() {
        let mut data = vec![b'a'; 100];
        data[99] = b'b';
        assert!(!all_equal(&data));
    }

    #[test]
    fn test_all_equal_exact_lanes() {
        assert!(all_equal(&[b'x'; 32]));
        let mut data = vec![b'x'; 32];
        data[31] = b'y';
        assert!(!all_equal(&data));
    }

    #[test]
    fn test_find_newlines_empty() {
        assert_eq!(find_newlines(&[]), Vec::<usize>::new());
    }

    #[test]
    fn test_find_newlines_none() {
        assert_eq!(find_newlines(b"no newlines here"), Vec::<usize>::new());
    }

    #[test]
    fn test_find_newlines_single() {
        assert_eq!(find_newlines(b"hello\nworld"), vec![5]);
    }

    #[test]
    fn test_find_newlines_multiple() {
        assert_eq!(find_newlines(b"a\nb\nc\n"), vec![1, 3, 5]);
    }

    #[test]
    fn test_find_newlines_at_boundaries() {
        assert_eq!(find_newlines(b"\nstart"), vec![0]);
        assert_eq!(find_newlines(b"end\n"), vec![3]);
        assert_eq!(find_newlines(b"\n"), vec![0]);
    }

    #[test]
    fn test_find_newlines_consecutive() {
        assert_eq!(find_newlines(b"\n\n\n"), vec![0, 1, 2]);
    }

    #[test]
    fn test_find_newlines_exact_lanes() {
        // 32 bytes with newlines at positions 0, 15, 31
        let mut data = vec![b'x'; 32];
        data[0] = b'\n';
        data[15] = b'\n';
        data[31] = b'\n';
        assert_eq!(find_newlines(&data), vec![0, 15, 31]);
    }

    #[test]
    fn test_find_newlines_with_remainder() {
        // 37 bytes with newlines
        let mut data = vec![b'x'; 37];
        data[5] = b'\n';
        data[35] = b'\n';
        assert_eq!(find_newlines(&data), vec![5, 35]);
    }

    #[test]
    fn test_squared_norm() {
        let v = [3.0_f32, 4.0];
        assert!((squared_norm(&v) - 25.0).abs() < 1e-6);
    }

    #[test]
    fn test_squared_norm_empty() {
        assert_eq!(squared_norm(&[]), 0.0);
    }

    #[test]
    fn test_cosine_similarity_identical() {
        let v = [1.0_f32, 2.0, 3.0];
        assert!((cosine_similarity(&v, &v) - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_cosine_similarity_orthogonal() {
        let a = [1.0_f32, 0.0];
        let b = [0.0_f32, 1.0];
        assert!(cosine_similarity(&a, &b).abs() < 1e-6);
    }

    #[test]
    fn test_cosine_similarity_opposite() {
        let a = [1.0_f32, 0.0];
        let b = [-1.0_f32, 0.0];
        assert!((cosine_similarity(&a, &b) + 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_cosine_similarity_zero_vector() {
        let a = [0.0_f32, 0.0];
        let b = [1.0_f32, 1.0];
        assert_eq!(cosine_similarity(&a, &b), 0.0);
    }

    #[test]
    fn test_find_matching_u32_empty() {
        assert_eq!(find_matching_u32(&[], 5), Vec::<usize>::new());
    }

    #[test]
    fn test_find_matching_u32_not_found() {
        let data = [1u32, 2, 3, 4, 6, 7, 8, 9];
        assert_eq!(find_matching_u32(&data, 5), Vec::<usize>::new());
    }

    #[test]
    fn test_find_matching_u32_single() {
        let data = [1u32, 5, 3, 4, 6, 7, 8, 9];
        assert_eq!(find_matching_u32(&data, 5), vec![1]);
    }

    #[test]
    fn test_find_matching_u32_multiple() {
        let data = [1u32, 5, 3, 5, 5, 2, 7, 5, 9, 5];
        assert_eq!(find_matching_u32(&data, 5), vec![1, 3, 4, 7, 9]);
    }

    #[test]
    fn test_find_matching_u32_exact_lanes() {
        // Exactly 8 elements (one SIMD lane)
        let data = [5u32, 1, 5, 2, 3, 5, 4, 5];
        assert_eq!(find_matching_u32(&data, 5), vec![0, 2, 5, 7]);
    }

    #[test]
    fn test_find_matching_u32_with_remainder() {
        // 11 elements = 1 full lane + 3 remainder
        let data = [1u32, 2, 3, 4, 5, 6, 7, 8, 9, 5, 5];
        assert_eq!(find_matching_u32(&data, 5), vec![4, 9, 10]);
    }

    #[test]
    fn test_find_matching_u32_all_match() {
        let data = [5u32; 16];
        let expected: Vec<usize> = (0..16).collect();
        assert_eq!(find_matching_u32(&data, 5), expected);
    }

    #[test]
    fn test_find_matching_u32_large() {
        // Test with larger data to ensure SIMD batching works
        let mut data = vec![0u32; 1000];
        data[0] = 42;
        data[100] = 42;
        data[500] = 42;
        data[999] = 42;
        assert_eq!(find_matching_u32(&data, 42), vec![0, 100, 500, 999]);
    }

    #[test]
    fn test_find_matching_u32_into_reuse() {
        let data1 = [1u32, 5, 3, 5];
        let data2 = [5u32, 5, 5, 1, 1, 5];
        let mut buffer = Vec::new();

        find_matching_u32_into(&data1, 5, &mut buffer);
        assert_eq!(buffer, vec![1, 3]);

        find_matching_u32_into(&data2, 5, &mut buffer);
        assert_eq!(buffer, vec![0, 1, 2, 5]);
    }
}
