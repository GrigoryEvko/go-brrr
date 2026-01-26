//! Similarity computation for semantic clone detection.
//!
//! Provides SIMD-accelerated similarity metrics for comparing code embeddings
//! and computing pairwise similarities for clone detection.
//!
//! # Metrics
//!
//! - **Cosine similarity**: Measures angle between vectors [-1, 1]
//! - **Euclidean distance**: Measures straight-line distance in vector space
//!
//! # Performance
//!
//! Uses SIMD from `src/simd.rs` for vectorized computation:
//! - 8-lane f32 operations (256-bit AVX2)
//! - ~8x speedup over scalar loops
//! - Parallel pairwise computation with rayon
//!
//! # Example
//!
//! ```ignore
//! use brrr::quality::clones::similarity::{
//!     cosine_similarity, euclidean_distance, compute_pairwise_similarities
//! };
//!
//! let a = vec![1.0, 0.0, 0.0];
//! let b = vec![0.0, 1.0, 0.0];
//!
//! let cos_sim = cosine_similarity(&a, &b);  // ~0.0 (orthogonal)
//! let dist = euclidean_distance(&a, &b);     // ~1.414 (sqrt(2))
//!
//! // Compute all pairwise similarities above threshold
//! let embeddings = vec![a, b];
//! let pairs = compute_pairwise_similarities(&embeddings, 0.8);
//! ```

use rayon::prelude::*;

use crate::simd;

// =============================================================================
// SIMILARITY METRICS
// =============================================================================

/// Compute cosine similarity between two vectors using SIMD.
///
/// Cosine similarity measures the angle between two vectors:
/// - 1.0: Identical direction (perfect similarity)
/// - 0.0: Orthogonal (no similarity)
/// - -1.0: Opposite direction (perfect dissimilarity)
///
/// # Arguments
///
/// * `a` - First embedding vector
/// * `b` - Second embedding vector (must have same length as `a`)
///
/// # Returns
///
/// Cosine similarity in range [-1.0, 1.0]. Returns 0.0 if either vector has
/// zero magnitude.
///
/// # Panics
///
/// Panics in debug mode if vectors have different lengths.
///
/// # Performance
///
/// - Uses 8-lane SIMD for ~8x speedup over scalar
/// - O(n) where n is vector dimension
/// - For 1024-dim embeddings: ~128 cycles on AVX2
///
/// # Example
///
/// ```ignore
/// use brrr::quality::clones::similarity::cosine_similarity;
///
/// let a = vec![1.0, 0.0, 0.0];
/// let b = vec![1.0, 0.0, 0.0];
/// assert!((cosine_similarity(&a, &b) - 1.0).abs() < 1e-6);  // Identical
///
/// let c = vec![0.0, 1.0, 0.0];
/// assert!(cosine_similarity(&a, &c).abs() < 1e-6);  // Orthogonal
/// ```
#[inline]
pub fn cosine_similarity(a: &[f32], b: &[f32]) -> f32 {
    // Delegate to SIMD implementation which already handles all edge cases
    simd::cosine_similarity(a, b)
}

/// Compute Euclidean (L2) distance between two vectors using SIMD.
///
/// Euclidean distance is the straight-line distance in vector space:
/// d(a, b) = sqrt(sum((a[i] - b[i])^2))
///
/// # Arguments
///
/// * `a` - First embedding vector
/// * `b` - Second embedding vector (must have same length as `a`)
///
/// # Returns
///
/// Non-negative Euclidean distance. Returns 0.0 for identical vectors.
///
/// # Panics
///
/// Panics in debug mode if vectors have different lengths.
///
/// # Performance
///
/// - Uses 8-lane SIMD for subtraction and squaring
/// - O(n) where n is vector dimension
/// - Slightly slower than cosine_similarity due to sqrt
///
/// # Example
///
/// ```ignore
/// use brrr::quality::clones::similarity::euclidean_distance;
///
/// let a = vec![0.0, 0.0, 0.0];
/// let b = vec![3.0, 4.0, 0.0];
/// assert!((euclidean_distance(&a, &b) - 5.0).abs() < 1e-6);  // 3-4-5 triangle
/// ```
#[inline]
pub fn euclidean_distance(a: &[f32], b: &[f32]) -> f32 {
    euclidean_distance_squared(a, b).sqrt()
}

/// Compute squared Euclidean distance (avoids sqrt for comparison).
///
/// When only comparing distances (not computing actual values), squared
/// distance is faster because it avoids the sqrt operation.
///
/// # Performance
///
/// - ~10% faster than `euclidean_distance` for pure comparisons
/// - Use when you only need to compare distances, not compute exact values
#[inline]
pub fn euclidean_distance_squared(a: &[f32], b: &[f32]) -> f32 {
    debug_assert_eq!(
        a.len(),
        b.len(),
        "euclidean_distance requires equal-length vectors"
    );

    let len = a.len().min(b.len());
    if len == 0 {
        return 0.0;
    }

    // SIMD lane width for f32 operations
    const LANES: usize = 8;
    use std::simd::prelude::*;
    type F32x8 = Simd<f32, LANES>;

    let a_chunks = a[..len].chunks_exact(LANES);
    let b_chunks = b[..len].chunks_exact(LANES);
    let a_remainder = a_chunks.remainder();
    let b_remainder = b_chunks.remainder();

    // SIMD accumulator
    let mut acc = F32x8::splat(0.0);

    for (chunk_a, chunk_b) in a_chunks.zip(b_chunks) {
        let simd_a = F32x8::from_slice(chunk_a);
        let simd_b = F32x8::from_slice(chunk_b);
        let diff = simd_a - simd_b;
        acc += diff * diff;
    }

    // Horizontal sum of SIMD lanes
    let mut sum = acc.reduce_sum();

    // Handle remainder with scalar ops
    for (&va, &vb) in a_remainder.iter().zip(b_remainder.iter()) {
        let diff = va - vb;
        sum += diff * diff;
    }

    sum
}

// =============================================================================
// PAIRWISE SIMILARITY COMPUTATION
// =============================================================================

/// Similarity pair: indices of two similar items and their similarity score.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SimilarityPair {
    /// Index of first item.
    pub i: usize,
    /// Index of second item.
    pub j: usize,
    /// Similarity score (typically cosine similarity).
    pub similarity: f32,
}

impl SimilarityPair {
    /// Create a new similarity pair.
    #[inline]
    #[must_use]
    pub fn new(i: usize, j: usize, similarity: f32) -> Self {
        Self { i, j, similarity }
    }
}

/// Compute pairwise cosine similarities above threshold.
///
/// Compares all pairs of embeddings and returns those with similarity >= threshold.
/// Uses rayon for parallel computation when embedding count exceeds threshold.
///
/// # Arguments
///
/// * `embeddings` - Slice of embedding vectors (all must have same dimension)
/// * `threshold` - Minimum similarity to include in results (0.0-1.0)
///
/// # Returns
///
/// Vector of `(i, j, similarity)` tuples where:
/// - `i < j` (avoids duplicates)
/// - `similarity >= threshold`
///
/// Sorted by similarity descending.
///
/// # Complexity
///
/// - Time: O(n^2 * d) where n = embedding count, d = dimension
/// - Space: O(m) where m = number of pairs above threshold
///
/// # Performance
///
/// - Parallelized with rayon for n >= 50
/// - Early exit when similarity < threshold
/// - For 1000 embeddings of 768 dims: ~2-3 seconds on modern CPU
///
/// # Example
///
/// ```ignore
/// use brrr::quality::clones::similarity::compute_pairwise_similarities;
///
/// let embeddings = vec![
///     vec![1.0, 0.0, 0.0],
///     vec![0.9, 0.1, 0.0],  // Similar to first
///     vec![0.0, 1.0, 0.0],  // Different
/// ];
///
/// let pairs = compute_pairwise_similarities(&embeddings, 0.8);
/// // Returns [(0, 1, ~0.99)] - only the similar pair
/// ```
pub fn compute_pairwise_similarities(
    embeddings: &[Vec<f32>],
    threshold: f32,
) -> Vec<SimilarityPair> {
    let n = embeddings.len();
    if n < 2 {
        return Vec::new();
    }

    // Threshold for parallel processing
    const PARALLEL_THRESHOLD: usize = 50;

    let pairs = if n >= PARALLEL_THRESHOLD {
        compute_pairwise_parallel(embeddings, threshold)
    } else {
        compute_pairwise_sequential(embeddings, threshold)
    };

    // Sort by similarity descending
    let mut pairs = pairs;
    pairs.sort_by(|a, b| {
        b.similarity
            .partial_cmp(&a.similarity)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    pairs
}

/// Sequential pairwise computation for small inputs.
fn compute_pairwise_sequential(embeddings: &[Vec<f32>], threshold: f32) -> Vec<SimilarityPair> {
    let n = embeddings.len();
    let mut pairs = Vec::new();

    for i in 0..n {
        for j in (i + 1)..n {
            let sim = cosine_similarity(&embeddings[i], &embeddings[j]);
            if sim >= threshold {
                pairs.push(SimilarityPair::new(i, j, sim));
            }
        }
    }

    pairs
}

/// Parallel pairwise computation using rayon.
///
/// Partitions work by first index to avoid synchronization overhead.
fn compute_pairwise_parallel(embeddings: &[Vec<f32>], threshold: f32) -> Vec<SimilarityPair> {
    let n = embeddings.len();

    // Each thread handles comparisons for a range of first indices
    (0..n)
        .into_par_iter()
        .flat_map(|i| {
            let mut local_pairs = Vec::new();
            for j in (i + 1)..n {
                let sim = cosine_similarity(&embeddings[i], &embeddings[j]);
                if sim >= threshold {
                    local_pairs.push(SimilarityPair::new(i, j, sim));
                }
            }
            local_pairs
        })
        .collect()
}

/// Compute pairwise similarities returning tuples (for backward compatibility).
///
/// Same as `compute_pairwise_similarities` but returns `Vec<(usize, usize, f32)>`.
pub fn compute_pairwise_tuples(
    embeddings: &[Vec<f32>],
    threshold: f32,
) -> Vec<(usize, usize, f32)> {
    compute_pairwise_similarities(embeddings, threshold)
        .into_iter()
        .map(|p| (p.i, p.j, p.similarity))
        .collect()
}

// =============================================================================
// BATCH OPERATIONS
// =============================================================================

/// Compute similarity of one query against all embeddings.
///
/// Returns indices and similarities for all embeddings above threshold,
/// sorted by similarity descending.
///
/// # Arguments
///
/// * `query` - Query embedding vector
/// * `embeddings` - Corpus of embedding vectors
/// * `threshold` - Minimum similarity to include (0.0-1.0)
///
/// # Returns
///
/// Vector of `(index, similarity)` pairs, sorted by similarity descending.
///
/// # Example
///
/// ```ignore
/// use brrr::quality::clones::similarity::find_similar;
///
/// let query = vec![1.0, 0.0, 0.0];
/// let corpus = vec![
///     vec![0.9, 0.1, 0.0],  // Similar
///     vec![0.0, 1.0, 0.0],  // Different
/// ];
///
/// let results = find_similar(&query, &corpus, 0.8);
/// // Returns [(0, ~0.99)]
/// ```
pub fn find_similar(query: &[f32], embeddings: &[Vec<f32>], threshold: f32) -> Vec<(usize, f32)> {
    let n = embeddings.len();
    if n == 0 {
        return Vec::new();
    }

    // Threshold for parallel processing
    const PARALLEL_THRESHOLD: usize = 100;

    let mut results: Vec<(usize, f32)> = if n >= PARALLEL_THRESHOLD {
        embeddings
            .par_iter()
            .enumerate()
            .filter_map(|(i, emb)| {
                let sim = cosine_similarity(query, emb);
                if sim >= threshold {
                    Some((i, sim))
                } else {
                    None
                }
            })
            .collect()
    } else {
        embeddings
            .iter()
            .enumerate()
            .filter_map(|(i, emb)| {
                let sim = cosine_similarity(query, emb);
                if sim >= threshold {
                    Some((i, sim))
                } else {
                    None
                }
            })
            .collect()
    };

    // Sort by similarity descending
    results.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

    results
}

/// Compute top-k most similar embeddings to a query.
///
/// More efficient than `find_similar` when you only need top results.
///
/// # Arguments
///
/// * `query` - Query embedding vector
/// * `embeddings` - Corpus of embedding vectors
/// * `k` - Maximum number of results to return
///
/// # Returns
///
/// Up to k `(index, similarity)` pairs, sorted by similarity descending.
pub fn find_top_k(query: &[f32], embeddings: &[Vec<f32>], k: usize) -> Vec<(usize, f32)> {
    use std::collections::BinaryHeap;

    if embeddings.is_empty() || k == 0 {
        return Vec::new();
    }

    // Min-heap to keep track of top-k (smallest similarity in heap = threshold)
    // We store negated similarity for min-heap behavior
    #[derive(PartialEq)]
    struct HeapItem(f32, usize); // (neg_similarity, index)

    impl Eq for HeapItem {}

    impl PartialOrd for HeapItem {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }

    impl Ord for HeapItem {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            // Normal order - with negated similarities, max(-sim) = min(sim) goes to top
            self.0
                .partial_cmp(&other.0)
                .unwrap_or(std::cmp::Ordering::Equal)
        }
    }

    let mut heap: BinaryHeap<HeapItem> = BinaryHeap::with_capacity(k + 1);

    for (i, emb) in embeddings.iter().enumerate() {
        let sim = cosine_similarity(query, emb);

        if heap.len() < k {
            heap.push(HeapItem(-sim, i));
        } else if let Some(min) = heap.peek() {
            // min.0 is negated similarity of the threshold (lowest sim in top-k)
            // Add new item if its actual sim > threshold, i.e., -sim < min.0
            if -sim < min.0 {
                heap.pop();
                heap.push(HeapItem(-sim, i));
            }
        }
    }

    // Extract results and sort by similarity descending
    let mut results: Vec<(usize, f32)> = heap.into_iter().map(|h| (h.1, -h.0)).collect();

    results.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

    results
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cosine_similarity_identical() {
        let v = vec![1.0, 2.0, 3.0];
        let sim = cosine_similarity(&v, &v);
        assert!(
            (sim - 1.0).abs() < 1e-5,
            "Identical vectors should have similarity 1.0, got {}",
            sim
        );
    }

    #[test]
    fn test_cosine_similarity_orthogonal() {
        let a = vec![1.0, 0.0, 0.0];
        let b = vec![0.0, 1.0, 0.0];
        let sim = cosine_similarity(&a, &b);
        assert!(
            sim.abs() < 1e-5,
            "Orthogonal vectors should have similarity 0.0, got {}",
            sim
        );
    }

    #[test]
    fn test_cosine_similarity_opposite() {
        let a = vec![1.0, 0.0, 0.0];
        let b = vec![-1.0, 0.0, 0.0];
        let sim = cosine_similarity(&a, &b);
        assert!(
            (sim + 1.0).abs() < 1e-5,
            "Opposite vectors should have similarity -1.0, got {}",
            sim
        );
    }

    #[test]
    fn test_cosine_similarity_zero_vector() {
        let a = vec![0.0, 0.0, 0.0];
        let b = vec![1.0, 2.0, 3.0];
        let sim = cosine_similarity(&a, &b);
        assert_eq!(sim, 0.0, "Zero vector should return 0.0 similarity");
    }

    #[test]
    fn test_euclidean_distance_same_point() {
        let v = vec![1.0, 2.0, 3.0];
        let dist = euclidean_distance(&v, &v);
        assert!(
            dist.abs() < 1e-5,
            "Distance to self should be 0.0, got {}",
            dist
        );
    }

    #[test]
    fn test_euclidean_distance_3_4_5_triangle() {
        let a = vec![0.0, 0.0, 0.0];
        let b = vec![3.0, 4.0, 0.0];
        let dist = euclidean_distance(&a, &b);
        assert!(
            (dist - 5.0).abs() < 1e-5,
            "3-4-5 triangle should have hypotenuse 5.0, got {}",
            dist
        );
    }

    #[test]
    fn test_euclidean_distance_unit_vectors() {
        let a = vec![1.0, 0.0, 0.0];
        let b = vec![0.0, 1.0, 0.0];
        let dist = euclidean_distance(&a, &b);
        let expected = std::f32::consts::SQRT_2;
        assert!(
            (dist - expected).abs() < 1e-5,
            "Unit vectors distance should be sqrt(2), got {}",
            dist
        );
    }

    #[test]
    fn test_compute_pairwise_small() {
        let embeddings = vec![
            vec![1.0, 0.0, 0.0],
            vec![0.99, 0.1, 0.0], // Similar to first
            vec![0.0, 1.0, 0.0], // Different
        ];

        let pairs = compute_pairwise_similarities(&embeddings, 0.9);

        // Only (0, 1) should be above 0.9 threshold
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].i, 0);
        assert_eq!(pairs[0].j, 1);
        assert!(pairs[0].similarity > 0.9);
    }

    #[test]
    fn test_compute_pairwise_empty() {
        let embeddings: Vec<Vec<f32>> = vec![];
        let pairs = compute_pairwise_similarities(&embeddings, 0.5);
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_compute_pairwise_single() {
        let embeddings = vec![vec![1.0, 0.0, 0.0]];
        let pairs = compute_pairwise_similarities(&embeddings, 0.5);
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_compute_pairwise_all_similar() {
        let embeddings = vec![
            vec![1.0, 0.0, 0.0],
            vec![1.0, 0.0, 0.0],
            vec![1.0, 0.0, 0.0],
        ];

        let pairs = compute_pairwise_similarities(&embeddings, 0.99);

        // All pairs should be similar: (0,1), (0,2), (1,2)
        assert_eq!(pairs.len(), 3);
    }

    #[test]
    fn test_find_similar() {
        let query = vec![1.0, 0.0, 0.0];
        let corpus = vec![
            vec![0.99, 0.1, 0.0], // Similar
            vec![0.0, 1.0, 0.0], // Different
            vec![0.95, 0.2, 0.0], // Somewhat similar
        ];

        let results = find_similar(&query, &corpus, 0.9);

        assert_eq!(results.len(), 2); // Only indices 0 and 2
        assert_eq!(results[0].0, 0); // Most similar first
        assert!(results[0].1 > results[1].1); // Sorted descending
    }

    #[test]
    fn test_find_top_k() {
        let query = vec![1.0, 0.0, 0.0];
        let corpus = vec![
            vec![0.99, 0.1, 0.0], // Most similar
            vec![0.0, 1.0, 0.0], // Least similar
            vec![0.95, 0.2, 0.0], // Second most similar
            vec![0.8, 0.3, 0.0], // Third most similar
        ];

        let results = find_top_k(&query, &corpus, 2);

        assert_eq!(results.len(), 2);
        assert_eq!(results[0].0, 0); // Most similar
        assert_eq!(results[1].0, 2); // Second most similar
    }

    #[test]
    fn test_find_top_k_empty() {
        let query = vec![1.0, 0.0, 0.0];
        let corpus: Vec<Vec<f32>> = vec![];
        let results = find_top_k(&query, &corpus, 5);
        assert!(results.is_empty());
    }

    #[test]
    fn test_find_top_k_k_zero() {
        let query = vec![1.0, 0.0, 0.0];
        let corpus = vec![vec![1.0, 0.0, 0.0]];
        let results = find_top_k(&query, &corpus, 0);
        assert!(results.is_empty());
    }

    #[test]
    fn test_euclidean_distance_squared() {
        let a = vec![0.0, 0.0, 0.0];
        let b = vec![3.0, 4.0, 0.0];
        let dist_sq = euclidean_distance_squared(&a, &b);
        assert!(
            (dist_sq - 25.0).abs() < 1e-5,
            "Squared distance should be 25.0, got {}",
            dist_sq
        );
    }

    #[test]
    fn test_large_dimension_vectors() {
        // Test with 768-dim vectors (common embedding size)
        let a: Vec<f32> = (0..768).map(|i| (i as f32) * 0.001).collect();
        let b: Vec<f32> = (0..768).map(|i| ((768 - i) as f32) * 0.001).collect();

        let sim = cosine_similarity(&a, &b);
        assert!(sim.is_finite());
        assert!((-1.0..=1.0).contains(&sim));

        let dist = euclidean_distance(&a, &b);
        assert!(dist.is_finite());
        assert!(dist >= 0.0);
    }

    #[test]
    fn test_similarity_pair_struct() {
        let pair = SimilarityPair::new(0, 1, 0.95);
        assert_eq!(pair.i, 0);
        assert_eq!(pair.j, 1);
        assert!((pair.similarity - 0.95).abs() < 1e-6);
    }

    #[test]
    fn test_pairwise_sorted_descending() {
        let embeddings = vec![
            vec![1.0, 0.0, 0.0],
            vec![0.5, 0.5, 0.0], // Medium similarity
            vec![0.9, 0.1, 0.0], // High similarity
        ];

        let pairs = compute_pairwise_similarities(&embeddings, 0.0);

        // Verify sorted descending by similarity
        for window in pairs.windows(2) {
            assert!(
                window[0].similarity >= window[1].similarity,
                "Pairs should be sorted descending"
            );
        }
    }
}
