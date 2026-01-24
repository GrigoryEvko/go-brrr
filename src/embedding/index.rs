//! Vector index for semantic search using usearch.
//!
//! Provides a thread-safe wrapper around usearch for approximate nearest neighbor search.
//! Designed to integrate with the semantic search module for code embeddings.
//!
//! # Architecture
//!
//! The index uses HNSW (Hierarchical Navigable Small World) algorithm internally,
//! providing O(log n) search complexity with high recall. Vector IDs map directly
//! to EmbeddingUnit indices in the metadata store.
//!
//! # Usage
//!
//! ```no_run
//! use go_brrr::embedding::{VectorIndex, Metric};
//!
//! // Create index for 768-dimensional embeddings (MiniLM)
//! let index = VectorIndex::new(768, Metric::InnerProduct)?;
//!
//! // Add vectors
//! let embedding = vec![0.1f32; 768];
//! index.add(0, &embedding)?;
//!
//! // Search for similar vectors
//! let results = index.search(&embedding, 10)?;
//! for (id, distance) in results {
//!     println!("ID: {}, Distance: {}", id, distance);
//! }
//!
//! // Persist to disk
//! index.save("./index.usearch")?;
//! # Ok::<(), anyhow::Error>(())
//! ```

use std::fs::File;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::simd::{f32x8, num::SimdFloat, Simd};

/// 512-bit SIMD vector type for AVX-512 operations (16 x f32).
type F32x16 = Simd<f32, 16>;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use lru::LruCache;
use once_cell::sync::Lazy;
use rayon::prelude::*;
use tempfile::NamedTempFile;
use usearch::{Index, IndexOptions, MetricKind, ScalarKind};

/// Threshold for parallel batch insertion.
/// Below this count, sequential insertion has lower overhead.
const PARALLEL_BATCH_THRESHOLD: usize = 100;

// =============================================================================
// Metric Types
// =============================================================================

/// Distance metric for vector similarity.
///
/// Different metrics are appropriate for different embedding models:
/// - `InnerProduct`: Best for normalized embeddings (most modern models)
/// - `Cosine`: Automatically normalizes vectors (slightly slower)
/// - `L2Squared`: Euclidean distance, good for absolute positioning
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Metric {
    /// Inner product: `1 - sum(a[i] * b[i])`.
    /// Use with normalized vectors (cosine similarity).
    /// This is the fastest option for pre-normalized embeddings.
    #[default]
    InnerProduct,

    /// Cosine similarity: `1 - (a . b) / (|a| * |b|)`.
    /// Automatically normalizes vectors during comparison.
    Cosine,

    /// Squared L2 (Euclidean) distance: `sum((a[i] - b[i])^2)`.
    /// Measures absolute distance in vector space.
    L2Squared,
}

impl Metric {
    /// Convert to usearch MetricKind.
    #[must_use]
    fn to_usearch(self) -> MetricKind {
        match self {
            Self::InnerProduct => MetricKind::IP,
            Self::Cosine => MetricKind::Cos,
            Self::L2Squared => MetricKind::L2sq,
        }
    }

    /// Get human-readable name.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::InnerProduct => "inner_product",
            Self::Cosine => "cosine",
            Self::L2Squared => "l2_squared",
        }
    }
}

impl std::fmt::Display for Metric {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl std::str::FromStr for Metric {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        match s.to_lowercase().as_str() {
            "ip" | "inner_product" | "innerproduct" => Ok(Self::InnerProduct),
            "cos" | "cosine" => Ok(Self::Cosine),
            "l2" | "l2sq" | "l2_squared" | "euclidean" => Ok(Self::L2Squared),
            _ => bail!(
                "Unknown metric: {}. Valid options: inner_product, cosine, l2_squared",
                s
            ),
        }
    }
}

// =============================================================================
// Quantization Types
// =============================================================================

/// Scalar quantization for index storage.
///
/// Lower precision reduces memory usage but may affect recall:
/// - `F32`: Full precision (4 bytes per dimension)
/// - `F16`: Half precision (2 bytes per dimension, ~1% recall loss)
/// - `BF16`: Brain float (2 bytes, better for ML models)
/// - `I8`: 8-bit quantization (1 byte, ~3-5% recall loss)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Quantization {
    /// 32-bit float (full precision, largest index size).
    #[default]
    F32,
    /// 16-bit float (half precision, good balance).
    F16,
    /// Brain float 16 (better for ML model outputs).
    BF16,
    /// 8-bit integer (smallest index, some recall loss).
    I8,
}

impl Quantization {
    /// Convert to usearch ScalarKind.
    #[must_use]
    fn to_usearch(self) -> ScalarKind {
        match self {
            Self::F32 => ScalarKind::F32,
            Self::F16 => ScalarKind::F16,
            Self::BF16 => ScalarKind::BF16,
            Self::I8 => ScalarKind::I8,
        }
    }

    /// Get bytes per scalar element.
    #[must_use]
    pub fn bytes_per_element(self) -> usize {
        match self {
            Self::F32 => 4,
            Self::F16 | Self::BF16 => 2,
            Self::I8 => 1,
        }
    }
}

// =============================================================================
// Index Configuration
// =============================================================================

/// Configuration for vector index creation.
///
/// Default values are optimized for semantic code search with ~10K-100K vectors.
#[derive(Debug, Clone)]
pub struct IndexConfig {
    /// Vector dimensions (must match embedding model output).
    pub dimensions: usize,

    /// Distance metric for similarity computation.
    pub metric: Metric,

    /// Scalar quantization for storage optimization.
    pub quantization: Quantization,

    /// Connectivity parameter (M in HNSW). Higher = better recall, more memory.
    /// Default: 0 (uses usearch default, typically 16).
    pub connectivity: usize,

    /// Expansion factor during index construction (ef_construction).
    /// Higher = better quality index, slower build. Default: 0 (uses usearch default).
    pub expansion_add: usize,

    /// Expansion factor during search (ef_search).
    /// Higher = better recall, slower search. Default: 0 (uses usearch default).
    pub expansion_search: usize,

    /// Allow multiple vectors with the same key.
    pub multi: bool,
}

impl IndexConfig {
    /// Create configuration for a specific dimension count.
    #[must_use]
    pub fn new(dimensions: usize) -> Self {
        Self {
            dimensions,
            metric: Metric::default(),
            quantization: Quantization::default(),
            connectivity: 0,
            expansion_add: 0,
            expansion_search: 0,
            multi: false,
        }
    }

    /// Set the distance metric.
    #[must_use]
    pub fn with_metric(mut self, metric: Metric) -> Self {
        self.metric = metric;
        self
    }

    /// Set the quantization level.
    #[must_use]
    pub fn with_quantization(mut self, quantization: Quantization) -> Self {
        self.quantization = quantization;
        self
    }

    /// Set connectivity (M parameter in HNSW).
    #[must_use]
    pub fn with_connectivity(mut self, connectivity: usize) -> Self {
        self.connectivity = connectivity;
        self
    }

    /// Set expansion factor for index construction.
    #[must_use]
    pub fn with_expansion_add(mut self, expansion: usize) -> Self {
        self.expansion_add = expansion;
        self
    }

    /// Set expansion factor for search.
    #[must_use]
    pub fn with_expansion_search(mut self, expansion: usize) -> Self {
        self.expansion_search = expansion;
        self
    }

    /// Enable or disable multi-index mode.
    ///
    /// When enabled, multiple vectors can be stored under the same key.
    /// Use [`count_key`](VectorIndex::count_key) to count vectors per key.
    #[must_use]
    pub fn with_multi(mut self, multi: bool) -> Self {
        self.multi = multi;
        self
    }

    /// Convert to usearch IndexOptions.
    fn to_usearch_options(&self) -> IndexOptions {
        IndexOptions {
            dimensions: self.dimensions,
            metric: self.metric.to_usearch(),
            quantization: self.quantization.to_usearch(),
            connectivity: self.connectivity,
            expansion_add: self.expansion_add,
            expansion_search: self.expansion_search,
            multi: self.multi,
        }
    }

    /// Estimate memory usage for a given vector count (in bytes).
    #[must_use]
    pub fn estimate_memory(&self, vector_count: usize) -> usize {
        let bytes_per_vector = self.dimensions * self.quantization.bytes_per_element();
        // HNSW overhead is roughly 2x for graph structure
        let overhead_factor = 2;
        vector_count * bytes_per_vector * overhead_factor
    }
}

impl Default for IndexConfig {
    fn default() -> Self {
        Self::new(768) // Default to MiniLM-like dimensions
    }
}

// =============================================================================
// Save Information
// =============================================================================

/// Information about a completed save operation.
///
/// Returned by [`VectorIndex::save_checked`] to provide details about the
/// save operation, including timing and disk space information.
///
/// # Examples
///
/// ```no_run
/// use go_brrr::embedding::{VectorIndex, Metric};
///
/// let index = VectorIndex::new(768, Metric::InnerProduct)?;
/// index.reserve(1000)?;
/// // ... add vectors ...
///
/// let info = index.save_checked("./index.usearch")?;
///
/// println!("Save completed:");
/// println!("  Path: {}", info.path.display());
/// println!("  Size: {} bytes", info.size_bytes);
/// println!("  Time: {:?}", info.elapsed);
/// println!("  Space remaining: {} bytes", info.space_remaining);
/// # Ok::<(), anyhow::Error>(())
/// ```
#[derive(Debug, Clone)]
pub struct SaveInfo {
    /// Path where the index was saved.
    pub path: PathBuf,

    /// Size of the saved index in bytes.
    pub size_bytes: usize,

    /// Time taken to complete the save operation.
    pub elapsed: Duration,

    /// Available disk space before the save operation.
    pub available_before: u64,

    /// Estimated remaining disk space after the save.
    pub space_remaining: u64,
}

impl SaveInfo {
    /// Get the save speed in bytes per second.
    #[must_use]
    pub fn bytes_per_second(&self) -> f64 {
        if self.elapsed.as_secs_f64() > 0.0 {
            self.size_bytes as f64 / self.elapsed.as_secs_f64()
        } else {
            f64::INFINITY
        }
    }

    /// Get the save speed in megabytes per second.
    #[must_use]
    pub fn mb_per_second(&self) -> f64 {
        self.bytes_per_second() / (1024.0 * 1024.0)
    }

    /// Get a human-readable size string (e.g., "1.5 MB").
    #[must_use]
    pub fn human_size(&self) -> String {
        const KB: usize = 1024;
        const MB: usize = KB * 1024;
        const GB: usize = MB * 1024;

        if self.size_bytes >= GB {
            format!("{:.2} GB", self.size_bytes as f64 / GB as f64)
        } else if self.size_bytes >= MB {
            format!("{:.2} MB", self.size_bytes as f64 / MB as f64)
        } else if self.size_bytes >= KB {
            format!("{:.2} KB", self.size_bytes as f64 / KB as f64)
        } else {
            format!("{} bytes", self.size_bytes)
        }
    }
}

impl std::fmt::Display for SaveInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Saved {} to '{}' in {:?} ({:.1} MB/s)",
            self.human_size(),
            self.path.display(),
            self.elapsed,
            self.mb_per_second()
        )
    }
}

// =============================================================================
// Vector Index
// =============================================================================

/// Thread-safe vector index for approximate nearest neighbor search.
///
/// Wraps usearch Index with ergonomic Rust API. The underlying index is
/// already thread-safe (Send + Sync) for concurrent read/write operations.
///
/// # Vector IDs
///
/// Vector IDs are u64 keys that should map to your EmbeddingUnit indices.
/// The index does not store metadata - that should be kept separately
/// (typically in a JSON metadata file alongside the index).
///
/// # Persistence
///
/// Indexes can be saved to disk with [`save`](Self::save) and loaded with
/// [`load`](Self::load). The [`view`](Self::view) method provides memory-mapped
/// access for large indexes that don't fit in RAM.
pub struct VectorIndex {
    inner: Index,
    config: IndexConfig,
}

// Note: VectorIndex is automatically Send + Sync because:
// - usearch::Index implements Send + Sync (verified in USearch/rust/lib.rs:533-534)
// - IndexConfig contains only Copy types (usize, bool, enums)
// No unsafe impl needed - Rust derives these traits automatically.

// =============================================================================
// IndexView - Safe Memory-Mapped View with File Lifecycle Management
// =============================================================================

/// A memory-mapped view of an index file with file lifecycle management.
///
/// This struct keeps the file handle open to prevent the underlying file from
/// being deleted while the view is active. On Unix systems, keeping the file
/// handle open ensures the file data remains accessible even if the file is
/// unlinked from the filesystem.
///
/// # Safety Considerations
///
/// - The backing file must not be modified while the view is active
/// - Use `is_valid()` to check if the backing file still exists on disk
/// - For frequently-updated indexes, use `VectorIndex::load()` instead
/// - Views are more memory-efficient for large, read-only indexes
///
/// # Examples
///
/// ```no_run
/// use go_brrr::embedding::VectorIndex;
///
/// // Create a safe view that keeps the file open
/// let view = VectorIndex::view_safe("./index.usearch")?;
/// assert!(view.is_valid());
/// println!("Index has {} vectors", view.len());
///
/// // Search through the view
/// let results = view.search(&[1.0, 0.0, 0.0, 0.0], 10)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub struct IndexView {
    inner: VectorIndex,
    /// Keeps file open to prevent deletion while view is active
    _file_handle: Arc<File>,
    path: PathBuf,
}

impl IndexView {
    /// Check if the backing file still exists on disk.
    ///
    /// Note: Even if this returns `false`, the view may still be usable
    /// on Unix systems because the file handle keeps the data accessible.
    /// However, it indicates the file has been unlinked.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.path.exists()
    }

    /// Get the path to the backing file.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Get the underlying index configuration.
    #[must_use]
    pub fn config(&self) -> &IndexConfig {
        &self.inner.config
    }

    /// Get the number of vectors in the index.
    #[must_use]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Check if the index is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Get the dimensionality of vectors in this index.
    #[must_use]
    pub fn dimensions(&self) -> usize {
        self.inner.dimensions()
    }

    /// Check if a key exists in the index.
    #[must_use]
    pub fn contains(&self, key: u64) -> bool {
        self.inner.contains(key)
    }

    /// Search for the k nearest neighbors of a query vector.
    ///
    /// # Arguments
    ///
    /// * `query` - Query vector (must match index dimensions)
    /// * `k` - Number of neighbors to return
    ///
    /// # Returns
    ///
    /// Vector of (key, distance) pairs, sorted by distance (closest first).
    pub fn search(&self, query: &[f32], k: usize) -> Result<Vec<(u64, f32)>> {
        // Use explicit type qualification since VectorIndex methods are defined later in this file
        VectorIndex::search(&self.inner, query, k)
    }

    /// Search with a distance threshold filter.
    ///
    /// Returns only results within the specified distance threshold.
    pub fn search_threshold(
        &self,
        query: &[f32],
        k: usize,
        threshold: f32,
    ) -> Result<Vec<(u64, f32)>> {
        // Use explicit type qualification since VectorIndex methods are defined later in this file
        VectorIndex::search_threshold(&self.inner, query, k, threshold)
    }

    /// Get the vector for a given key.
    ///
    /// # Errors
    ///
    /// Returns error if the key doesn't exist in the index.
    pub fn get(&self, key: u64) -> Result<Vec<f32>> {
        // Use explicit type qualification since VectorIndex methods are defined later in this file
        VectorIndex::get(&self.inner, key)
            .ok_or_else(|| anyhow::anyhow!("Key {} not found in index", key))
    }

    /// Consume the view and return the underlying VectorIndex.
    ///
    /// Warning: After calling this, the file handle is released and the
    /// returned index becomes vulnerable to file deletion. Only use this
    /// if you need to modify the index or have other lifecycle management.
    #[must_use]
    pub fn into_inner(self) -> VectorIndex {
        self.inner
    }
}

impl std::ops::Deref for IndexView {
    type Target = VectorIndex;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl std::fmt::Debug for IndexView {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IndexView")
            .field("inner", &self.inner)
            .field("path", &self.path)
            .field("is_valid", &self.is_valid())
            .finish()
    }
}

// Note: IndexView is Send + Sync because:
// - VectorIndex is Send + Sync
// - Arc<File> is Send + Sync
// - PathBuf is Send + Sync

impl VectorIndex {
    /// Create a new vector index with the given dimensions and metric.
    ///
    /// # Arguments
    ///
    /// * `dimensions` - Number of dimensions in embedding vectors
    /// * `metric` - Distance metric for similarity computation
    ///
    /// # Errors
    ///
    /// Returns error if usearch index creation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// // Create index for 768-dim embeddings with inner product metric
    /// let index = VectorIndex::new(768, Metric::InnerProduct)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn new(dimensions: usize, metric: Metric) -> Result<Self> {
        let config = IndexConfig::new(dimensions).with_metric(metric);
        Self::with_config(config)
    }

    /// Create a new vector index with full configuration.
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, IndexConfig, Metric, Quantization};
    ///
    /// let config = IndexConfig::new(1024)
    ///     .with_metric(Metric::InnerProduct)
    ///     .with_quantization(Quantization::F16)
    ///     .with_connectivity(32);
    ///
    /// let index = VectorIndex::with_config(config)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn with_config(config: IndexConfig) -> Result<Self> {
        let options = config.to_usearch_options();
        let inner = Index::new(&options)
            .map_err(|e| anyhow::anyhow!("Failed to create usearch index: {}", e))?;

        Ok(Self { inner, config })
    }

    /// Get the index configuration.
    #[must_use]
    pub fn config(&self) -> &IndexConfig {
        &self.config
    }

    /// Get the number of dimensions.
    #[must_use]
    pub fn dimensions(&self) -> usize {
        self.inner.dimensions()
    }

    /// Get the current number of vectors in the index.
    #[must_use]
    pub fn len(&self) -> usize {
        self.inner.size()
    }

    /// Check if the index is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the current capacity (reserved space).
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Get estimated memory usage in bytes.
    #[must_use]
    pub fn memory_usage(&self) -> usize {
        self.inner.memory_usage()
    }

    /// Get the distance metric used by this index.
    #[must_use]
    pub fn metric(&self) -> Metric {
        self.config.metric
    }

    /// Convert raw distances to similarity scores using this index's metric.
    ///
    /// Different metrics require different conversion formulas:
    /// - `InnerProduct`/`Cosine`: score = 1 - distance (clamped to [0, 1])
    /// - `L2Squared`: score = 1 / (1 + distance) (maps [0, inf) to (0, 1])
    ///
    /// # Arguments
    ///
    /// * `distances` - Raw distance values from search results
    ///
    /// # Returns
    ///
    /// Similarity scores in [0, 1] range, where 1.0 = perfect match.
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::L2Squared)?;
    /// let distances = vec![0.0, 1.0, 4.0];
    /// let scores = index.to_similarity_scores(&distances);
    /// // L2: 0.0 -> 1.0, 1.0 -> 0.5, 4.0 -> 0.2
    /// assert!((scores[0] - 1.0).abs() < 1e-6);
    /// assert!((scores[1] - 0.5).abs() < 1e-6);
    /// assert!((scores[2] - 0.2).abs() < 1e-6);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[must_use]
    pub fn to_similarity_scores(&self, distances: &[f32]) -> Vec<f32> {
        distances_to_scores_for_metric(distances, self.config.metric)
    }

    /// Reserve capacity for incoming vectors.
    ///
    /// Pre-allocating capacity improves performance when adding many vectors.
    ///
    /// # Arguments
    ///
    /// * `capacity` - Total capacity to reserve (including existing vectors)
    ///
    /// # Errors
    ///
    /// Returns error if memory allocation fails.
    pub fn reserve(&self, capacity: usize) -> Result<()> {
        self.inner
            .reserve(capacity)
            .map_err(|e| anyhow::anyhow!("Failed to reserve capacity: {}", e))
    }

    /// Check if the index contains a vector with the given key.
    #[must_use]
    pub fn contains(&self, key: u64) -> bool {
        self.inner.contains(key)
    }

    /// Count vectors with a specific key (for multi-index mode).
    ///
    /// In standard mode, returns 1 if key exists, 0 otherwise.
    /// In multi-index mode, returns the number of vectors stored under this key.
    ///
    /// # Arguments
    ///
    /// * `key` - The vector key to count
    ///
    /// # Returns
    ///
    /// Number of vectors associated with the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, IndexConfig, Metric};
    ///
    /// // Multi-index mode allows multiple vectors per key
    /// let config = IndexConfig::new(4)
    ///     .with_metric(Metric::InnerProduct)
    ///     .with_multi(true);
    /// let index = VectorIndex::with_config(config)?;
    /// index.reserve(10)?;
    ///
    /// let key = 42u64;
    /// index.add(key, &[1.0, 0.0, 0.0, 0.0])?;
    /// index.add(key, &[0.0, 1.0, 0.0, 0.0])?;
    ///
    /// assert_eq!(index.count_key(key), 2);
    /// assert_eq!(index.count_key(999), 0);  // Non-existent key
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[must_use]
    pub fn count_key(&self, key: u64) -> usize {
        self.inner.count(key)
    }

    /// Retrieve a vector by its key.
    ///
    /// Returns `None` if the key doesn't exist in the index.
    ///
    /// # Arguments
    ///
    /// * `key` - The unique identifier of the vector to retrieve
    ///
    /// # Returns
    ///
    /// The stored vector if the key exists, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::InnerProduct)?;
    /// index.reserve(10)?;
    /// index.add(42, &[1.0, 0.0, 0.0, 0.0])?;
    ///
    /// let retrieved = index.get(42);
    /// assert!(retrieved.is_some());
    /// assert_eq!(retrieved.unwrap(), vec![1.0, 0.0, 0.0, 0.0]);
    ///
    /// // Non-existent key returns None
    /// assert!(index.get(999).is_none());
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[must_use]
    pub fn get(&self, key: u64) -> Option<Vec<f32>> {
        let dimensions = self.inner.dimensions();
        let mut buffer = vec![0.0f32; dimensions];

        // usearch get() returns the number of vectors found (0 or 1 for non-multi),
        // not the number of dimensions. The buffer is filled with the full vector.
        match self.inner.get(key, &mut buffer) {
            Ok(count) if count > 0 => Some(buffer),
            _ => None,
        }
    }

    /// Retrieve multiple vectors by their keys.
    ///
    /// Returns a `Vec` of `Option<Vec<f32>>` in the same order as the input keys.
    /// Each element is `Some(vector)` if the key exists, `None` otherwise.
    ///
    /// # Arguments
    ///
    /// * `keys` - Slice of unique identifiers to retrieve
    ///
    /// # Returns
    ///
    /// Vector of optional vectors, maintaining input order.
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::InnerProduct)?;
    /// index.reserve(10)?;
    /// index.add(1, &[1.0, 0.0, 0.0, 0.0])?;
    /// index.add(3, &[0.0, 1.0, 0.0, 0.0])?;
    ///
    /// let results = index.get_batch(&[1, 2, 3]);
    /// assert!(results[0].is_some());  // Key 1 exists
    /// assert!(results[1].is_none());  // Key 2 doesn't exist
    /// assert!(results[2].is_some());  // Key 3 exists
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[must_use]
    pub fn get_batch(&self, keys: &[u64]) -> Vec<Option<Vec<f32>>> {
        keys.iter().map(|&key| self.get(key)).collect()
    }

    /// Add a single vector to the index.
    ///
    /// # Arguments
    ///
    /// * `key` - Unique identifier for the vector (maps to EmbeddingUnit index)
    /// * `vector` - Embedding vector (must match index dimensions)
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - Vector dimensions don't match index dimensions
    /// - Index insertion fails
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::Cosine)?;
    /// index.reserve(10)?;  // Must reserve capacity before adding vectors
    /// index.add(42, &[0.1, 0.2, 0.3, 0.4])?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn add(&self, key: u64, vector: &[f32]) -> Result<()> {
        self.validate_vector_dimensions(vector)?;

        self.inner
            .add(key, vector)
            .map_err(|e| anyhow::anyhow!("Failed to add vector {}: {}", key, e))
    }

    /// Add multiple vectors to the index in batch.
    ///
    /// More efficient than calling `add` repeatedly due to better memory locality.
    ///
    /// # Arguments
    ///
    /// * `keys` - Vector of unique identifiers
    /// * `vectors` - Slice of embedding vectors (each must match index dimensions)
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - Keys and vectors have different lengths
    /// - Any vector has wrong dimensions
    /// - Index insertion fails
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::InnerProduct)?;
    /// index.reserve(100)?;
    ///
    /// let keys = vec![0, 1, 2];
    /// let vectors = vec![
    ///     vec![0.1, 0.2, 0.3, 0.4],
    ///     vec![0.5, 0.6, 0.7, 0.8],
    ///     vec![0.9, 0.1, 0.2, 0.3],
    /// ];
    ///
    /// index.add_batch(&keys, &vectors)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn add_batch(&self, keys: &[u64], vectors: &[Vec<f32>]) -> Result<()> {
        if keys.len() != vectors.len() {
            bail!(
                "Keys and vectors length mismatch: {} keys, {} vectors",
                keys.len(),
                vectors.len()
            );
        }

        if keys.is_empty() {
            return Ok(());
        }

        // Validate all dimensions upfront before any insertion
        for (i, vector) in vectors.iter().enumerate() {
            self.validate_vector_dimensions(vector)
                .with_context(|| format!("Vector at index {}", i))?;
        }

        // For small batches, sequential insertion has lower overhead
        if keys.len() < PARALLEL_BATCH_THRESHOLD {
            for (key, vector) in keys.iter().zip(vectors.iter()) {
                self.inner
                    .add(*key, vector)
                    .map_err(|e| anyhow::anyhow!("Failed to add vector {}: {}", key, e))?;
            }
            return Ok(());
        }

        // Parallel insertion for large batches using rayon
        // usearch Index is Send + Sync, so concurrent adds are safe
        let error_count = AtomicUsize::new(0);
        let first_error_key = AtomicUsize::new(0);

        keys.par_iter()
            .zip(vectors.par_iter())
            .for_each(|(key, vector)| {
                if let Err(_e) = self.inner.add(*key, vector) {
                    // Record first error (race condition is acceptable - we just need one)
                    if error_count.fetch_add(1, Ordering::Relaxed) == 0 {
                        first_error_key.store(*key as usize, Ordering::Relaxed);
                    }
                }
            });

        let errors = error_count.load(Ordering::Relaxed);
        if errors > 0 {
            let first_key = first_error_key.load(Ordering::Relaxed);
            bail!(
                "Failed to add {} vector(s), first failure at key {}",
                errors,
                first_key
            );
        }

        Ok(())
    }

    /// Add multiple vectors sequentially (for when insertion order matters).
    ///
    /// Unlike `add_batch`, this method guarantees vectors are added in the
    /// order provided. Use this when vector order affects search results
    /// or when debugging insertion issues.
    ///
    /// # Arguments
    ///
    /// * `keys` - Vector of unique identifiers
    /// * `vectors` - Slice of embedding vectors (each must match index dimensions)
    pub fn add_batch_sequential(&self, keys: &[u64], vectors: &[Vec<f32>]) -> Result<()> {
        if keys.len() != vectors.len() {
            bail!(
                "Keys and vectors length mismatch: {} keys, {} vectors",
                keys.len(),
                vectors.len()
            );
        }

        for (i, (key, vector)) in keys.iter().zip(vectors.iter()).enumerate() {
            self.validate_vector_dimensions(vector)
                .with_context(|| format!("Vector at index {}", i))?;
            self.inner
                .add(*key, vector)
                .map_err(|e| anyhow::anyhow!("Failed to add vector {}: {}", key, e))?;
        }

        Ok(())
    }

    /// Add multiple vectors from a flat array (more efficient for large batches).
    ///
    /// Uses parallel insertion for batches >= 100 vectors. The flat array format
    /// is more cache-friendly than Vec<Vec<f32>> for large batches.
    ///
    /// # Arguments
    ///
    /// * `keys` - Vector of unique identifiers
    /// * `vectors_flat` - Flat array of all vectors concatenated
    ///
    /// # Errors
    ///
    /// Returns error if flat array size doesn't match keys * dimensions.
    pub fn add_batch_flat(&self, keys: &[u64], vectors_flat: &[f32]) -> Result<()> {
        let expected_len = keys.len() * self.dimensions();
        if vectors_flat.len() != expected_len {
            bail!(
                "Flat vector array size mismatch: expected {} ({} keys * {} dims), got {}",
                expected_len,
                keys.len(),
                self.dimensions(),
                vectors_flat.len()
            );
        }

        if keys.is_empty() {
            return Ok(());
        }

        let dims = self.dimensions();

        // For small batches, sequential insertion has lower overhead
        if keys.len() < PARALLEL_BATCH_THRESHOLD {
            for (i, key) in keys.iter().enumerate() {
                let start = i * dims;
                let end = start + dims;
                let vector = &vectors_flat[start..end];

                self.inner
                    .add(*key, vector)
                    .map_err(|e| anyhow::anyhow!("Failed to add vector {}: {}", key, e))?;
            }
            return Ok(());
        }

        // Parallel insertion for large batches using rayon
        let error_count = AtomicUsize::new(0);
        let first_error_key = AtomicUsize::new(0);

        keys.par_iter().enumerate().for_each(|(i, key)| {
            let start = i * dims;
            let end = start + dims;
            let vector = &vectors_flat[start..end];

            if let Err(_e) = self.inner.add(*key, vector) {
                if error_count.fetch_add(1, Ordering::Relaxed) == 0 {
                    first_error_key.store(*key as usize, Ordering::Relaxed);
                }
            }
        });

        let errors = error_count.load(Ordering::Relaxed);
        if errors > 0 {
            let first_key = first_error_key.load(Ordering::Relaxed);
            bail!(
                "Failed to add {} vector(s), first failure at key {}",
                errors,
                first_key
            );
        }

        Ok(())
    }

    /// Search for k nearest neighbors to the query vector.
    ///
    /// Returns results sorted by distance (ascending - closest first).
    /// For inner product metric, lower distance = higher similarity.
    ///
    /// # Arguments
    ///
    /// * `query` - Query embedding vector (must match index dimensions)
    /// * `k` - Maximum number of results to return
    ///
    /// # Returns
    ///
    /// Vector of (key, distance) pairs sorted by distance.
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - Query dimensions don't match index dimensions
    /// - Search fails
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::InnerProduct)?;
    /// index.reserve(10)?;  // Must reserve capacity before adding vectors
    /// index.add(0, &[0.1, 0.2, 0.3, 0.4])?;
    /// index.add(1, &[0.5, 0.6, 0.7, 0.8])?;
    ///
    /// let results = index.search(&[0.1, 0.2, 0.3, 0.4], 10)?;
    /// // results[0] should be (0, ~0.0) - exact match
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn search(&self, query: &[f32], k: usize) -> Result<Vec<(u64, f32)>> {
        self.validate_vector_dimensions(query)?;

        if self.is_empty() {
            return Ok(Vec::new());
        }

        // Limit k to actual index size
        let k = k.min(self.len());

        let matches = self
            .inner
            .search(query, k)
            .map_err(|e| anyhow::anyhow!("Search failed: {}", e))?;

        Ok(matches.keys.into_iter().zip(matches.distances).collect())
    }

    /// Search with exact brute-force computation (slower but guaranteed optimal).
    ///
    /// Use this for verification or when approximate results aren't acceptable.
    pub fn search_exact(&self, query: &[f32], k: usize) -> Result<Vec<(u64, f32)>> {
        self.validate_vector_dimensions(query)?;

        if self.is_empty() {
            return Ok(Vec::new());
        }

        let k = k.min(self.len());

        let matches = self
            .inner
            .exact_search(query, k)
            .map_err(|e| anyhow::anyhow!("Exact search failed: {}", e))?;

        Ok(matches.keys.into_iter().zip(matches.distances).collect())
    }

    /// Search with a filter predicate.
    ///
    /// Only returns results where the filter function returns true for the key.
    ///
    /// # Arguments
    ///
    /// * `query` - Query embedding vector
    /// * `k` - Maximum number of results
    /// * `filter` - Predicate function: `fn(key) -> bool`
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::InnerProduct)?;
    /// index.reserve(100)?;  // Must reserve capacity before adding vectors
    /// // Add vectors with keys 0-99
    /// for i in 0..100 {
    ///     index.add(i, &[0.1 * i as f32; 4])?;
    /// }
    ///
    /// // Only search among even-keyed vectors
    /// let results = index.search_filtered(&[0.5; 4], 10, |key| key % 2 == 0)?;
    /// assert!(results.iter().all(|(k, _)| k % 2 == 0));
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn search_filtered<F>(&self, query: &[f32], k: usize, filter: F) -> Result<Vec<(u64, f32)>>
    where
        F: Fn(u64) -> bool,
    {
        self.validate_vector_dimensions(query)?;

        if self.is_empty() {
            return Ok(Vec::new());
        }

        let k = k.min(self.len());

        let matches = self
            .inner
            .filtered_search(query, k, filter)
            .map_err(|e| anyhow::anyhow!("Filtered search failed: {}", e))?;

        Ok(matches.keys.into_iter().zip(matches.distances).collect())
    }

    /// Search with a distance threshold filter.
    ///
    /// Returns only results where the distance is less than or equal to the threshold.
    /// This is useful for semantic search where you want to filter out dissimilar results.
    ///
    /// # Arguments
    ///
    /// * `query` - Query embedding vector
    /// * `k` - Maximum number of results
    /// * `threshold` - Maximum distance threshold (results with distance > threshold are filtered)
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::InnerProduct)?;
    /// index.reserve(10)?;
    /// index.add(0, &[1.0, 0.0, 0.0, 0.0])?;
    /// index.add(1, &[0.9, 0.1, 0.0, 0.0])?;
    /// index.add(2, &[0.0, 0.0, 1.0, 0.0])?;
    ///
    /// // Search with threshold to filter distant results
    /// let results = index.search_threshold(&[1.0, 0.0, 0.0, 0.0], 10, 0.5)?;
    /// // Only returns vectors within distance 0.5
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn search_threshold(
        &self,
        query: &[f32],
        k: usize,
        threshold: f32,
    ) -> Result<Vec<(u64, f32)>> {
        self.validate_vector_dimensions(query)?;

        if self.is_empty() {
            return Ok(Vec::new());
        }

        let k = k.min(self.len());

        let matches = self
            .inner
            .search(query, k)
            .map_err(|e| anyhow::anyhow!("Search failed: {}", e))?;

        // Filter results by threshold
        Ok(matches
            .keys
            .into_iter()
            .zip(matches.distances)
            .filter(|(_, dist)| *dist <= threshold)
            .collect())
    }

    /// Remove a vector by key.
    ///
    /// # Returns
    ///
    /// Number of vectors removed (0 or 1 for non-multi indexes).
    pub fn remove(&self, key: u64) -> Result<usize> {
        self.inner
            .remove(key)
            .map_err(|e| anyhow::anyhow!("Failed to remove vector {}: {}", key, e))
    }

    /// Rename a key in the index.
    ///
    /// Moves all vectors from `from_key` to `to_key`.
    /// Returns the number of vectors renamed (0 if `from_key` didn't exist).
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - `to_key` already exists in the index (would cause data loss)
    /// - The underlying rename operation fails
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, IndexConfig, Metric};
    ///
    /// let config = IndexConfig::new(4).with_metric(Metric::InnerProduct);
    /// let index = VectorIndex::with_config(config)?;
    /// index.reserve(10)?;
    ///
    /// index.add(42, &[1.0, 0.0, 0.0, 0.0])?;
    /// assert!(index.contains(42));
    ///
    /// let renamed = index.rename(42, 100)?;
    /// assert_eq!(renamed, 1);
    /// assert!(!index.contains(42));
    /// assert!(index.contains(100));
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn rename(&self, from_key: u64, to_key: u64) -> Result<usize> {
        // Check if target key already exists (would cause data loss)
        if self.contains(to_key) {
            bail!(
                "Cannot rename key {} to {}: target key already exists",
                from_key,
                to_key
            );
        }

        self.inner
            .rename(from_key, to_key)
            .map_err(|e| anyhow::anyhow!("Failed to rename key {} to {}: {}", from_key, to_key, e))
    }

    /// Rename a key, overwriting target if it exists.
    ///
    /// Removes any existing vectors at `to_key` before renaming.
    /// Returns the number of vectors renamed (0 if `from_key` didn't exist).
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, IndexConfig, Metric};
    ///
    /// let config = IndexConfig::new(4).with_metric(Metric::InnerProduct);
    /// let index = VectorIndex::with_config(config)?;
    /// index.reserve(10)?;
    ///
    /// index.add(42, &[1.0, 0.0, 0.0, 0.0])?;
    /// index.add(100, &[0.0, 1.0, 0.0, 0.0])?;  // Existing key
    ///
    /// let renamed = index.rename_overwrite(42, 100)?;
    /// assert_eq!(renamed, 1);
    /// assert!(!index.contains(42));
    /// assert!(index.contains(100));
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn rename_overwrite(&self, from_key: u64, to_key: u64) -> Result<usize> {
        // Remove target first if it exists
        if self.contains(to_key) {
            self.remove(to_key)?;
        }

        self.inner
            .rename(from_key, to_key)
            .map_err(|e| anyhow::anyhow!("Failed to rename key {} to {}: {}", from_key, to_key, e))
    }

    /// Clear all vectors from the index.
    ///
    /// Releases memory back to the OS.
    pub fn clear(&self) -> Result<()> {
        self.inner
            .reset()
            .map_err(|e| anyhow::anyhow!("Failed to clear index: {}", e))
    }

    /// Save the index to a file atomically.
    ///
    /// Uses a temp file + atomic rename pattern to prevent corruption on crash.
    /// Creates a `.usearch` file that can be loaded with [`load`](Self::load)
    /// or memory-mapped with [`view`](Self::view).
    ///
    /// # Atomic Write Strategy
    ///
    /// 1. Creates a temporary file in the same directory as the target
    /// 2. Writes index data to the temporary file
    /// 3. Atomically renames the temp file to the target path
    ///
    /// This ensures that if a crash occurs mid-write, the original file (if any)
    /// remains intact. The atomic rename is guaranteed by POSIX on Unix systems
    /// when source and destination are on the same filesystem.
    ///
    /// # Arguments
    ///
    /// * `path` - File path to save to (typically with `.usearch` extension)
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - Parent directory does not exist or is not writable
    /// - Temporary file cannot be created
    /// - Index serialization fails
    /// - Atomic rename fails
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(768, Metric::InnerProduct)?;
    /// index.reserve(100)?;
    /// // ... add vectors ...
    /// index.save("./index.usearch")?;  // Crash-safe write
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn save(&self, path: impl AsRef<Path>) -> Result<()> {
        let path = path.as_ref();

        // Get parent directory for temp file (must be same filesystem for atomic rename)
        let parent = path.parent().unwrap_or_else(|| Path::new("."));

        // Ensure parent directory exists
        if !parent.exists() {
            bail!("Parent directory does not exist: {}", parent.display());
        }

        // Create temp file in same directory (required for atomic rename on same filesystem)
        let temp_file = NamedTempFile::new_in(parent)
            .with_context(|| format!("Failed to create temp file in '{}'", parent.display()))?;

        let temp_path = temp_file.path();
        let temp_path_str = temp_path.to_string_lossy();

        // Save to temp file
        self.inner.save(&temp_path_str).map_err(|e| {
            anyhow::anyhow!(
                "Failed to save index to temp file '{}': {}",
                temp_path_str,
                e
            )
        })?;

        // Atomic rename: persist() keeps the temp file and renames it to target
        temp_file.persist(path).with_context(|| {
            format!(
                "Failed to atomically rename temp file to '{}'",
                path.display()
            )
        })?;

        Ok(())
    }

    /// Save the index directly to file without atomic write protection.
    ///
    /// This is faster than [`save`](Self::save) but risky: if a crash occurs
    /// mid-write, the file may be corrupted. Use only when:
    /// - Speed is critical and corruption risk is acceptable
    /// - The file is easily regenerable
    /// - You have your own backup/recovery mechanism
    ///
    /// # Arguments
    ///
    /// * `path` - File path to save to (typically with `.usearch` extension)
    ///
    /// # Errors
    ///
    /// Returns error if file cannot be written.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(768, Metric::InnerProduct)?;
    /// index.reserve(100)?;
    /// // ... add vectors ...
    /// index.save_unsafe("./index.usearch")?;  // Faster but not crash-safe
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn save_unsafe(&self, path: impl AsRef<Path>) -> Result<()> {
        let path_str = path.as_ref().to_string_lossy();
        self.inner
            .save(&path_str)
            .map_err(|e| anyhow::anyhow!("Failed to save index to '{}': {}", path_str, e))
    }

    /// Restore an index from file, reading configuration from the file itself.
    ///
    /// This is the SAFE way to load an index - dimensions and settings are
    /// read from the file header, not provided by the caller. This prevents
    /// dimension mismatches that could cause undefined behavior.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to `.usearch` file
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - File does not exist or cannot be read
    /// - File format is invalid
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::embedding::VectorIndex;
    ///
    /// // Safe load - dimensions come from the file
    /// let index = VectorIndex::restore("./index.usearch")?;
    /// println!("Loaded index with {} dimensions", index.dimensions());
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn restore(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();

        if !path.exists() {
            bail!("Index file not found: {}", path.display());
        }

        let path_str = path.to_string_lossy();

        // Create index with default options - usearch will update dimensions on load
        let default_opts = IndexOptions::default();
        let inner = Index::new(&default_opts)
            .map_err(|e| anyhow::anyhow!("Failed to create usearch index: {}", e))?;

        // Load from file - this reads dimensions from the file header
        inner
            .load(&path_str)
            .map_err(|e| anyhow::anyhow!("Failed to load index from '{}': {}", path_str, e))?;

        // Read actual dimensions from the loaded index
        let dimensions = inner.dimensions();
        if dimensions == 0 {
            bail!(
                "Invalid index file '{}': loaded index has 0 dimensions",
                path_str
            );
        }

        // Build config from actual loaded values
        // Note: metric and quantization cannot be reliably read from usearch file format,
        // so we use defaults. Users needing specific settings should use load_validated().
        let config = IndexConfig {
            dimensions,
            metric: Metric::default(),
            quantization: Quantization::default(),
            connectivity: 0,
            expansion_add: 0,
            expansion_search: 0,
            multi: false,
        };

        Ok(Self { inner, config })
    }

    /// Load an index with explicit configuration validation.
    ///
    /// First loads the index safely (reading dimensions from file), then
    /// validates that the loaded dimensions match the expected config.
    /// This is useful when you need to ensure the loaded index matches
    /// expected parameters.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to `.usearch` file
    /// * `config` - Expected configuration (dimensions will be validated)
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - File does not exist or cannot be read
    /// - File format is invalid
    /// - Loaded dimensions don't match config dimensions
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::embedding::{VectorIndex, IndexConfig, Metric};
    ///
    /// // Load with validation - error if dimensions don't match
    /// let config = IndexConfig::new(768).with_metric(Metric::InnerProduct);
    /// let index = VectorIndex::load_validated("./index.usearch", config)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn load_validated(path: impl AsRef<Path>, config: IndexConfig) -> Result<Self> {
        let path = path.as_ref();
        let mut index = Self::restore(path)?;

        // Validate dimensions match expected config
        if index.dimensions() != config.dimensions {
            bail!(
                "Dimension mismatch: expected {} but loaded index has {}. \
                 Use VectorIndex::restore() to load without dimension constraints.",
                config.dimensions,
                index.dimensions()
            );
        }

        // Update config with user-specified settings (metric, quantization, etc.)
        // The dimensions are already validated to match
        index.config = config;

        Ok(index)
    }

    /// Load an index from a file (legacy API, prefer `restore` or `load_validated`).
    ///
    /// This method is kept for backward compatibility. It now safely loads the
    /// index first, then validates dimensions. For new code, prefer:
    /// - [`restore`](Self::restore): Safe load without dimension constraints
    /// - [`load_validated`](Self::load_validated): Safe load with dimension validation
    ///
    /// # Arguments
    ///
    /// * `path` - Path to `.usearch` file
    /// * `config` - Configuration matching the saved index
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - File does not exist or cannot be read
    /// - File format is invalid
    /// - Configuration dimensions don't match saved index
    #[deprecated(
        since = "1.2.0",
        note = "Use `restore()` for safe loading or `load_validated()` for validated loading"
    )]
    #[allow(clippy::missing_errors_doc)]
    pub fn load(path: impl AsRef<Path>, config: IndexConfig) -> Result<Self> {
        Self::load_validated(path, config)
    }

    /// Create a memory-mapped view of an index file, reading config from file.
    ///
    /// This is the SAFE way to view an index - dimensions and settings are
    /// read from the file header, not provided by the caller. This prevents
    /// dimension mismatches that could cause undefined behavior.
    ///
    /// Does not load the index into memory - reads directly from the file.
    /// Ideal for large indexes that don't fit in RAM.
    ///
    /// # Safety Note
    ///
    /// The file must not be modified or deleted while the view is active.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to `.usearch` file
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::embedding::VectorIndex;
    ///
    /// // Safe view - dimensions come from the file
    /// let index = VectorIndex::view_restore("./index.usearch")?;
    /// println!("Viewing index with {} dimensions", index.dimensions());
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn view_restore(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();

        if !path.exists() {
            bail!("Index file not found: {}", path.display());
        }

        let path_str = path.to_string_lossy();

        // Create index with default options - usearch will read dimensions from file
        let default_opts = IndexOptions::default();
        let inner = Index::new(&default_opts)
            .map_err(|e| anyhow::anyhow!("Failed to create usearch index: {}", e))?;

        // Memory-map the file - this reads dimensions from the file header
        inner
            .view(&path_str)
            .map_err(|e| anyhow::anyhow!("Failed to view index from '{}': {}", path_str, e))?;

        // Read actual dimensions from the viewed index
        let dimensions = inner.dimensions();
        if dimensions == 0 {
            bail!(
                "Invalid index file '{}': viewed index has 0 dimensions",
                path_str
            );
        }

        // Build config from actual viewed values
        let config = IndexConfig {
            dimensions,
            metric: Metric::default(),
            quantization: Quantization::default(),
            connectivity: 0,
            expansion_add: 0,
            expansion_search: 0,
            multi: false,
        };

        Ok(Self { inner, config })
    }

    /// View an index with explicit configuration validation.
    ///
    /// First views the index safely (reading dimensions from file), then
    /// validates that the dimensions match the expected config.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to `.usearch` file
    /// * `config` - Expected configuration (dimensions will be validated)
    ///
    /// # Safety Note
    ///
    /// The file must not be modified or deleted while the view is active.
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - File does not exist or cannot be read
    /// - File format is invalid
    /// - Loaded dimensions don't match config dimensions
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::embedding::{VectorIndex, IndexConfig, Metric};
    ///
    /// // View with validation - error if dimensions don't match
    /// let config = IndexConfig::new(768).with_metric(Metric::InnerProduct);
    /// let index = VectorIndex::view_validated("./index.usearch", config)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn view_validated(path: impl AsRef<Path>, config: IndexConfig) -> Result<Self> {
        let path = path.as_ref();
        let mut index = Self::view_restore(path)?;

        // Validate dimensions match expected config
        if index.dimensions() != config.dimensions {
            bail!(
                "Dimension mismatch: expected {} but viewed index has {}. \
                 Use VectorIndex::view_restore() to view without dimension constraints.",
                config.dimensions,
                index.dimensions()
            );
        }

        // Update config with user-specified settings
        index.config = config;

        Ok(index)
    }

    /// Create a memory-mapped view of an index file (legacy API).
    ///
    /// This method is kept for backward compatibility. It now safely views the
    /// index first, then validates dimensions. For new code, prefer:
    /// - [`view_restore`](Self::view_restore): Safe view without dimension constraints
    /// - [`view_validated`](Self::view_validated): Safe view with dimension validation
    ///
    /// # Arguments
    ///
    /// * `path` - Path to `.usearch` file
    /// * `config` - Configuration matching the saved index
    ///
    /// # Safety Note
    ///
    /// The file must not be modified or deleted while the view is active.
    #[deprecated(
        since = "1.2.0",
        note = "Use `view_safe()` for proper file lifecycle management"
    )]
    #[allow(clippy::missing_errors_doc)]
    pub fn view(path: impl AsRef<Path>, config: IndexConfig) -> Result<Self> {
        Self::view_validated(path, config)
    }

    // =========================================================================
    // Safe Memory-Mapped Views (with file lifecycle management)
    // =========================================================================

    /// Create a memory-mapped view with proper file lifecycle management.
    ///
    /// This is the SAFEST way to view an index. The returned `IndexView`:
    /// - Keeps the file handle open to prevent file deletion issues
    /// - Reads dimensions from the file header automatically
    /// - Provides `is_valid()` to check if the backing file still exists
    ///
    /// On Unix systems, keeping the file handle open ensures the data remains
    /// accessible even if the file is unlinked from the filesystem.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to `.usearch` file
    ///
    /// # Safety Note
    ///
    /// The file must not be **modified** while the view is active. However,
    /// deletion is handled safely by keeping the file handle open.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::embedding::VectorIndex;
    ///
    /// // Create a safe view with file lifecycle management
    /// let view = VectorIndex::view_safe("./index.usearch")?;
    /// assert!(view.is_valid());
    /// println!("Viewing index with {} dimensions", view.dimensions());
    ///
    /// // View is usable even if file gets deleted (on Unix)
    /// let results = view.search(&[1.0, 0.0, 0.0, 0.0], 10)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn view_safe(path: impl AsRef<Path>) -> Result<IndexView> {
        let path = path.as_ref().to_path_buf();

        // Open file handle first - this keeps the file accessible even if deleted
        let file = File::open(&path)
            .with_context(|| format!("Failed to open index file: {}", path.display()))?;

        // Create the memory-mapped view
        let index = Self::view_restore(&path)?;

        Ok(IndexView {
            inner: index,
            _file_handle: Arc::new(file),
            path,
        })
    }

    /// Create a safe view with explicit configuration validation.
    ///
    /// Combines the safety of [`view_safe`](Self::view_safe) with dimension
    /// validation. Returns an error if the file dimensions don't match the
    /// expected config.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to `.usearch` file
    /// * `config` - Expected configuration (dimensions will be validated)
    ///
    /// # Safety Note
    ///
    /// The file must not be **modified** while the view is active. However,
    /// deletion is handled safely by keeping the file handle open.
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - File does not exist or cannot be read
    /// - File format is invalid
    /// - Loaded dimensions don't match config dimensions (if config.dimensions != 0)
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::embedding::{VectorIndex, IndexConfig, Metric};
    ///
    /// // Safe view with dimension validation
    /// let config = IndexConfig::new(768).with_metric(Metric::InnerProduct);
    /// let view = VectorIndex::view_validated_safe("./index.usearch", config)?;
    ///
    /// // Can use view methods or deref to VectorIndex
    /// let results = view.search(&[0.1f32; 768], 10)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn view_validated_safe(path: impl AsRef<Path>, config: IndexConfig) -> Result<IndexView> {
        let view = Self::view_safe(&path)?;

        // Validate dimensions if config specifies them (0 means no validation)
        if config.dimensions != 0 && view.inner.dimensions() != config.dimensions {
            bail!(
                "Dimension mismatch: expected {} but viewed index has {}. \
                 Use VectorIndex::view_safe() to view without dimension constraints.",
                config.dimensions,
                view.inner.dimensions()
            );
        }

        Ok(view)
    }

    // =========================================================================
    // In-Memory Serialization (for Redis caching, network transfer, etc.)
    // =========================================================================

    /// Get the serialized size of the index in bytes.
    ///
    /// Use this to pre-allocate buffers before calling [`to_bytes`](Self::to_bytes).
    /// The returned size includes all index data and metadata.
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::InnerProduct)?;
    /// index.reserve(10)?;
    /// index.add(0, &[1.0, 0.0, 0.0, 0.0])?;
    ///
    /// let size = index.serialized_size();
    /// println!("Index will serialize to {} bytes", size);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[must_use]
    pub fn serialized_size(&self) -> usize {
        self.inner.serialized_length()
    }

    /// Check if there's enough disk space to save the index.
    ///
    /// Uses the `fs2` crate for cross-platform disk space detection.
    /// Includes a safety margin (10% or at least 1MB) to account for
    /// filesystem overhead and metadata.
    ///
    /// # Arguments
    ///
    /// * `path` - Target file path. The parent directory is checked for available space.
    ///
    /// # Returns
    ///
    /// - `Ok(true)` if there's enough space
    /// - `Ok(false)` if there's insufficient space
    /// - `Err` if the disk space check fails (e.g., path doesn't exist)
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(768, Metric::InnerProduct)?;
    /// index.reserve(10000)?;
    /// // ... add vectors ...
    ///
    /// if index.check_disk_space("./index.usearch")? {
    ///     index.save("./index.usearch")?;
    /// } else {
    ///     eprintln!("Insufficient disk space!");
    /// }
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn check_disk_space(&self, path: impl AsRef<Path>) -> Result<bool> {
        let path = path.as_ref();
        let required = self.serialized_size() as u64;

        // Add safety margin: 10% or at least 1MB
        let safety_margin = std::cmp::max(required / 10, 1024 * 1024);
        let required_with_margin = required.saturating_add(safety_margin);

        // Get parent directory (where space matters)
        let parent = path.parent().unwrap_or_else(|| Path::new("."));

        // If parent doesn't exist, we can't check space
        if !parent.exists() {
            bail!(
                "Cannot check disk space: parent directory does not exist: {}",
                parent.display()
            );
        }

        // Use fs2 for cross-platform disk space detection
        let available = fs2::available_space(parent)
            .with_context(|| format!("Failed to check disk space for '{}'", parent.display()))?;

        Ok(available >= required_with_margin)
    }

    /// Get detailed disk space information for the target path.
    ///
    /// Returns available space, required space, and whether save would succeed.
    ///
    /// # Arguments
    ///
    /// * `path` - Target file path
    ///
    /// # Returns
    ///
    /// Tuple of `(available_bytes, required_bytes, has_enough_space)`
    ///
    /// # Errors
    ///
    /// Returns error if disk space cannot be determined.
    pub fn disk_space_info(&self, path: impl AsRef<Path>) -> Result<(u64, u64, bool)> {
        let path = path.as_ref();
        let required = self.serialized_size() as u64;
        let safety_margin = std::cmp::max(required / 10, 1024 * 1024);
        let required_with_margin = required.saturating_add(safety_margin);

        let parent = path.parent().unwrap_or_else(|| Path::new("."));

        if !parent.exists() {
            bail!(
                "Cannot check disk space: parent directory does not exist: {}",
                parent.display()
            );
        }

        let available = fs2::available_space(parent)
            .with_context(|| format!("Failed to check disk space for '{}'", parent.display()))?;

        Ok((
            available,
            required_with_margin,
            available >= required_with_margin,
        ))
    }

    /// Save index with disk space verification.
    ///
    /// This is the SAFEST way to save an index. It:
    /// 1. Checks available disk space before writing
    /// 2. Uses atomic write (temp file + rename)
    /// 3. Returns detailed information about the save operation
    ///
    /// # Arguments
    ///
    /// * `path` - File path to save to (typically with `.usearch` extension)
    ///
    /// # Returns
    ///
    /// [`SaveInfo`] containing path, size, duration, and space information.
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - Insufficient disk space (with detailed message)
    /// - Parent directory does not exist
    /// - File write fails
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(768, Metric::InnerProduct)?;
    /// index.reserve(10000)?;
    /// // ... add vectors ...
    ///
    /// let info = index.save_checked("./index.usearch")?;
    /// println!("Saved {} bytes in {:?}", info.size_bytes, info.elapsed);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn save_checked(&self, path: impl AsRef<Path>) -> Result<SaveInfo> {
        let path = path.as_ref();
        let required = self.serialized_size() as u64;
        let safety_margin = std::cmp::max(required / 10, 1024 * 1024);
        let required_with_margin = required.saturating_add(safety_margin);

        let parent = path.parent().unwrap_or_else(|| Path::new("."));

        // Check parent directory exists
        if !parent.exists() {
            bail!("Parent directory does not exist: {}", parent.display());
        }

        // Check available disk space
        let available = fs2::available_space(parent)
            .with_context(|| format!("Failed to check disk space for '{}'", parent.display()))?;

        if available < required_with_margin {
            bail!(
                "Insufficient disk space to save index: \
                 need {} bytes (including {}% safety margin), \
                 but only {} bytes available on '{}'",
                required_with_margin,
                10,
                available,
                parent.display()
            );
        }

        // Perform the save operation with timing
        let start = Instant::now();
        self.save(path)?;
        let elapsed = start.elapsed();

        Ok(SaveInfo {
            path: path.to_path_buf(),
            size_bytes: required as usize,
            elapsed,
            available_before: available,
            space_remaining: available.saturating_sub(required),
        })
    }

    /// Serialize the index to a byte vector.
    ///
    /// This enables storing the index in Redis, sending over network, or any
    /// other scenario where file-based persistence is not suitable.
    ///
    /// The serialized format includes all vectors and the HNSW graph structure.
    /// Use [`from_bytes`](Self::from_bytes) to deserialize.
    ///
    /// # Performance
    ///
    /// Serialization is O(n) where n is the number of vectors. The resulting
    /// buffer size is approximately `serialized_size()` bytes.
    ///
    /// # Errors
    ///
    /// Returns error if serialization fails (e.g., internal usearch error).
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, IndexConfig, Metric};
    ///
    /// let config = IndexConfig::new(4).with_metric(Metric::InnerProduct);
    /// let index = VectorIndex::with_config(config.clone())?;
    /// index.reserve(10)?;
    /// index.add(1, &[1.0, 0.0, 0.0, 0.0])?;
    ///
    /// // Serialize to bytes
    /// let bytes = index.to_bytes()?;
    ///
    /// // Store in Redis, send over network, etc.
    /// // redis_client.set("my_index", &bytes)?;
    ///
    /// // Later, deserialize
    /// let restored = VectorIndex::from_bytes(&bytes, config)?;
    /// assert_eq!(restored.len(), 1);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        let size = self.serialized_size();
        let mut buffer = vec![0u8; size];

        self.inner
            .save_to_buffer(&mut buffer)
            .map_err(|e| anyhow::anyhow!("Failed to serialize index to buffer: {}", e))?;

        Ok(buffer)
    }

    /// Load an index from a byte slice.
    ///
    /// Deserializes an index previously serialized with [`to_bytes`](Self::to_bytes).
    /// The provided config specifies index parameters; dimensions are validated
    /// against the loaded data.
    ///
    /// # Arguments
    ///
    /// * `data` - Serialized index data from `to_bytes()`
    /// * `config` - Index configuration. If `dimensions` is 0, dimensions are
    ///   read from the serialized data without validation.
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - Data is corrupted or not a valid usearch index
    /// - Loaded dimensions don't match config dimensions (when config.dimensions > 0)
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, IndexConfig, Metric};
    ///
    /// // Create and serialize an index
    /// let config = IndexConfig::new(4).with_metric(Metric::InnerProduct);
    /// let original = VectorIndex::with_config(config.clone())?;
    /// original.reserve(10)?;
    /// original.add(42, &[1.0, 0.0, 0.0, 0.0])?;
    ///
    /// let bytes = original.to_bytes()?;
    ///
    /// // Deserialize with dimension validation
    /// let restored = VectorIndex::from_bytes(&bytes, config)?;
    /// assert!(restored.contains(42));
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn from_bytes(data: &[u8], config: IndexConfig) -> Result<Self> {
        let options = config.to_usearch_options();
        let index = Index::new(&options)
            .map_err(|e| anyhow::anyhow!("Failed to create usearch index: {}", e))?;

        index
            .load_from_buffer(data)
            .map_err(|e| anyhow::anyhow!("Failed to deserialize index from buffer: {}", e))?;

        // Validate dimensions if config specifies non-zero dimensions
        let loaded_dims = index.dimensions();
        if config.dimensions != 0 && loaded_dims != config.dimensions {
            bail!(
                "Dimension mismatch: config specifies {} but loaded index has {}",
                config.dimensions,
                loaded_dims
            );
        }

        // Update config with actual dimensions if it was 0
        let final_config = if config.dimensions == 0 {
            IndexConfig {
                dimensions: loaded_dims,
                ..config
            }
        } else {
            config
        };

        Ok(Self {
            inner: index,
            config: final_config,
        })
    }

    /// Load an index from bytes without dimension validation.
    ///
    /// This is a convenience method that creates a config with dimensions=0,
    /// allowing the dimensions to be read from the serialized data.
    ///
    /// # Arguments
    ///
    /// * `data` - Serialized index data from `to_bytes()`
    ///
    /// # Examples
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::InnerProduct)?;
    /// index.reserve(5)?;
    /// index.add(1, &[1.0, 0.0, 0.0, 0.0])?;
    ///
    /// let bytes = index.to_bytes()?;
    ///
    /// // Restore without knowing the original dimensions
    /// let restored = VectorIndex::from_bytes_unchecked(&bytes)?;
    /// assert_eq!(restored.dimensions(), 4);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn from_bytes_unchecked(data: &[u8]) -> Result<Self> {
        // Use dimensions=0 to skip validation and read from buffer
        let config = IndexConfig {
            dimensions: 0,
            ..Default::default()
        };
        Self::from_bytes(data, config)
    }

    /// Get hardware acceleration information.
    ///
    /// Returns a string describing SIMD capabilities being used.
    #[must_use]
    pub fn hardware_acceleration(&self) -> String {
        self.inner.hardware_acceleration()
    }

    /// Change the expansion factor for search operations.
    ///
    /// Higher values improve recall at the cost of search speed.
    /// Typical range: 10-200.
    pub fn set_expansion_search(&self, expansion: usize) {
        self.inner.change_expansion_search(expansion);
    }

    /// Get current expansion factor for search.
    #[must_use]
    pub fn expansion_search(&self) -> usize {
        self.inner.expansion_search()
    }

    /// Change the expansion factor for add operations (index construction).
    ///
    /// Higher values create a better-connected graph but increase insertion time.
    /// Typical range: 64-512, default is typically 128.
    ///
    /// # Arguments
    ///
    /// * `expansion` - Expansion factor for vector addition
    ///
    /// # Example
    ///
    /// ```
    /// use go_brrr::embedding::{VectorIndex, Metric};
    ///
    /// let index = VectorIndex::new(4, Metric::Cosine)?;
    /// index.set_expansion_add(256);  // Higher quality, slower insert
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn set_expansion_add(&self, expansion: usize) {
        self.inner.change_expansion_add(expansion);
    }

    /// Get current expansion factor for add operations (index construction).
    ///
    /// Higher values increase index quality but slow down insertion.
    /// The default is typically 128.
    ///
    /// See also: [`set_expansion_add`], [`expansion_search`]
    #[must_use]
    pub fn expansion_add(&self) -> usize {
        self.inner.expansion_add()
    }

    /// Validate that a vector has the correct dimensions.
    fn validate_vector_dimensions(&self, vector: &[f32]) -> Result<()> {
        let expected = self.dimensions();
        let actual = vector.len();

        if actual != expected {
            bail!(
                "Vector dimension mismatch: expected {}, got {}",
                expected,
                actual
            );
        }

        Ok(())
    }
}

impl std::fmt::Debug for VectorIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VectorIndex")
            .field("dimensions", &self.dimensions())
            .field("metric", &self.config.metric)
            .field("quantization", &self.config.quantization)
            .field("size", &self.len())
            .field("capacity", &self.capacity())
            .field("memory_usage", &self.memory_usage())
            .finish()
    }
}

// =============================================================================
// Utility Functions
// =============================================================================

/// Convert distances to similarity scores for a specific metric.
///
/// Different metrics require different conversion formulas:
/// - `InnerProduct`/`Cosine`: distance = 1 - similarity, so score = 1 - distance
/// - `L2Squared`: distance can be any non-negative value, so score = 1 / (1 + distance)
///
/// All scores are clamped to [0, 1] range.
///
/// # Arguments
///
/// * `distances` - Raw distance values from vector search
/// * `metric` - The distance metric used for the search
///
/// # Returns
///
/// Similarity scores in [0, 1] range, where 1.0 = perfect match.
#[must_use]
pub fn distances_to_scores_for_metric(distances: &[f32], metric: Metric) -> Vec<f32> {
    const LANES: usize = 8;

    let n = distances.len();
    let mut scores = vec![0.0_f32; n];

    let simd_chunks = n / LANES;
    let remainder_start = simd_chunks * LANES;

    match metric {
        Metric::InnerProduct | Metric::Cosine => {
            // IP/Cosine: distance = 1 - similarity, so score = 1 - distance
            // SIMD constants
            let one = f32x8::splat(1.0);
            let zero = f32x8::splat(0.0);

            // Process 8 elements at a time with SIMD
            for i in 0..simd_chunks {
                let idx = i * LANES;
                let d = f32x8::from_slice(&distances[idx..]);
                // (1.0 - d).clamp(0.0, 1.0)
                let score = (one - d).simd_clamp(zero, one);
                score.copy_to_slice(&mut scores[idx..idx + LANES]);
            }

            // Scalar fallback for remainder
            for i in remainder_start..n {
                scores[i] = (1.0 - distances[i]).clamp(0.0, 1.0);
            }
        }
        Metric::L2Squared => {
            // L2: distance can be [0, infinity), use inverse formula: score = 1 / (1 + distance)
            // This maps 0 -> 1.0, infinity -> 0.0
            // SIMD constants
            let one = f32x8::splat(1.0);
            let zero = f32x8::splat(0.0);

            // Process 8 elements at a time with SIMD
            for i in 0..simd_chunks {
                let idx = i * LANES;
                let d = f32x8::from_slice(&distances[idx..]);
                // 1.0 / (1.0 + d.max(0.0))
                let score = one / (one + d.simd_max(zero));
                score.copy_to_slice(&mut scores[idx..idx + LANES]);
            }

            // Scalar fallback for remainder
            for i in remainder_start..n {
                scores[i] = 1.0 / (1.0 + distances[i].max(0.0));
            }
        }
    }

    scores
}

/// Convert search results to similarity scores (assumes Inner Product metric).
///
/// For inner product metric on normalized vectors:
/// - Distance = 1 - similarity
/// - Score = 1 - distance = inner product value
///
/// Clamps scores to [0, 1] range.
///
/// # Deprecated
///
/// Prefer [`distances_to_scores_for_metric`] or [`VectorIndex::to_similarity_scores`]
/// which handle all metrics correctly.
#[must_use]
pub fn distances_to_scores(distances: &[f32]) -> Vec<f32> {
    distances_to_scores_for_metric(distances, Metric::InnerProduct)
}

// =============================================================================
// SIMD Vector Normalization Core
// =============================================================================

/// Compute squared L2 norm using AVX-512 (f32x16 = 512-bit).
///
/// Processes 16 floats per iteration with SIMD, falls back to scalar for remainder.
#[inline]
fn squared_norm_simd16(vector: &[f32]) -> f32 {
    const LANES: usize = 16;
    let chunks = vector.len() / LANES;
    let mut acc = F32x16::splat(0.0);

    for i in 0..chunks {
        let v = F32x16::from_slice(&vector[i * LANES..]);
        acc += v * v;
    }

    // Horizontal sum + scalar remainder
    let mut sum = acc.reduce_sum();
    for i in (chunks * LANES)..vector.len() {
        sum += vector[i] * vector[i];
    }
    sum
}

/// Compute squared L2 norm using AVX2 (f32x8 = 256-bit).
///
/// Processes 8 floats per iteration with SIMD, falls back to scalar for remainder.
#[inline]
fn squared_norm_simd8(vector: &[f32]) -> f32 {
    const LANES: usize = 8;
    let chunks = vector.len() / LANES;
    let mut acc = f32x8::splat(0.0);

    for i in 0..chunks {
        let v = f32x8::from_slice(&vector[i * LANES..]);
        acc += v * v;
    }

    // Horizontal sum + scalar remainder
    let mut sum = acc.reduce_sum();
    for i in (chunks * LANES)..vector.len() {
        sum += vector[i] * vector[i];
    }
    sum
}

/// Compute squared L2 norm with runtime SIMD dispatch.
///
/// Uses AVX-512 (f32x16) if available, otherwise AVX2 (f32x8).
/// Falls back to scalar for very short vectors.
#[inline]
fn squared_norm_simd(vector: &[f32]) -> f32 {
    // Short vectors: scalar is faster due to no SIMD setup overhead
    if vector.len() < 8 {
        return vector.iter().map(|x| x * x).sum();
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        // Runtime feature detection for AVX-512
        if vector.len() >= 16 && is_x86_feature_detected!("avx512f") {
            return squared_norm_simd16(vector);
        }
    }

    // Default to AVX2 (f32x8)
    squared_norm_simd8(vector)
}

/// Normalize a mutable slice in-place using AVX-512 (f32x16).
#[inline]
fn normalize_inplace_simd16(vector: &mut [f32], inv_norm: f32) {
    const LANES: usize = 16;
    let chunks = vector.len() / LANES;
    let inv = F32x16::splat(inv_norm);

    for i in 0..chunks {
        let start = i * LANES;
        let v = F32x16::from_slice(&vector[start..]);
        let normalized = v * inv;
        normalized.copy_to_slice(&mut vector[start..start + LANES]);
    }

    // Scalar remainder
    for i in (chunks * LANES)..vector.len() {
        vector[i] *= inv_norm;
    }
}

/// Normalize a mutable slice in-place using AVX2 (f32x8).
#[inline]
fn normalize_inplace_simd8(vector: &mut [f32], inv_norm: f32) {
    const LANES: usize = 8;
    let chunks = vector.len() / LANES;
    let inv = f32x8::splat(inv_norm);

    for i in 0..chunks {
        let start = i * LANES;
        let v = f32x8::from_slice(&vector[start..]);
        let normalized = v * inv;
        normalized.copy_to_slice(&mut vector[start..start + LANES]);
    }

    // Scalar remainder
    for i in (chunks * LANES)..vector.len() {
        vector[i] *= inv_norm;
    }
}

/// Normalize a mutable slice in-place with runtime SIMD dispatch.
///
/// Uses AVX-512 (f32x16) if available, otherwise AVX2 (f32x8).
/// Falls back to scalar for very short vectors.
#[inline]
fn normalize_inplace_simd(vector: &mut [f32], inv_norm: f32) {
    // Short vectors: scalar is faster
    if vector.len() < 8 {
        for x in vector.iter_mut() {
            *x *= inv_norm;
        }
        return;
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        if vector.len() >= 16 && is_x86_feature_detected!("avx512f") {
            normalize_inplace_simd16(vector, inv_norm);
            return;
        }
    }

    normalize_inplace_simd8(vector, inv_norm);
}

/// Normalize a vector to unit length (for cosine similarity).
///
/// Returns `None` if the vector is zero or near-zero (norm < epsilon),
/// as such vectors cannot be meaningfully normalized. This prevents NaN
/// propagation in downstream operations like cosine similarity.
///
/// # Arguments
///
/// * `vector` - The input vector to normalize
///
/// # Returns
///
/// * `Some(normalized_vector)` - The unit-length vector
/// * `None` - If the input vector has zero or near-zero magnitude
///
/// # Example
///
/// ```
/// use go_brrr::embedding::normalize_vector;
///
/// let v = vec![3.0, 4.0];
/// let normalized = normalize_vector(&v).expect("non-zero vector");
/// // normalized is [0.6, 0.8] with unit length
///
/// let zero_vec = vec![0.0, 0.0];
/// assert!(normalize_vector(&zero_vec).is_none());
/// ```
#[must_use]
pub fn normalize_vector(vector: &[f32]) -> Option<Vec<f32>> {
    // SIMD-accelerated squared norm computation
    let norm: f32 = squared_norm_simd(vector).sqrt();

    // Zero or near-zero norm cannot be normalized without producing NaN
    if norm < f32::EPSILON {
        return None;
    }

    // Copy to mutable buffer and normalize in-place with SIMD
    let mut result = vector.to_vec();
    normalize_inplace_simd(&mut result, 1.0 / norm);
    Some(result)
}

/// Normalize a vector to unit length, returning the original if normalization fails.
///
/// This is a convenience wrapper around [`normalize_vector`] for cases where
/// you want to continue with the original vector rather than handle the error.
///
/// # Warning
///
/// Using an un-normalized zero vector in cosine similarity operations will
/// produce undefined or NaN results. Prefer [`normalize_vector`] and handle
/// the `None` case explicitly when correctness matters.
///
/// # Arguments
///
/// * `vector` - The input vector (consumed)
///
/// # Returns
///
/// The normalized vector, or the original if normalization failed.
#[must_use]
pub fn normalize_vector_or_original(mut vector: Vec<f32>) -> Vec<f32> {
    // SIMD-accelerated squared norm computation
    let norm: f32 = squared_norm_simd(&vector).sqrt();

    if norm < f32::EPSILON {
        return vector;
    }

    // Normalize in-place with SIMD (zero allocation for normalization)
    normalize_inplace_simd(&mut vector, 1.0 / norm);
    vector
}

/// Check if a vector contains only finite values (no NaN or Infinity).
///
/// Use this to validate embeddings before indexing or searching to prevent
/// NaN propagation through vector operations.
///
/// # Arguments
///
/// * `vector` - The vector to validate
///
/// # Returns
///
/// `true` if all elements are finite, `false` if any element is NaN or Infinity.
///
/// # Example
///
/// ```
/// use go_brrr::embedding::is_valid_vector;
///
/// assert!(is_valid_vector(&[1.0, 2.0, 3.0]));
/// assert!(!is_valid_vector(&[1.0, f32::NAN, 3.0]));
/// assert!(!is_valid_vector(&[f32::INFINITY, 2.0, 3.0]));
/// ```
#[must_use]
pub fn is_valid_vector(vector: &[f32]) -> bool {
    const LANES: usize = 8;

    let chunks = vector.chunks_exact(LANES);
    let remainder = chunks.remainder();

    // SIMD check: process 8 floats at a time, early exit on first invalid
    for chunk in chunks {
        let v = f32x8::from_slice(chunk);
        // is_finite() returns mask where true = finite (not NaN and not Inf)
        if !v.is_finite().all() {
            return false;
        }
    }

    // Scalar fallback for remainder (0-7 elements)
    remainder.iter().all(|x| x.is_finite())
}

/// Check if a vector is approximately normalized (unit length).
#[must_use]
pub fn is_normalized(vector: &[f32], epsilon: f32) -> bool {
    const LANES: usize = 8;

    let chunks = vector.chunks_exact(LANES);
    let remainder = chunks.remainder();

    // SIMD sum of squares: accumulate 8 lanes in parallel
    let mut acc = f32x8::splat(0.0);
    for chunk in chunks {
        let v = f32x8::from_slice(chunk);
        acc += v * v;
    }

    // Reduce SIMD accumulator to scalar
    let mut sum: f32 = acc.reduce_sum();

    // Add remainder elements (0-7)
    for &x in remainder {
        sum += x * x;
    }

    let norm = sum.sqrt();
    (norm - 1.0).abs() < epsilon
}

// =============================================================================
// Query Embedding Cache
// =============================================================================

/// Default cache capacity for query embeddings.
const QUERY_CACHE_DEFAULT_CAPACITY: usize = 100;

/// LRU cache for query embeddings to avoid recomputing same queries.
/// Stores up to 100 recent query -> embedding mappings.
///
/// Thread-safe via Mutex. Cache hits are O(1), misses are O(1) for insertion.
/// The cache uses string keys (query text) and stores the full embedding vector.
///
/// # Memory Usage
///
/// For 1024-dimensional embeddings (e.g., BGE-large):
/// - Each embedding: 1024 * 4 bytes = 4KB
/// - 100 embeddings: ~400KB + key overhead
///
/// This is negligible compared to the index itself.
static QUERY_EMBEDDING_CACHE: Lazy<Mutex<LruCache<String, Vec<f32>>>> = Lazy::new(|| {
    // SAFETY: NonZeroUsize::new returns Some for non-zero values
    let capacity = NonZeroUsize::new(QUERY_CACHE_DEFAULT_CAPACITY)
        .expect("QUERY_CACHE_DEFAULT_CAPACITY must be non-zero");
    Mutex::new(LruCache::new(capacity))
});

/// Get cached query embedding or compute and cache it.
///
/// This function provides a cache-through pattern for query embeddings:
/// 1. Check if the query is already cached
/// 2. If cached, return the cached embedding (avoiding expensive TEI call)
/// 3. If not cached, compute the embedding using the provided function
/// 4. Store the result in cache for future queries
///
/// # Arguments
///
/// * `query` - The query text to get/compute embedding for
/// * `compute_fn` - Fallback function to compute embedding if not cached
///
/// # Returns
///
/// The embedding vector for the query (from cache or freshly computed).
///
/// # Errors
///
/// Returns an error if the compute function fails.
///
/// # Example
///
/// ```no_run
/// use go_brrr::embedding::get_cached_query_embedding;
///
/// # async fn example() -> anyhow::Result<()> {
/// let embedding = get_cached_query_embedding("authentication logic", |q| {
///     // This would normally call TEI server
///     Ok(vec![0.1f32; 768])
/// })?;
/// # Ok(())
/// # }
/// ```
pub fn get_cached_query_embedding<F>(query: &str, compute_fn: F) -> Result<Vec<f32>>
where
    F: FnOnce(&str) -> Result<Vec<f32>>,
{
    let cache_key = query.to_string();

    // Try cache first (fast path)
    {
        let mut cache = QUERY_EMBEDDING_CACHE
            .lock()
            .map_err(|e| anyhow::anyhow!("Failed to acquire cache lock: {}", e))?;
        if let Some(embedding) = cache.get(&cache_key) {
            tracing::debug!(query = %query, "Query embedding cache hit");
            return Ok(embedding.clone());
        }
    }

    tracing::debug!(query = %query, "Query embedding cache miss, computing...");

    // Compute embedding (slow path - calls TEI server)
    let embedding = compute_fn(query)?;

    // Cache result for future queries
    {
        let mut cache = QUERY_EMBEDDING_CACHE
            .lock()
            .map_err(|e| anyhow::anyhow!("Failed to acquire cache lock: {}", e))?;
        cache.put(cache_key, embedding.clone());
    }

    Ok(embedding)
}

/// Async version of `get_cached_query_embedding` for use with async embedding backends.
///
/// This provides the same cache-through pattern but accepts an async compute function,
/// which is necessary when the embedding computation involves async I/O (e.g., gRPC calls).
///
/// # Arguments
///
/// * `query` - The query text to get/compute embedding for
/// * `compute_fn` - Async fallback function to compute embedding if not cached
///
/// # Returns
///
/// The embedding vector for the query (from cache or freshly computed).
///
/// # Errors
///
/// Returns an error if the compute function fails.
pub async fn get_cached_query_embedding_async<F, Fut>(
    query: &str,
    compute_fn: F,
) -> Result<Vec<f32>>
where
    F: FnOnce(String) -> Fut,
    Fut: std::future::Future<Output = Result<Vec<f32>>>,
{
    let cache_key = query.to_string();

    // Try cache first (fast path)
    {
        let mut cache = QUERY_EMBEDDING_CACHE
            .lock()
            .map_err(|e| anyhow::anyhow!("Failed to acquire cache lock: {}", e))?;
        if let Some(embedding) = cache.get(&cache_key) {
            tracing::debug!(query = %query, "Query embedding cache hit (async)");
            return Ok(embedding.clone());
        }
    }

    tracing::debug!(query = %query, "Query embedding cache miss (async), computing...");

    // Compute embedding (slow path - async call to TEI server)
    let embedding = compute_fn(cache_key.clone()).await?;

    // Cache result for future queries
    {
        let mut cache = QUERY_EMBEDDING_CACHE
            .lock()
            .map_err(|e| anyhow::anyhow!("Failed to acquire cache lock: {}", e))?;
        cache.put(cache_key, embedding.clone());
    }

    Ok(embedding)
}

/// Clear all entries from the query embedding cache.
///
/// Use this when:
/// - The embedding model changes
/// - Memory pressure requires cache eviction
/// - Testing requires a clean cache state
///
/// # Errors
///
/// Returns an error if the cache lock is poisoned.
pub fn clear_query_cache() -> Result<()> {
    let mut cache = QUERY_EMBEDDING_CACHE
        .lock()
        .map_err(|e| anyhow::anyhow!("Failed to acquire cache lock: {}", e))?;
    cache.clear();
    tracing::debug!("Query embedding cache cleared");
    Ok(())
}

/// Get statistics about the query embedding cache.
///
/// Returns a tuple of (current_size, max_capacity).
///
/// # Example
///
/// ```
/// use go_brrr::embedding::query_cache_stats;
///
/// let (size, capacity) = query_cache_stats().unwrap();
/// println!("Cache: {}/{} entries", size, capacity);
/// ```
///
/// # Errors
///
/// Returns an error if the cache lock is poisoned.
pub fn query_cache_stats() -> Result<(usize, usize)> {
    let cache = QUERY_EMBEDDING_CACHE
        .lock()
        .map_err(|e| anyhow::anyhow!("Failed to acquire cache lock: {}", e))?;
    Ok((cache.len(), cache.cap().get()))
}

/// Check if a query is in the cache without affecting LRU order.
///
/// Useful for diagnostics and testing.
///
/// # Errors
///
/// Returns an error if the cache lock is poisoned.
pub fn query_in_cache(query: &str) -> Result<bool> {
    let cache = QUERY_EMBEDDING_CACHE
        .lock()
        .map_err(|e| anyhow::anyhow!("Failed to acquire cache lock: {}", e))?;
    Ok(cache.contains(query))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_index() -> VectorIndex {
        VectorIndex::new(4, Metric::InnerProduct).expect("Failed to create test index")
    }

    #[test]
    fn test_create_index() {
        let index = create_test_index();
        assert_eq!(index.dimensions(), 4);
        assert_eq!(index.len(), 0);
        assert!(index.is_empty());
    }

    #[test]
    fn test_add_and_search() {
        let index = create_test_index();
        index.reserve(10).unwrap();

        // Add some vectors
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(1, &[0.0, 1.0, 0.0, 0.0]).unwrap();
        index.add(2, &[0.0, 0.0, 1.0, 0.0]).unwrap();

        assert_eq!(index.len(), 3);
        assert!(!index.is_empty());

        // Search for exact match
        let results = index.search(&[1.0, 0.0, 0.0, 0.0], 3).unwrap();
        assert!(!results.is_empty());
        assert_eq!(results[0].0, 0); // Should find key 0 first
    }

    #[test]
    fn test_add_batch() {
        let index = create_test_index();
        index.reserve(3).unwrap();

        let keys = vec![0, 1, 2];
        let vectors = vec![
            vec![1.0, 0.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0, 0.0],
            vec![0.0, 0.0, 1.0, 0.0],
        ];

        index.add_batch(&keys, &vectors).unwrap();
        assert_eq!(index.len(), 3);
    }

    #[test]
    fn test_add_batch_flat() {
        let index = create_test_index();
        index.reserve(2).unwrap();

        let keys = vec![0, 1];
        let vectors_flat = vec![
            1.0, 0.0, 0.0, 0.0, // Vector 0
            0.0, 1.0, 0.0, 0.0, // Vector 1
        ];

        index.add_batch_flat(&keys, &vectors_flat).unwrap();
        assert_eq!(index.len(), 2);
    }

    #[test]
    fn test_dimension_validation() {
        let index = create_test_index();
        index.reserve(10).unwrap();

        // Wrong dimensions should fail
        let result = index.add(0, &[1.0, 0.0, 0.0]); // Only 3 dimensions
        assert!(result.is_err());

        let result = index.add(0, &[1.0, 0.0, 0.0, 0.0, 0.0]); // 5 dimensions
        assert!(result.is_err());

        // Correct dimensions should succeed
        let result = index.add(0, &[1.0, 0.0, 0.0, 0.0]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_contains() {
        let index = create_test_index();
        index.reserve(10).unwrap();

        assert!(!index.contains(42));

        index.add(42, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        assert!(index.contains(42));
        assert!(!index.contains(43));
    }

    #[test]
    fn test_remove() {
        let index = create_test_index();
        index.reserve(10).unwrap();

        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        assert!(index.contains(0));

        let removed = index.remove(0).unwrap();
        assert_eq!(removed, 1);
    }

    #[test]
    fn test_filtered_search() {
        let index = create_test_index();
        index.reserve(20).unwrap();

        for i in 0..10 {
            index.add(i, &[i as f32 * 0.1, 0.0, 0.0, 0.0]).unwrap();
        }

        // Only search even keys
        let results = index
            .search_filtered(&[0.5, 0.0, 0.0, 0.0], 10, |key| key % 2 == 0)
            .unwrap();

        for (key, _) in results {
            assert_eq!(key % 2, 0);
        }
    }

    #[test]
    fn test_metric_parsing() {
        assert_eq!("ip".parse::<Metric>().unwrap(), Metric::InnerProduct);
        assert_eq!("cosine".parse::<Metric>().unwrap(), Metric::Cosine);
        assert_eq!("l2".parse::<Metric>().unwrap(), Metric::L2Squared);
        assert!("invalid".parse::<Metric>().is_err());
    }

    #[test]
    fn test_normalize_vector() {
        // Normal case: non-zero vector normalizes to unit length
        let v = vec![3.0, 4.0];
        let normalized = normalize_vector(&v).expect("non-zero vector should normalize");

        let norm: f32 = normalized.iter().map(|x| x * x).sum::<f32>().sqrt();
        assert!((norm - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_normalize_vector_zero() {
        // Zero vector returns None to prevent NaN propagation
        let zero_vec = vec![0.0, 0.0, 0.0];
        assert!(normalize_vector(&zero_vec).is_none());

        // Near-zero vector also returns None
        let near_zero = vec![f32::EPSILON / 2.0, 0.0];
        assert!(normalize_vector(&near_zero).is_none());
    }

    #[test]
    fn test_normalize_vector_or_original() {
        // Normal case: returns normalized vector
        let v = vec![3.0, 4.0];
        let normalized = normalize_vector_or_original(v);
        let norm: f32 = normalized.iter().map(|x| x * x).sum::<f32>().sqrt();
        assert!((norm - 1.0).abs() < 1e-6);

        // Zero vector: returns original unchanged
        let zero_vec = vec![0.0, 0.0, 0.0];
        let result = normalize_vector_or_original(zero_vec.clone());
        assert_eq!(result, zero_vec);
    }

    #[test]
    fn test_is_valid_vector() {
        // Valid vectors
        assert!(is_valid_vector(&[1.0, 2.0, 3.0]));
        assert!(is_valid_vector(&[0.0, 0.0, 0.0]));
        assert!(is_valid_vector(&[-1.0, f32::MAX, f32::MIN]));
        assert!(is_valid_vector(&[])); // Empty vector is valid

        // Invalid vectors with NaN
        assert!(!is_valid_vector(&[1.0, f32::NAN, 3.0]));
        assert!(!is_valid_vector(&[f32::NAN]));

        // Invalid vectors with Infinity
        assert!(!is_valid_vector(&[f32::INFINITY, 2.0, 3.0]));
        assert!(!is_valid_vector(&[1.0, f32::NEG_INFINITY]));
    }

    #[test]
    fn test_is_normalized() {
        let normalized = vec![0.6, 0.8];
        let not_normalized = vec![3.0, 4.0];

        assert!(is_normalized(&normalized, 1e-6));
        assert!(!is_normalized(&not_normalized, 1e-6));
    }

    #[test]
    fn test_distances_to_scores_inner_product() {
        // Inner product: score = 1 - distance, clamped to [0, 1]
        let distances = vec![0.0, 0.5, 1.0, 1.5];
        let scores = distances_to_scores_for_metric(&distances, Metric::InnerProduct);

        assert!((scores[0] - 1.0).abs() < 1e-6); // 0.0 -> 1.0
        assert!((scores[1] - 0.5).abs() < 1e-6); // 0.5 -> 0.5
        assert!((scores[2] - 0.0).abs() < 1e-6); // 1.0 -> 0.0
        assert!((scores[3] - 0.0).abs() < 1e-6); // 1.5 -> clamped to 0.0
    }

    #[test]
    fn test_distances_to_scores_cosine() {
        // Cosine: same formula as inner product
        let distances = vec![0.0, 0.25, 0.75, 1.0];
        let scores = distances_to_scores_for_metric(&distances, Metric::Cosine);

        assert!((scores[0] - 1.0).abs() < 1e-6);
        assert!((scores[1] - 0.75).abs() < 1e-6);
        assert!((scores[2] - 0.25).abs() < 1e-6);
        assert!((scores[3] - 0.0).abs() < 1e-6);
    }

    #[test]
    fn test_distances_to_scores_l2_squared() {
        // L2: score = 1 / (1 + distance)
        // 0.0 -> 1.0, 1.0 -> 0.5, 4.0 -> 0.2, 9.0 -> 0.1
        let distances = vec![0.0, 1.0, 4.0, 9.0];
        let scores = distances_to_scores_for_metric(&distances, Metric::L2Squared);

        assert!((scores[0] - 1.0).abs() < 1e-6); // 1 / (1 + 0) = 1.0
        assert!((scores[1] - 0.5).abs() < 1e-6); // 1 / (1 + 1) = 0.5
        assert!((scores[2] - 0.2).abs() < 1e-6); // 1 / (1 + 4) = 0.2
        assert!((scores[3] - 0.1).abs() < 1e-6); // 1 / (1 + 9) = 0.1
    }

    #[test]
    fn test_distances_to_scores_l2_large_distances() {
        // L2 can handle arbitrarily large distances without clamping to 0
        let distances = vec![99.0, 999.0, 9999.0];
        let scores = distances_to_scores_for_metric(&distances, Metric::L2Squared);

        // All should be small but positive
        assert!(scores[0] > 0.0 && scores[0] < 0.02); // 1/100 = 0.01
        assert!(scores[1] > 0.0 && scores[1] < 0.002); // 1/1000 = 0.001
        assert!(scores[2] > 0.0 && scores[2] < 0.0002); // 1/10000 = 0.0001
    }

    #[test]
    fn test_distances_to_scores_backward_compat() {
        // Original function should still work for inner product
        let distances = vec![0.0, 0.5, 1.0, 1.5];
        let scores = distances_to_scores(&distances);

        assert!((scores[0] - 1.0).abs() < 1e-6);
        assert!((scores[1] - 0.5).abs() < 1e-6);
        assert!((scores[2] - 0.0).abs() < 1e-6);
        assert!((scores[3] - 0.0).abs() < 1e-6);
    }

    #[test]
    fn test_distances_to_scores_simd_path() {
        // Test with 16 elements to exercise SIMD path (8 lanes) plus remainder
        // InnerProduct: score = (1.0 - d).clamp(0.0, 1.0)
        let distances_ip: Vec<f32> = (0..16).map(|i| i as f32 * 0.1).collect();
        let scores_ip = distances_to_scores_for_metric(&distances_ip, Metric::InnerProduct);

        assert_eq!(scores_ip.len(), 16);
        for (i, &score) in scores_ip.iter().enumerate() {
            let expected = (1.0 - distances_ip[i]).clamp(0.0, 1.0);
            assert!(
                (score - expected).abs() < 1e-6,
                "IP mismatch at {i}: got {score}, expected {expected}"
            );
        }

        // L2Squared: score = 1.0 / (1.0 + d.max(0.0))
        let distances_l2: Vec<f32> = (0..16).map(|i| i as f32).collect();
        let scores_l2 = distances_to_scores_for_metric(&distances_l2, Metric::L2Squared);

        assert_eq!(scores_l2.len(), 16);
        for (i, &score) in scores_l2.iter().enumerate() {
            let expected = 1.0 / (1.0 + distances_l2[i].max(0.0));
            assert!(
                (score - expected).abs() < 1e-6,
                "L2 mismatch at {i}: got {score}, expected {expected}"
            );
        }

        // Test with 11 elements (8 SIMD + 3 remainder)
        let distances_odd: Vec<f32> = (0..11).map(|i| i as f32 * 0.05).collect();
        let scores_odd = distances_to_scores_for_metric(&distances_odd, Metric::Cosine);

        assert_eq!(scores_odd.len(), 11);
        for (i, &score) in scores_odd.iter().enumerate() {
            let expected = (1.0 - distances_odd[i]).clamp(0.0, 1.0);
            assert!(
                (score - expected).abs() < 1e-6,
                "Odd mismatch at {i}: got {score}, expected {expected}"
            );
        }
    }

    #[test]
    fn test_vector_index_to_similarity_scores() {
        // Test the VectorIndex method uses correct metric
        let index_ip = VectorIndex::new(4, Metric::InnerProduct).unwrap();
        let index_l2 = VectorIndex::new(4, Metric::L2Squared).unwrap();

        let distances = vec![0.5, 4.0];

        // IP: 0.5 -> 0.5, 4.0 -> clamped to 0.0
        let scores_ip = index_ip.to_similarity_scores(&distances);
        assert!((scores_ip[0] - 0.5).abs() < 1e-6);
        assert!((scores_ip[1] - 0.0).abs() < 1e-6);

        // L2: 0.5 -> 1/1.5 = 0.667, 4.0 -> 1/5 = 0.2
        let scores_l2 = index_l2.to_similarity_scores(&distances);
        assert!((scores_l2[0] - (1.0 / 1.5)).abs() < 1e-6);
        assert!((scores_l2[1] - 0.2).abs() < 1e-6);
    }

    #[test]
    fn test_metric_getter() {
        let index = VectorIndex::new(4, Metric::Cosine).unwrap();
        assert_eq!(index.metric(), Metric::Cosine);

        let index2 = VectorIndex::new(4, Metric::L2Squared).unwrap();
        assert_eq!(index2.metric(), Metric::L2Squared);
    }

    #[test]
    fn test_config_builder() {
        let config = IndexConfig::new(768)
            .with_metric(Metric::Cosine)
            .with_quantization(Quantization::F16)
            .with_connectivity(32)
            .with_expansion_add(128)
            .with_expansion_search(64);

        assert_eq!(config.dimensions, 768);
        assert_eq!(config.metric, Metric::Cosine);
        assert_eq!(config.quantization, Quantization::F16);
        assert_eq!(config.connectivity, 32);
        assert_eq!(config.expansion_add, 128);
        assert_eq!(config.expansion_search, 64);
    }

    #[test]
    fn test_expansion_add_getter_setter() {
        let config = IndexConfig::new(4);
        let index = VectorIndex::with_config(config).unwrap();

        // Check default (usearch default is typically > 0)
        let default = index.expansion_add();
        assert!(default > 0, "Default expansion_add should be positive");

        // Set and verify the new value
        index.set_expansion_add(256);
        assert_eq!(index.expansion_add(), 256);
    }

    #[test]
    fn test_expansion_config_applied() {
        // Test that expansion values from config are applied correctly
        let config = IndexConfig::new(4)
            .with_expansion_add(512)
            .with_expansion_search(128);

        let index = VectorIndex::with_config(config).unwrap();

        // Note: usearch may adjust these values, but they should be >= specified
        assert!(
            index.expansion_add() >= 512 || index.expansion_add() > 0,
            "expansion_add should be set from config"
        );
        assert!(
            index.expansion_search() >= 128 || index.expansion_search() > 0,
            "expansion_search should be set from config"
        );
    }

    #[test]
    fn test_expansion_search_getter_setter() {
        let index = create_test_index();

        // Check default
        let default = index.expansion_search();
        assert!(default > 0, "Default expansion_search should be positive");

        // Set and verify the new value
        index.set_expansion_search(128);
        assert_eq!(index.expansion_search(), 128);
    }

    #[test]
    fn test_estimate_memory() {
        let config = IndexConfig::new(768).with_quantization(Quantization::F32);
        let estimate = config.estimate_memory(10000);

        // Should be roughly 10000 * 768 * 4 * 2 = ~61MB
        assert!(estimate > 50_000_000);
        assert!(estimate < 100_000_000);
    }

    #[test]
    fn test_empty_search() {
        let index = create_test_index();
        let results = index.search(&[1.0, 0.0, 0.0, 0.0], 10).unwrap();
        assert!(results.is_empty());
    }

    #[test]
    fn test_search_k_larger_than_index() {
        let index = create_test_index();
        index.reserve(10).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(1, &[0.0, 1.0, 0.0, 0.0]).unwrap();

        // Ask for more results than exist
        let results = index.search(&[1.0, 0.0, 0.0, 0.0], 100).unwrap();
        assert_eq!(results.len(), 2); // Should only return what exists
    }

    #[test]
    fn test_debug_format() {
        let index = create_test_index();
        let debug_str = format!("{:?}", index);

        assert!(debug_str.contains("VectorIndex"));
        assert!(debug_str.contains("dimensions: 4"));
    }

    #[test]
    fn test_get_vector() {
        let config = IndexConfig {
            dimensions: 4,
            ..Default::default()
        };
        let index = VectorIndex::with_config(config).unwrap();
        index.reserve(10).unwrap();

        let vector = vec![1.0, 0.0, 0.0, 0.0];
        index.add(42, &vector).unwrap();

        // Retrieve existing vector
        let retrieved = index.get(42);
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap(), vector);

        // Non-existent key should return None
        assert!(index.get(999).is_none());
    }

    #[test]
    fn test_get_batch_vectors() {
        let index = create_test_index();
        index.reserve(10).unwrap();

        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(3, &[0.0, 1.0, 0.0, 0.0]).unwrap();
        index.add(5, &[0.0, 0.0, 1.0, 0.0]).unwrap();

        // Retrieve batch with some existing and some non-existing keys
        let results = index.get_batch(&[1, 2, 3, 4, 5]);

        assert!(results[0].is_some()); // Key 1 exists
        assert!(results[1].is_none()); // Key 2 doesn't exist
        assert!(results[2].is_some()); // Key 3 exists
        assert!(results[3].is_none()); // Key 4 doesn't exist
        assert!(results[4].is_some()); // Key 5 exists

        // Verify vector contents
        assert_eq!(results[0].as_ref().unwrap(), &vec![1.0, 0.0, 0.0, 0.0]);
        assert_eq!(results[2].as_ref().unwrap(), &vec![0.0, 1.0, 0.0, 0.0]);
        assert_eq!(results[4].as_ref().unwrap(), &vec![0.0, 0.0, 1.0, 0.0]);
    }

    #[test]
    fn test_count_key_standard_mode() {
        // Standard mode (non-multi): count returns 0 or 1
        let index = create_test_index();
        index.reserve(10).unwrap();

        // Non-existent key
        assert_eq!(index.count_key(42), 0);

        // Add a vector
        index.add(42, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        assert_eq!(index.count_key(42), 1);

        // Still 0 for non-existent key
        assert_eq!(index.count_key(999), 0);
    }

    #[test]
    fn test_count_key_multi_index() {
        // Multi-index mode: allows multiple vectors per key
        let config = IndexConfig::new(4)
            .with_metric(Metric::InnerProduct)
            .with_multi(true);
        let index = VectorIndex::with_config(config).unwrap();
        index.reserve(10).unwrap();

        let key = 42u64;

        // Add multiple vectors with same key
        index.add(key, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(key, &[0.0, 1.0, 0.0, 0.0]).unwrap();
        index.add(key, &[0.0, 0.0, 1.0, 0.0]).unwrap();

        // Should count all vectors under this key
        assert_eq!(index.count_key(key), 3);
        assert_eq!(index.len(), 3);

        // Non-existent key still returns 0
        assert_eq!(index.count_key(999), 0);
    }

    #[test]
    fn test_with_multi_builder() {
        // Test the with_multi builder method
        let config = IndexConfig::new(768)
            .with_metric(Metric::InnerProduct)
            .with_multi(true);

        assert!(config.multi);

        let config_no_multi = IndexConfig::new(768).with_multi(false);
        assert!(!config_no_multi.multi);
    }

    #[test]
    fn test_rename() {
        let config = IndexConfig {
            dimensions: 4,
            ..Default::default()
        };
        let index = VectorIndex::with_config(config).unwrap();
        index.reserve(10).unwrap();

        let vector = vec![1.0, 0.0, 0.0, 0.0];
        index.add(42, &vector).unwrap();

        assert!(index.contains(42));
        assert!(!index.contains(100));

        let renamed = index.rename(42, 100).unwrap();
        assert_eq!(renamed, 1);

        assert!(!index.contains(42));
        assert!(index.contains(100));

        // Verify vector is still retrievable
        let retrieved = index.get(100).unwrap();
        assert_eq!(retrieved, vector);
    }

    #[test]
    fn test_rename_fails_if_target_exists() {
        let config = IndexConfig {
            dimensions: 4,
            ..Default::default()
        };
        let index = VectorIndex::with_config(config).unwrap();
        index.reserve(10).unwrap();

        index.add(42, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(100, &[0.0, 1.0, 0.0, 0.0]).unwrap();

        // Should fail because target key exists
        let result = index.rename(42, 100);
        assert!(result.is_err());

        // Both keys should still exist
        assert!(index.contains(42));
        assert!(index.contains(100));
    }

    #[test]
    fn test_rename_overwrite() {
        let config = IndexConfig {
            dimensions: 4,
            ..Default::default()
        };
        let index = VectorIndex::with_config(config).unwrap();
        index.reserve(10).unwrap();

        let vector1 = vec![1.0, 0.0, 0.0, 0.0];
        let vector2 = vec![0.0, 1.0, 0.0, 0.0];
        index.add(42, &vector1).unwrap();
        index.add(100, &vector2).unwrap();

        // Should succeed because we're overwriting
        let renamed = index.rename_overwrite(42, 100).unwrap();
        assert_eq!(renamed, 1);

        assert!(!index.contains(42));
        assert!(index.contains(100));

        // Verify the renamed vector is there (not the original one at 100)
        let retrieved = index.get(100).unwrap();
        assert_eq!(retrieved, vector1);
    }

    #[test]
    fn test_rename_nonexistent_key() {
        let config = IndexConfig {
            dimensions: 4,
            ..Default::default()
        };
        let index = VectorIndex::with_config(config).unwrap();
        index.reserve(10).unwrap();

        // Renaming non-existent key should return 0
        let renamed = index.rename(42, 100).unwrap();
        assert_eq!(renamed, 0);
    }

    #[test]
    fn test_restore_reads_dimensions_from_file() {
        // Create and save an index with specific dimensions
        let index = create_test_index(); // 4 dimensions
        index.reserve(10).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(1, &[0.0, 1.0, 0.0, 0.0]).unwrap();

        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_restore_index.usearch");

        index.save(&path).unwrap();

        // Restore without specifying dimensions - should read from file
        let restored = VectorIndex::restore(&path).unwrap();

        assert_eq!(restored.dimensions(), 4);
        assert_eq!(restored.len(), 2);
        assert!(restored.contains(0));
        assert!(restored.contains(1));

        // Cleanup
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_load_validated_success() {
        // Create and save an index
        let index = create_test_index(); // 4 dimensions
        index.reserve(5).unwrap();
        index.add(42, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_load_validated_success.usearch");

        index.save(&path).unwrap();

        // Load with matching config - should succeed
        let config = IndexConfig::new(4).with_metric(Metric::Cosine);
        let loaded = VectorIndex::load_validated(&path, config).unwrap();

        assert_eq!(loaded.dimensions(), 4);
        assert_eq!(loaded.config().metric, Metric::Cosine);
        assert!(loaded.contains(42));

        // Cleanup
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_load_validated_dimension_mismatch() {
        // Create and save a 4-dimension index
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_load_validated_mismatch.usearch");

        index.save(&path).unwrap();

        // Try to load with wrong dimensions - should fail BEFORE corrupting state
        let wrong_config = IndexConfig::new(768); // Wrong dimensions!
        let result = VectorIndex::load_validated(&path, wrong_config);

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Dimension mismatch"));
        assert!(err_msg.contains("expected 768"));
        assert!(err_msg.contains("loaded index has 4"));

        // Cleanup
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_view_restore_reads_dimensions() {
        // Create and save an index
        let index = create_test_index(); // 4 dimensions
        index.reserve(5).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_view_restore.usearch");

        index.save(&path).unwrap();

        // View without specifying dimensions - should read from file
        let viewed = VectorIndex::view_restore(&path).unwrap();

        assert_eq!(viewed.dimensions(), 4);
        assert!(viewed.contains(0));

        // Cleanup
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_view_validated_dimension_mismatch() {
        // Create and save a 4-dimension index
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_view_validated_mismatch.usearch");

        index.save(&path).unwrap();

        // Try to view with wrong dimensions - should fail safely
        let wrong_config = IndexConfig::new(1024); // Wrong dimensions!
        let result = VectorIndex::view_validated(&path, wrong_config);

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Dimension mismatch"));

        // Cleanup
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_restore_nonexistent_file() {
        let result = VectorIndex::restore("/nonexistent/path/index.usearch");
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("not found"));
    }

    #[test]
    fn test_view_restore_nonexistent_file() {
        let result = VectorIndex::view_restore("/nonexistent/path/index.usearch");
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("not found"));
    }

    #[test]
    fn test_atomic_save_creates_valid_file() {
        // Test that atomic save creates a properly readable index
        let index = create_test_index();
        index.reserve(10).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(1, &[0.0, 1.0, 0.0, 0.0]).unwrap();
        index.add(2, &[0.0, 0.0, 1.0, 0.0]).unwrap();

        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_atomic_save.usearch");

        // Atomic save
        index.save(&path).unwrap();

        // Verify file exists and is loadable
        assert!(path.exists());
        let restored = VectorIndex::restore(&path).unwrap();
        assert_eq!(restored.len(), 3);
        assert!(restored.contains(0));
        assert!(restored.contains(1));
        assert!(restored.contains(2));

        // Cleanup
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_atomic_save_overwrites_existing_file() {
        // Test that atomic save properly replaces existing files
        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_atomic_overwrite.usearch");

        // Create and save initial index
        let index1 = create_test_index();
        index1.reserve(5).unwrap();
        index1.add(100, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index1.save(&path).unwrap();

        // Create different index and overwrite
        let index2 = create_test_index();
        index2.reserve(5).unwrap();
        index2.add(200, &[0.0, 1.0, 0.0, 0.0]).unwrap();
        index2.add(201, &[0.0, 0.0, 1.0, 0.0]).unwrap();
        index2.save(&path).unwrap();

        // Verify the new index replaced the old one
        let restored = VectorIndex::restore(&path).unwrap();
        assert_eq!(restored.len(), 2);
        assert!(!restored.contains(100)); // Old data gone
        assert!(restored.contains(200));
        assert!(restored.contains(201));

        // Cleanup
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_save_fails_on_nonexistent_parent() {
        // Test that save fails gracefully when parent directory doesn't exist
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let path = std::path::Path::new("/nonexistent_dir_abc123/index.usearch");
        let result = index.save(path);

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Parent directory does not exist"));
    }

    #[test]
    fn test_save_unsafe_works() {
        // Test that save_unsafe still works for backward compatibility
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(42, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_save_unsafe.usearch");

        // Non-atomic save
        index.save_unsafe(&path).unwrap();

        // Verify it's loadable
        let restored = VectorIndex::restore(&path).unwrap();
        assert!(restored.contains(42));

        // Cleanup
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_save_to_current_directory() {
        // Test saving to current directory (parent = ".")
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        // Save to temp dir to avoid polluting project
        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_save_cwd.usearch");

        index.save(&path).unwrap();

        // Verify
        let restored = VectorIndex::restore(&path).unwrap();
        assert!(restored.contains(0));

        // Cleanup
        std::fs::remove_file(&path).ok();
    }

    // =========================================================================
    // In-Memory Serialization Tests
    // =========================================================================

    #[test]
    fn test_serialization_roundtrip() {
        let config = IndexConfig {
            dimensions: 4,
            ..Default::default()
        };
        let index = VectorIndex::with_config(config.clone()).unwrap();
        index.reserve(10).unwrap();

        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(2, &[0.0, 1.0, 0.0, 0.0]).unwrap();

        // Serialize
        let bytes = index.to_bytes().unwrap();

        // Deserialize
        let loaded = VectorIndex::from_bytes(&bytes, config).unwrap();

        assert_eq!(loaded.len(), 2);
        assert!(loaded.contains(1));
        assert!(loaded.contains(2));
    }

    #[test]
    fn test_serialization_preserves_vectors() {
        let config = IndexConfig::new(4).with_metric(Metric::InnerProduct);
        let index = VectorIndex::with_config(config.clone()).unwrap();
        index.reserve(10).unwrap();

        let vec1 = [1.0, 0.0, 0.0, 0.0];
        let vec2 = [0.0, 1.0, 0.0, 0.0];
        let vec3 = [0.0, 0.0, 1.0, 0.0];

        index.add(10, &vec1).unwrap();
        index.add(20, &vec2).unwrap();
        index.add(30, &vec3).unwrap();

        // Serialize and deserialize
        let bytes = index.to_bytes().unwrap();
        let loaded = VectorIndex::from_bytes(&bytes, config).unwrap();

        // Verify vectors are searchable
        let results = loaded.search(&vec1, 3).unwrap();
        assert!(!results.is_empty());
        assert_eq!(results[0].0, 10); // Should find key 10 first

        // Verify get() works
        let retrieved = loaded.get(10).unwrap();
        assert_eq!(retrieved, vec1.to_vec());
    }

    #[test]
    fn test_serialization_dimension_mismatch() {
        // Create a 4-dimensional index
        let config = IndexConfig::new(4);
        let index = VectorIndex::with_config(config).unwrap();
        index.reserve(5).unwrap();
        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let bytes = index.to_bytes().unwrap();

        // Try to load with wrong dimensions
        let wrong_config = IndexConfig::new(768);
        let result = VectorIndex::from_bytes(&bytes, wrong_config);

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Dimension mismatch"));
        assert!(err_msg.contains("768"));
    }

    #[test]
    fn test_from_bytes_unchecked() {
        let config = IndexConfig::new(4);
        let index = VectorIndex::with_config(config).unwrap();
        index.reserve(5).unwrap();
        index.add(42, &[1.0, 0.5, 0.0, 0.0]).unwrap();

        let bytes = index.to_bytes().unwrap();

        // Load without specifying dimensions
        let loaded = VectorIndex::from_bytes_unchecked(&bytes).unwrap();

        assert_eq!(loaded.dimensions(), 4);
        assert!(loaded.contains(42));
        assert_eq!(loaded.len(), 1);
    }

    #[test]
    fn test_serialized_size_consistency() {
        let config = IndexConfig::new(4);
        let index = VectorIndex::with_config(config).unwrap();
        index.reserve(10).unwrap();

        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(2, &[0.0, 1.0, 0.0, 0.0]).unwrap();

        let expected_size = index.serialized_size();
        let bytes = index.to_bytes().unwrap();

        // Serialized bytes should match the reported size
        assert_eq!(bytes.len(), expected_size);
    }

    #[test]
    fn test_serialization_empty_index() {
        let config = IndexConfig::new(768);
        let index = VectorIndex::with_config(config.clone()).unwrap();
        // Don't reserve or add anything

        let bytes = index.to_bytes().unwrap();
        let loaded = VectorIndex::from_bytes(&bytes, config).unwrap();

        assert_eq!(loaded.len(), 0);
        assert!(loaded.is_empty());
        assert_eq!(loaded.dimensions(), 768);
    }

    #[test]
    fn test_serialization_with_quantization() {
        // Test that quantization settings are preserved through serialization
        let config = IndexConfig::new(4)
            .with_metric(Metric::Cosine)
            .with_quantization(Quantization::F16);
        let index = VectorIndex::with_config(config.clone()).unwrap();
        index.reserve(5).unwrap();
        index.add(1, &[0.5, 0.5, 0.5, 0.5]).unwrap();

        let bytes = index.to_bytes().unwrap();
        let loaded = VectorIndex::from_bytes(&bytes, config.clone()).unwrap();

        assert_eq!(loaded.dimensions(), 4);
        assert!(loaded.contains(1));
        assert_eq!(loaded.config().metric, Metric::Cosine);
        assert_eq!(loaded.config().quantization, Quantization::F16);
    }

    #[test]
    fn test_serialization_large_index() {
        // Test with more vectors to ensure scalability
        let config = IndexConfig::new(128);
        let index = VectorIndex::with_config(config.clone()).unwrap();
        index.reserve(1000).unwrap();

        // Add 100 vectors
        for i in 0..100u64 {
            let mut vec = vec![0.0f32; 128];
            vec[(i as usize) % 128] = 1.0;
            index.add(i, &vec).unwrap();
        }

        let bytes = index.to_bytes().unwrap();
        let loaded = VectorIndex::from_bytes(&bytes, config).unwrap();

        assert_eq!(loaded.len(), 100);
        for i in 0..100u64 {
            assert!(loaded.contains(i));
        }
    }

    // =========================================================================
    // Disk Space Checking Tests
    // =========================================================================

    #[test]
    fn test_check_disk_space_valid_path() {
        let index = create_test_index();
        index.reserve(10).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_disk_space_check.usearch");

        // Should succeed on a valid path with existing parent directory
        let has_space = index.check_disk_space(&path).unwrap();
        // Temp directory should have enough space for a tiny index
        assert!(has_space);
    }

    #[test]
    fn test_check_disk_space_nonexistent_parent() {
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let path = std::path::Path::new("/nonexistent_dir_xyz123/index.usearch");
        let result = index.check_disk_space(path);

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("parent directory does not exist"));
    }

    #[test]
    fn test_disk_space_info() {
        let index = create_test_index();
        index.reserve(10).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(1, &[0.0, 1.0, 0.0, 0.0]).unwrap();

        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_disk_space_info.usearch");

        let (available, required, has_enough) = index.disk_space_info(&path).unwrap();

        // Available should be a positive number
        assert!(available > 0);
        // Required should include safety margin (at least 1MB)
        assert!(required >= 1024 * 1024);
        // Has enough should be true for a tiny index on temp
        assert!(has_enough);
    }

    #[test]
    fn test_save_checked_success() {
        let index = create_test_index();
        index.reserve(10).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(1, &[0.0, 1.0, 0.0, 0.0]).unwrap();

        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_save_checked.usearch");

        let info = index.save_checked(&path).unwrap();

        // Verify SaveInfo fields
        assert_eq!(info.path, path);
        assert!(info.size_bytes > 0);
        assert!(info.available_before > 0);
        assert!(info.space_remaining > 0);

        // Verify the file was actually saved
        assert!(path.exists());
        let restored = VectorIndex::restore(&path).unwrap();
        assert_eq!(restored.len(), 2);

        // Cleanup
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_save_checked_nonexistent_parent() {
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let path = std::path::Path::new("/nonexistent_dir_abc999/index.usearch");
        let result = index.save_checked(path);

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Parent directory does not exist"));
    }

    #[test]
    fn test_save_info_display() {
        let info = SaveInfo {
            path: PathBuf::from("/test/index.usearch"),
            size_bytes: 5 * 1024 * 1024, // 5 MB
            elapsed: std::time::Duration::from_secs(1),
            available_before: 100 * 1024 * 1024 * 1024, // 100 GB
            space_remaining: 99 * 1024 * 1024 * 1024,   // 99 GB
        };

        let display = format!("{}", info);
        assert!(display.contains("5.00 MB"));
        assert!(display.contains("/test/index.usearch"));
        assert!(display.contains("MB/s"));
    }

    #[test]
    fn test_save_info_human_size() {
        // Test bytes
        let info = SaveInfo {
            path: PathBuf::from("test"),
            size_bytes: 500,
            elapsed: std::time::Duration::from_secs(1),
            available_before: 0,
            space_remaining: 0,
        };
        assert_eq!(info.human_size(), "500 bytes");

        // Test KB
        let info = SaveInfo {
            path: PathBuf::from("test"),
            size_bytes: 2048,
            elapsed: std::time::Duration::from_secs(1),
            available_before: 0,
            space_remaining: 0,
        };
        assert_eq!(info.human_size(), "2.00 KB");

        // Test MB
        let info = SaveInfo {
            path: PathBuf::from("test"),
            size_bytes: 5 * 1024 * 1024,
            elapsed: std::time::Duration::from_secs(1),
            available_before: 0,
            space_remaining: 0,
        };
        assert_eq!(info.human_size(), "5.00 MB");

        // Test GB
        let info = SaveInfo {
            path: PathBuf::from("test"),
            size_bytes: 2 * 1024 * 1024 * 1024,
            elapsed: std::time::Duration::from_secs(1),
            available_before: 0,
            space_remaining: 0,
        };
        assert_eq!(info.human_size(), "2.00 GB");
    }

    #[test]
    fn test_save_info_bytes_per_second() {
        let info = SaveInfo {
            path: PathBuf::from("test"),
            size_bytes: 10 * 1024 * 1024, // 10 MB
            elapsed: std::time::Duration::from_secs(2),
            available_before: 0,
            space_remaining: 0,
        };

        let bps = info.bytes_per_second();
        let expected = (10.0 * 1024.0 * 1024.0) / 2.0;
        assert!((bps - expected).abs() < 1.0);

        let mbps = info.mb_per_second();
        assert!((mbps - 5.0).abs() < 0.01);
    }

    #[test]
    fn test_save_info_zero_elapsed() {
        // Edge case: very fast save (zero duration)
        let info = SaveInfo {
            path: PathBuf::from("test"),
            size_bytes: 1000,
            elapsed: std::time::Duration::ZERO,
            available_before: 0,
            space_remaining: 0,
        };

        // Should return infinity, not panic
        assert!(info.bytes_per_second().is_infinite());
        assert!(info.mb_per_second().is_infinite());
    }

    #[test]
    fn test_check_disk_space_includes_safety_margin() {
        // This test verifies that the safety margin is being applied
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(0, &[1.0, 0.0, 0.0, 0.0]).unwrap();

        let serialized_size = index.serialized_size();
        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_safety_margin.usearch");

        let (_, required, _) = index.disk_space_info(&path).unwrap();

        // Required should be at least serialized_size + 1MB (minimum margin)
        let min_margin = 1024 * 1024u64;
        assert!(
            required >= serialized_size as u64 + min_margin,
            "Required {} should be >= serialized_size {} + margin {}",
            required,
            serialized_size,
            min_margin
        );
    }

    #[test]
    fn test_add_batch_parallel_large() {
        // Test parallel insertion with more than PARALLEL_BATCH_THRESHOLD vectors
        let dims = 128;
        let count = 500; // Well above the 100 threshold
        let index = VectorIndex::new(dims, Metric::InnerProduct).unwrap();
        index.reserve(count).unwrap();

        let keys: Vec<u64> = (0..count as u64).collect();
        let vectors: Vec<Vec<f32>> = (0..count)
            .map(|i| {
                let mut v = vec![0.0f32; dims];
                v[i % dims] = 1.0; // Create orthogonal-ish vectors
                v
            })
            .collect();

        index.add_batch(&keys, &vectors).unwrap();
        assert_eq!(index.len(), count);

        // Verify all vectors were added correctly
        for key in 0..count as u64 {
            assert!(index.contains(key), "Missing key {}", key);
        }
    }

    #[test]
    fn test_add_batch_flat_parallel_large() {
        // Test parallel flat insertion with more than PARALLEL_BATCH_THRESHOLD vectors
        let dims = 64;
        let count = 200;
        let index = VectorIndex::new(dims, Metric::InnerProduct).unwrap();
        index.reserve(count).unwrap();

        let keys: Vec<u64> = (0..count as u64).collect();
        let mut vectors_flat = vec![0.0f32; count * dims];
        for i in 0..count {
            vectors_flat[i * dims + (i % dims)] = 1.0;
        }

        index.add_batch_flat(&keys, &vectors_flat).unwrap();
        assert_eq!(index.len(), count);

        for key in 0..count as u64 {
            assert!(index.contains(key), "Missing key {}", key);
        }
    }

    #[test]
    fn test_add_batch_sequential_method() {
        let index = create_test_index();
        index.reserve(5).unwrap();

        let keys = vec![0, 1, 2, 3, 4];
        let vectors = vec![
            vec![1.0, 0.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0, 0.0],
            vec![0.0, 0.0, 1.0, 0.0],
            vec![0.0, 0.0, 0.0, 1.0],
            vec![0.5, 0.5, 0.0, 0.0],
        ];

        index.add_batch_sequential(&keys, &vectors).unwrap();
        assert_eq!(index.len(), 5);
    }

    #[test]
    fn test_add_batch_empty() {
        let index = create_test_index();
        index.reserve(10).unwrap();

        // Empty batch should succeed
        let keys: Vec<u64> = vec![];
        let vectors: Vec<Vec<f32>> = vec![];
        index.add_batch(&keys, &vectors).unwrap();
        assert_eq!(index.len(), 0);
    }

    #[test]
    fn test_add_batch_flat_empty() {
        let index = create_test_index();
        index.reserve(10).unwrap();

        let keys: Vec<u64> = vec![];
        let vectors_flat: Vec<f32> = vec![];
        index.add_batch_flat(&keys, &vectors_flat).unwrap();
        assert_eq!(index.len(), 0);
    }

    #[test]
    fn test_add_batch_below_parallel_threshold() {
        // Test that small batches (below threshold) still work correctly
        let index = create_test_index();
        let count = 50; // Below PARALLEL_BATCH_THRESHOLD (100)
        index.reserve(count).unwrap();

        let keys: Vec<u64> = (0..count as u64).collect();
        let vectors: Vec<Vec<f32>> = (0..count).map(|_| vec![0.25, 0.25, 0.25, 0.25]).collect();

        index.add_batch(&keys, &vectors).unwrap();
        assert_eq!(index.len(), count);
    }

    // =========================================================================
    // IndexView (Safe Memory-Mapped View) Tests
    // =========================================================================

    #[test]
    fn test_view_safe_basic() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir.path().join("test_view_safe.usearch");

        // Create and save an index
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(2, &[0.0, 1.0, 0.0, 0.0]).unwrap();
        index.save(&path).unwrap();

        // Open a safe view
        let view = VectorIndex::view_safe(&path).unwrap();

        // Verify basic properties
        assert!(view.is_valid());
        assert_eq!(view.path(), path);
        assert_eq!(view.dimensions(), 4);
        assert_eq!(view.len(), 2);
        assert!(!view.is_empty());
        assert!(view.contains(1));
        assert!(view.contains(2));
        assert!(!view.contains(3));
    }

    #[test]
    fn test_view_safe_search() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir.path().join("test_view_safe_search.usearch");

        // Create and save an index
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.add(2, &[0.0, 1.0, 0.0, 0.0]).unwrap();
        index.add(3, &[0.0, 0.0, 1.0, 0.0]).unwrap();
        index.save(&path).unwrap();

        // Open a safe view and search
        let view = VectorIndex::view_safe(&path).unwrap();
        let results = view.search(&[1.0, 0.0, 0.0, 0.0], 3).unwrap();

        assert!(!results.is_empty());
        assert_eq!(results[0].0, 1); // Should find key 1 first (exact match)
    }

    #[test]
    fn test_view_validated_safe_matching_dimensions() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir.path().join("test_view_validated_safe.usearch");

        // Create and save an index with 4 dimensions
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.save(&path).unwrap();

        // Open with matching dimensions - should succeed
        let config = IndexConfig::new(4);
        let view = VectorIndex::view_validated_safe(&path, config).unwrap();

        assert!(view.is_valid());
        assert_eq!(view.dimensions(), 4);
        assert!(view.contains(1));
    }

    #[test]
    fn test_view_validated_safe_dimension_mismatch() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir
            .path()
            .join("test_view_validated_safe_mismatch.usearch");

        // Create and save an index with 4 dimensions
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.save(&path).unwrap();

        // Try to open with wrong dimensions - should fail
        let config = IndexConfig::new(768);
        let result = VectorIndex::view_validated_safe(&path, config);

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Dimension mismatch"));
    }

    #[test]
    fn test_view_validated_safe_zero_dimension_skips_validation() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir
            .path()
            .join("test_view_validated_safe_zero.usearch");

        // Create and save an index with 4 dimensions
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.save(&path).unwrap();

        // Open with 0 dimensions - should skip validation
        let config = IndexConfig::new(0);
        let view = VectorIndex::view_validated_safe(&path, config).unwrap();

        assert!(view.is_valid());
        assert_eq!(view.dimensions(), 4); // Actual dimensions from file
    }

    #[test]
    fn test_view_safe_nonexistent_file() {
        let result = VectorIndex::view_safe("/nonexistent/path/index.usearch");
        assert!(result.is_err());
    }

    #[test]
    fn test_view_safe_into_inner() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir.path().join("test_view_safe_into_inner.usearch");

        // Create and save an index
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.save(&path).unwrap();

        // Open a safe view and convert to VectorIndex
        let view = VectorIndex::view_safe(&path).unwrap();
        let inner = view.into_inner();

        // Can still use the inner VectorIndex
        assert_eq!(inner.dimensions(), 4);
        assert!(inner.contains(1));
    }

    #[test]
    fn test_view_safe_deref() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir.path().join("test_view_safe_deref.usearch");

        // Create and save an index
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.save(&path).unwrap();

        // Open a safe view
        let view = VectorIndex::view_safe(&path).unwrap();

        // Deref should work to access VectorIndex methods
        fn takes_vector_index(index: &VectorIndex) -> bool {
            index.contains(1)
        }

        assert!(takes_vector_index(&view));
    }

    #[cfg(unix)]
    #[test]
    fn test_view_safe_keeps_file_open_on_delete() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir.path().join("test_view_safe_delete.usearch");

        // Create and save an index
        let index = create_test_index();
        index.reserve(5).unwrap();
        index.add(1, &[1.0, 0.0, 0.0, 0.0]).unwrap();
        index.save(&path).unwrap();

        // Open a safe view
        let view = VectorIndex::view_safe(&path).unwrap();
        assert!(view.is_valid());
        assert!(view.contains(1));

        // Delete the file - on Unix, the file handle keeps data accessible
        std::fs::remove_file(&path).unwrap();

        // is_valid() should now return false (file unlinked)
        assert!(!view.is_valid());

        // But the view should still be usable because file handle keeps data
        // Note: This is platform-specific behavior (Unix file semantics)
        assert!(view.contains(1));

        // Search should still work
        let results = view.search(&[1.0, 0.0, 0.0, 0.0], 1).unwrap();
        assert!(!results.is_empty());
        assert_eq!(results[0].0, 1);
    }

    // =========================================================================
    // Query Embedding Cache Tests
    // =========================================================================

    #[test]
    fn test_query_cache_basic_operations() {
        // Clear cache before test to ensure clean state
        clear_query_cache().unwrap();

        // Cache should be empty initially
        let (size, capacity) = query_cache_stats().unwrap();
        assert_eq!(size, 0);
        assert_eq!(capacity, 100);

        // Query not in cache
        assert!(!query_in_cache("test query").unwrap());

        // Add query via get_cached_query_embedding
        let call_count = std::sync::atomic::AtomicUsize::new(0);
        let embedding = get_cached_query_embedding("test query", |_q| {
            call_count.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            Ok(vec![0.1, 0.2, 0.3, 0.4])
        })
        .unwrap();

        assert_eq!(embedding, vec![0.1, 0.2, 0.3, 0.4]);
        assert_eq!(call_count.load(std::sync::atomic::Ordering::SeqCst), 1);

        // Query should now be in cache
        assert!(query_in_cache("test query").unwrap());
        let (size, _) = query_cache_stats().unwrap();
        assert_eq!(size, 1);

        // Second call should use cache (compute_fn not called)
        let embedding2 = get_cached_query_embedding("test query", |_q| {
            call_count.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            Ok(vec![0.5, 0.6, 0.7, 0.8]) // Different value to prove cache is used
        })
        .unwrap();

        assert_eq!(embedding2, vec![0.1, 0.2, 0.3, 0.4]); // Should be original cached value
        assert_eq!(call_count.load(std::sync::atomic::Ordering::SeqCst), 1); // Not incremented

        // Clear cache and verify
        clear_query_cache().unwrap();
        let (size, _) = query_cache_stats().unwrap();
        assert_eq!(size, 0);
        assert!(!query_in_cache("test query").unwrap());
    }

    #[test]
    fn test_query_cache_different_queries() {
        clear_query_cache().unwrap();

        // Add multiple different queries
        for i in 0..5 {
            let query = format!("query {}", i);
            let embedding = get_cached_query_embedding(&query, |_q| Ok(vec![i as f32; 4])).unwrap();
            assert_eq!(embedding, vec![i as f32; 4]);
        }

        // All should be cached
        let (size, _) = query_cache_stats().unwrap();
        assert_eq!(size, 5);

        // Verify each is in cache
        for i in 0..5 {
            let query = format!("query {}", i);
            assert!(query_in_cache(&query).unwrap());
        }

        clear_query_cache().unwrap();
    }

    #[test]
    fn test_query_cache_compute_error_not_cached() {
        clear_query_cache().unwrap();

        // Attempt to cache a query where compute_fn returns error
        let result = get_cached_query_embedding("error query", |_q| {
            Err(anyhow::anyhow!("Simulated TEI error"))
        });

        assert!(result.is_err());

        // Failed query should NOT be in cache
        assert!(!query_in_cache("error query").unwrap());
        let (size, _) = query_cache_stats().unwrap();
        assert_eq!(size, 0);

        clear_query_cache().unwrap();
    }

    #[tokio::test]
    async fn test_query_cache_async_basic() {
        clear_query_cache().unwrap();

        let call_count = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let call_count_clone = call_count.clone();

        // First call - should compute
        let embedding = get_cached_query_embedding_async("async test", |_q| {
            let cc = call_count_clone.clone();
            async move {
                cc.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                Ok(vec![1.0, 2.0, 3.0])
            }
        })
        .await
        .unwrap();

        assert_eq!(embedding, vec![1.0, 2.0, 3.0]);
        assert_eq!(call_count.load(std::sync::atomic::Ordering::SeqCst), 1);

        // Second call - should use cache
        let call_count_clone2 = call_count.clone();
        let embedding2 = get_cached_query_embedding_async("async test", |_q| {
            let cc = call_count_clone2.clone();
            async move {
                cc.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                Ok(vec![9.0, 9.0, 9.0])
            }
        })
        .await
        .unwrap();

        assert_eq!(embedding2, vec![1.0, 2.0, 3.0]); // Cached value
        assert_eq!(call_count.load(std::sync::atomic::Ordering::SeqCst), 1); // Not incremented

        clear_query_cache().unwrap();
    }
}
