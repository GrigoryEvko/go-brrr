//! Semantic clone detection (Type-4 clones).
//!
//! Detects semantically similar code using embedding-based comparison.
//! Unlike textual (Type-1) or structural (Type-2/Type-3) clone detection,
//! semantic clone detection finds code that does similar things even if
//! the implementation differs significantly.
//!
//! # Algorithm
//!
//! 1. **Unit Extraction**: Extract code units (functions, methods, classes) using
//!    the semantic extractor from `src/semantic/extractor.rs`
//! 2. **Embedding Generation**: Generate embeddings for each unit using the
//!    embedding infrastructure from `src/embedding/`
//! 3. **Similarity Computation**: Compute cosine similarity between embeddings
//!    using SIMD-accelerated operations
//! 4. **Clustering**: Group similar units into clone clusters using HNSW
//!    for approximate nearest neighbor search
//!
//! # Example
//!
//! ```ignore
//! use brrr::quality::clones::semantic::{
//!     SemanticCloneDetector, SemanticCloneConfig, detect_semantic_clones
//! };
//!
//! // Quick detection with defaults
//! let result = detect_semantic_clones("./src", None)?;
//! for pair in &result.clone_pairs {
//!     println!("Clone pair: {} <-> {} (similarity: {:.2}%)",
//!         pair.unit_a_id, pair.unit_b_id, pair.similarity * 100.0);
//! }
//!
//! // Custom configuration
//! let config = SemanticCloneConfig::default()
//!     .with_high_similarity_threshold(0.85)
//!     .with_min_lines(10);
//! let detector = SemanticCloneDetector::new(config);
//! let result = detector.detect("./src")?;
//! ```
//!
//! # Thresholds
//!
//! The detector uses configurable similarity thresholds:
//!
//! | Threshold | Default | Description |
//! |-----------|---------|-------------|
//! | `identical_threshold` | 0.98 | Consider as exact semantic clone |
//! | `high_similarity` | 0.90 | Strongly recommend deduplication |
//! | `medium_similarity` | 0.80 | Suggest review |
//! | `low_similarity` | 0.70 | Report but don't recommend action |

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use fixedbitset::FixedBitSet;
use fxhash::FxHashSet;
use serde::{Deserialize, Serialize};
use tracing::{debug, info, warn};

use crate::embedding::{Metric, VectorIndex};
use crate::semantic::{EmbeddingUnit, UnitKind};

// =============================================================================
// BOILERPLATE FILTERING
// =============================================================================

/// Names of functions/methods that are boilerplate and should be excluded
/// from semantic clone detection. These are typically trait implementations,
/// standard library patterns, or trivial accessor methods that naturally
/// have high similarity across the codebase.
const BOILERPLATE_NAMES: &[&str] = &[
    // Rust trait implementations (Debug, Clone, Default, etc.)
    "fmt",
    "clone",
    "clone_from",
    "default",
    "drop",
    "deref",
    "deref_mut",
    "from",
    "into",
    "try_from",
    "try_into",
    "as_ref",
    "as_mut",
    "borrow",
    "borrow_mut",
    "eq",
    "ne",
    "partial_cmp",
    "cmp",
    "hash",
    "serialize",
    "deserialize",
    // Common trivial constructors/builders
    "new",
    "build",
    "builder",
    "with_capacity",
    "create",
    "make",
    "init",
    "setup",
    // Trivial accessors
    "get",
    "set",
    "is_empty",
    "len",
    "size",
    "capacity",
    "count",
    "is_some",
    "is_none",
    "is_ok",
    "is_err",
    "as_str",
    "as_bytes",
    "as_slice",
    "as_ptr",
    "as_mut_ptr",
    // Iterator methods
    "iter",
    "iter_mut",
    "into_iter",
    "next",
    "size_hint",
    // Collection methods
    "push",
    "pop",
    "insert",
    "remove",
    "clear",
    "contains",
    "get_mut",
    "entry",
    // Option/Result methods
    "unwrap",
    "expect",
    "ok",
    "err",
    "map",
    "and_then",
    "or_else",
    "map_err",
    "unwrap_or",
    "unwrap_or_else",
    "unwrap_or_default",
    // Display/formatting
    "to_string",
    "display",
    "write",
    "read",
    // Python dunder methods
    "__init__",
    "__str__",
    "__repr__",
    "__eq__",
    "__ne__",
    "__lt__",
    "__le__",
    "__gt__",
    "__ge__",
    "__hash__",
    "__len__",
    "__iter__",
    "__next__",
    "__enter__",
    "__exit__",
    "__getitem__",
    "__setitem__",
    "__delitem__",
    "__contains__",
    "__call__",
    "__bool__",
    // Go interface methods
    "String",
    "Error",
    "Read",
    "Write",
    "Close",
    "Len",
    "Less",
    "Swap",
    "MarshalJSON",
    "UnmarshalJSON",
    // JavaScript/TypeScript
    "constructor",
    "toString",
    "valueOf",
    "toJSON",
    "render",
    "componentDidMount",
    "componentWillUnmount",
    "shouldComponentUpdate",
    "componentDidUpdate",
];

/// Short names that are likely to be trivial getters/setters.
/// Functions with names this short are often not interesting for clone detection.
const MIN_INTERESTING_NAME_LENGTH: usize = 4;

/// Default metric string for serde.
fn default_metric_string() -> String {
    "inner_product".to_string()
}

// =============================================================================
// TYPES
// =============================================================================

/// Type of semantic clone based on similarity score.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SemanticCloneType {
    /// Identical semantic clone (similarity >= 0.98).
    /// Code that is semantically equivalent, possibly with minor differences.
    Identical,

    /// High similarity clone (0.90 <= similarity < 0.98).
    /// Strong candidates for deduplication.
    HighSimilarity,

    /// Medium similarity clone (0.80 <= similarity < 0.90).
    /// Should be reviewed for potential refactoring.
    MediumSimilarity,

    /// Low similarity clone (0.70 <= similarity < 0.80).
    /// Reported for awareness but may not need action.
    LowSimilarity,
}

impl SemanticCloneType {
    /// Get human-readable description.
    #[must_use]
    pub fn description(&self) -> &'static str {
        match self {
            Self::Identical => "Identical semantic clone - strongly recommend deduplication",
            Self::HighSimilarity => "High similarity - consider refactoring into shared abstraction",
            Self::MediumSimilarity => "Medium similarity - review for potential consolidation",
            Self::LowSimilarity => "Low similarity - awareness only, may share concepts",
        }
    }

    /// Get the recommended action for this clone type.
    #[must_use]
    pub fn recommendation(&self) -> &'static str {
        match self {
            Self::Identical => "Delete duplicate, redirect callers",
            Self::HighSimilarity => "Extract common function with parameters",
            Self::MediumSimilarity => "Review for shared abstraction opportunities",
            Self::LowSimilarity => "No action required - informational",
        }
    }

    /// Get severity level (1-4, higher is more severe).
    #[must_use]
    pub fn severity(&self) -> u8 {
        match self {
            Self::Identical => 4,
            Self::HighSimilarity => 3,
            Self::MediumSimilarity => 2,
            Self::LowSimilarity => 1,
        }
    }

    /// Convert to string representation.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Identical => "identical",
            Self::HighSimilarity => "high_similarity",
            Self::MediumSimilarity => "medium_similarity",
            Self::LowSimilarity => "low_similarity",
        }
    }
}

impl std::fmt::Display for SemanticCloneType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// A pair of semantically similar code units.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClonePair {
    /// ID of the first unit (format: file::name or file::class.method).
    pub unit_a_id: String,

    /// ID of the second unit.
    pub unit_b_id: String,

    /// Cosine similarity score (0.0 to 1.0, higher is more similar).
    pub similarity: f32,

    /// Classification based on similarity threshold.
    pub clone_type: SemanticCloneType,

    /// File containing unit A.
    pub file_a: String,

    /// File containing unit B.
    pub file_b: String,

    /// Line number where unit A starts.
    pub line_a: usize,

    /// Line number where unit B starts.
    pub line_b: usize,

    /// Name of unit A.
    pub name_a: String,

    /// Name of unit B.
    pub name_b: String,

    /// Kind of unit A (function, method, class).
    pub kind_a: UnitKind,

    /// Kind of unit B.
    pub kind_b: UnitKind,

    /// Whether this is a cross-file clone.
    pub cross_file: bool,
}

impl ClonePair {
    /// Create a new clone pair from two embedding units.
    #[must_use]
    pub fn new(
        unit_a: &EmbeddingUnit,
        unit_b: &EmbeddingUnit,
        similarity: f32,
        config: &SemanticCloneConfig,
    ) -> Self {
        let clone_type = config.classify_similarity(similarity);
        let cross_file = unit_a.file != unit_b.file;

        Self {
            unit_a_id: unit_a.id.clone(),
            unit_b_id: unit_b.id.clone(),
            similarity,
            clone_type,
            file_a: unit_a.file.clone(),
            file_b: unit_b.file.clone(),
            line_a: unit_a.start_line,
            line_b: unit_b.start_line,
            name_a: unit_a.name.clone(),
            name_b: unit_b.name.clone(),
            kind_a: unit_a.kind,
            kind_b: unit_b.kind,
            cross_file,
        }
    }

    /// Check if this is a cross-file clone (potential copy-paste).
    #[must_use]
    pub fn is_cross_file(&self) -> bool {
        self.cross_file
    }

    /// Get a display-friendly summary of this clone pair.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "{} <-> {} ({:.1}% similar, {})",
            self.name_a,
            self.name_b,
            self.similarity * 100.0,
            self.clone_type
        )
    }
}

/// A cluster of semantically similar code units.
///
/// Clusters group 3 or more units that are all mutually similar,
/// representing potential opportunities for abstraction.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CloneCluster {
    /// Unique identifier for this cluster.
    pub id: usize,

    /// IDs of all units in this cluster.
    pub unit_ids: Vec<String>,

    /// Centroid embedding (average of all member embeddings).
    /// Optional because it may not be computed for all clusters.
    #[serde(skip)]
    pub centroid: Option<Vec<f32>>,

    /// Average similarity within the cluster.
    pub avg_similarity: f32,

    /// Minimum similarity within the cluster.
    pub min_similarity: f32,

    /// Maximum similarity within the cluster.
    pub max_similarity: f32,

    /// Clone type classification (based on minimum similarity).
    pub clone_type: SemanticCloneType,

    /// Number of different files represented in this cluster.
    pub file_count: usize,

    /// Files containing cluster members.
    pub files: Vec<String>,

    /// Total lines of code across all cluster members.
    pub total_lines: usize,
}

impl CloneCluster {
    /// Number of units in this cluster.
    #[must_use]
    pub fn size(&self) -> usize {
        self.unit_ids.len()
    }

    /// Estimated lines that could be saved by consolidation.
    /// Assumes all but one instance could be replaced with shared implementation.
    #[must_use]
    pub fn potential_savings(&self) -> usize {
        if self.size() <= 1 {
            return 0;
        }
        // Estimate: keep one implementation, remove others
        let avg_lines = self.total_lines / self.size();
        avg_lines * (self.size() - 1)
    }

    /// Check if this cluster spans multiple files.
    #[must_use]
    pub fn is_cross_file(&self) -> bool {
        self.file_count > 1
    }
}

/// Configuration for semantic clone detection.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SemanticCloneConfig {
    // =========================================================================
    // Similarity Thresholds
    // =========================================================================
    /// Threshold for identical semantic clones.
    /// Code with similarity >= this value is considered semantically equivalent.
    /// Default: 0.98
    pub identical_threshold: f32,

    /// Threshold for high similarity clones.
    /// Code with similarity >= this value is a strong deduplication candidate.
    /// Default: 0.90
    pub high_similarity_threshold: f32,

    /// Threshold for medium similarity clones.
    /// Code with similarity >= this value should be reviewed.
    /// Default: 0.80
    pub medium_similarity_threshold: f32,

    /// Minimum threshold for reporting clones.
    /// Code below this threshold is not reported.
    /// Default: 0.70
    pub low_similarity_threshold: f32,

    // =========================================================================
    // Filtering
    // =========================================================================
    /// Minimum lines of code for a unit to be considered.
    /// Filters out trivial functions.
    /// Default: 5
    pub min_lines: usize,

    /// Maximum lines of code for a unit to be considered.
    /// Filters out huge generated code.
    /// Default: 500
    pub max_lines: usize,

    /// Whether to exclude test files from analysis.
    /// Default: true
    pub ignore_tests: bool,

    /// Whether to exclude generated code (detected by patterns/comments).
    /// Default: true
    pub ignore_generated: bool,

    /// Whether to exclude chunks (only analyze complete units).
    /// Default: true
    pub ignore_chunks: bool,

    // =========================================================================
    // High-Signal Filtering (reduces false positives)
    // =========================================================================
    /// Whether to exclude boilerplate function names (fmt, clone, new, etc.).
    /// These are typically trait implementations or trivial methods that
    /// naturally have high similarity across the codebase.
    /// Default: true
    pub ignore_boilerplate: bool,

    /// Minimum number of statements for a function to be considered.
    /// Filters out trivial single-statement functions like getters.
    /// Default: 3
    pub min_statements: usize,

    /// Maximum size ratio between compared functions.
    /// Prevents comparing a 5-line function to a 100-line function.
    /// A ratio of 3.0 means the larger function can be at most 3x
    /// the size of the smaller one.
    /// Default: 3.0
    pub max_size_ratio: f32,

    /// Only report clones where the functions have different names.
    /// Same-named functions are often intentional (trait impls, interface
    /// implementations) and not useful to report.
    /// Default: true
    pub require_different_names: bool,

    /// Minimum function name length for consideration.
    /// Very short names (get, set, is) are often trivial accessors.
    /// Default: 4
    pub min_name_length: usize,

    /// Filter out simple enum variant-like definitions (Confidence, Severity, etc.).
    /// These often have identical structure across the codebase.
    /// Default: true
    pub ignore_simple_enums: bool,

    // =========================================================================
    // Comparison Scope
    // =========================================================================
    /// Only compare units across different files.
    /// Useful for copy-paste detection.
    /// Default: false
    pub cross_file_only: bool,

    /// Only compare units of the same language.
    /// Default: true
    pub same_language_only: bool,

    /// Only compare units of the same kind (function to function, etc.).
    /// Default: false
    pub same_kind_only: bool,

    // =========================================================================
    // Performance
    // =========================================================================
    /// Maximum number of units to process.
    /// Use 0 for unlimited.
    /// Default: 0 (unlimited)
    pub max_units: usize,

    /// Batch size for embedding generation.
    /// Default: 64
    pub batch_size: usize,

    /// Whether to use cached embeddings if available.
    /// Default: true
    pub use_cache: bool,

    /// Number of nearest neighbors to consider for each unit.
    /// Higher values find more clones but increase processing time.
    /// Default: 50
    pub k_neighbors: usize,

    // =========================================================================
    // Embedding Service
    // =========================================================================
    /// TEI server URL for embedding generation.
    /// Default: "http://localhost:8080"
    pub tei_url: String,

    /// Embedding dimensions (must match the model).
    /// Default: 1024 (for Qwen3-Embedding-0.6B)
    pub embedding_dimensions: usize,

    /// Distance metric for similarity computation (as string).
    /// Valid values: "inner_product", "cosine", "l2_squared"
    /// Default: "inner_product" (for normalized embeddings)
    #[serde(default = "default_metric_string")]
    pub metric_string: String,

    /// Distance metric (derived from metric_string, not serialized)
    #[serde(skip)]
    pub metric: Metric,

    // =========================================================================
    // Language Filter
    // =========================================================================
    /// Only process files of this language.
    /// None means all supported languages.
    pub language: Option<String>,

    // =========================================================================
    // Path Patterns
    // =========================================================================
    /// Glob patterns to include (empty = include all).
    #[serde(default)]
    pub include_patterns: Vec<String>,

    /// Glob patterns to exclude.
    #[serde(default)]
    pub exclude_patterns: Vec<String>,
}

impl Default for SemanticCloneConfig {
    fn default() -> Self {
        Self {
            // Thresholds from design doc section 11.3.1
            identical_threshold: 0.98,
            high_similarity_threshold: 0.90,
            medium_similarity_threshold: 0.80,
            low_similarity_threshold: 0.70,

            // Filtering defaults
            min_lines: 5,
            max_lines: 500,
            ignore_tests: true,
            ignore_generated: true,
            ignore_chunks: true,

            // High-signal filtering defaults (reduce false positives)
            ignore_boilerplate: true,
            min_statements: 3,
            max_size_ratio: 3.0,
            require_different_names: true,
            min_name_length: MIN_INTERESTING_NAME_LENGTH,
            ignore_simple_enums: true,

            // Comparison scope
            cross_file_only: false,
            same_language_only: true,
            same_kind_only: false,

            // Performance
            max_units: 0,
            batch_size: 64,
            use_cache: true,
            k_neighbors: 50,

            // Embedding service
            tei_url: "http://localhost:8080".to_string(),
            embedding_dimensions: 1024,
            metric_string: "inner_product".to_string(),
            metric: Metric::InnerProduct,

            // Language filter
            language: None,

            // Path patterns
            include_patterns: Vec::new(),
            exclude_patterns: Vec::new(),
        }
    }
}

impl SemanticCloneConfig {
    /// Classify a similarity score into a clone type.
    #[must_use]
    pub fn classify_similarity(&self, similarity: f32) -> SemanticCloneType {
        if similarity >= self.identical_threshold {
            SemanticCloneType::Identical
        } else if similarity >= self.high_similarity_threshold {
            SemanticCloneType::HighSimilarity
        } else if similarity >= self.medium_similarity_threshold {
            SemanticCloneType::MediumSimilarity
        } else {
            SemanticCloneType::LowSimilarity
        }
    }

    /// Check if a similarity score meets the minimum threshold.
    #[must_use]
    pub fn meets_threshold(&self, similarity: f32) -> bool {
        similarity >= self.low_similarity_threshold
    }

    // =========================================================================
    // Builder Methods
    // =========================================================================

    /// Set the identical similarity threshold.
    #[must_use]
    pub fn with_identical_threshold(mut self, threshold: f32) -> Self {
        self.identical_threshold = threshold.clamp(0.0, 1.0);
        self
    }

    /// Set the high similarity threshold.
    #[must_use]
    pub fn with_high_similarity_threshold(mut self, threshold: f32) -> Self {
        self.high_similarity_threshold = threshold.clamp(0.0, 1.0);
        self
    }

    /// Set the medium similarity threshold.
    #[must_use]
    pub fn with_medium_similarity_threshold(mut self, threshold: f32) -> Self {
        self.medium_similarity_threshold = threshold.clamp(0.0, 1.0);
        self
    }

    /// Set the low similarity threshold (minimum for reporting).
    #[must_use]
    pub fn with_low_similarity_threshold(mut self, threshold: f32) -> Self {
        self.low_similarity_threshold = threshold.clamp(0.0, 1.0);
        self
    }

    /// Set the minimum lines filter.
    #[must_use]
    pub fn with_min_lines(mut self, min: usize) -> Self {
        self.min_lines = min;
        self
    }

    /// Set the maximum lines filter.
    #[must_use]
    pub fn with_max_lines(mut self, max: usize) -> Self {
        self.max_lines = max;
        self
    }

    /// Enable/disable test file filtering.
    #[must_use]
    pub fn with_ignore_tests(mut self, ignore: bool) -> Self {
        self.ignore_tests = ignore;
        self
    }

    /// Enable/disable generated code filtering.
    #[must_use]
    pub fn with_ignore_generated(mut self, ignore: bool) -> Self {
        self.ignore_generated = ignore;
        self
    }

    /// Enable/disable cross-file only mode.
    #[must_use]
    pub fn with_cross_file_only(mut self, cross_file_only: bool) -> Self {
        self.cross_file_only = cross_file_only;
        self
    }

    /// Set the language filter.
    #[must_use]
    pub fn with_language(mut self, lang: impl Into<String>) -> Self {
        self.language = Some(lang.into());
        self
    }

    /// Set the TEI server URL.
    #[must_use]
    pub fn with_tei_url(mut self, url: impl Into<String>) -> Self {
        self.tei_url = url.into();
        self
    }

    /// Set the embedding dimensions.
    #[must_use]
    pub fn with_embedding_dimensions(mut self, dims: usize) -> Self {
        self.embedding_dimensions = dims;
        self
    }

    /// Set the number of neighbors to consider.
    #[must_use]
    pub fn with_k_neighbors(mut self, k: usize) -> Self {
        self.k_neighbors = k;
        self
    }

    /// Set the batch size for embedding generation.
    #[must_use]
    pub fn with_batch_size(mut self, size: usize) -> Self {
        self.batch_size = size.max(1);
        self
    }

    /// Set the distance metric.
    #[must_use]
    pub fn with_metric(mut self, metric: Metric) -> Self {
        self.metric = metric;
        self.metric_string = metric.as_str().to_string();
        self
    }

    // =========================================================================
    // High-Signal Filtering Builder Methods
    // =========================================================================

    /// Enable/disable boilerplate function name filtering.
    /// When enabled, functions like fmt, clone, new, etc. are excluded.
    #[must_use]
    pub fn with_ignore_boilerplate(mut self, ignore: bool) -> Self {
        self.ignore_boilerplate = ignore;
        self
    }

    /// Set the minimum number of statements for a function to be considered.
    /// Functions with fewer statements are filtered out.
    #[must_use]
    pub fn with_min_statements(mut self, min: usize) -> Self {
        self.min_statements = min;
        self
    }

    /// Set the maximum size ratio for comparing functions.
    /// Functions differing in size by more than this ratio are not compared.
    #[must_use]
    pub fn with_max_size_ratio(mut self, ratio: f32) -> Self {
        self.max_size_ratio = ratio.max(1.0);
        self
    }

    /// Enable/disable requirement for different names in clone pairs.
    /// When enabled, only functions with different names are reported as clones.
    #[must_use]
    pub fn with_require_different_names(mut self, require: bool) -> Self {
        self.require_different_names = require;
        self
    }

    /// Set the minimum function name length for consideration.
    /// Functions with shorter names are filtered out.
    #[must_use]
    pub fn with_min_name_length(mut self, min: usize) -> Self {
        self.min_name_length = min;
        self
    }

    /// Enable/disable simple enum filtering.
    /// When enabled, simple enum-like definitions are excluded.
    #[must_use]
    pub fn with_ignore_simple_enums(mut self, ignore: bool) -> Self {
        self.ignore_simple_enums = ignore;
        self
    }

    /// Configure for high-signal, low false-positive results.
    /// This enables all filtering heuristics with stricter thresholds.
    #[must_use]
    pub fn high_signal_mode(self) -> Self {
        self.with_ignore_boilerplate(true)
            .with_min_statements(3)
            .with_max_size_ratio(3.0)
            .with_require_different_names(true)
            .with_min_name_length(MIN_INTERESTING_NAME_LENGTH)
            .with_ignore_simple_enums(true)
            .with_min_lines(8)
    }

    /// Configure for permissive mode (more results, more false positives).
    /// This disables most filtering heuristics.
    #[must_use]
    pub fn permissive_mode(self) -> Self {
        self.with_ignore_boilerplate(false)
            .with_min_statements(1)
            .with_max_size_ratio(10.0)
            .with_require_different_names(false)
            .with_min_name_length(1)
            .with_ignore_simple_enums(false)
            .with_min_lines(3)
    }
}

/// Statistics about semantic clone detection.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SemanticCloneStats {
    /// Total files scanned.
    pub files_scanned: usize,

    /// Total units extracted.
    pub units_extracted: usize,

    /// Units filtered out (too small, tests, generated, etc.).
    pub units_filtered: usize,

    /// Units actually analyzed.
    pub units_analyzed: usize,

    /// Total clone pairs found.
    pub pairs_found: usize,

    /// Identical clones found.
    pub identical_count: usize,

    /// High similarity clones found.
    pub high_similarity_count: usize,

    /// Medium similarity clones found.
    pub medium_similarity_count: usize,

    /// Low similarity clones found.
    pub low_similarity_count: usize,

    /// Cross-file clones found.
    pub cross_file_count: usize,

    /// Total clusters formed.
    pub clusters_found: usize,

    /// Processing time in milliseconds.
    pub processing_time_ms: u64,

    /// Embedding generation time in milliseconds.
    pub embedding_time_ms: u64,

    /// Similarity computation time in milliseconds.
    pub similarity_time_ms: u64,
}

impl SemanticCloneStats {
    /// Calculate percentage of units that are part of clone pairs.
    #[must_use]
    pub fn clone_percentage(&self) -> f32 {
        if self.units_analyzed == 0 {
            return 0.0;
        }
        // Each pair involves 2 units, but units can be in multiple pairs
        // This is a rough estimate
        let unique_units_in_clones = (self.pairs_found * 2).min(self.units_analyzed);
        (unique_units_in_clones as f32 / self.units_analyzed as f32) * 100.0
    }
}

/// Result of semantic clone detection.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SemanticCloneAnalysis {
    /// Project path analyzed.
    pub project_path: PathBuf,

    /// Configuration used for detection.
    pub config: SemanticCloneConfig,

    /// All detected clone pairs.
    pub clone_pairs: Vec<ClonePair>,

    /// Clone clusters (groups of 3+ similar units).
    pub clusters: Vec<CloneCluster>,

    /// Detection statistics.
    pub stats: SemanticCloneStats,
}

impl SemanticCloneAnalysis {
    /// Get clone pairs of a specific type.
    #[must_use]
    pub fn pairs_by_type(&self, clone_type: SemanticCloneType) -> Vec<&ClonePair> {
        self.clone_pairs
            .iter()
            .filter(|p| p.clone_type == clone_type)
            .collect()
    }

    /// Get only identical clones.
    #[must_use]
    pub fn identical_clones(&self) -> Vec<&ClonePair> {
        self.pairs_by_type(SemanticCloneType::Identical)
    }

    /// Get only high similarity clones.
    #[must_use]
    pub fn high_similarity_clones(&self) -> Vec<&ClonePair> {
        self.pairs_by_type(SemanticCloneType::HighSimilarity)
    }

    /// Get only cross-file clones (potential copy-paste).
    #[must_use]
    pub fn cross_file_clones(&self) -> Vec<&ClonePair> {
        self.clone_pairs
            .iter()
            .filter(|p| p.is_cross_file())
            .collect()
    }

    /// Get pairs sorted by similarity (highest first).
    #[must_use]
    pub fn pairs_by_similarity(&self) -> Vec<&ClonePair> {
        let mut pairs: Vec<_> = self.clone_pairs.iter().collect();
        pairs.sort_by(|a, b| b.similarity.partial_cmp(&a.similarity).unwrap());
        pairs
    }
}

// =============================================================================
// DETECTOR
// =============================================================================

/// Semantic clone detector using embedding-based similarity.
pub struct SemanticCloneDetector {
    /// Detection configuration.
    config: SemanticCloneConfig,
}

impl SemanticCloneDetector {
    /// Create a new detector with the given configuration.
    #[must_use]
    pub fn new(config: SemanticCloneConfig) -> Self {
        Self { config }
    }

    /// Create a detector with default configuration.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(SemanticCloneConfig::default())
    }

    /// Detect semantic clones in a project using the pre-built index.
    ///
    /// This method uses the existing semantic index created by `brrr semantic index .`
    /// instead of regenerating embeddings. The index must exist at
    /// `.brrr_index/vectors.usearch` with metadata at `.brrr_index/metadata.json`.
    ///
    /// # Arguments
    ///
    /// * `project_path` - Path to the project directory containing `.brrr_index/`
    ///
    /// # Returns
    ///
    /// Analysis result containing clone pairs, clusters, and statistics.
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - No semantic index found (user needs to run `brrr semantic index .` first)
    /// - Index or metadata files are corrupted
    /// - Vector index operations fail
    pub fn detect(&self, project_path: impl AsRef<Path>) -> Result<SemanticCloneAnalysis> {
        let project_path = project_path.as_ref();
        let start_time = std::time::Instant::now();

        info!("Starting semantic clone detection in {:?}", project_path);

        // Locate index directory
        let index_dir = project_path.join(".brrr_index");
        let index_path = index_dir.join("vectors.usearch");
        let metadata_path = index_dir.join("metadata.json");

        // Check if index exists
        if !index_path.exists() {
            return Err(anyhow::anyhow!(
                "No semantic index found at {}. Run `brrr semantic index .` first to build the index.",
                index_path.display()
            ));
        }

        if !metadata_path.exists() {
            return Err(anyhow::anyhow!(
                "Metadata file not found at {}. The index may be corrupted. Run `brrr semantic index .` to rebuild.",
                metadata_path.display()
            ));
        }

        // Load metadata to get units
        info!("Loading index metadata from: {}", metadata_path.display());
        let metadata_content = std::fs::read_to_string(&metadata_path)
            .context("Failed to read metadata file")?;
        let metadata: serde_json::Value = serde_json::from_str(&metadata_content)
            .context("Failed to parse metadata JSON")?;

        let all_units: Vec<EmbeddingUnit> = serde_json::from_value(
            metadata
                .get("units")
                .cloned()
                .unwrap_or(serde_json::json!([])),
        )
        .context("Failed to parse units from metadata")?;

        // Build statistics from loaded units
        let mut stats = SemanticCloneStats::default();
        stats.units_extracted = all_units.len();

        // Count unique files
        let unique_files: FxHashSet<_> = all_units.iter().map(|u| &u.file).collect();
        stats.files_scanned = unique_files.len();

        // Apply filters to units
        let filtered_units: Vec<(usize, &EmbeddingUnit)> = all_units
            .iter()
            .enumerate()
            .filter(|(_, unit)| self.should_include_unit(unit))
            .collect();

        stats.units_filtered = stats.units_extracted - filtered_units.len();
        stats.units_analyzed = filtered_units.len();

        if filtered_units.is_empty() {
            info!("No units to analyze after filtering");
            return Ok(SemanticCloneAnalysis {
                project_path: project_path.to_path_buf(),
                config: self.config.clone(),
                clone_pairs: Vec::new(),
                clusters: Vec::new(),
                stats,
            });
        }

        // Apply max_units limit if set
        let units_to_analyze: Vec<(usize, &EmbeddingUnit)> = if self.config.max_units > 0
            && filtered_units.len() > self.config.max_units
        {
            filtered_units
                .into_iter()
                .take(self.config.max_units)
                .collect()
        } else {
            filtered_units
        };

        info!(
            "Analyzing {} units for semantic clones (filtered from {})",
            units_to_analyze.len(),
            stats.units_extracted
        );

        // Load the vector index
        info!("Loading vector index from: {}", index_path.display());
        let index = VectorIndex::restore(&index_path)
            .context("Failed to load vector index")?;

        info!(
            "Loaded index: {} vectors, {} dimensions",
            index.len(),
            index.dimensions()
        );

        // Validate index has vectors
        if index.is_empty() {
            warn!("Index contains no vectors");
            return Ok(SemanticCloneAnalysis {
                project_path: project_path.to_path_buf(),
                config: self.config.clone(),
                clone_pairs: Vec::new(),
                clusters: Vec::new(),
                stats,
            });
        }

        // Find clone pairs using the pre-built index
        let similarity_start = std::time::Instant::now();
        let clone_pairs = self.find_clone_pairs_from_index(&index, &all_units, &units_to_analyze)?;
        stats.similarity_time_ms = similarity_start.elapsed().as_millis() as u64;

        // Update statistics
        stats.pairs_found = clone_pairs.len();
        for pair in &clone_pairs {
            match pair.clone_type {
                SemanticCloneType::Identical => stats.identical_count += 1,
                SemanticCloneType::HighSimilarity => stats.high_similarity_count += 1,
                SemanticCloneType::MediumSimilarity => stats.medium_similarity_count += 1,
                SemanticCloneType::LowSimilarity => stats.low_similarity_count += 1,
            }
            if pair.is_cross_file() {
                stats.cross_file_count += 1;
            }
        }

        stats.processing_time_ms = start_time.elapsed().as_millis() as u64;

        info!(
            "Found {} clone pairs in {}ms",
            stats.pairs_found, stats.processing_time_ms
        );

        Ok(SemanticCloneAnalysis {
            project_path: project_path.to_path_buf(),
            config: self.config.clone(),
            clone_pairs,
            clusters: Vec::new(), // Clustering handled separately
            stats,
        })
    }

    /// Check if a unit should be included based on configuration filters.
    fn should_include_unit(&self, unit: &EmbeddingUnit) -> bool {
        // Filter by line count
        let line_count = unit.end_line.saturating_sub(unit.start_line) + 1;
        if line_count < self.config.min_lines || line_count > self.config.max_lines {
            return false;
        }

        // Filter out chunks if configured
        if self.config.ignore_chunks && unit.kind == UnitKind::Chunk {
            return false;
        }

        // Filter out tests if configured
        if self.config.ignore_tests && is_test_unit(unit) {
            return false;
        }

        // Filter out generated code if configured
        if self.config.ignore_generated && is_generated_unit(unit) {
            return false;
        }

        // Apply language filter if configured
        if let Some(ref lang) = self.config.language {
            if unit.language.to_lowercase() != lang.to_lowercase() {
                return false;
            }
        }

        // HIGH-SIGNAL FILTERING: Reduce false positives

        // Filter out boilerplate function names (fmt, clone, new, etc.)
        if self.config.ignore_boilerplate && is_boilerplate_name(&unit.name) {
            debug!(
                "Filtered boilerplate function: {} in {}",
                unit.name, unit.file
            );
            return false;
        }

        // Filter out short function names (get, set, is)
        if unit.name.len() < self.config.min_name_length {
            debug!(
                "Filtered short name: {} (len={}) in {}",
                unit.name,
                unit.name.len(),
                unit.file
            );
            return false;
        }

        // Filter out simple enum-like definitions
        if self.config.ignore_simple_enums && is_simple_enum_like(unit) {
            debug!(
                "Filtered simple enum-like: {} in {}",
                unit.name, unit.file
            );
            return false;
        }

        // Filter by minimum statement count
        if self.config.min_statements > 0 {
            let stmt_count = count_statements(&unit.code);
            if stmt_count < self.config.min_statements {
                debug!(
                    "Filtered by statement count: {} has {} statements (min: {})",
                    unit.name, stmt_count, self.config.min_statements
                );
                return false;
            }
        }

        true
    }

    /// Check if two units are compatible for comparison based on size ratio.
    fn are_size_compatible(&self, unit_a: &EmbeddingUnit, unit_b: &EmbeddingUnit) -> bool {
        let a_lines = (unit_a.end_line.saturating_sub(unit_a.start_line) + 1).max(1);
        let b_lines = (unit_b.end_line.saturating_sub(unit_b.start_line) + 1).max(1);
        let ratio = a_lines.max(b_lines) as f32 / a_lines.min(b_lines) as f32;
        ratio <= self.config.max_size_ratio
    }

    /// Check if two units should be compared (applies pairwise filters).
    fn should_compare_pair(&self, unit_a: &EmbeddingUnit, unit_b: &EmbeddingUnit) -> bool {
        // Check size compatibility
        if !self.are_size_compatible(unit_a, unit_b) {
            return false;
        }

        // Check different names requirement
        if self.config.require_different_names && unit_a.name == unit_b.name {
            return false;
        }

        true
    }

    /// Find clone pairs using the pre-built vector index.
    ///
    /// For each unit in `units_to_analyze`, retrieves its vector from the index
    /// and searches for similar vectors among all units.
    fn find_clone_pairs_from_index(
        &self,
        index: &VectorIndex,
        all_units: &[EmbeddingUnit],
        units_to_analyze: &[(usize, &EmbeddingUnit)],
    ) -> Result<Vec<ClonePair>> {
        if units_to_analyze.is_empty() {
            return Ok(Vec::new());
        }

        let mut clone_pairs = Vec::new();
        let mut seen_pairs: FxHashSet<(usize, usize)> = FxHashSet::default();
        // Location-based dedup to handle multiple extraction granularities at same location
        let mut seen_locations: FxHashSet<String> = FxHashSet::default();

        // Create a bitset of indices we're analyzing for quick lookup
        let max_idx = units_to_analyze.iter().map(|(idx, _)| *idx).max().unwrap_or(0);
        let mut analyzing_indices = FixedBitSet::with_capacity(max_idx + 1);
        for (idx, _) in units_to_analyze {
            analyzing_indices.insert(*idx);
        }

        // Search for neighbors of each unit we're analyzing
        for &(unit_idx, unit) in units_to_analyze {
            // Get the vector for this unit from the index
            let query_vec = match index.get(unit_idx as u64) {
                Some(vec) => vec,
                None => {
                    debug!(
                        "No vector found for unit {} (index {}), skipping",
                        unit.id, unit_idx
                    );
                    continue;
                }
            };

            // Search for similar vectors
            let neighbors = index.search(&query_vec, self.config.k_neighbors + 1)?;

            for (neighbor_id, distance) in neighbors {
                let neighbor_idx = neighbor_id as usize;

                // Skip self-match
                if unit_idx == neighbor_idx {
                    continue;
                }

                // Skip if neighbor index is out of bounds
                if neighbor_idx >= all_units.len() {
                    warn!(
                        "Neighbor index {} out of bounds (units: {}), skipping",
                        neighbor_idx,
                        all_units.len()
                    );
                    continue;
                }

                // Only include pairs where at least one unit is in our analysis set
                // This prevents comparing units that were both filtered out
                let unit_in_set = unit_idx < analyzing_indices.len() && analyzing_indices.contains(unit_idx);
                let neighbor_in_set = neighbor_idx < analyzing_indices.len() && analyzing_indices.contains(neighbor_idx);
                if !unit_in_set && !neighbor_in_set {
                    continue;
                }

                // Avoid duplicate pairs using file:line as key (handles multiple extraction granularities)
                let unit_loc = format!("{}:{}", unit.file, unit.start_line);
                let neighbor_loc = format!("{}:{}", all_units[neighbor_idx].file, all_units[neighbor_idx].start_line);
                let pair_key = if unit_loc < neighbor_loc {
                    (unit_idx, neighbor_idx) // Keep original indices for actual storage
                } else {
                    (neighbor_idx, unit_idx)
                };
                // Also check location-based dedup
                let loc_key_str = if unit_loc < neighbor_loc {
                    format!("{}|{}", unit_loc, neighbor_loc)
                } else {
                    format!("{}|{}", neighbor_loc, unit_loc)
                };
                // Skip if we've already seen this pair (by index or by location)
                if seen_pairs.contains(&pair_key) || seen_locations.contains(&loc_key_str) {
                    continue;
                }

                // Convert distance to similarity based on metric
                let similarity = distance_to_similarity(distance, self.config.metric);

                // Check threshold
                if !self.config.meets_threshold(similarity) {
                    continue;
                }

                let neighbor_unit = &all_units[neighbor_idx];

                // Skip if same file+line+name (duplicate extraction of same code)
                if unit.file == neighbor_unit.file
                    && unit.start_line == neighbor_unit.start_line
                    && unit.name == neighbor_unit.name
                {
                    continue;
                }

                // Apply cross-file filter if configured
                if self.config.cross_file_only && unit.file == neighbor_unit.file {
                    continue;
                }

                // Apply same-language filter if configured
                if self.config.same_language_only && unit.language != neighbor_unit.language {
                    continue;
                }

                // Apply same-kind filter if configured
                if self.config.same_kind_only && unit.kind != neighbor_unit.kind {
                    continue;
                }

                // Apply unit filters to the neighbor (it might not be in units_to_analyze)
                if !self.should_include_unit(neighbor_unit) {
                    continue;
                }

                // Apply pairwise comparison filters (size ratio, name requirements)
                if !self.should_compare_pair(unit, neighbor_unit) {
                    continue;
                }

                // Create clone pair
                let pair = ClonePair::new(unit, neighbor_unit, similarity, &self.config);
                clone_pairs.push(pair);
                seen_pairs.insert(pair_key);
                seen_locations.insert(loc_key_str);
            }
        }

        // Sort by similarity (highest first)
        clone_pairs.sort_by(|a, b| {
            b.similarity
                .partial_cmp(&a.similarity)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        Ok(clone_pairs)
    }
}

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

/// Check if a unit is a test function/class.
fn is_test_unit(unit: &EmbeddingUnit) -> bool {
    let name_lower = unit.name.to_lowercase();
    let file_lower = unit.file.to_lowercase();

    // Check function/class name
    if name_lower.starts_with("test_")
        || name_lower.starts_with("test")
        || name_lower.ends_with("_test")
        || name_lower.ends_with("test")
        || name_lower.contains("_test_")
    {
        return true;
    }

    // Check file path
    if file_lower.contains("test")
        || file_lower.contains("spec")
        || file_lower.contains("__tests__")
    {
        return true;
    }

    // Check semantic tags
    unit.semantic_tags.iter().any(|tag| tag == "test")
}

/// Check if a unit appears to be generated code.
fn is_generated_unit(unit: &EmbeddingUnit) -> bool {
    let file_lower = unit.file.to_lowercase();
    let code_lower = unit.code.to_lowercase();

    // Check file patterns
    if file_lower.contains("generated")
        || file_lower.contains("_gen.")
        || file_lower.contains(".gen.")
        || file_lower.ends_with(".pb.go")
        || file_lower.ends_with("_pb2.py")
        || file_lower.ends_with(".g.dart")
    {
        return true;
    }

    // Check code comments
    if code_lower.contains("auto-generated")
        || code_lower.contains("autogenerated")
        || code_lower.contains("code generated by")
        || code_lower.contains("do not edit")
        || code_lower.contains("this file is generated")
    {
        return true;
    }

    false
}

/// Check if a function name is a boilerplate/common trait implementation name.
///
/// Returns true for names like `fmt`, `clone`, `new`, `from`, etc.
/// These functions are typically trait implementations or trivial methods
/// that naturally have high similarity across the codebase.
fn is_boilerplate_name(name: &str) -> bool {
    // Normalize the name for comparison
    let name_lower = name.to_lowercase();

    // Check against the boilerplate names list
    BOILERPLATE_NAMES.iter().any(|&boilerplate| {
        let bp_lower = boilerplate.to_lowercase();
        name_lower == bp_lower
    })
}

/// Check if a unit appears to be a simple enum-like definition.
///
/// Simple enums are things like `Confidence`, `Severity`, etc. that
/// just contain variant definitions with no complex logic. These
/// naturally have identical structure and aren't interesting clones.
fn is_simple_enum_like(unit: &EmbeddingUnit) -> bool {
    // Only check class/struct-like units
    if unit.kind != UnitKind::Class {
        return false;
    }

    let code = &unit.code;
    let code_lower = code.to_lowercase();

    // Check for enum keyword
    let is_enum = code_lower.contains("enum ")
        || code_lower.starts_with("enum")
        || code.contains("#[derive")  // Rust derive macro often on enums
        || code.contains("class ") && (
            code.contains("(Enum)") || code.contains("(IntEnum)") || code.contains("(StrEnum)")
        );  // Python enums

    if !is_enum {
        return false;
    }

    // Check complexity - simple enums have few lines and no methods
    let line_count = unit.end_line.saturating_sub(unit.start_line) + 1;
    if line_count > 20 {
        return false;  // Too complex to be a simple enum
    }

    // Check for method definitions - if it has methods, it's not simple
    let has_methods = code.contains("fn ")  // Rust
        || code.contains("def ")  // Python
        || code.contains("func ")  // Go
        || (code.contains("(") && code.contains("->"));  // Various function signatures

    !has_methods
}

/// Count approximate number of statements in code.
///
/// This is a heuristic count based on line patterns, not a full AST parse.
/// Used to filter out trivial functions like single-return getters.
fn count_statements(code: &str) -> usize {
    let mut count = 0;

    for line in code.lines() {
        let trimmed = line.trim();

        // Skip empty lines and comments
        if trimmed.is_empty()
            || trimmed.starts_with("//")
            || trimmed.starts_with('#')
            || trimmed.starts_with("/*")
            || trimmed.starts_with('*')
            || trimmed.starts_with("'''")
            || trimmed.starts_with("\"\"\"")
        {
            continue;
        }

        // Skip pure braces/brackets
        if trimmed == "{" || trimmed == "}" || trimmed == "(" || trimmed == ")"
            || trimmed == "[" || trimmed == "]" || trimmed == ","
        {
            continue;
        }

        // Skip function/method signatures (they're structural, not statements)
        if trimmed.starts_with("fn ")
            || trimmed.starts_with("def ")
            || trimmed.starts_with("func ")
            || trimmed.starts_with("function ")
            || trimmed.starts_with("pub fn ")
            || trimmed.starts_with("pub async fn ")
            || trimmed.starts_with("async fn ")
            || trimmed.starts_with("async def ")
            || trimmed.starts_with("pub(crate) fn ")
            || trimmed.starts_with("pub(super) fn ")
            || (trimmed.starts_with("pub ") && trimmed.contains("fn "))
        {
            continue;
        }

        // Skip class/struct declarations
        if trimmed.starts_with("class ")
            || trimmed.starts_with("struct ")
            || trimmed.starts_with("impl ")
            || trimmed.starts_with("trait ")
            || trimmed.starts_with("interface ")
            || trimmed.starts_with("enum ")
        {
            continue;
        }

        // Skip decorators and attributes
        if trimmed.starts_with('@') || trimmed.starts_with("#[") {
            continue;
        }

        // Count this as a statement
        count += 1;
    }

    count
}

/// Convert distance to similarity based on metric.
fn distance_to_similarity(distance: f32, metric: Metric) -> f32 {
    match metric {
        // For inner product, usearch returns 1 - dot_product, so similarity = 1 - distance
        Metric::InnerProduct => 1.0 - distance,
        // For cosine, usearch returns 1 - cos_sim, so similarity = 1 - distance
        Metric::Cosine => 1.0 - distance,
        // For L2, convert to similarity using inverse
        Metric::L2Squared => 1.0 / (1.0 + distance.sqrt()),
    }
}


// =============================================================================
// PUBLIC API
// =============================================================================

/// Detect semantic clones in a project using default configuration.
///
/// # Arguments
///
/// * `project_path` - Path to the project directory
/// * `config` - Optional configuration (uses defaults if None)
///
/// # Returns
///
/// Analysis result containing clone pairs and statistics.
///
/// # Example
///
/// ```ignore
/// let result = detect_semantic_clones("./src", None)?;
/// println!("Found {} clone pairs", result.clone_pairs.len());
/// ```
pub fn detect_semantic_clones(
    project_path: impl AsRef<Path>,
    config: Option<SemanticCloneConfig>,
) -> Result<SemanticCloneAnalysis> {
    let config = config.unwrap_or_default();
    let detector = SemanticCloneDetector::new(config);
    detector.detect(project_path)
}

/// Format a summary of semantic clone detection results.
#[must_use]
pub fn format_semantic_clone_summary(analysis: &SemanticCloneAnalysis) -> String {
    let mut output = String::new();

    output.push_str("=== Semantic Clone Detection Summary ===\n\n");

    // Statistics
    output.push_str(&format!("Files scanned: {}\n", analysis.stats.files_scanned));
    output.push_str(&format!(
        "Units extracted: {}\n",
        analysis.stats.units_extracted
    ));
    output.push_str(&format!(
        "Units analyzed: {} (filtered {})\n",
        analysis.stats.units_analyzed, analysis.stats.units_filtered
    ));
    output.push_str(&format!(
        "Processing time: {}ms\n\n",
        analysis.stats.processing_time_ms
    ));

    // Clone pairs by type
    output.push_str("Clone Pairs Found:\n");
    output.push_str(&format!(
        "  Identical (>=98%): {}\n",
        analysis.stats.identical_count
    ));
    output.push_str(&format!(
        "  High similarity (>=90%): {}\n",
        analysis.stats.high_similarity_count
    ));
    output.push_str(&format!(
        "  Medium similarity (>=80%): {}\n",
        analysis.stats.medium_similarity_count
    ));
    output.push_str(&format!(
        "  Low similarity (>=70%): {}\n",
        analysis.stats.low_similarity_count
    ));
    output.push_str(&format!(
        "  Cross-file clones: {}\n\n",
        analysis.stats.cross_file_count
    ));

    // Top clone pairs
    if !analysis.clone_pairs.is_empty() {
        output.push_str("Top Clone Pairs:\n");
        for (i, pair) in analysis.pairs_by_similarity().iter().take(10).enumerate() {
            output.push_str(&format!(
                "  {}. {} <-> {} ({:.1}% similar)\n",
                i + 1,
                pair.name_a,
                pair.name_b,
                pair.similarity * 100.0
            ));
            output.push_str(&format!(
                "     {}:{} <-> {}:{}\n",
                pair.file_a, pair.line_a, pair.file_b, pair.line_b
            ));
        }
    }

    output
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clone_type_classification() {
        let config = SemanticCloneConfig::default();

        assert_eq!(
            config.classify_similarity(0.99),
            SemanticCloneType::Identical
        );
        assert_eq!(
            config.classify_similarity(0.95),
            SemanticCloneType::HighSimilarity
        );
        assert_eq!(
            config.classify_similarity(0.85),
            SemanticCloneType::MediumSimilarity
        );
        assert_eq!(
            config.classify_similarity(0.75),
            SemanticCloneType::LowSimilarity
        );
    }

    #[test]
    fn test_meets_threshold() {
        let config = SemanticCloneConfig::default();

        assert!(config.meets_threshold(0.70));
        assert!(config.meets_threshold(0.99));
        assert!(!config.meets_threshold(0.69));
        assert!(!config.meets_threshold(0.50));
    }

    #[test]
    fn test_semantic_clone_type_methods() {
        assert_eq!(SemanticCloneType::Identical.severity(), 4);
        assert_eq!(SemanticCloneType::LowSimilarity.severity(), 1);
        assert_eq!(SemanticCloneType::Identical.as_str(), "identical");
        assert!(!SemanticCloneType::HighSimilarity.description().is_empty());
        assert!(!SemanticCloneType::MediumSimilarity
            .recommendation()
            .is_empty());
    }

    #[test]
    fn test_config_builder() {
        let config = SemanticCloneConfig::default()
            .with_identical_threshold(0.95)
            .with_min_lines(10)
            .with_max_lines(200)
            .with_ignore_tests(false)
            .with_cross_file_only(true)
            .with_language("python");

        assert_eq!(config.identical_threshold, 0.95);
        assert_eq!(config.min_lines, 10);
        assert_eq!(config.max_lines, 200);
        assert!(!config.ignore_tests);
        assert!(config.cross_file_only);
        assert_eq!(config.language, Some("python".to_string()));
    }

    #[test]
    fn test_is_test_unit() {
        let mut unit = EmbeddingUnit::new("src/main.py", "test_foo", UnitKind::Function, "", 1, "python");
        assert!(is_test_unit(&unit));

        unit.name = "process_data".to_string();
        unit.file = "tests/test_main.py".to_string();
        assert!(is_test_unit(&unit));

        unit.file = "src/main.py".to_string();
        assert!(!is_test_unit(&unit));
    }

    #[test]
    fn test_is_generated_unit() {
        let mut unit = EmbeddingUnit::new("gen/model.pb.go", "Foo", UnitKind::Function, "", 1, "go");
        assert!(is_generated_unit(&unit));

        unit.file = "src/main.py".to_string();
        unit.code = "# Auto-generated code - do not edit\ndef foo(): pass".to_string();
        assert!(is_generated_unit(&unit));

        unit.code = "def foo(): pass".to_string();
        assert!(!is_generated_unit(&unit));
    }

    #[test]
    fn test_distance_to_similarity() {
        // Inner product: similarity = 1 - distance
        assert!((distance_to_similarity(0.1, Metric::InnerProduct) - 0.9).abs() < 0.001);
        assert!((distance_to_similarity(0.0, Metric::InnerProduct) - 1.0).abs() < 0.001);

        // Cosine: same as inner product
        assert!((distance_to_similarity(0.2, Metric::Cosine) - 0.8).abs() < 0.001);

        // L2: inverse relationship
        let sim = distance_to_similarity(0.0, Metric::L2Squared);
        assert!((sim - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_clone_pair_creation() {
        let unit_a = EmbeddingUnit::new("src/a.py", "func_a", UnitKind::Function, "def func_a(): pass", 1, "python");
        let unit_b = EmbeddingUnit::new("src/b.py", "func_b", UnitKind::Function, "def func_b(): pass", 10, "python");
        let config = SemanticCloneConfig::default();

        let pair = ClonePair::new(&unit_a, &unit_b, 0.95, &config);

        assert_eq!(pair.name_a, "func_a");
        assert_eq!(pair.name_b, "func_b");
        assert_eq!(pair.similarity, 0.95);
        assert_eq!(pair.clone_type, SemanticCloneType::HighSimilarity);
        assert!(pair.is_cross_file());
    }

    #[test]
    fn test_clone_cluster_methods() {
        let cluster = CloneCluster {
            id: 1,
            unit_ids: vec!["a".to_string(), "b".to_string(), "c".to_string()],
            centroid: None,
            avg_similarity: 0.85,
            min_similarity: 0.80,
            max_similarity: 0.90,
            clone_type: SemanticCloneType::MediumSimilarity,
            file_count: 2,
            files: vec!["file1.py".to_string(), "file2.py".to_string()],
            total_lines: 90,
        };

        assert_eq!(cluster.size(), 3);
        assert!(cluster.is_cross_file());
        assert_eq!(cluster.potential_savings(), 60); // 90/3 * 2 = 60
    }

    #[test]
    fn test_stats_clone_percentage() {
        let mut stats = SemanticCloneStats::default();
        stats.units_analyzed = 100;
        stats.pairs_found = 10;

        // 10 pairs * 2 = 20 units involved, 20/100 = 20%
        assert!((stats.clone_percentage() - 20.0).abs() < 0.1);

        stats.units_analyzed = 0;
        assert_eq!(stats.clone_percentage(), 0.0);
    }

    // =========================================================================
    // New tests for high-signal filtering
    // =========================================================================

    #[test]
    fn test_is_boilerplate_name() {
        // Rust trait implementations
        assert!(is_boilerplate_name("fmt"));
        assert!(is_boilerplate_name("clone"));
        assert!(is_boilerplate_name("default"));
        assert!(is_boilerplate_name("from"));
        assert!(is_boilerplate_name("into"));
        assert!(is_boilerplate_name("eq"));
        assert!(is_boilerplate_name("hash"));

        // Common trivial methods
        assert!(is_boilerplate_name("new"));
        assert!(is_boilerplate_name("get"));
        assert!(is_boilerplate_name("set"));
        assert!(is_boilerplate_name("is_empty"));
        assert!(is_boilerplate_name("len"));

        // Python dunder methods
        assert!(is_boilerplate_name("__init__"));
        assert!(is_boilerplate_name("__str__"));
        assert!(is_boilerplate_name("__repr__"));

        // Non-boilerplate names
        assert!(!is_boilerplate_name("process_data"));
        assert!(!is_boilerplate_name("calculate_total"));
        assert!(!is_boilerplate_name("parse_configuration"));
        assert!(!is_boilerplate_name("validate_input"));
    }

    #[test]
    fn test_count_statements() {
        // Single-line function with one statement
        let simple = "fn get_value(&self) -> i32 {\n    self.value\n}";
        assert_eq!(count_statements(simple), 1);

        // Function with multiple statements
        let multi = r#"fn process_data(&self) {
    let x = self.get_value();
    let y = x * 2;
    self.set_value(y);
    println!("Done");
}"#;
        assert_eq!(count_statements(multi), 4);

        // Function with comments and empty lines
        let with_comments = r#"fn example() {
    // This is a comment
    let x = 1;

    /* Another comment */
    let y = 2;
}"#;
        assert_eq!(count_statements(with_comments), 2);

        // Empty function
        let empty = "fn empty() {}";
        assert_eq!(count_statements(empty), 0);
    }

    #[test]
    fn test_is_simple_enum_like() {
        // Simple Rust enum
        let mut unit = EmbeddingUnit::new(
            "src/types.rs",
            "Status",
            UnitKind::Class,
            "#[derive(Debug, Clone)]\nenum Status {\n    Pending,\n    Active,\n    Done,\n}",
            1,
            "rust",
        );
        unit.end_line = 6;
        assert!(is_simple_enum_like(&unit));

        // Enum with methods is not simple
        let mut unit_with_methods = EmbeddingUnit::new(
            "src/types.rs",
            "Status",
            UnitKind::Class,
            "enum Status {\n    Pending,\n    Active,\n}\nimpl Status {\n    fn is_active(&self) -> bool { true }\n}",
            1,
            "rust",
        );
        unit_with_methods.end_line = 7;
        // This contains "fn " so it shouldn't be considered simple
        assert!(!is_simple_enum_like(&unit_with_methods));

        // Function units are not enums
        let func_unit = EmbeddingUnit::new(
            "src/lib.rs",
            "process",
            UnitKind::Function,
            "fn process() {}",
            1,
            "rust",
        );
        assert!(!is_simple_enum_like(&func_unit));
    }

    #[test]
    fn test_config_high_signal_mode() {
        let config = SemanticCloneConfig::default().high_signal_mode();

        assert!(config.ignore_boilerplate);
        assert_eq!(config.min_statements, 3);
        assert_eq!(config.max_size_ratio, 3.0);
        assert!(config.require_different_names);
        assert_eq!(config.min_name_length, MIN_INTERESTING_NAME_LENGTH);
        assert!(config.ignore_simple_enums);
        assert_eq!(config.min_lines, 8);
    }

    #[test]
    fn test_config_permissive_mode() {
        let config = SemanticCloneConfig::default().permissive_mode();

        assert!(!config.ignore_boilerplate);
        assert_eq!(config.min_statements, 1);
        assert_eq!(config.max_size_ratio, 10.0);
        assert!(!config.require_different_names);
        assert_eq!(config.min_name_length, 1);
        assert!(!config.ignore_simple_enums);
        assert_eq!(config.min_lines, 3);
    }

    #[test]
    fn test_config_builder_new_fields() {
        let config = SemanticCloneConfig::default()
            .with_ignore_boilerplate(false)
            .with_min_statements(5)
            .with_max_size_ratio(2.5)
            .with_require_different_names(false)
            .with_min_name_length(6)
            .with_ignore_simple_enums(false);

        assert!(!config.ignore_boilerplate);
        assert_eq!(config.min_statements, 5);
        assert!((config.max_size_ratio - 2.5).abs() < 0.001);
        assert!(!config.require_different_names);
        assert_eq!(config.min_name_length, 6);
        assert!(!config.ignore_simple_enums);
    }

    #[test]
    fn test_default_config_has_high_signal_defaults() {
        let config = SemanticCloneConfig::default();

        // By default, high-signal filtering should be enabled
        assert!(config.ignore_boilerplate);
        assert_eq!(config.min_statements, 3);
        assert_eq!(config.max_size_ratio, 3.0);
        assert!(config.require_different_names);
        assert_eq!(config.min_name_length, MIN_INTERESTING_NAME_LENGTH);
        assert!(config.ignore_simple_enums);
    }
}
