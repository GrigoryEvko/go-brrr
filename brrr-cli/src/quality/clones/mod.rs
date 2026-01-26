//! Code clone detection module.
//!
//! Provides detection of code duplicates (clones) using various techniques:
//!
//! - **Type-1 (textual)**: Exact copies ignoring whitespace/comments
//! - **Type-2 (structural)**: Same structure with renamed identifiers/literals
//! - **Type-3 (near-miss)**: Similar structure with small modifications
//! - **Type-4 (semantic)**: Semantically similar code using embeddings
//!
//! Additionally provides **refactoring suggestions** for detected clone clusters,
//! recommending actions such as:
//! - Delete duplicate (redirect callers)
//! - Extract common function with parameters
//! - Extract trait/interface
//! - Make generic over type
//! - Apply Strategy pattern
//!
//! # Type-1 Clone Detection (Textual)
//!
//! ```ignore
//! use brrr::quality::clones::{detect_clones, CloneConfig, TextualCloneDetector};
//!
//! // Quick Type-1 detection with defaults
//! let result = detect_clones("./src", Some(6), None)?;
//!
//! // Custom configuration
//! let config = CloneConfig::default()
//!     .with_min_lines(10)
//!     .with_language("rust");
//! let detector = TextualCloneDetector::new(config);
//! let result = detector.detect("./src")?;
//! ```
//!
//! # Structural Clone Detection (Type-2/Type-3)
//!
//! ```ignore
//! use brrr::quality::clones::{
//!     detect_structural_clones, StructuralCloneConfig, StructuralCloneDetector
//! };
//!
//! // Detect structural clones with 80% similarity threshold
//! let result = detect_structural_clones("./src", Some(0.8), None)?;
//!
//! // Custom configuration
//! let config = StructuralCloneConfig::default()
//!     .with_similarity_threshold(0.85)
//!     .with_min_nodes(15);
//! let detector = StructuralCloneDetector::new(config);
//! let result = detector.detect("./src")?;
//!
//! // Get only Type-2 (exact structural) clones
//! for clone in result.type2_clones() {
//!     println!("Type-2 clone: {} instances", clone.instances.len());
//! }
//! ```
//!
//! # Semantic Clone Detection (Type-4)
//!
//! ```ignore
//! use brrr::quality::clones::{
//!     detect_semantic_clones, SemanticCloneConfig, SemanticCloneDetector
//! };
//!
//! // Quick semantic clone detection
//! let result = detect_semantic_clones("./src", None)?;
//! for pair in &result.clone_pairs {
//!     println!("{} <-> {} ({:.1}% similar)",
//!         pair.name_a, pair.name_b, pair.similarity * 100.0);
//! }
//!
//! // Custom configuration with thresholds
//! let config = SemanticCloneConfig::default()
//!     .with_high_similarity_threshold(0.85)
//!     .with_min_lines(10)
//!     .with_cross_file_only(true);
//! let detector = SemanticCloneDetector::new(config);
//! let result = detector.detect("./src")?;
//!
//! // Get identical clones (highest similarity)
//! for pair in result.identical_clones() {
//!     println!("Identical: {} <-> {}", pair.name_a, pair.name_b);
//! }
//! ```

pub mod cluster;
pub mod semantic;
pub mod similarity;
pub mod structural;
pub mod suggestions;
pub mod textual;

// Re-export textual clone detection (Type-1)
pub use textual::{
    // Main API
    detect_clones,
    format_clone_summary,
    // Types
    Clone,
    CloneAnalysis,
    CloneConfig,
    CloneError,
    CloneInstance,
    CloneStats,
    CloneType,
    TextualCloneDetector,
};

// Re-export structural clone detection (Type-2/Type-3)
pub use structural::{
    // Main API
    detect_structural_clones,
    format_structural_clone_summary,
    // Types
    Difference,
    StructuralClone,
    StructuralCloneAnalysis,
    StructuralCloneConfig,
    StructuralCloneDetector,
    StructuralCloneError,
    StructuralCloneInstance,
    StructuralCloneStats,
};

// Re-export semantic clone detection (Type-4)
pub use semantic::{
    // Main API
    detect_semantic_clones,
    format_semantic_clone_summary,
    // Types
    CloneCluster,
    ClonePair,
    SemanticCloneAnalysis,
    SemanticCloneConfig,
    SemanticCloneDetector,
    SemanticCloneStats,
    SemanticCloneType,
};

// Re-export similarity computation (SIMD-accelerated)
pub use similarity::{
    // Metrics
    cosine_similarity,
    euclidean_distance,
    euclidean_distance_squared,
    // Pairwise computation
    compute_pairwise_similarities,
    compute_pairwise_tuples,
    find_similar,
    find_top_k,
    // Types
    SimilarityPair,
};

// Re-export clustering utilities (union-find based)
pub use cluster::{
    // Main clustering function
    cluster_clones,
    // Approximate nearest neighbor
    cluster_clones_approximate,
    find_all_similar_approximate,
    find_similar_approximate,
    // Types
    CloneCluster as RawCloneCluster,
    ClusterMemberInfo,
};

// Re-export refactoring suggestions
pub use suggestions::{
    // Main API
    generate_suggestions,
    generate_suggestions_for_pairs,
    // Types
    EffortLevel,
    RefactoringKind,
    RefactoringSuggestion,
};
