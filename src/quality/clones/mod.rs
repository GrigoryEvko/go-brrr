//! Code clone detection module.
//!
//! Provides detection of code duplicates (clones) using various techniques:
//!
//! - **Type-1 (textual)**: Exact copies ignoring whitespace/comments
//! - **Type-2 (structural)**: Same structure with renamed identifiers/literals
//! - **Type-3 (near-miss)**: Similar structure with small modifications
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::quality::clones::{detect_clones, CloneConfig, TextualCloneDetector};
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
//! use go_brrr::quality::clones::{
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

pub mod structural;
pub mod textual;

// Re-export textual clone detection (Type-1)
pub use textual::{
    // Main API
    detect_clones,
    format_clone_summary,
    TextualCloneDetector,
    // Types
    Clone,
    CloneAnalysis,
    CloneConfig,
    CloneError,
    CloneInstance,
    CloneStats,
    CloneType,
};

// Re-export structural clone detection (Type-2/Type-3)
pub use structural::{
    // Main API
    detect_structural_clones,
    format_structural_clone_summary,
    StructuralCloneDetector,
    // Types
    Difference,
    StructuralClone,
    StructuralCloneAnalysis,
    StructuralCloneConfig,
    StructuralCloneError,
    StructuralCloneInstance,
    StructuralCloneStats,
};
