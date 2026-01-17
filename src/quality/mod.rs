//! Code quality analysis module.
//!
//! Provides tools for analyzing and improving code quality:
//!
//! - **Clone Detection** ([`clones`]): Detect code duplication (Type-1, Type-2, Type-3)
//!   - **Type-1 (textual)**: Exact copies ignoring whitespace/comments
//!   - **Type-2 (structural)**: Same structure with renamed identifiers
//!   - **Type-3 (near-miss)**: Similar structure with modifications
//!
//! - **Code Smells** ([`smells`]): Detection of design anti-patterns
//!   - **Long Method**: Methods that are too long and complex
//!   - **God Class**: Classes that do too much (violate SRP)
//!
//! - **Circular Dependencies** ([`circular`]): Detect dependency cycles
//!   - **Module level**: Import cycles (A imports B imports A)
//!   - **Package level**: Package-to-package cycles
//!   - **Class level**: Class usage cycles
//!   - **Function level**: Call graph cycles
//!
//! # Type-1 Clone Detection (Textual)
//!
//! ```ignore
//! use go_brrr::quality::clones::{detect_clones, CloneConfig};
//!
//! // Detect code clones in a project
//! let result = detect_clones("./src", Some(6), None)?;
//! println!("Found {} clone groups ({:.1}% duplication)",
//!     result.clone_groups.len(),
//!     result.stats.duplication_percentage);
//! ```
//!
//! # Type-2/Type-3 Clone Detection (Structural)
//!
//! ```ignore
//! use go_brrr::quality::clones::{detect_structural_clones, StructuralCloneConfig};
//!
//! // Detect structural clones with 80% similarity threshold
//! let result = detect_structural_clones("./src", Some(0.8), None)?;
//! println!("Found {} Type-2 and {} Type-3 clone groups",
//!     result.stats.type2_groups,
//!     result.stats.type3_groups);
//! ```
//!
//! # Long Method Detection
//!
//! ```ignore
//! use go_brrr::quality::smells::{detect_long_methods, LongMethodConfig};
//!
//! // Detect long methods with default thresholds
//! let result = detect_long_methods("./src", Some("python"), None)?;
//! for finding in &result.findings {
//!     println!("{}: {} lines, complexity {}",
//!         finding.function_name, finding.length.lines, finding.complexity.cyclomatic);
//!     for suggestion in &finding.suggestions {
//!         println!("  -> {}", suggestion.description);
//!     }
//! }
//! ```
//!
//! # God Class Detection
//!
//! ```ignore
//! use go_brrr::quality::smells::{detect_god_classes, GodClassConfig};
//!
//! // Detect God classes with default thresholds
//! let result = detect_god_classes("./src", None, None)?;
//! for finding in &result.findings {
//!     println!("{}: score={:.1}, severity={}",
//!         finding.class_name, finding.score, finding.severity);
//! }
//! ```

pub mod circular;
pub mod clones;
pub mod smells;

// Re-export Type-1 (textual) clone detection for convenience
pub use clones::{
    detect_clones, format_clone_summary, Clone, CloneAnalysis, CloneConfig, CloneError,
    CloneInstance, CloneStats, CloneType, TextualCloneDetector,
};

// Re-export Type-2/Type-3 (structural) clone detection
pub use clones::{
    detect_structural_clones, format_structural_clone_summary, Difference, StructuralClone,
    StructuralCloneAnalysis, StructuralCloneConfig, StructuralCloneDetector,
    StructuralCloneError, StructuralCloneInstance, StructuralCloneStats,
};

// Re-export Long Method detection
pub use smells::{
    detect_long_methods, detect_long_methods_in_file, format_long_method_summary,
    BlockType, ComplexityMetrics, ExtractionCandidate, LengthMetrics,
    LongMethodAnalysis, LongMethodConfig, LongMethodError, LongMethodFinding,
    LongMethodSeverity, LongMethodStats, MethodCategory, RefactoringType,
    RefactoringSuggestion, Violation,
};

// Re-export God class detection
pub use smells::{
    detect_god_classes, format_god_class_summary, GodClassAnalysis, GodClassConfig,
    GodClassError, GodClassFinding, GodClassIndicators, GodClassSeverity,
    GodClassStats, SuggestedClass,
};

// Re-export Circular dependency detection
pub use circular::{
    detect_circular_dependencies, format_circular_report, BreakingSuggestion,
    CircularConfig, CircularDependencyReport, CircularError, CircularStats,
    DependencyCycle, DependencyLevel, Severity as CircularSeverity,
};
