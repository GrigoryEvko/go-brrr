//! Code quality analysis module.
//!
//! Provides tools for analyzing and improving code quality:
//!
//! - **Clone Detection** ([`clones`]): Detect code duplication (Type-1, Type-2, Type-3, Type-4)
//!   - **Type-1 (textual)**: Exact copies ignoring whitespace/comments
//!   - **Type-2 (structural)**: Same structure with renamed identifiers
//!   - **Type-3 (near-miss)**: Similar structure with modifications
//!   - **Type-4 (semantic)**: Semantically similar code using embeddings
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
//! - **Test Quality** ([`test_quality`]): Analyze test effectiveness
//!   - **Assertion Density**: Assertions per test function
//!   - **Test Isolation**: Detection of shared state and external dependencies
//!   - **Boundary Testing**: Detection of edge case coverage
//!   - **Mutation Score Estimation**: Heuristic mutation testing analysis
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
//! # Type-4 Clone Detection (Semantic)
//!
//! ```ignore
//! use go_brrr::quality::clones::{detect_semantic_clones, SemanticCloneConfig};
//!
//! // Detect semantic clones using embedding similarity
//! let result = detect_semantic_clones("./src", None)?;
//! println!("Found {} semantic clone pairs", result.clone_pairs.len());
//!
//! // Get only high-similarity clones
//! for pair in result.high_similarity_clones() {
//!     println!("{} <-> {} ({:.1}% similar)",
//!         pair.name_a, pair.name_b, pair.similarity * 100.0);
//! }
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
pub mod doc_coverage;
pub mod smells;
pub mod test_quality;

// Re-export Type-1 (textual) clone detection for convenience
pub use clones::{
    detect_clones, format_clone_summary, Clone, CloneAnalysis, CloneConfig, CloneError,
    CloneInstance, CloneStats, CloneType, TextualCloneDetector,
};

// Re-export Type-2/Type-3 (structural) clone detection
pub use clones::{
    detect_structural_clones, format_structural_clone_summary, Difference, StructuralClone,
    StructuralCloneAnalysis, StructuralCloneConfig, StructuralCloneDetector, StructuralCloneError,
    StructuralCloneInstance, StructuralCloneStats,
};

// Re-export Type-4 (semantic) clone detection
pub use clones::{
    detect_semantic_clones, format_semantic_clone_summary, CloneCluster, ClonePair,
    SemanticCloneAnalysis, SemanticCloneConfig, SemanticCloneDetector, SemanticCloneStats,
    SemanticCloneType,
};

// Re-export Long Method detection
pub use smells::{
    detect_long_methods, detect_long_methods_in_file, format_long_method_summary, BlockType,
    ComplexityMetrics, ExtractionCandidate, LengthMetrics, LongMethodAnalysis, LongMethodConfig,
    LongMethodError, LongMethodFinding, LongMethodSeverity, LongMethodStats, MethodCategory,
    RefactoringSuggestion, RefactoringType, Violation,
};

// Re-export God class detection
pub use smells::{
    detect_god_classes, format_god_class_summary, GodClassAnalysis, GodClassConfig, GodClassError,
    GodClassFinding, GodClassIndicators, GodClassSeverity, GodClassStats, SuggestedClass,
};

// Re-export Circular dependency detection
pub use circular::{
    detect_circular_dependencies, format_circular_report, BreakingSuggestion, CircularConfig,
    CircularDependencyReport, CircularError, CircularStats, DependencyCycle, DependencyLevel,
    Severity as CircularSeverity,
};

// Re-export Test Quality analysis
pub use test_quality::{
    analyze_test_quality, format_test_quality_report, AssertionType, DetectedAssertion,
    ImprovementCategory, MockUsageMetrics, TestFileQuality, TestFunctionQuality, TestImprovement,
    TestIssue, TestQualityAnalysis, TestQualityConfig, TestQualityError, TestQualitySummary,
    WeakTest,
};

// Re-export Documentation Coverage analysis
pub use doc_coverage::{
    analyze_doc_coverage, format_doc_coverage_report, DocCoverageAnalysis, DocCoverageConfig,
    DocCoverageError, DocCoverageMetrics, DocQuality, DocTodo, DocType, FileDocCoverage, ItemType,
    Location, MissingDoc, TypeCoverage, Visibility,
};
