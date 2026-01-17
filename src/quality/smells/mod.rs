//! Code smell detection module.
//!
//! Provides analysis for common design anti-patterns:
//!
//! - **Long Method**: Methods that are too long and do too much
//!   - Lines of code > threshold (default: 30)
//!   - Too many statements, variables, parameters
//!   - High cyclomatic complexity
//!   - Deep nesting
//!   - Context-aware (adjusts for tests, constructors, factories)
//!   - Provides extraction candidates and refactoring suggestions
//!
//! - **God Class**: Classes that do too many things, violating Single Responsibility Principle
//!   - Too many methods (> 20)
//!   - Too many attributes (> 15)
//!   - Too many lines (> 500)
//!   - Low cohesion (LCOM3 > 2)
//!   - High coupling (depends on many classes)
//!
//! # Long Method Detection
//!
//! ```ignore
//! use go_brrr::quality::smells::{detect_long_methods, LongMethodConfig};
//!
//! let result = detect_long_methods("./src", Some("python"), None)?;
//! for finding in &result.findings {
//!     println!("{} at {}:{} - {} violations",
//!         finding.function_name, finding.file.display(), finding.line,
//!         finding.violations.len());
//!     for suggestion in &finding.suggestions {
//!         println!("  Suggestion: {}", suggestion.description);
//!         if let Some((start, end)) = suggestion.line_range {
//!             println!("    Extract lines {}-{}", start, end);
//!         }
//!     }
//! }
//! ```
//!
//! # God Class Detection
//!
//! ```ignore
//! use go_brrr::quality::smells::god_class::{detect_god_classes, GodClassConfig};
//!
//! let result = detect_god_classes("./src", None, None)?;
//! for finding in &result.findings {
//!     println!("{}: score={:.1}", finding.class_name, finding.score);
//!     for suggestion in &finding.suggested_splits {
//!         println!("  -> {}: {:?}", suggestion.name_hint, suggestion.methods);
//!     }
//! }
//! ```
//!
//! # Future Modules
//!
//! - **Feature Envy**: Methods that use other classes more than their own
//! - **Data Clumps**: Groups of data that appear together repeatedly
//! - **Shotgun Surgery**: Changes that require many small modifications

pub mod god_class;
pub mod long_method;

// Re-export Long Method detection types
pub use long_method::{
    detect_long_methods, detect_long_methods_in_file, format_long_method_summary,
    BlockType, ComplexityMetrics, ExtractionCandidate, LengthMetrics,
    LongMethodAnalysis, LongMethodConfig, LongMethodError, LongMethodFinding,
    LongMethodSeverity, LongMethodStats, MethodCategory, RefactoringType,
    RefactoringSuggestion, Violation,
};

// Re-export God class detection types
pub use god_class::{
    detect_god_classes, format_god_class_summary, GodClassAnalysis, GodClassConfig,
    GodClassError, GodClassFinding, GodClassIndicators, GodClassSeverity,
    GodClassStats, SuggestedClass,
};
