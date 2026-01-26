//! Code metrics calculation for software quality analysis.
//!
//! This module provides various metrics for analyzing code quality:
//!
//! - **Complexity Metrics**: Cyclomatic, cognitive, and Halstead complexity
//! - **Size Metrics**: Lines of code (LOC), function count
//! - **Coupling Metrics**: Afferent/efferent coupling, instability, main sequence analysis
//! - **Cohesion Metrics**: LCOM variants for class cohesion analysis
//!
//! # Example
//!
//! ```ignore
//! use brrr::metrics::{analyze_complexity, RiskLevel};
//!
//! let results = analyze_complexity("./src", Some("python"), None)?;
//! for result in results.functions {
//!     if result.risk_level == RiskLevel::High {
//!         println!("High complexity: {} ({})", result.function_name, result.complexity);
//!     }
//! }
//! ```
//!
//! # Cognitive Complexity Example
//!
//! ```ignore
//! use brrr::metrics::{analyze_cognitive_complexity, CognitiveRiskLevel};
//!
//! let results = analyze_cognitive_complexity("./src", Some("python"), Some(10))?;
//! for func in &results.functions {
//!     if func.risk_level == CognitiveRiskLevel::High {
//!         println!("Hard to understand: {} (score: {})", func.function_name, func.complexity);
//!         for contrib in &func.breakdown {
//!             println!("  Line {}: {} (+{} base, +{} nesting)",
//!                 contrib.line, contrib.construct, contrib.base_increment, contrib.nesting_increment);
//!         }
//!     }
//! }
//! ```
//!
//! # Halstead Complexity Example
//!
//! ```ignore
//! use brrr::metrics::{analyze_halstead, QualityLevel};
//!
//! let results = analyze_halstead("./src", Some("python"), false)?;
//! for func in &results.functions {
//!     println!("{}: volume={:.1}, difficulty={:.1}, bugs={:.2}",
//!         func.function_name, func.metrics.volume, func.metrics.difficulty, func.metrics.bugs);
//! }
//! println!("Total estimated bugs: {:.2}", results.stats.total_bugs);
//! ```
//!
//! # Lines of Code Example
//!
//! ```ignore
//! use brrr::metrics::{analyze_loc, LOCMetrics};
//!
//! let results = analyze_loc("./src", Some("python"), None)?;
//! println!("Total SLOC: {}", results.stats.total_sloc);
//! println!("Code-to-comment ratio: {:.2}", results.stats.code_to_comment_ratio);
//! for lang in &results.by_language {
//!     println!("{}: {} SLOC across {} files", lang.language, lang.metrics.source, lang.file_count);
//! }
//! ```
//!
//! # Nesting Depth Example
//!
//! ```ignore
//! use brrr::metrics::{analyze_nesting, NestingDepthLevel};
//!
//! let results = analyze_nesting("./src", Some("python"), Some(5))?;
//! for func in &results.functions {
//!     if func.risk_level == NestingDepthLevel::Severe {
//!         println!("Deep nesting in {}: depth {} at line {}",
//!             func.function_name, func.max_depth, func.deepest_line);
//!         for suggestion in &func.suggestions {
//!             println!("  - {}", suggestion);
//!         }
//!     }
//! }
//! ```
//!
//! # Function Size Metrics Example
//!
//! ```ignore
//! use brrr::metrics::{analyze_function_size, SizeIssue};
//!
//! let results = analyze_function_size("./src", Some("python"), None)?;
//! for func in &results.violations {
//!     println!("{} at {}:{} - {} issues:",
//!         func.name, func.file.display(), func.line, func.issues.len());
//!     for issue in &func.issues {
//!         println!("  - {}", issue);
//!     }
//! }
//! ```
//!
//! # Coupling Metrics Example
//!
//! ```ignore
//! use brrr::metrics::{analyze_coupling, CouplingLevel};
//!
//! let results = analyze_coupling("./src", Some("python"), CouplingLevel::File)?;
//! for module in &results.modules {
//!     println!("{}: Ca={}, Ce={}, I={:.2}, D={:.2}",
//!         module.module, module.afferent, module.efferent,
//!         module.instability, module.distance);
//!     if module.is_in_zone_of_pain() {
//!         println!("  WARNING: In Zone of Pain (stable, concrete - rigid)");
//!     }
//!     if module.distance > 0.5 {
//!         println!("  WARNING: Far from main sequence!");
//!     }
//! }
//! ```
//!
//! # Cohesion Metrics Example (LCOM)
//!
//! ```ignore
//! use brrr::metrics::{analyze_cohesion, CohesionLevel};
//!
//! let results = analyze_cohesion("./src", Some("python"), Some(1))?;
//! for class in &results.classes {
//!     println!("{}: LCOM3={}, LCOM4={}, methods={}, attributes={}",
//!         class.class_name, class.lcom3, class.lcom4, class.methods, class.attributes);
//!     if class.is_low_cohesion {
//!         println!("  WARNING: Low cohesion detected!");
//!         if let Some(suggestion) = &class.suggestion {
//!             println!("  Suggestion: {}", suggestion);
//!         }
//!         for (i, component) in class.components.iter().enumerate() {
//!             println!("  Component {}: {:?}", i + 1, component);
//!         }
//!     }
//! }
//! println!("Stats: {}/{} classes have low cohesion",
//!     results.stats.low_cohesion_classes, results.stats.total_classes);
//! ```
//!
//! # Unified Metrics Report
//!
//! For a comprehensive analysis combining all metrics:
//!
//! ```ignore
//! use brrr::metrics::{analyze_all_metrics, MetricsConfig, QualityGate};
//!
//! let config = MetricsConfig::default();
//! let report = analyze_all_metrics("./src", Some("python"), &config)?;
//!
//! // Check quality gates for CI/CD
//! let gate = QualityGate::default();
//! let result = gate.check(&report);
//! if result.failed {
//!     eprintln!("Quality gate failed: {} critical issues", result.critical_count);
//!     std::process::exit(1);
//! }
//!
//! // Access unified function metrics
//! for func in &report.function_metrics {
//!     println!("{}: CC={}, cognitive={}, MI={:.1}",
//!         func.name, func.cyclomatic, func.cognitive, func.maintainability);
//! }
//! ```

// =============================================================================
// SUBMODULES
// =============================================================================

pub mod cohesion;
pub mod common;
pub mod complexity;
pub mod coupling;
pub mod function_size;
pub mod loc;
pub mod nesting;
pub mod node_types;
pub mod unified;

// =============================================================================
// COMPLEXITY MODULE RE-EXPORTS
// =============================================================================

// Cyclomatic complexity
pub use complexity::{
    analyze_complexity, analyze_file_complexity, ComplexityAnalysis, ComplexityStats,
    CyclomaticComplexity, FunctionComplexity, RiskLevel,
};

// Cognitive complexity
pub use complexity::{
    analyze_cognitive_complexity, analyze_file_cognitive_complexity, CognitiveAnalysis,
    CognitiveAnalysisError, CognitiveComplexity, CognitiveRiskLevel, CognitiveStats,
    ComplexityContribution, ConstructType, FunctionCognitiveComplexity,
};

// Halstead complexity
pub use complexity::{
    analyze_file_halstead, analyze_halstead, FunctionHalstead, HalsteadAnalysis, HalsteadError,
    HalsteadMetrics, HalsteadQuality, HalsteadStats, QualityLevel,
};

// Maintainability Index
pub use complexity::{
    analyze_file_maintainability, analyze_maintainability, FunctionMaintainability, LinesOfCode,
    MaintainabilityAnalysis, MaintainabilityError, MaintainabilityIndex, MaintainabilityRiskLevel,
    MaintainabilityStats,
};

// Complexity common utilities
pub use complexity::common::{
    build_histogram, find_function_body, find_function_node, is_function_node,
    is_function_signature_part, AnalysisError, BaseComplexityStats, BaseF64Stats, HistogramBucket,
};

// =============================================================================
// LOC MODULE RE-EXPORTS
// =============================================================================

pub use loc::{
    analyze_file_loc, analyze_loc, FileLOC, FileRanking, FunctionSize, LanguageLOC, LOCAnalysis,
    LOCDistribution, LOCError, LOCMetrics,
};

// =============================================================================
// NESTING MODULE RE-EXPORTS
// =============================================================================

pub use nesting::{
    analyze_file_nesting, analyze_nesting, DeepNesting, FunctionNesting, NestingAnalysis,
    NestingAnalysisError, NestingConstruct, NestingDepthLevel, NestingMetrics, NestingStats,
};

// =============================================================================
// FUNCTION SIZE MODULE RE-EXPORTS
// =============================================================================

pub use function_size::{
    analyze_file_function_size, analyze_function_size, sort_functions as sort_size_functions,
    FunctionCategory, FunctionSizeAnalysis, FunctionSizeError, FunctionSizeMetrics,
    FunctionSizeStats, SizeIssue, SizeSeverity, SizeSortBy, SizeThresholds,
};

// =============================================================================
// COUPLING MODULE RE-EXPORTS
// =============================================================================

pub use coupling::{
    analyze_coupling, analyze_file_coupling, CouplingAnalysis, CouplingError, CouplingLevel,
    CouplingMetrics, CouplingRisk, CouplingStats, DependencyEdge, DependencyType,
};

// =============================================================================
// COHESION MODULE RE-EXPORTS
// =============================================================================

pub use cohesion::{
    analyze_cohesion, analyze_file_cohesion, CohesionAnalysis, CohesionError, CohesionLevel,
    CohesionMetrics, CohesionStats,
};

// =============================================================================
// COMMON MODULE RE-EXPORTS
// =============================================================================

pub use common::MetricStats;

// =============================================================================
// UNIFIED MODULE RE-EXPORTS
// =============================================================================

pub use unified::{
    // Main analysis functions
    analyze_all_metrics,
    analyze_all_metrics_with_progress,
    // CSV formatting utilities
    format_classes_csv,
    format_files_csv,
    format_functions_csv,
    format_issues_csv,
    // Sorting
    sort_functions as sort_unified_functions,
    FunctionSortBy,
    // Configuration types
    IssueCategory,
    IssueSeverity,
    MetricIssue,
    MetricThresholds,
    MetricsConfig,
    // Quality gate
    QualityGate,
    QualityGateResult,
    // Report types
    ClassMetrics as UnifiedClassMetrics,
    FileMetrics as UnifiedFileMetrics,
    FunctionMetrics as UnifiedFunctionMetrics,
    IssueStats,
    MetricsReport,
    ProjectMetrics,
    ProgressCallback,
};
