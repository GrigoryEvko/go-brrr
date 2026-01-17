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
//! use go_brrr::metrics::{analyze_complexity, RiskLevel};
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
//! use go_brrr::metrics::{analyze_cognitive_complexity, CognitiveRiskLevel};
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
//! use go_brrr::metrics::{analyze_halstead, QualityLevel};
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
//! use go_brrr::metrics::{analyze_loc, LOCMetrics};
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
//! use go_brrr::metrics::{analyze_nesting, NestingDepthLevel};
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
//! use go_brrr::metrics::{analyze_function_size, SizeIssue};
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
//! use go_brrr::metrics::{analyze_coupling, CouplingLevel};
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
//! use go_brrr::metrics::{analyze_cohesion, CohesionLevel};
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
//! use go_brrr::metrics::{analyze_all_metrics, MetricsConfig, QualityGate};
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

pub mod cohesion;
pub mod complexity;
pub mod coupling;
pub mod function_size;
pub mod loc;
pub mod nesting;
pub mod unified;

// Re-export primary types for convenience
pub use complexity::{
    // Cyclomatic complexity
    analyze_complexity, analyze_file_complexity, CyclomaticComplexity,
    ComplexityAnalysis, RiskLevel, ComplexityStats, FunctionComplexity,
    // Cognitive complexity
    analyze_cognitive_complexity, analyze_file_cognitive_complexity,
    CognitiveComplexity, CognitiveAnalysis, CognitiveRiskLevel,
    CognitiveStats, FunctionCognitiveComplexity, ComplexityContribution,
    ConstructType, CognitiveAnalysisError,
    // Halstead complexity
    analyze_halstead, analyze_file_halstead, HalsteadMetrics, HalsteadAnalysis,
    HalsteadStats, FunctionHalstead, HalsteadQuality, QualityLevel, HalsteadError,
    // Maintainability Index
    analyze_maintainability, analyze_file_maintainability, MaintainabilityIndex,
    MaintainabilityAnalysis, MaintainabilityStats, FunctionMaintainability,
    MaintainabilityRiskLevel, MaintainabilityError, LinesOfCode,
};

// Re-export LOC types
pub use loc::{
    analyze_loc, analyze_file_loc, LOCMetrics, LOCAnalysis, LOCDistribution,
    FileLOC, FunctionSize, LanguageLOC, FileRanking, LOCError,
};

// Re-export nesting types
pub use nesting::{
    analyze_nesting, analyze_file_nesting, NestingMetrics, NestingAnalysis,
    NestingStats, FunctionNesting, NestingDepthLevel, NestingConstruct,
    DeepNesting, NestingAnalysisError,
};

// Re-export function size types
pub use function_size::{
    analyze_function_size, analyze_file_function_size, FunctionSizeMetrics,
    FunctionSizeAnalysis, FunctionSizeStats, FunctionSizeError, SizeIssue,
    SizeSeverity, SizeThresholds, FunctionCategory, SizeSortBy,
    sort_functions,
};

// Re-export coupling types
pub use coupling::{
    analyze_coupling, analyze_file_coupling, CouplingMetrics, CouplingAnalysis,
    CouplingStats, CouplingLevel, CouplingRisk, CouplingError,
    DependencyType, DependencyEdge,
};

// Re-export cohesion types
pub use cohesion::{
    analyze_cohesion, analyze_file_cohesion, CohesionMetrics, CohesionAnalysis,
    CohesionStats, CohesionLevel, CohesionError,
};

// Re-export unified metrics types
pub use unified::{
    // Main analysis function
    analyze_all_metrics, analyze_all_metrics_with_progress,
    // Report types
    MetricsReport, ProjectMetrics, FileMetrics, FunctionMetrics, ClassMetrics,
    // Issue types
    MetricIssue, IssueCategory, IssueSeverity, IssueStats,
    // Configuration (MetricThresholds includes load_from_project and from_toml)
    MetricsConfig, MetricThresholds,
    // Quality gate
    QualityGate, QualityGateResult,
    // Sorting
    FunctionSortBy, sort_functions as sort_unified_functions,
    // CSV formatting
    format_functions_csv, format_issues_csv, format_classes_csv, format_files_csv,
    // Progress reporting
    ProgressCallback,
};
