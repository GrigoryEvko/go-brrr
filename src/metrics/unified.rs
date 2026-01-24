//! Unified metrics report combining all metric analyzers into a single view.
//!
//! This module provides a comprehensive code quality report that aggregates:
//! - Cyclomatic complexity
//! - Cognitive complexity
//! - Halstead metrics
//! - Maintainability Index
//! - Lines of code
//! - Nesting depth
//! - Function size
//! - Coupling metrics
//! - Cohesion metrics (LCOM)
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::metrics::unified::{analyze_all_metrics, MetricsConfig, QualityGate};
//!
//! let config = MetricsConfig::default();
//! let report = analyze_all_metrics("./src", Some("python"), &config)?;
//!
//! // Check quality gates
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

use std::borrow::Cow;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use serde::{Deserialize, Serialize};
use tracing::{info, warn};

use crate::error::{BrrrError, Result};

use super::cohesion::{analyze_cohesion, CohesionLevel};
use super::complexity::{
    analyze_cognitive_complexity, analyze_complexity, analyze_halstead, analyze_maintainability,
    CognitiveRiskLevel, HalsteadMetrics, MaintainabilityRiskLevel, RiskLevel,
};
use super::coupling::CouplingLevel;
use super::function_size::analyze_function_size;
use super::loc::{analyze_loc, LOCMetrics};
use super::nesting::{analyze_nesting, NestingDepthLevel};

// =============================================================================
// THRESHOLD CONFIGURATION
// =============================================================================

/// Configurable thresholds for metric analysis.
///
/// These thresholds define when metrics indicate warnings or critical issues.
/// Based on industry standards and research:
/// - McCabe (1976) for cyclomatic complexity
/// - SonarSource for cognitive complexity
/// - SEI for maintainability index
/// - Clean Code guidelines for function size
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricThresholds {
    // Cyclomatic complexity (McCabe)
    /// Cyclomatic complexity warning threshold (default: 10)
    pub cyclomatic_warning: u32,
    /// Cyclomatic complexity critical threshold (default: 20)
    pub cyclomatic_critical: u32,

    // Cognitive complexity (SonarSource)
    /// Cognitive complexity warning threshold (default: 15)
    pub cognitive_warning: u32,
    /// Cognitive complexity critical threshold (default: 30)
    pub cognitive_critical: u32,

    // Maintainability Index
    /// MI warning threshold - below this is concerning (default: 40)
    pub maintainability_warning: f64,
    /// MI critical threshold - below this is critical (default: 20)
    pub maintainability_critical: f64,

    // Lines of Code
    /// Function LOC warning threshold (default: 50)
    pub loc_warning: u32,
    /// Function LOC critical threshold (default: 100)
    pub loc_critical: u32,

    // Nesting depth
    /// Nesting depth warning threshold (default: 4)
    pub nesting_warning: u32,
    /// Nesting depth critical threshold (default: 6)
    pub nesting_critical: u32,

    // Parameters
    /// Function parameter count warning threshold (default: 5)
    pub params_warning: u32,
    /// Function parameter count critical threshold (default: 8)
    pub params_critical: u32,

    // Coupling
    /// Distance from main sequence warning threshold (default: 0.5)
    pub coupling_distance_warning: f64,
    /// Distance from main sequence critical threshold (default: 0.7)
    pub coupling_distance_critical: f64,

    // Cohesion
    /// LCOM3 warning threshold (default: 2)
    pub lcom_warning: u32,
    /// LCOM3 critical threshold (default: 4)
    pub lcom_critical: u32,

    // Halstead
    /// Volume warning threshold (default: 1000)
    pub halstead_volume_warning: f64,
    /// Volume critical threshold (default: 3000)
    pub halstead_volume_critical: f64,
    /// Estimated bugs warning threshold (default: 0.5)
    pub halstead_bugs_warning: f64,
    /// Estimated bugs critical threshold (default: 2.0)
    pub halstead_bugs_critical: f64,
}

impl Default for MetricThresholds {
    fn default() -> Self {
        Self {
            cyclomatic_warning: 10,
            cyclomatic_critical: 20,
            cognitive_warning: 15,
            cognitive_critical: 30,
            maintainability_warning: 40.0,
            maintainability_critical: 20.0,
            loc_warning: 50,
            loc_critical: 100,
            nesting_warning: 4,
            nesting_critical: 6,
            params_warning: 5,
            params_critical: 8,
            coupling_distance_warning: 0.5,
            coupling_distance_critical: 0.7,
            lcom_warning: 2,
            lcom_critical: 4,
            halstead_volume_warning: 1000.0,
            halstead_volume_critical: 3000.0,
            halstead_bugs_warning: 0.5,
            halstead_bugs_critical: 2.0,
        }
    }
}

impl MetricThresholds {
    /// Create strict thresholds for high-quality codebases.
    #[must_use]
    pub fn strict() -> Self {
        Self {
            cyclomatic_warning: 5,
            cyclomatic_critical: 10,
            cognitive_warning: 8,
            cognitive_critical: 15,
            maintainability_warning: 60.0,
            maintainability_critical: 40.0,
            loc_warning: 30,
            loc_critical: 50,
            nesting_warning: 3,
            nesting_critical: 4,
            params_warning: 3,
            params_critical: 5,
            coupling_distance_warning: 0.3,
            coupling_distance_critical: 0.5,
            lcom_warning: 1,
            lcom_critical: 2,
            halstead_volume_warning: 500.0,
            halstead_volume_critical: 1500.0,
            halstead_bugs_warning: 0.2,
            halstead_bugs_critical: 1.0,
        }
    }

    /// Create relaxed thresholds for legacy or transitional codebases.
    #[must_use]
    pub fn relaxed() -> Self {
        Self {
            cyclomatic_warning: 15,
            cyclomatic_critical: 30,
            cognitive_warning: 25,
            cognitive_critical: 50,
            maintainability_warning: 30.0,
            maintainability_critical: 15.0,
            loc_warning: 80,
            loc_critical: 150,
            nesting_warning: 5,
            nesting_critical: 8,
            params_warning: 7,
            params_critical: 10,
            coupling_distance_warning: 0.6,
            coupling_distance_critical: 0.8,
            lcom_warning: 3,
            lcom_critical: 6,
            halstead_volume_warning: 2000.0,
            halstead_volume_critical: 5000.0,
            halstead_bugs_warning: 1.0,
            halstead_bugs_critical: 3.0,
        }
    }

    /// Load thresholds from a TOML configuration file.
    ///
    /// The configuration file format is:
    ///
    /// ```toml
    /// [metrics.thresholds]
    /// cyclomatic_warning = 10
    /// cyclomatic_critical = 20
    /// cognitive_warning = 15
    /// cognitive_critical = 30
    /// maintainability_warning = 40.0
    /// maintainability_critical = 20.0
    /// loc_warning = 50
    /// loc_critical = 100
    /// ```
    ///
    /// Only specified values are overridden; others use defaults.
    pub fn from_toml(content: &str) -> std::result::Result<Self, String> {
        // Parse as TOML table
        let value: toml::Value = content
            .parse()
            .map_err(|e| format!("Invalid TOML: {}", e))?;

        let mut thresholds = Self::default();

        // Navigate to metrics.thresholds section
        if let Some(metrics) = value.get("metrics") {
            if let Some(t) = metrics.get("thresholds") {
                // Apply overrides
                if let Some(v) = t.get("cyclomatic_warning").and_then(|v| v.as_integer()) {
                    thresholds.cyclomatic_warning = v as u32;
                }
                if let Some(v) = t.get("cyclomatic_critical").and_then(|v| v.as_integer()) {
                    thresholds.cyclomatic_critical = v as u32;
                }
                if let Some(v) = t.get("cognitive_warning").and_then(|v| v.as_integer()) {
                    thresholds.cognitive_warning = v as u32;
                }
                if let Some(v) = t.get("cognitive_critical").and_then(|v| v.as_integer()) {
                    thresholds.cognitive_critical = v as u32;
                }
                if let Some(v) = t.get("maintainability_warning").and_then(|v| v.as_float()) {
                    thresholds.maintainability_warning = v;
                }
                if let Some(v) = t.get("maintainability_critical").and_then(|v| v.as_float()) {
                    thresholds.maintainability_critical = v;
                }
                if let Some(v) = t.get("loc_warning").and_then(|v| v.as_integer()) {
                    thresholds.loc_warning = v as u32;
                }
                if let Some(v) = t.get("loc_critical").and_then(|v| v.as_integer()) {
                    thresholds.loc_critical = v as u32;
                }
                if let Some(v) = t.get("nesting_warning").and_then(|v| v.as_integer()) {
                    thresholds.nesting_warning = v as u32;
                }
                if let Some(v) = t.get("nesting_critical").and_then(|v| v.as_integer()) {
                    thresholds.nesting_critical = v as u32;
                }
                if let Some(v) = t.get("params_warning").and_then(|v| v.as_integer()) {
                    thresholds.params_warning = v as u32;
                }
                if let Some(v) = t.get("params_critical").and_then(|v| v.as_integer()) {
                    thresholds.params_critical = v as u32;
                }
                if let Some(v) = t
                    .get("coupling_distance_warning")
                    .and_then(|v| v.as_float())
                {
                    thresholds.coupling_distance_warning = v;
                }
                if let Some(v) = t
                    .get("coupling_distance_critical")
                    .and_then(|v| v.as_float())
                {
                    thresholds.coupling_distance_critical = v;
                }
                if let Some(v) = t.get("lcom_warning").and_then(|v| v.as_integer()) {
                    thresholds.lcom_warning = v as u32;
                }
                if let Some(v) = t.get("lcom_critical").and_then(|v| v.as_integer()) {
                    thresholds.lcom_critical = v as u32;
                }
                if let Some(v) = t.get("halstead_volume_warning").and_then(|v| v.as_float()) {
                    thresholds.halstead_volume_warning = v;
                }
                if let Some(v) = t.get("halstead_volume_critical").and_then(|v| v.as_float()) {
                    thresholds.halstead_volume_critical = v;
                }
                if let Some(v) = t.get("halstead_bugs_warning").and_then(|v| v.as_float()) {
                    thresholds.halstead_bugs_warning = v;
                }
                if let Some(v) = t.get("halstead_bugs_critical").and_then(|v| v.as_float()) {
                    thresholds.halstead_bugs_critical = v;
                }
            }
        }

        Ok(thresholds)
    }

    /// Load thresholds from .brrr/config.toml in the project root.
    ///
    /// Returns default thresholds if the config file doesn't exist.
    pub fn load_from_project<P: AsRef<Path>>(project_root: P) -> Self {
        let config_path = project_root.as_ref().join(".brrr").join("config.toml");

        if config_path.exists() {
            match fs::read_to_string(&config_path) {
                Ok(content) => match Self::from_toml(&content) {
                    Ok(thresholds) => {
                        info!("Loaded metric thresholds from {}", config_path.display());
                        return thresholds;
                    }
                    Err(e) => {
                        warn!("Failed to parse {}: {}", config_path.display(), e);
                    }
                },
                Err(e) => {
                    warn!("Failed to read {}: {}", config_path.display(), e);
                }
            }
        }

        Self::default()
    }
}

// =============================================================================
// ANALYSIS CONFIGURATION
// =============================================================================

/// Configuration for unified metrics analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricsConfig {
    /// Metric thresholds for issue detection
    pub thresholds: MetricThresholds,
    /// Whether to include Halstead detailed token lists
    pub include_halstead_tokens: bool,
    /// Whether to include cognitive complexity breakdown
    pub include_cognitive_breakdown: bool,
    /// Whether to include cohesion component details
    pub include_cohesion_components: bool,
    /// Whether to analyze coupling (can be slow for large projects)
    pub analyze_coupling: bool,
    /// Coupling analysis level (file, module, or class)
    pub coupling_level: CouplingLevel,
    /// Maximum files to analyze (0 = unlimited)
    pub max_files: usize,
    /// Whether to show progress during analysis
    pub show_progress: bool,
}

impl Default for MetricsConfig {
    fn default() -> Self {
        Self {
            thresholds: MetricThresholds::default(),
            include_halstead_tokens: false,
            include_cognitive_breakdown: false,
            include_cohesion_components: false,
            analyze_coupling: true,
            coupling_level: CouplingLevel::File,
            max_files: 0,
            show_progress: false,
        }
    }
}

impl MetricsConfig {
    /// Create a minimal configuration for quick analysis.
    #[must_use]
    pub fn minimal() -> Self {
        Self {
            analyze_coupling: false,
            max_files: 100,
            ..Default::default()
        }
    }

    /// Create a comprehensive configuration for detailed analysis.
    #[must_use]
    pub fn comprehensive() -> Self {
        Self {
            include_halstead_tokens: true,
            include_cognitive_breakdown: true,
            include_cohesion_components: true,
            analyze_coupling: true,
            coupling_level: CouplingLevel::File,
            ..Default::default()
        }
    }

    /// Set custom thresholds.
    #[must_use]
    pub fn with_thresholds(mut self, thresholds: MetricThresholds) -> Self {
        self.thresholds = thresholds;
        self
    }
}

// =============================================================================
// ISSUE TYPES
// =============================================================================

/// Severity level for metric issues.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum IssueSeverity {
    /// Informational - not necessarily a problem
    Info,
    /// Warning - should be reviewed
    Warning,
    /// Critical - should be addressed
    Critical,
}

impl IssueSeverity {
    /// Get ANSI color code for CLI output.
    #[must_use]
    pub const fn color_code(&self) -> &'static str {
        match self {
            Self::Info => "\x1b[36m",     // Cyan
            Self::Warning => "\x1b[33m",  // Yellow
            Self::Critical => "\x1b[31m", // Red
        }
    }
}

impl std::fmt::Display for IssueSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Info => write!(f, "info"),
            Self::Warning => write!(f, "warning"),
            Self::Critical => write!(f, "critical"),
        }
    }
}

/// Category of metric issue.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IssueCategory {
    /// Cyclomatic complexity issue
    CyclomaticComplexity,
    /// Cognitive complexity issue
    CognitiveComplexity,
    /// Maintainability Index issue
    Maintainability,
    /// Function too long
    FunctionLength,
    /// Too many parameters
    ParameterCount,
    /// Deep nesting
    NestingDepth,
    /// Coupling issue
    Coupling,
    /// Cohesion issue
    Cohesion,
    /// Halstead complexity issue
    HalsteadComplexity,
    /// Estimated bugs
    EstimatedBugs,
}

impl std::fmt::Display for IssueCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CyclomaticComplexity => write!(f, "cyclomatic_complexity"),
            Self::CognitiveComplexity => write!(f, "cognitive_complexity"),
            Self::Maintainability => write!(f, "maintainability"),
            Self::FunctionLength => write!(f, "function_length"),
            Self::ParameterCount => write!(f, "parameter_count"),
            Self::NestingDepth => write!(f, "nesting_depth"),
            Self::Coupling => write!(f, "coupling"),
            Self::Cohesion => write!(f, "cohesion"),
            Self::HalsteadComplexity => write!(f, "halstead_complexity"),
            Self::EstimatedBugs => write!(f, "estimated_bugs"),
        }
    }
}

/// A detected metric issue.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricIssue {
    /// Issue severity
    pub severity: IssueSeverity,
    /// Issue category
    pub category: IssueCategory,
    /// Human-readable message
    pub message: String,
    /// File where issue was found
    pub file: PathBuf,
    /// Line number (if applicable)
    pub line: Option<usize>,
    /// Name of the affected code unit (function, class, module)
    pub unit_name: String,
    /// Current metric value
    pub value: f64,
    /// Threshold that was exceeded
    pub threshold: f64,
    /// Suggested remediation
    pub suggestion: Option<String>,
}

// =============================================================================
// UNIFIED METRICS TYPES
// =============================================================================

/// Project-level metrics summary.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProjectMetrics {
    /// Total files analyzed
    pub total_files: u32,
    /// Total functions analyzed
    pub total_functions: u32,
    /// Total classes analyzed
    pub total_classes: u32,
    /// Aggregate LOC metrics
    pub total_loc: LOCMetrics,
    /// Average cyclomatic complexity
    pub avg_cyclomatic: f64,
    /// Average cognitive complexity
    pub avg_cognitive: f64,
    /// Average maintainability index
    pub avg_maintainability: f64,
    /// Average nesting depth
    pub avg_nesting: f64,
    /// Average function size (SLOC)
    pub avg_function_size: f64,
    /// Total estimated bugs (Halstead)
    pub total_estimated_bugs: f64,
    /// Total estimated development time (hours)
    pub total_estimated_hours: f64,
    /// Files with critical issues
    pub files_with_critical_issues: u32,
    /// Functions exceeding complexity thresholds
    pub complex_functions: u32,
    /// Classes with low cohesion
    pub low_cohesion_classes: u32,
}

/// Per-file metrics summary.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileMetrics {
    /// File path (relative to project root)
    pub path: PathBuf,
    /// Detected language
    pub language: Option<String>,
    /// LOC metrics for the file
    pub loc: LOCMetrics,
    /// Number of functions in file
    pub function_count: u32,
    /// Number of classes in file
    pub class_count: u32,
    /// Average cyclomatic complexity in file
    pub avg_cyclomatic: f64,
    /// Max cyclomatic complexity in file
    pub max_cyclomatic: u32,
    /// Average cognitive complexity in file
    pub avg_cognitive: f64,
    /// Max cognitive complexity in file
    pub max_cognitive: u32,
    /// Average maintainability index in file
    pub avg_maintainability: f64,
    /// Min maintainability index in file (worst)
    pub min_maintainability: f64,
    /// Number of issues in this file
    pub issue_count: u32,
    /// Number of critical issues in this file
    pub critical_issue_count: u32,
}

/// Unified function metrics combining all analyzers.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionMetrics {
    /// Function name (may include class prefix for methods)
    pub name: String,
    /// File containing the function
    pub file: PathBuf,
    /// Starting line number (1-indexed)
    pub line: usize,
    /// Ending line number (1-indexed)
    pub end_line: usize,

    // Complexity metrics
    /// Cyclomatic complexity
    pub cyclomatic: u32,
    /// Cyclomatic risk level
    pub cyclomatic_risk: RiskLevel,
    /// Cognitive complexity
    pub cognitive: u32,
    /// Cognitive risk level
    pub cognitive_risk: CognitiveRiskLevel,

    // Halstead metrics
    /// Halstead metrics (if computed)
    pub halstead: Option<HalsteadMetrics>,

    // Maintainability
    /// Maintainability Index (0-100)
    pub maintainability: f64,
    /// Maintainability risk level
    pub maintainability_risk: MaintainabilityRiskLevel,

    // Size metrics
    /// Source lines of code
    pub loc: u32,
    /// Number of statements
    pub statements: u32,
    /// Max nesting depth
    pub nesting: u32,
    /// Nesting risk level
    pub nesting_risk: NestingDepthLevel,
    /// Number of parameters
    pub params: u32,
    /// Number of local variables
    pub variables: u32,
    /// Number of return statements
    pub returns: u32,

    // Issues for this function
    /// Size-related issues detected
    pub size_issues: Vec<String>,
}

/// Per-class metrics summary.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClassMetrics {
    /// Class name
    pub name: String,
    /// File containing the class
    pub file: PathBuf,
    /// Starting line number
    pub line: usize,
    /// Ending line number
    pub end_line: usize,
    /// Number of methods
    pub method_count: u32,
    /// Number of attributes/fields
    pub attribute_count: u32,
    /// LCOM3 value (connected components)
    pub lcom3: u32,
    /// LCOM4 value (with method calls)
    pub lcom4: u32,
    /// Cohesion level
    pub cohesion_level: CohesionLevel,
    /// Is low cohesion detected
    pub is_low_cohesion: bool,
    /// Average method complexity
    pub avg_method_complexity: f64,
    /// Suggestion for improvement
    pub suggestion: Option<String>,
}

/// Complete unified metrics report.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricsReport {
    /// Path that was analyzed
    pub path: PathBuf,
    /// Detected or specified language
    pub language: Option<String>,
    /// Analysis duration in milliseconds
    pub analysis_duration_ms: u64,
    /// Configuration used
    pub config: MetricsConfig,

    /// Project-level summary
    pub project_summary: ProjectMetrics,
    /// Per-file metrics
    pub file_metrics: Vec<FileMetrics>,
    /// Per-function metrics (unified view)
    pub function_metrics: Vec<FunctionMetrics>,
    /// Per-class metrics
    pub class_metrics: Vec<ClassMetrics>,
    /// All detected issues
    pub issues: Vec<MetricIssue>,

    /// Issue statistics by severity
    pub issue_stats: IssueStats,
}

/// Statistics about detected issues.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct IssueStats {
    /// Total issue count
    pub total: u32,
    /// Info-level issues
    pub info: u32,
    /// Warning-level issues
    pub warnings: u32,
    /// Critical issues
    pub critical: u32,
    /// Issues by category
    pub by_category: HashMap<String, u32>,
}

// =============================================================================
// QUALITY GATE
// =============================================================================

/// Quality gate configuration for CI/CD integration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QualityGate {
    /// Fail on any critical issue
    pub fail_on_critical: bool,
    /// Maximum allowed critical issues (0 = any fails)
    pub max_critical_issues: u32,
    /// Maximum allowed warning issues (0 = unlimited)
    pub max_warning_issues: u32,
    /// Minimum required maintainability index average
    pub min_maintainability: Option<f64>,
    /// Maximum allowed average cyclomatic complexity
    pub max_avg_cyclomatic: Option<f64>,
}

impl Default for QualityGate {
    fn default() -> Self {
        Self {
            fail_on_critical: true,
            max_critical_issues: 0,
            max_warning_issues: 0,
            min_maintainability: None,
            max_avg_cyclomatic: None,
        }
    }
}

impl QualityGate {
    /// Create a permissive gate (only fails on critical issues).
    #[must_use]
    pub fn permissive() -> Self {
        Self {
            fail_on_critical: true,
            max_critical_issues: 0,
            max_warning_issues: 0,
            min_maintainability: None,
            max_avg_cyclomatic: None,
        }
    }

    /// Create a strict gate (fails on warnings or critical).
    #[must_use]
    pub fn strict() -> Self {
        Self {
            fail_on_critical: true,
            max_critical_issues: 0,
            max_warning_issues: 10,
            min_maintainability: Some(50.0),
            max_avg_cyclomatic: Some(10.0),
        }
    }

    /// Check if the report passes the quality gate.
    #[must_use]
    pub fn check(&self, report: &MetricsReport) -> QualityGateResult {
        let mut reasons = Vec::new();

        // Check critical issues
        let critical_count = report.issue_stats.critical;
        if self.fail_on_critical && critical_count > 0 {
            reasons.push(format!("{} critical issues found", critical_count));
        }
        if self.max_critical_issues > 0 && critical_count > self.max_critical_issues {
            reasons.push(format!(
                "Critical issues ({}) exceed maximum ({})",
                critical_count, self.max_critical_issues
            ));
        }

        // Check warning issues
        let warning_count = report.issue_stats.warnings;
        if self.max_warning_issues > 0 && warning_count > self.max_warning_issues {
            reasons.push(format!(
                "Warning issues ({}) exceed maximum ({})",
                warning_count, self.max_warning_issues
            ));
        }

        // Check maintainability
        if let Some(min_mi) = self.min_maintainability {
            if report.project_summary.avg_maintainability < min_mi {
                reasons.push(format!(
                    "Average maintainability ({:.1}) below minimum ({:.1})",
                    report.project_summary.avg_maintainability, min_mi
                ));
            }
        }

        // Check average cyclomatic
        if let Some(max_cc) = self.max_avg_cyclomatic {
            if report.project_summary.avg_cyclomatic > max_cc {
                reasons.push(format!(
                    "Average cyclomatic complexity ({:.1}) exceeds maximum ({:.1})",
                    report.project_summary.avg_cyclomatic, max_cc
                ));
            }
        }

        QualityGateResult {
            passed: reasons.is_empty(),
            failed: !reasons.is_empty(),
            critical_count,
            warning_count,
            reasons,
        }
    }
}

/// Result of quality gate check.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QualityGateResult {
    /// Whether the gate passed
    pub passed: bool,
    /// Whether the gate failed
    pub failed: bool,
    /// Number of critical issues
    pub critical_count: u32,
    /// Number of warning issues
    pub warning_count: u32,
    /// Reasons for failure (if any)
    pub reasons: Vec<String>,
}

// =============================================================================
// ANALYSIS IMPLEMENTATION
// =============================================================================

/// Analyze all metrics for a path.
///
/// This function runs all metric analyzers in parallel and combines results
/// into a unified report.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `lang` - Optional language filter (auto-detected if not specified)
/// * `config` - Analysis configuration
///
/// # Returns
///
/// A comprehensive `MetricsReport` containing all metrics and detected issues.
///
/// # Errors
///
/// Returns error if path doesn't exist or analysis fails.
pub fn analyze_all_metrics<P: AsRef<Path>>(
    path: P,
    lang: Option<&str>,
    config: &MetricsConfig,
) -> Result<MetricsReport> {
    let path = path.as_ref();
    let start = Instant::now();

    // Validate path exists
    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Path not found: {}", path.display()),
        )));
    }

    info!("Starting unified metrics analysis for: {}", path.display());

    // Run all analyzers in parallel using rayon::scope for cleaner parallel execution
    let lang_str = lang.map(ToString::to_string);

    // Use parallel execution with explicit types to avoid inference issues
    let (complexity_result, other_results) = rayon::join(
        || analyze_complexity(path, lang_str.as_deref(), None),
        || {
            let (cognitive, rest1) = rayon::join(
                || analyze_cognitive_complexity(path, lang_str.as_deref(), None),
                || {
                    let (halstead, rest2) = rayon::join(
                        || {
                            analyze_halstead(
                                path,
                                lang_str.as_deref(),
                                config.include_halstead_tokens,
                            )
                        },
                        || {
                            let (maint, rest3) = rayon::join(
                                || analyze_maintainability(path, lang_str.as_deref(), None, false),
                                || {
                                    let (loc, rest4) = rayon::join(
                                        || analyze_loc(path, lang_str.as_deref(), None),
                                        || {
                                            rayon::join(
                                                || analyze_nesting(path, lang_str.as_deref(), None),
                                                || {
                                                    analyze_function_size(
                                                        path,
                                                        lang_str.as_deref(),
                                                        None,
                                                    )
                                                },
                                            )
                                        },
                                    );
                                    (loc, rest4)
                                },
                            );
                            (maint, rest3)
                        },
                    );
                    (halstead, rest2)
                },
            );
            (cognitive, rest1)
        },
    );

    // Unpack the nested results
    let (
        cognitive_result,
        (
            halstead_result,
            (maintainability_result, (loc_result, (nesting_result, function_size_result))),
        ),
    ) = other_results;

    // Handle errors gracefully - collect what we can
    let complexity_analysis = complexity_result.ok();
    let cognitive_analysis = cognitive_result.ok();
    let halstead_analysis = halstead_result.ok();
    let maintainability_analysis = maintainability_result.ok();
    let loc_analysis = loc_result.ok();
    let nesting_analysis = nesting_result.ok();
    let function_size_analysis = function_size_result.ok();

    // Analyze coupling if enabled (can be slow)
    let cohesion_analysis = if config.analyze_coupling {
        analyze_cohesion(path, lang_str.as_deref(), None).ok()
    } else {
        None
    };

    // Build unified function metrics
    let function_metrics = build_function_metrics(
        &complexity_analysis,
        &cognitive_analysis,
        &halstead_analysis,
        &maintainability_analysis,
        &loc_analysis,
        &nesting_analysis,
        &function_size_analysis,
    );

    // Detect issues based on thresholds
    let mut issues = detect_issues(&function_metrics, &cohesion_analysis, &config.thresholds);

    // Sort issues by severity (critical first)
    issues.sort_by(|a, b| b.severity.cmp(&a.severity));

    // Build class metrics
    let class_metrics = build_class_metrics(&cohesion_analysis);

    // Build file metrics
    let file_metrics = build_file_metrics(
        &complexity_analysis,
        &cognitive_analysis,
        &maintainability_analysis,
        &loc_analysis,
        &issues,
    );

    // Build project summary
    let project_summary = build_project_summary(
        &file_metrics,
        &function_metrics,
        &class_metrics,
        &loc_analysis,
        &halstead_analysis,
        &issues,
    );

    // Build issue statistics
    let issue_stats = build_issue_stats(&issues);

    let duration = start.elapsed();

    Ok(MetricsReport {
        path: path.to_path_buf(),
        language: lang.map(ToString::to_string).or_else(|| {
            complexity_analysis
                .as_ref()
                .and_then(|a| a.language.clone())
        }),
        analysis_duration_ms: duration.as_millis() as u64,
        config: config.clone(),
        project_summary,
        file_metrics,
        function_metrics,
        class_metrics,
        issues,
        issue_stats,
    })
}

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

/// Build unified function metrics from individual analyzer results.
fn build_function_metrics(
    complexity: &Option<super::complexity::ComplexityAnalysis>,
    cognitive: &Option<super::complexity::CognitiveAnalysis>,
    halstead: &Option<super::complexity::HalsteadAnalysis>,
    maintainability: &Option<super::complexity::MaintainabilityAnalysis>,
    _loc: &Option<super::loc::LOCAnalysis>,
    nesting: &Option<super::nesting::NestingAnalysis>,
    function_size: &Option<super::function_size::FunctionSizeAnalysis>,
) -> Vec<FunctionMetrics> {
    // Use complexity analysis as the base since it has all functions
    let Some(cc) = complexity else {
        return Vec::new();
    };

    let mut result = Vec::with_capacity(cc.functions.len());

    for func in &cc.functions {
        let key = (&func.file, &func.function_name, func.line);

        // Look up cognitive complexity for this function
        let (cognitive_val, cognitive_risk) = cognitive
            .as_ref()
            .and_then(|ca| {
                ca.functions
                    .iter()
                    .find(|f| &f.file == key.0 && &f.function_name == key.1 && f.line == key.2)
            })
            .map(|f| (f.complexity, f.risk_level))
            .unwrap_or((0, CognitiveRiskLevel::Low));

        // Look up Halstead metrics
        let halstead_metrics = halstead
            .as_ref()
            .and_then(|ha| {
                ha.functions
                    .iter()
                    .find(|f| &f.file == key.0 && &f.function_name == key.1 && f.line == key.2)
            })
            .map(|f| f.metrics.clone());

        // Look up maintainability
        let (mi_val, mi_risk) = maintainability
            .as_ref()
            .and_then(|ma| {
                ma.functions
                    .iter()
                    .find(|f| &f.file == key.0 && &f.function_name == key.1 && f.line == key.2)
            })
            .map(|f| (f.index.score, f.index.risk_level))
            .unwrap_or((100.0, MaintainabilityRiskLevel::Low));

        // Look up nesting
        let (nesting_val, nesting_risk) = nesting
            .as_ref()
            .and_then(|na| {
                na.functions
                    .iter()
                    .find(|f| &f.file == key.0 && &f.function_name == key.1 && f.line == key.2)
            })
            .map(|f| (f.max_depth, f.risk_level))
            .unwrap_or((0, NestingDepthLevel::Good));

        // Look up function size metrics
        let (loc, stmts, params, vars, returns, end_line, size_issues) = function_size
            .as_ref()
            .and_then(|fa| {
                fa.functions
                    .iter()
                    .find(|f| &f.file == key.0 && &f.name == key.1 && f.line == key.2)
            })
            .map(|f| {
                let issues: Vec<String> = f.issues.iter().map(|i| format!("{:?}", i)).collect();
                (
                    f.sloc,
                    f.statements,
                    f.parameters,
                    f.local_variables,
                    f.return_statements,
                    f.end_line,
                    issues,
                )
            })
            .unwrap_or((0, 0, 0, 0, 0, func.line, Vec::new()));

        result.push(FunctionMetrics {
            name: func.function_name.clone(),
            file: func.file.clone(),
            line: func.line,
            end_line,
            cyclomatic: func.complexity,
            cyclomatic_risk: func.risk_level,
            cognitive: cognitive_val,
            cognitive_risk,
            halstead: halstead_metrics,
            maintainability: mi_val,
            maintainability_risk: mi_risk,
            loc,
            statements: stmts,
            nesting: nesting_val,
            nesting_risk,
            params,
            variables: vars,
            returns,
            size_issues,
        });
    }

    result
}

/// Detect issues based on function metrics and thresholds.
fn detect_issues(
    functions: &[FunctionMetrics],
    cohesion: &Option<super::cohesion::CohesionAnalysis>,
    thresholds: &MetricThresholds,
) -> Vec<MetricIssue> {
    let mut issues = Vec::new();

    // Check function metrics
    for func in functions {
        // Cyclomatic complexity
        if func.cyclomatic >= thresholds.cyclomatic_critical {
            issues.push(MetricIssue {
                severity: IssueSeverity::Critical,
                category: IssueCategory::CyclomaticComplexity,
                message: format!(
                    "Function '{}' has critical cyclomatic complexity ({})",
                    func.name, func.cyclomatic
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: f64::from(func.cyclomatic),
                threshold: f64::from(thresholds.cyclomatic_critical),
                suggestion: Some("Consider extracting smaller helper functions".to_string()),
            });
        } else if func.cyclomatic >= thresholds.cyclomatic_warning {
            issues.push(MetricIssue {
                severity: IssueSeverity::Warning,
                category: IssueCategory::CyclomaticComplexity,
                message: format!(
                    "Function '{}' has high cyclomatic complexity ({})",
                    func.name, func.cyclomatic
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: f64::from(func.cyclomatic),
                threshold: f64::from(thresholds.cyclomatic_warning),
                suggestion: Some("Review for potential simplification".to_string()),
            });
        }

        // Cognitive complexity
        if func.cognitive >= thresholds.cognitive_critical {
            issues.push(MetricIssue {
                severity: IssueSeverity::Critical,
                category: IssueCategory::CognitiveComplexity,
                message: format!(
                    "Function '{}' has critical cognitive complexity ({})",
                    func.name, func.cognitive
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: f64::from(func.cognitive),
                threshold: f64::from(thresholds.cognitive_critical),
                suggestion: Some("Reduce nesting depth and extract helper functions".to_string()),
            });
        } else if func.cognitive >= thresholds.cognitive_warning {
            issues.push(MetricIssue {
                severity: IssueSeverity::Warning,
                category: IssueCategory::CognitiveComplexity,
                message: format!(
                    "Function '{}' has high cognitive complexity ({})",
                    func.name, func.cognitive
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: f64::from(func.cognitive),
                threshold: f64::from(thresholds.cognitive_warning),
                suggestion: Some("Consider using early returns and extracting logic".to_string()),
            });
        }

        // Maintainability Index (lower is worse)
        if func.maintainability <= thresholds.maintainability_critical {
            issues.push(MetricIssue {
                severity: IssueSeverity::Critical,
                category: IssueCategory::Maintainability,
                message: format!(
                    "Function '{}' has critical maintainability index ({:.1})",
                    func.name, func.maintainability
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: func.maintainability,
                threshold: thresholds.maintainability_critical,
                suggestion: Some(
                    "Major refactoring recommended - reduce complexity and size".to_string(),
                ),
            });
        } else if func.maintainability <= thresholds.maintainability_warning {
            issues.push(MetricIssue {
                severity: IssueSeverity::Warning,
                category: IssueCategory::Maintainability,
                message: format!(
                    "Function '{}' has low maintainability index ({:.1})",
                    func.name, func.maintainability
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: func.maintainability,
                threshold: thresholds.maintainability_warning,
                suggestion: Some(
                    "Consider reducing complexity and improving documentation".to_string(),
                ),
            });
        }

        // Function length
        if func.loc >= thresholds.loc_critical {
            issues.push(MetricIssue {
                severity: IssueSeverity::Critical,
                category: IssueCategory::FunctionLength,
                message: format!(
                    "Function '{}' is critically long ({} lines)",
                    func.name, func.loc
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: f64::from(func.loc),
                threshold: f64::from(thresholds.loc_critical),
                suggestion: Some("Split into smaller, focused functions".to_string()),
            });
        } else if func.loc >= thresholds.loc_warning {
            issues.push(MetricIssue {
                severity: IssueSeverity::Warning,
                category: IssueCategory::FunctionLength,
                message: format!("Function '{}' is too long ({} lines)", func.name, func.loc),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: f64::from(func.loc),
                threshold: f64::from(thresholds.loc_warning),
                suggestion: Some(
                    "Consider extracting logical sections into helper functions".to_string(),
                ),
            });
        }

        // Nesting depth
        if func.nesting >= thresholds.nesting_critical {
            issues.push(MetricIssue {
                severity: IssueSeverity::Critical,
                category: IssueCategory::NestingDepth,
                message: format!(
                    "Function '{}' has critical nesting depth ({})",
                    func.name, func.nesting
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: f64::from(func.nesting),
                threshold: f64::from(thresholds.nesting_critical),
                suggestion: Some(
                    "Use early returns, extract methods, or flatten conditionals".to_string(),
                ),
            });
        } else if func.nesting >= thresholds.nesting_warning {
            issues.push(MetricIssue {
                severity: IssueSeverity::Warning,
                category: IssueCategory::NestingDepth,
                message: format!(
                    "Function '{}' has deep nesting ({})",
                    func.name, func.nesting
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: f64::from(func.nesting),
                threshold: f64::from(thresholds.nesting_warning),
                suggestion: Some(
                    "Consider using guard clauses and extracting nested logic".to_string(),
                ),
            });
        }

        // Parameter count
        if func.params >= thresholds.params_critical {
            issues.push(MetricIssue {
                severity: IssueSeverity::Critical,
                category: IssueCategory::ParameterCount,
                message: format!(
                    "Function '{}' has too many parameters ({})",
                    func.name, func.params
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: f64::from(func.params),
                threshold: f64::from(thresholds.params_critical),
                suggestion: Some("Use a parameter object or builder pattern".to_string()),
            });
        } else if func.params >= thresholds.params_warning {
            issues.push(MetricIssue {
                severity: IssueSeverity::Warning,
                category: IssueCategory::ParameterCount,
                message: format!(
                    "Function '{}' has many parameters ({})",
                    func.name, func.params
                ),
                file: func.file.clone(),
                line: Some(func.line),
                unit_name: func.name.clone(),
                value: f64::from(func.params),
                threshold: f64::from(thresholds.params_warning),
                suggestion: Some("Consider grouping related parameters".to_string()),
            });
        }

        // Halstead estimated bugs
        if let Some(ref halstead) = func.halstead {
            if halstead.bugs >= thresholds.halstead_bugs_critical {
                issues.push(MetricIssue {
                    severity: IssueSeverity::Critical,
                    category: IssueCategory::EstimatedBugs,
                    message: format!(
                        "Function '{}' has high estimated bug count ({:.2})",
                        func.name, halstead.bugs
                    ),
                    file: func.file.clone(),
                    line: Some(func.line),
                    unit_name: func.name.clone(),
                    value: halstead.bugs,
                    threshold: thresholds.halstead_bugs_critical,
                    suggestion: Some("Simplify logic and reduce vocabulary".to_string()),
                });
            } else if halstead.bugs >= thresholds.halstead_bugs_warning {
                issues.push(MetricIssue {
                    severity: IssueSeverity::Warning,
                    category: IssueCategory::EstimatedBugs,
                    message: format!(
                        "Function '{}' may have bugs (estimated: {:.2})",
                        func.name, halstead.bugs
                    ),
                    file: func.file.clone(),
                    line: Some(func.line),
                    unit_name: func.name.clone(),
                    value: halstead.bugs,
                    threshold: thresholds.halstead_bugs_warning,
                    suggestion: Some("Review carefully and consider simplification".to_string()),
                });
            }
        }
    }

    // Check cohesion metrics
    if let Some(ref ca) = cohesion {
        for class in &ca.classes {
            if class.lcom3 >= thresholds.lcom_critical {
                issues.push(MetricIssue {
                    severity: IssueSeverity::Critical,
                    category: IssueCategory::Cohesion,
                    message: format!(
                        "Class '{}' has critically low cohesion (LCOM3={})",
                        class.class_name, class.lcom3
                    ),
                    file: class.file.clone(),
                    line: Some(class.line),
                    unit_name: class.class_name.clone(),
                    value: f64::from(class.lcom3),
                    threshold: f64::from(thresholds.lcom_critical),
                    suggestion: Some(format!(
                        "Consider splitting into {} separate classes",
                        class.lcom3
                    )),
                });
            } else if class.lcom3 >= thresholds.lcom_warning {
                issues.push(MetricIssue {
                    severity: IssueSeverity::Warning,
                    category: IssueCategory::Cohesion,
                    message: format!(
                        "Class '{}' has low cohesion (LCOM3={})",
                        class.class_name, class.lcom3
                    ),
                    file: class.file.clone(),
                    line: Some(class.line),
                    unit_name: class.class_name.clone(),
                    value: f64::from(class.lcom3),
                    threshold: f64::from(thresholds.lcom_warning),
                    suggestion: Some(
                        "Review class responsibilities for Single Responsibility Principle"
                            .to_string(),
                    ),
                });
            }
        }
    }

    issues
}

/// Build class metrics from cohesion analysis.
fn build_class_metrics(cohesion: &Option<super::cohesion::CohesionAnalysis>) -> Vec<ClassMetrics> {
    let Some(ca) = cohesion else {
        return Vec::new();
    };

    ca.classes
        .iter()
        .map(|c| ClassMetrics {
            name: c.class_name.clone(),
            file: c.file.clone(),
            line: c.line,
            end_line: c.end_line,
            method_count: c.methods,
            attribute_count: c.attributes,
            lcom3: c.lcom3,
            lcom4: c.lcom4,
            cohesion_level: c.cohesion_level,
            is_low_cohesion: c.is_low_cohesion,
            avg_method_complexity: 0.0, // Would need to compute from complexity analysis
            suggestion: c.suggestion.clone(),
        })
        .collect()
}

/// Build file metrics from individual analyses.
fn build_file_metrics(
    complexity: &Option<super::complexity::ComplexityAnalysis>,
    cognitive: &Option<super::complexity::CognitiveAnalysis>,
    maintainability: &Option<super::complexity::MaintainabilityAnalysis>,
    loc: &Option<super::loc::LOCAnalysis>,
    issues: &[MetricIssue],
) -> Vec<FileMetrics> {
    // Group data by file
    let mut file_data: HashMap<PathBuf, FileMetrics> = HashMap::new();

    // Populate from LOC analysis (has comprehensive file data)
    if let Some(la) = loc {
        for file_loc in &la.files {
            let issue_count = issues.iter().filter(|i| i.file == file_loc.file).count() as u32;
            let critical_count = issues
                .iter()
                .filter(|i| i.file == file_loc.file && i.severity == IssueSeverity::Critical)
                .count() as u32;

            file_data.insert(
                file_loc.file.clone(),
                FileMetrics {
                    path: file_loc.file.clone(),
                    language: file_loc.language.clone(),
                    loc: file_loc.metrics.clone(),
                    function_count: file_loc.functions.len() as u32,
                    class_count: 0, // Would need separate analysis
                    avg_cyclomatic: 0.0,
                    max_cyclomatic: 0,
                    avg_cognitive: 0.0,
                    max_cognitive: 0,
                    avg_maintainability: 0.0,
                    min_maintainability: 100.0,
                    issue_count,
                    critical_issue_count: critical_count,
                },
            );
        }
    }

    // Add complexity data
    if let Some(ca) = complexity {
        for func in &ca.functions {
            if let Some(fm) = file_data.get_mut(&func.file) {
                fm.max_cyclomatic = fm.max_cyclomatic.max(func.complexity);
            }
        }

        // Calculate averages per file - use &Path keys to avoid cloning PathBuf
        let mut file_cc: HashMap<&Path, (u32, u32)> = HashMap::new();
        for func in &ca.functions {
            let entry = file_cc.entry(func.file.as_path()).or_insert((0, 0));
            entry.0 += func.complexity;
            entry.1 += 1;
        }
        for (file_path, (sum, count)) in file_cc {
            if let Some(fm) = file_data.get_mut(file_path) {
                if count > 0 {
                    fm.avg_cyclomatic = f64::from(sum) / f64::from(count);
                }
            }
        }
    }

    // Add cognitive data
    if let Some(ca) = cognitive {
        for func in &ca.functions {
            if let Some(fm) = file_data.get_mut(&func.file) {
                fm.max_cognitive = fm.max_cognitive.max(func.complexity);
            }
        }

        // Use &Path keys to avoid cloning PathBuf
        let mut file_cog: HashMap<&Path, (u32, u32)> = HashMap::new();
        for func in &ca.functions {
            let entry = file_cog.entry(func.file.as_path()).or_insert((0, 0));
            entry.0 += func.complexity;
            entry.1 += 1;
        }
        for (file_path, (sum, count)) in file_cog {
            if let Some(fm) = file_data.get_mut(file_path) {
                if count > 0 {
                    fm.avg_cognitive = f64::from(sum) / f64::from(count);
                }
            }
        }
    }

    // Add maintainability data
    if let Some(ma) = maintainability {
        for func in &ma.functions {
            if let Some(fm) = file_data.get_mut(&func.file) {
                fm.min_maintainability = fm.min_maintainability.min(func.index.score);
            }
        }

        // Use &Path keys to avoid cloning PathBuf
        let mut file_mi: HashMap<&Path, (f64, u32)> = HashMap::new();
        for func in &ma.functions {
            let entry = file_mi.entry(func.file.as_path()).or_insert((0.0, 0));
            entry.0 += func.index.score;
            entry.1 += 1;
        }
        for (file_path, (sum, count)) in file_mi {
            if let Some(fm) = file_data.get_mut(file_path) {
                if count > 0 {
                    fm.avg_maintainability = sum / f64::from(count);
                }
            }
        }
    }

    file_data.into_values().collect()
}

/// Build project-level summary.
fn build_project_summary(
    files: &[FileMetrics],
    functions: &[FunctionMetrics],
    classes: &[ClassMetrics],
    loc: &Option<super::loc::LOCAnalysis>,
    halstead: &Option<super::complexity::HalsteadAnalysis>,
    _issues: &[MetricIssue],
) -> ProjectMetrics {
    let total_files = files.len() as u32;
    let total_functions = functions.len() as u32;
    let total_classes = classes.len() as u32;

    // Aggregate LOC - access fields directly to avoid clone
    let total_loc = loc
        .as_ref()
        .map(|la| LOCMetrics {
            physical: la.stats.total_physical,
            source: la.stats.total_sloc,
            logical: la.stats.total_logical,
            comment: la.stats.total_comment,
            blank: la.stats.total_blank,
            code_to_comment_ratio: la.stats.code_to_comment_ratio,
        })
        .unwrap_or_default();

    // Calculate averages
    let avg_cyclomatic = if functions.is_empty() {
        0.0
    } else {
        functions
            .iter()
            .map(|f| f64::from(f.cyclomatic))
            .sum::<f64>()
            / functions.len() as f64
    };

    let avg_cognitive = if functions.is_empty() {
        0.0
    } else {
        functions
            .iter()
            .map(|f| f64::from(f.cognitive))
            .sum::<f64>()
            / functions.len() as f64
    };

    let avg_maintainability = if functions.is_empty() {
        100.0
    } else {
        functions.iter().map(|f| f.maintainability).sum::<f64>() / functions.len() as f64
    };

    let avg_nesting = if functions.is_empty() {
        0.0
    } else {
        functions.iter().map(|f| f64::from(f.nesting)).sum::<f64>() / functions.len() as f64
    };

    let avg_function_size = if functions.is_empty() {
        0.0
    } else {
        functions.iter().map(|f| f64::from(f.loc)).sum::<f64>() / functions.len() as f64
    };

    // Halstead totals
    let (total_estimated_bugs, total_estimated_hours) = halstead
        .as_ref()
        .map(|ha| (ha.stats.total_bugs, ha.stats.total_time_seconds / 3600.0))
        .unwrap_or((0.0, 0.0));

    // Count issues
    let files_with_critical = files.iter().filter(|f| f.critical_issue_count > 0).count() as u32;

    let complex_functions = functions
        .iter()
        .filter(|f| {
            f.cyclomatic_risk == RiskLevel::High || f.cyclomatic_risk == RiskLevel::Critical
        })
        .count() as u32;

    let low_cohesion_classes = classes.iter().filter(|c| c.is_low_cohesion).count() as u32;

    ProjectMetrics {
        total_files,
        total_functions,
        total_classes,
        total_loc,
        avg_cyclomatic,
        avg_cognitive,
        avg_maintainability,
        avg_nesting,
        avg_function_size,
        total_estimated_bugs,
        total_estimated_hours,
        files_with_critical_issues: files_with_critical,
        complex_functions,
        low_cohesion_classes,
    }
}

/// Build issue statistics.
fn build_issue_stats(issues: &[MetricIssue]) -> IssueStats {
    let mut stats = IssueStats {
        total: issues.len() as u32,
        ..Default::default()
    };

    for issue in issues {
        match issue.severity {
            IssueSeverity::Info => stats.info += 1,
            IssueSeverity::Warning => stats.warnings += 1,
            IssueSeverity::Critical => stats.critical += 1,
        }

        *stats
            .by_category
            .entry(issue.category.to_string())
            .or_insert(0) += 1;
    }

    stats
}

// =============================================================================
// SORTING UTILITIES
// =============================================================================

/// Sort field for function metrics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionSortBy {
    /// Sort by cyclomatic complexity (descending)
    Cyclomatic,
    /// Sort by cognitive complexity (descending)
    Cognitive,
    /// Sort by maintainability index (ascending - worst first)
    Maintainability,
    /// Sort by lines of code (descending)
    Loc,
    /// Sort by nesting depth (descending)
    Nesting,
    /// Sort by parameter count (descending)
    Params,
    /// Sort by file name then line number
    Location,
}

impl std::str::FromStr for FunctionSortBy {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "cyclomatic" | "cc" | "complexity" => Ok(Self::Cyclomatic),
            "cognitive" | "cog" => Ok(Self::Cognitive),
            "maintainability" | "mi" => Ok(Self::Maintainability),
            "loc" | "lines" | "sloc" => Ok(Self::Loc),
            "nesting" | "depth" => Ok(Self::Nesting),
            "params" | "parameters" => Ok(Self::Params),
            "location" | "file" => Ok(Self::Location),
            _ => Err(format!("Unknown sort field: {}", s)),
        }
    }
}

/// Sort function metrics by specified field.
pub fn sort_functions(functions: &mut [FunctionMetrics], sort_by: FunctionSortBy) {
    match sort_by {
        FunctionSortBy::Cyclomatic => {
            functions.sort_by(|a, b| b.cyclomatic.cmp(&a.cyclomatic));
        }
        FunctionSortBy::Cognitive => {
            functions.sort_by(|a, b| b.cognitive.cmp(&a.cognitive));
        }
        FunctionSortBy::Maintainability => {
            functions.sort_by(|a, b| {
                a.maintainability
                    .partial_cmp(&b.maintainability)
                    .unwrap_or(std::cmp::Ordering::Equal)
            });
        }
        FunctionSortBy::Loc => {
            functions.sort_by(|a, b| b.loc.cmp(&a.loc));
        }
        FunctionSortBy::Nesting => {
            functions.sort_by(|a, b| b.nesting.cmp(&a.nesting));
        }
        FunctionSortBy::Params => {
            functions.sort_by(|a, b| b.params.cmp(&a.params));
        }
        FunctionSortBy::Location => {
            functions.sort_by(|a, b| a.file.cmp(&b.file).then_with(|| a.line.cmp(&b.line)));
        }
    }
}

// =============================================================================
// CSV FORMATTING
// =============================================================================

/// Format function metrics as CSV string.
///
/// Generates a CSV with columns for all key metrics, suitable for spreadsheet
/// import or CI/CD reporting.
///
/// # Columns
///
/// name, file, line, end_line, cyclomatic, cyclomatic_risk, cognitive,
/// cognitive_risk, maintainability, maintainability_risk, loc, statements,
/// nesting, nesting_risk, params, variables, returns, halstead_volume,
/// halstead_difficulty, halstead_bugs
pub fn format_functions_csv(functions: &[FunctionMetrics]) -> String {
    let mut output = String::with_capacity(functions.len() * 256);

    // Header row
    output.push_str("name,file,line,end_line,cyclomatic,cyclomatic_risk,cognitive,");
    output.push_str("cognitive_risk,maintainability,maintainability_risk,loc,statements,");
    output.push_str("nesting,nesting_risk,params,variables,returns,");
    output.push_str("halstead_volume,halstead_difficulty,halstead_bugs\n");

    // Data rows
    for func in functions {
        let (volume, difficulty, bugs) = func
            .halstead
            .as_ref()
            .map(|h| (h.volume, h.difficulty, h.bugs))
            .unwrap_or((0.0, 0.0, 0.0));

        // Escape commas and quotes in name and file path
        let name = escape_csv_field(&func.name);
        let file_str = func.file.display().to_string();
        let file = escape_csv_field(&file_str);

        output.push_str(&format!(
            "{},{},{},{},{},{},{},{},{:.2},{},{},{},{},{},{},{},{},{:.2},{:.2},{:.4}\n",
            name,
            file,
            func.line,
            func.end_line,
            func.cyclomatic,
            func.cyclomatic_risk,
            func.cognitive,
            func.cognitive_risk,
            func.maintainability,
            func.maintainability_risk,
            func.loc,
            func.statements,
            func.nesting,
            func.nesting_risk,
            func.params,
            func.variables,
            func.returns,
            volume,
            difficulty,
            bugs,
        ));
    }

    output
}

/// Format issues as CSV string.
pub fn format_issues_csv(issues: &[MetricIssue]) -> String {
    let mut output = String::with_capacity(issues.len() * 128);

    // Header
    output.push_str("severity,category,file,line,unit_name,value,threshold,message,suggestion\n");

    for issue in issues {
        let file_str = issue.file.display().to_string();
        let file = escape_csv_field(&file_str);
        let unit = escape_csv_field(&issue.unit_name);
        let msg = escape_csv_field(&issue.message);
        let suggestion = issue
            .suggestion
            .as_ref()
            .map(|s| escape_csv_field(s))
            .unwrap_or_default();

        output.push_str(&format!(
            "{},{},{},{},{},{:.2},{:.2},{},{}\n",
            issue.severity,
            issue.category,
            file,
            issue.line.map(|l| l.to_string()).unwrap_or_default(),
            unit,
            issue.value,
            issue.threshold,
            msg,
            suggestion,
        ));
    }

    output
}

/// Format class metrics as CSV string.
pub fn format_classes_csv(classes: &[ClassMetrics]) -> String {
    let mut output = String::with_capacity(classes.len() * 128);

    // Header
    output.push_str("name,file,line,end_line,method_count,attribute_count,lcom3,lcom4,");
    output.push_str("cohesion_level,is_low_cohesion,avg_method_complexity\n");

    for class in classes {
        let name = escape_csv_field(&class.name);
        let file_str = class.file.display().to_string();
        let file = escape_csv_field(&file_str);

        output.push_str(&format!(
            "{},{},{},{},{},{},{},{},{},{},{:.2}\n",
            name,
            file,
            class.line,
            class.end_line,
            class.method_count,
            class.attribute_count,
            class.lcom3,
            class.lcom4,
            class.cohesion_level,
            class.is_low_cohesion,
            class.avg_method_complexity,
        ));
    }

    output
}

/// Format file metrics as CSV string.
pub fn format_files_csv(files: &[FileMetrics]) -> String {
    let mut output = String::with_capacity(files.len() * 128);

    // Header
    output.push_str("path,language,physical_loc,source_loc,comment_loc,blank_loc,");
    output.push_str("function_count,class_count,avg_cyclomatic,max_cyclomatic,");
    output.push_str("avg_cognitive,max_cognitive,avg_maintainability,min_maintainability,");
    output.push_str("issue_count,critical_issue_count\n");

    for file in files {
        let path_str = file.path.display().to_string();
        let path = escape_csv_field(&path_str);
        let lang = file.language.as_deref().unwrap_or("");

        output.push_str(&format!(
            "{},{},{},{},{},{},{},{},{:.2},{},{:.2},{},{:.2},{:.2},{},{}\n",
            path,
            lang,
            file.loc.physical,
            file.loc.source,
            file.loc.comment,
            file.loc.blank,
            file.function_count,
            file.class_count,
            file.avg_cyclomatic,
            file.max_cyclomatic,
            file.avg_cognitive,
            file.max_cognitive,
            file.avg_maintainability,
            file.min_maintainability,
            file.issue_count,
            file.critical_issue_count,
        ));
    }

    output
}

/// Escape a CSV field (handle commas and quotes).
/// Returns Cow to avoid allocation when no escaping is needed.
fn escape_csv_field(s: &str) -> Cow<'_, str> {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        Cow::Owned(format!("\"{}\"", s.replace('"', "\"\"")))
    } else {
        Cow::Borrowed(s)
    }
}

// =============================================================================
// PROGRESS REPORTING
// =============================================================================

/// Progress callback type for metrics analysis.
pub type ProgressCallback = Box<dyn Fn(usize, usize, &str) + Send + Sync>;

/// Analyze all metrics with progress reporting.
///
/// # Arguments
///
/// * `path` - Path to analyze
/// * `lang` - Optional language filter
/// * `config` - Analysis configuration
/// * `progress` - Optional callback for progress reporting (files_done, total_files, current_file)
///
/// # Example
///
/// ```ignore
/// let progress = Box::new(|done, total, file| {
///     eprintln!("[{}/{}] Analyzing: {}", done, total, file);
/// });
/// let report = analyze_all_metrics_with_progress(path, None, &config, Some(progress))?;
/// ```
pub fn analyze_all_metrics_with_progress<P: AsRef<Path>>(
    path: P,
    lang: Option<&str>,
    config: &MetricsConfig,
    progress: Option<ProgressCallback>,
) -> Result<MetricsReport> {
    // For now, delegate to the main function (progress integration would require
    // refactoring the parallel analysis to report per-file progress)
    let _ = progress; // Silence unused warning
    analyze_all_metrics(path, lang, config)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_metric_thresholds_default() {
        let thresholds = MetricThresholds::default();
        assert_eq!(thresholds.cyclomatic_warning, 10);
        assert_eq!(thresholds.cyclomatic_critical, 20);
        assert_eq!(thresholds.cognitive_warning, 15);
        assert_eq!(thresholds.cognitive_critical, 30);
    }

    #[test]
    fn test_metric_thresholds_strict() {
        let thresholds = MetricThresholds::strict();
        assert_eq!(thresholds.cyclomatic_warning, 5);
        assert_eq!(thresholds.cyclomatic_critical, 10);
    }

    #[test]
    fn test_quality_gate_check() {
        let gate = QualityGate::default();

        // Create a minimal report with no issues
        let report = MetricsReport {
            path: PathBuf::from("."),
            language: Some("rust".to_string()),
            analysis_duration_ms: 100,
            config: MetricsConfig::default(),
            project_summary: ProjectMetrics {
                total_files: 1,
                total_functions: 1,
                total_classes: 0,
                total_loc: LOCMetrics::default(),
                avg_cyclomatic: 5.0,
                avg_cognitive: 3.0,
                avg_maintainability: 70.0,
                avg_nesting: 2.0,
                avg_function_size: 20.0,
                total_estimated_bugs: 0.1,
                total_estimated_hours: 1.0,
                files_with_critical_issues: 0,
                complex_functions: 0,
                low_cohesion_classes: 0,
            },
            file_metrics: vec![],
            function_metrics: vec![],
            class_metrics: vec![],
            issues: vec![],
            issue_stats: IssueStats::default(),
        };

        let result = gate.check(&report);
        assert!(result.passed);
        assert!(!result.failed);
    }

    #[test]
    fn test_issue_severity_ordering() {
        assert!(IssueSeverity::Critical > IssueSeverity::Warning);
        assert!(IssueSeverity::Warning > IssueSeverity::Info);
    }

    #[test]
    fn test_function_sort_by_parse() {
        assert_eq!(
            "cyclomatic".parse::<FunctionSortBy>().unwrap(),
            FunctionSortBy::Cyclomatic
        );
        assert_eq!(
            "cc".parse::<FunctionSortBy>().unwrap(),
            FunctionSortBy::Cyclomatic
        );
        assert_eq!(
            "mi".parse::<FunctionSortBy>().unwrap(),
            FunctionSortBy::Maintainability
        );
    }

    #[test]
    fn test_metric_thresholds_from_toml() {
        let toml_content = r#"
[metrics.thresholds]
cyclomatic_warning = 8
cyclomatic_critical = 15
cognitive_warning = 12
maintainability_warning = 50.0
"#;
        let thresholds = MetricThresholds::from_toml(toml_content).unwrap();
        assert_eq!(thresholds.cyclomatic_warning, 8);
        assert_eq!(thresholds.cyclomatic_critical, 15);
        assert_eq!(thresholds.cognitive_warning, 12);
        // Check that unspecified values use defaults
        assert_eq!(thresholds.cognitive_critical, 30);
        assert!((thresholds.maintainability_warning - 50.0).abs() < 0.01);
    }

    #[test]
    fn test_metric_thresholds_from_toml_invalid() {
        let invalid_toml = "this is not valid [toml";
        let result = MetricThresholds::from_toml(invalid_toml);
        assert!(result.is_err());
    }

    #[test]
    fn test_metric_thresholds_from_toml_empty() {
        // Empty or missing sections should return defaults
        let empty_toml = "";
        let thresholds = MetricThresholds::from_toml(empty_toml).unwrap();
        assert_eq!(thresholds.cyclomatic_warning, 10);
        assert_eq!(thresholds.cyclomatic_critical, 20);
    }

    #[test]
    fn test_escape_csv_field() {
        assert_eq!(escape_csv_field("simple"), "simple");
        assert_eq!(escape_csv_field("with,comma"), "\"with,comma\"");
        assert_eq!(escape_csv_field("with\"quote"), "\"with\"\"quote\"");
        assert_eq!(escape_csv_field("with\nnewline"), "\"with\nnewline\"");
    }

    #[test]
    fn test_format_functions_csv_header() {
        let functions: Vec<FunctionMetrics> = vec![];
        let csv = format_functions_csv(&functions);
        // Should have header even with no data
        assert!(csv.starts_with("name,file,line,end_line,"));
        assert!(csv.contains("cyclomatic,"));
        assert!(csv.contains("halstead_bugs"));
    }

    #[test]
    fn test_format_issues_csv_header() {
        let issues: Vec<MetricIssue> = vec![];
        let csv = format_issues_csv(&issues);
        // Should have header even with no data
        assert!(csv.starts_with("severity,category,file,"));
        assert!(csv.contains("suggestion"));
    }
}
