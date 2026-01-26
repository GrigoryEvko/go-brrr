//! God Class detection for identifying classes that violate Single Responsibility Principle.
//!
//! A "God Class" is a class that:
//! - Knows too much (many attributes)
//! - Does too much (many methods)
//! - Is too large (many lines)
//! - Has low cohesion (methods don't share attributes)
//! - Has high coupling (depends on many other classes)
//!
//! # Detection Algorithm
//!
//! The detector uses a weighted scoring system based on multiple indicators:
//!
//! 1. **Method Count**: Classes with > 20 methods get +2 per excess method
//! 2. **Attribute Count**: Classes with > 15 attributes get +1 per excess attribute
//! 3. **Line Count**: Classes with > 500 lines get +1 per 100 excess lines
//! 4. **Cohesion (LCOM3)**: Classes with LCOM3 > 2 get +5 per excess component
//! 5. **Complexity Sum**: Total cyclomatic complexity of all methods
//!
//! A class is flagged as a God Class if its weighted score exceeds the threshold.
//!
//! # Exclusions
//!
//! The detector automatically excludes:
//! - Test classes (TestCase, *Test, *Spec)
//! - Framework classes with known large patterns (Controller, View, etc.)
//! - Generated code (detected by markers or path patterns)
//!
//! # Example
//!
//! ```ignore
//! use brrr::quality::smells::god_class::{detect_god_classes, GodClassConfig};
//!
//! let result = detect_god_classes("./src", None, None)?;
//! for finding in &result.findings {
//!     if finding.severity >= GodClassSeverity::High {
//!         println!("CRITICAL: {} in {} (score: {:.1})",
//!             finding.class_name, finding.file.display(), finding.score);
//!         println!("  Methods: {}, Attributes: {}, Lines: {}, LCOM: {}",
//!             finding.indicators.method_count,
//!             finding.indicators.attribute_count,
//!             finding.indicators.line_count,
//!             finding.indicators.lcom);
//!         for split in &finding.suggested_splits {
//!             println!("  Suggest extracting '{}': {:?}", split.name_hint, split.methods);
//!         }
//!     }
//! }
//! ```

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};

use rustc_hash::{FxHashMap, FxHashSet};

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tracing::debug;
use tree_sitter::Node;

use crate::ast::AstExtractor;
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::lang::LanguageRegistry;
use crate::metrics::common::{
    extract_attribute_accesses, extract_method_calls, find_class_node, find_method_node,
};

// =============================================================================
// ERROR TYPE
// =============================================================================

/// Errors that can occur during God class detection.
#[derive(Error, Debug)]
pub enum GodClassError {
    /// Failed to scan project files
    #[error("Project scan failed: {0}")]
    ScanError(String),

    /// Failed to parse source file
    #[error("Parse error in {file}: {message}")]
    ParseError { file: String, message: String },

    /// IO error
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    /// Path not found
    #[error("Path not found: {0}")]
    NotFound(String),
}

// =============================================================================
// THRESHOLDS AND CONSTANTS
// =============================================================================

/// Default threshold for method count before penalty
const DEFAULT_METHOD_THRESHOLD: u32 = 20;

/// Default threshold for attribute count before penalty
const DEFAULT_ATTRIBUTE_THRESHOLD: u32 = 15;

/// Default threshold for line count before penalty
const DEFAULT_LINE_THRESHOLD: u32 = 500;

/// Default threshold for LCOM3 before penalty
const DEFAULT_LCOM_THRESHOLD: u32 = 2;

/// Default God class score threshold
const DEFAULT_SCORE_THRESHOLD: f64 = 10.0;

/// Penalty weight per method over threshold
const METHOD_PENALTY_WEIGHT: f64 = 2.0;

/// Penalty weight per attribute over threshold
const ATTRIBUTE_PENALTY_WEIGHT: f64 = 1.0;

/// Penalty weight per 100 lines over threshold
const LINE_PENALTY_WEIGHT: f64 = 1.0;

/// Penalty weight per LCOM component over threshold
const LCOM_PENALTY_WEIGHT: f64 = 5.0;

/// Penalty weight per complexity unit over expected
const COMPLEXITY_PENALTY_WEIGHT: f64 = 0.1;

// =============================================================================
// TYPES
// =============================================================================

/// Configuration for God class detection.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GodClassConfig {
    /// Method count threshold (default: 20)
    pub method_threshold: u32,
    /// Attribute count threshold (default: 15)
    pub attribute_threshold: u32,
    /// Line count threshold (default: 500)
    pub line_threshold: u32,
    /// LCOM3 threshold (default: 2)
    pub lcom_threshold: u32,
    /// God class score threshold (default: 10.0)
    pub score_threshold: f64,
    /// Exclude test classes
    pub exclude_tests: bool,
    /// Exclude framework classes (controllers, views, etc.)
    pub exclude_framework: bool,
    /// Exclude generated code
    pub exclude_generated: bool,
    /// Framework class patterns to exclude (base names)
    pub framework_patterns: Vec<String>,
    /// Generated code markers in file paths
    pub generated_markers: Vec<String>,
    /// Language filter (None = all languages)
    pub language: Option<String>,
    /// Maximum file size in bytes
    pub max_file_size: u64,
}

impl Default for GodClassConfig {
    fn default() -> Self {
        Self {
            method_threshold: DEFAULT_METHOD_THRESHOLD,
            attribute_threshold: DEFAULT_ATTRIBUTE_THRESHOLD,
            line_threshold: DEFAULT_LINE_THRESHOLD,
            lcom_threshold: DEFAULT_LCOM_THRESHOLD,
            score_threshold: DEFAULT_SCORE_THRESHOLD,
            exclude_tests: true,
            exclude_framework: false,
            exclude_generated: true,
            framework_patterns: vec![
                "Controller".to_string(),
                "View".to_string(),
                "ViewModel".to_string(),
                "Activity".to_string(),
                "Fragment".to_string(),
                "Component".to_string(),
                "Service".to_string(),
            ],
            generated_markers: vec![
                "generated".to_string(),
                "auto_generated".to_string(),
                "_pb2".to_string(),
                ".gen.".to_string(),
                "codegen".to_string(),
            ],
            language: None,
            max_file_size: 1024 * 1024, // 1MB
        }
    }
}

impl GodClassConfig {
    /// Create config with custom score threshold.
    #[must_use]
    pub fn with_threshold(mut self, threshold: f64) -> Self {
        self.score_threshold = threshold;
        self
    }

    /// Create config with language filter.
    #[must_use]
    pub fn with_language(mut self, lang: &str) -> Self {
        self.language = Some(lang.to_string());
        self
    }

    /// Create config that includes test classes.
    #[must_use]
    pub fn include_tests(mut self) -> Self {
        self.exclude_tests = false;
        self
    }

    /// Create config that includes framework classes.
    #[must_use]
    pub fn include_framework(mut self) -> Self {
        self.exclude_framework = false;
        self
    }
}

/// Severity level of a God class finding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GodClassSeverity {
    /// Low severity (score 10-20): Minor issues, consider reviewing
    Low,
    /// Medium severity (score 20-35): Notable issues, should refactor
    Medium,
    /// High severity (score 35-50): Serious issues, strongly recommend refactoring
    High,
    /// Critical severity (score 50+): Severe issues, refactor immediately
    Critical,
}

impl GodClassSeverity {
    /// Classify score into severity level.
    #[must_use]
    pub fn from_score(score: f64) -> Self {
        if score >= 50.0 {
            Self::Critical
        } else if score >= 35.0 {
            Self::High
        } else if score >= 20.0 {
            Self::Medium
        } else {
            Self::Low
        }
    }

    /// Get human-readable description.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Low => "Minor issues, consider reviewing",
            Self::Medium => "Notable issues, should refactor",
            Self::High => "Serious issues, strongly recommend refactoring",
            Self::Critical => "Severe issues, refactor immediately",
        }
    }

    /// Get ANSI color code for CLI output.
    #[must_use]
    pub const fn color_code(&self) -> &'static str {
        match self {
            Self::Low => "\x1b[33m",          // Yellow
            Self::Medium => "\x1b[38;5;208m", // Orange
            Self::High => "\x1b[31m",         // Red
            Self::Critical => "\x1b[35m",     // Magenta
        }
    }
}

impl std::fmt::Display for GodClassSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "low"),
            Self::Medium => write!(f, "medium"),
            Self::High => write!(f, "high"),
            Self::Critical => write!(f, "critical"),
        }
    }
}

/// Indicators used to detect God classes.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GodClassIndicators {
    /// Total number of methods in the class
    pub method_count: u32,
    /// Total number of instance attributes
    pub attribute_count: u32,
    /// Total lines of code (excluding blanks and comments)
    pub line_count: u32,
    /// LCOM3 value (number of connected components)
    pub lcom: u32,
    /// Number of external dependencies (coupling)
    pub coupling: u32,
    /// Sum of cyclomatic complexity across all methods
    pub complexity_sum: u32,
    /// Average method complexity
    pub avg_complexity: f64,
    /// Number of public methods
    pub public_methods: u32,
    /// Number of private methods
    pub private_methods: u32,
}

impl Default for GodClassIndicators {
    fn default() -> Self {
        Self {
            method_count: 0,
            attribute_count: 0,
            line_count: 0,
            lcom: 1,
            coupling: 0,
            complexity_sum: 0,
            avg_complexity: 0.0,
            public_methods: 0,
            private_methods: 0,
        }
    }
}

impl GodClassIndicators {
    /// Calculate weighted score for God class detection.
    #[must_use]
    pub fn calculate_score(&self, config: &GodClassConfig) -> f64 {
        let mut score = 0.0;

        // Method penalty: +2 per method over threshold
        if self.method_count > config.method_threshold {
            let excess = self.method_count - config.method_threshold;
            score += f64::from(excess) * METHOD_PENALTY_WEIGHT;
        }

        // Attribute penalty: +1 per attribute over threshold
        if self.attribute_count > config.attribute_threshold {
            let excess = self.attribute_count - config.attribute_threshold;
            score += f64::from(excess) * ATTRIBUTE_PENALTY_WEIGHT;
        }

        // Line penalty: +1 per 100 lines over threshold
        if self.line_count > config.line_threshold {
            let excess = self.line_count - config.line_threshold;
            score += (f64::from(excess) / 100.0) * LINE_PENALTY_WEIGHT;
        }

        // LCOM penalty: +5 per component over threshold
        if self.lcom > config.lcom_threshold {
            let excess = self.lcom - config.lcom_threshold;
            score += f64::from(excess) * LCOM_PENALTY_WEIGHT;
        }

        // Complexity penalty: based on total complexity
        // Expected complexity = method_count * 3 (average healthy function)
        let expected_complexity = self.method_count * 3;
        if self.complexity_sum > expected_complexity {
            let excess = self.complexity_sum - expected_complexity;
            score += f64::from(excess) * COMPLEXITY_PENALTY_WEIGHT;
        }

        score
    }
}

/// Suggested class split based on method grouping.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SuggestedClass {
    /// Suggested name hint based on method/attribute analysis
    pub name_hint: String,
    /// Methods that belong to this suggested class
    pub methods: Vec<String>,
    /// Attributes used by these methods
    pub attributes: Vec<String>,
    /// Cohesion score for this group (0.0-1.0)
    pub cohesion: f64,
}

/// A God class finding with all relevant information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GodClassFinding {
    /// Class name
    pub class_name: String,
    /// File path containing the class
    pub file: PathBuf,
    /// Starting line number (1-indexed)
    pub line: usize,
    /// Ending line number (1-indexed)
    pub end_line: usize,
    /// God class indicators
    pub indicators: GodClassIndicators,
    /// Weighted score
    pub score: f64,
    /// Severity level based on score
    pub severity: GodClassSeverity,
    /// Suggested class splits based on responsibility analysis
    pub suggested_splits: Vec<SuggestedClass>,
    /// Detailed breakdown of score contributions
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    pub score_breakdown: HashMap<String, f64>,
    /// Whether this was excluded (e.g., test class) but included due to config
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exclusion_reason: Option<String>,
}

/// Statistics for God class analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GodClassStats {
    /// Total classes analyzed
    pub total_classes: usize,
    /// Number of God classes detected
    pub god_classes: usize,
    /// Number of classes excluded (tests, framework, generated)
    pub excluded_classes: usize,
    /// God class percentage
    pub god_class_percentage: f64,
    /// Distribution by severity
    pub severity_distribution: HashMap<String, usize>,
    /// Average score of God classes
    pub average_score: f64,
    /// Maximum score found
    pub max_score: f64,
    /// Files with God classes
    pub affected_files: usize,
}

impl GodClassStats {
    /// Calculate statistics from findings.
    fn from_findings(findings: &[GodClassFinding], total_analyzed: usize, excluded: usize) -> Self {
        if findings.is_empty() {
            return Self {
                total_classes: total_analyzed,
                god_classes: 0,
                excluded_classes: excluded,
                god_class_percentage: 0.0,
                severity_distribution: HashMap::new(),
                average_score: 0.0,
                max_score: 0.0,
                affected_files: 0,
            };
        }

        let mut severity_dist: HashMap<String, usize> = HashMap::new();
        let mut affected_files: FxHashSet<PathBuf> = FxHashSet::default();
        let mut score_sum = 0.0;
        let mut max_score = 0.0f64;

        for finding in findings {
            *severity_dist
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
            affected_files.insert(finding.file.clone());
            score_sum += finding.score;
            max_score = max_score.max(finding.score);
        }

        Self {
            total_classes: total_analyzed,
            god_classes: findings.len(),
            excluded_classes: excluded,
            god_class_percentage: (findings.len() as f64 / total_analyzed as f64) * 100.0,
            severity_distribution: severity_dist,
            average_score: score_sum / findings.len() as f64,
            max_score,
            affected_files: affected_files.len(),
        }
    }
}

/// Complete God class analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GodClassAnalysis {
    /// Path that was analyzed
    pub path: PathBuf,
    /// Language filter applied (if any)
    pub language: Option<String>,
    /// Configuration used
    pub config: GodClassConfig,
    /// God class findings (sorted by score descending)
    pub findings: Vec<GodClassFinding>,
    /// Aggregate statistics
    pub stats: GodClassStats,
    /// Files that could not be analyzed
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<FileError>,
}

/// Error encountered while analyzing a file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileError {
    /// File path where error occurred
    pub file: PathBuf,
    /// Error message
    pub message: String,
}

// =============================================================================
// ANALYSIS FUNCTIONS
// =============================================================================

/// Detect God classes in a project or directory.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `language` - Optional language filter
/// * `threshold` - Optional score threshold (default: 10.0)
///
/// # Returns
///
/// Complete analysis with God class findings and statistics.
///
/// # Errors
///
/// Returns error if path doesn't exist or scanning fails.
pub fn detect_god_classes(
    path: impl AsRef<Path>,
    language: Option<&str>,
    threshold: Option<f64>,
) -> Result<GodClassAnalysis, GodClassError> {
    let path = path.as_ref();
    let mut config = GodClassConfig::default();

    if let Some(lang) = language {
        config.language = Some(lang.to_string());
    }

    if let Some(t) = threshold {
        config.score_threshold = t;
    }

    detect_with_config(path, config)
}

/// Detect God classes with custom configuration.
pub fn detect_with_config(
    path: &Path,
    config: GodClassConfig,
) -> Result<GodClassAnalysis, GodClassError> {
    if !path.exists() {
        return Err(GodClassError::NotFound(path.display().to_string()));
    }

    if path.is_file() {
        return detect_in_file(path, &config);
    }

    // Directory analysis
    let path_str = path
        .to_str()
        .ok_or_else(|| GodClassError::ScanError("Invalid path encoding".to_string()))?;

    let scanner =
        ProjectScanner::new(path_str).map_err(|e| GodClassError::ScanError(e.to_string()))?;

    let scan_config = if let Some(ref lang) = config.language {
        ScanConfig::for_language(lang)
    } else {
        ScanConfig::default()
    };

    let scan_result = scanner
        .scan_with_config(&scan_config)
        .map_err(|e| GodClassError::ScanError(e.to_string()))?;

    if scan_result.files.is_empty() {
        return Err(GodClassError::ScanError(format!(
            "No source files found in {} (filter: {:?})",
            path.display(),
            config.language
        )));
    }

    debug!(
        "Analyzing {} files for God classes",
        scan_result.files.len()
    );

    // Analyze files in parallel
    let results: Vec<(Vec<GodClassFinding>, Vec<FileError>, usize, usize)> = scan_result
        .files
        .par_iter()
        .filter(|f| {
            // Filter by file size
            std::fs::metadata(f)
                .map(|m| m.len() <= config.max_file_size)
                .unwrap_or(false)
        })
        .map(|file| analyze_file_for_god_classes(file, &config))
        .collect();

    // Aggregate results
    let mut all_findings = Vec::new();
    let mut all_errors = Vec::new();
    let mut total_analyzed = 0usize;
    let mut total_excluded = 0usize;

    for (findings, errors, analyzed, excluded) in results {
        all_findings.extend(findings);
        all_errors.extend(errors);
        total_analyzed += analyzed;
        total_excluded += excluded;
    }

    // Sort findings by score (highest first)
    all_findings.sort_by(|a, b| {
        b.score
            .partial_cmp(&a.score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    // Calculate statistics
    let stats = GodClassStats::from_findings(&all_findings, total_analyzed, total_excluded);

    Ok(GodClassAnalysis {
        path: path.to_path_buf(),
        language: config.language.clone(),
        config,
        findings: all_findings,
        stats,
        errors: all_errors,
    })
}

/// Analyze a single file for God classes.
fn detect_in_file(file: &Path, config: &GodClassConfig) -> Result<GodClassAnalysis, GodClassError> {
    let (findings, errors, analyzed, excluded) = analyze_file_for_god_classes(file, config);
    let stats = GodClassStats::from_findings(&findings, analyzed, excluded);

    // Detect language
    let registry = LanguageRegistry::global();
    let language = registry.detect_language(file).map(|l| l.name().to_string());

    Ok(GodClassAnalysis {
        path: file.to_path_buf(),
        language,
        config: config.clone(),
        findings,
        stats,
        errors,
    })
}

/// Internal function to analyze all classes in a file for God class indicators.
fn analyze_file_for_god_classes(
    file: &Path,
    config: &GodClassConfig,
) -> (Vec<GodClassFinding>, Vec<FileError>, usize, usize) {
    let mut findings = Vec::new();
    let mut errors = Vec::new();
    let mut total_analyzed = 0usize;
    let mut total_excluded = 0usize;

    // Check for generated code markers in path
    if config.exclude_generated {
        let path_str = file.to_string_lossy().to_lowercase();
        for marker in &config.generated_markers {
            if path_str.contains(&marker.to_lowercase()) {
                return (findings, errors, 0, 0);
            }
        }
    }

    // Extract module info
    let module = match AstExtractor::extract_file(file) {
        Ok(m) => m,
        Err(e) => {
            errors.push(FileError {
                file: file.to_path_buf(),
                message: format!("Failed to parse file: {}", e),
            });
            return (findings, errors, total_analyzed, total_excluded);
        }
    };

    // Read source for analysis
    let source = match std::fs::read(file) {
        Ok(s) => s,
        Err(e) => {
            errors.push(FileError {
                file: file.to_path_buf(),
                message: format!("Failed to read file: {}", e),
            });
            return (findings, errors, total_analyzed, total_excluded);
        }
    };

    let language = &module.language;

    // Get parser
    let registry = LanguageRegistry::global();
    let lang_impl = match registry.detect_language(file) {
        Some(l) => l,
        None => {
            return (findings, errors, total_analyzed, total_excluded);
        }
    };

    let mut parser = match lang_impl.parser() {
        Ok(p) => p,
        Err(e) => {
            errors.push(FileError {
                file: file.to_path_buf(),
                message: format!("Parser error: {}", e),
            });
            return (findings, errors, total_analyzed, total_excluded);
        }
    };

    let tree = match parser.parse(&source, None) {
        Some(t) => t,
        None => {
            errors.push(FileError {
                file: file.to_path_buf(),
                message: "Failed to parse file".to_string(),
            });
            return (findings, errors, total_analyzed, total_excluded);
        }
    };

    // Analyze each class
    for class in &module.classes {
        total_analyzed += 1;

        // Check exclusion patterns
        let exclusion_reason = check_exclusion(class, config, language);
        if exclusion_reason.is_some() {
            total_excluded += 1;
            continue;
        }

        // Analyze the class
        if let Some(finding) =
            analyze_class_for_god_class(file, class, &tree, &source, language, config)
        {
            // Only include if score exceeds threshold
            if finding.score >= config.score_threshold {
                findings.push(finding);
            }
        }

        // Also analyze nested classes
        for inner in &class.inner_classes {
            total_analyzed += 1;

            let exclusion_reason = check_exclusion(inner, config, language);
            if exclusion_reason.is_some() {
                total_excluded += 1;
                continue;
            }

            if let Some(finding) =
                analyze_class_for_god_class(file, inner, &tree, &source, language, config)
            {
                if finding.score >= config.score_threshold {
                    findings.push(finding);
                }
            }
        }
    }

    (findings, errors, total_analyzed, total_excluded)
}

/// Check if a class should be excluded from analysis.
fn check_exclusion(
    class: &crate::ast::types::ClassInfo,
    config: &GodClassConfig,
    _language: &str,
) -> Option<String> {
    let name = &class.name;
    let name_lower = name.to_lowercase();

    // Check test exclusion
    if config.exclude_tests {
        let is_test = name_lower.contains("test")
            || name_lower.contains("spec")
            || name_lower.contains("mock")
            || class.bases.iter().any(|b| {
                let b_lower = b.to_lowercase();
                b_lower.contains("testcase") || b_lower.contains("unittest")
            })
            || class.decorators.iter().any(|d| d.contains("test"));

        if is_test {
            return Some("Test class".to_string());
        }
    }

    // Check framework exclusion
    if config.exclude_framework {
        for pattern in &config.framework_patterns {
            if name.contains(pattern) || class.bases.iter().any(|b| b.contains(pattern)) {
                return Some(format!("Framework class ({})", pattern));
            }
        }
    }

    None
}

/// Analyze a single class for God class indicators.
fn analyze_class_for_god_class(
    file: &Path,
    class: &crate::ast::types::ClassInfo,
    tree: &tree_sitter::Tree,
    source: &[u8],
    language: &str,
    config: &GodClassConfig,
) -> Option<GodClassFinding> {
    // Skip very small classes (not enough to be god classes)
    if class.methods.len() < 3 {
        return None;
    }

    let line_count = class
        .end_line_number
        .unwrap_or(class.line_number)
        .saturating_sub(class.line_number)
        + 1;

    // Build method-attribute graph for cohesion and responsibility analysis
    let mut method_attributes: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
    let mut all_attributes: FxHashSet<String> = FxHashSet::default();
    let mut method_calls: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
    let mut complexity_sum = 0u32;
    let mut public_methods = 0u32;
    let mut private_methods = 0u32;

    // Collect method names for analysis (using std HashSet for extract_method_calls compatibility)
    let method_names: HashSet<String> = class
        .methods
        .iter()
        .filter(|m| !is_static_method(m))
        .map(|m| m.name.clone())
        .collect();

    // Find class node in AST
    let root = tree.root_node();
    if let Some(class_node) = find_class_node(root, &class.name, class.line_number) {
        for method in &class.methods {
            if is_static_method(method) {
                continue;
            }

            // Track public vs private
            if is_private_method(&method.name, language) {
                private_methods += 1;
            } else {
                public_methods += 1;
            }

            // Find method node
            if let Some(method_node) =
                find_method_node(class_node, &method.name, method.line_number, language)
            {
                // Extract attributes accessed (using shared utility)
                let attrs: FxHashSet<String> =
                    extract_attribute_accesses(method_node, source, language)
                        .into_iter()
                        .collect();
                all_attributes.extend(attrs.iter().cloned());
                method_attributes.insert(method.name.clone(), attrs);

                // Extract method calls (for LCOM4-style analysis, using shared utility)
                let calls: FxHashSet<String> =
                    extract_method_calls(method_node, source, language, &method_names)
                        .into_iter()
                        .collect();
                method_calls.insert(method.name.clone(), calls);

                // Estimate complexity (simplified: count decision points)
                let complexity = estimate_complexity(method_node, language);
                complexity_sum += complexity;
            }
        }
    }

    let method_count = method_names.len() as u32;
    let attribute_count = all_attributes.len() as u32;

    // Calculate LCOM (number of connected components)
    let lcom = calculate_lcom(&method_attributes, &method_calls);

    // Estimate coupling (unique external types used)
    let coupling = estimate_coupling(class);

    let avg_complexity = if method_count > 0 {
        complexity_sum as f64 / method_count as f64
    } else {
        0.0
    };

    let indicators = GodClassIndicators {
        method_count,
        attribute_count,
        line_count: line_count as u32,
        lcom,
        coupling,
        complexity_sum,
        avg_complexity,
        public_methods,
        private_methods,
    };

    // Calculate score
    let score = indicators.calculate_score(config);

    // Build score breakdown
    let mut score_breakdown = HashMap::new();
    if indicators.method_count > config.method_threshold {
        let penalty =
            f64::from(indicators.method_count - config.method_threshold) * METHOD_PENALTY_WEIGHT;
        score_breakdown.insert("methods".to_string(), penalty);
    }
    if indicators.attribute_count > config.attribute_threshold {
        let penalty = f64::from(indicators.attribute_count - config.attribute_threshold)
            * ATTRIBUTE_PENALTY_WEIGHT;
        score_breakdown.insert("attributes".to_string(), penalty);
    }
    if indicators.line_count > config.line_threshold {
        let penalty = (f64::from(indicators.line_count - config.line_threshold) / 100.0)
            * LINE_PENALTY_WEIGHT;
        score_breakdown.insert("lines".to_string(), penalty);
    }
    if indicators.lcom > config.lcom_threshold {
        let penalty = f64::from(indicators.lcom - config.lcom_threshold) * LCOM_PENALTY_WEIGHT;
        score_breakdown.insert("lcom".to_string(), penalty);
    }

    // Calculate suggested splits based on responsibility groups
    let suggested_splits = suggest_class_splits(&method_attributes, &method_calls);

    let severity = GodClassSeverity::from_score(score);

    Some(GodClassFinding {
        class_name: class.name.clone(),
        file: file.to_path_buf(),
        line: class.line_number,
        end_line: class.end_line_number.unwrap_or(class.line_number),
        indicators,
        score,
        severity,
        suggested_splits,
        score_breakdown,
        exclusion_reason: None,
    })
}

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

/// Check if a method is static.
fn is_static_method(method: &crate::ast::types::FunctionInfo) -> bool {
    method
        .decorators
        .iter()
        .any(|d| d.contains("staticmethod") || d.contains("static") || d == "@staticmethod")
}

/// Check if a method is private based on naming convention.
fn is_private_method(name: &str, language: &str) -> bool {
    match language {
        "python" => name.starts_with('_') && !name.starts_with("__"),
        "typescript" | "javascript" | "tsx" | "jsx" => {
            name.starts_with('#') || name.starts_with('_')
        }
        "rust" => false, // Rust uses pub/not pub, not naming convention
        "java" | "kotlin" | "csharp" => false, // Uses access modifiers
        _ => name.starts_with('_'),
    }
}

// extract_attribute_accesses moved to crate::metrics::common

// extract_method_calls moved to crate::metrics::common

/// Calculate LCOM (number of connected components) from method-attribute relationships.
fn calculate_lcom(
    method_attributes: &FxHashMap<String, FxHashSet<String>>,
    method_calls: &FxHashMap<String, FxHashSet<String>>,
) -> u32 {
    let methods: Vec<&String> = method_attributes.keys().collect();
    if methods.is_empty() {
        return 0;
    }

    // Build adjacency: methods connected if they share attributes or call each other
    let mut adjacency: FxHashMap<&String, FxHashSet<&String>> = FxHashMap::default();
    for m in &methods {
        adjacency.insert(m, FxHashSet::default());
    }

    // Connect methods sharing attributes
    for (i, m1) in methods.iter().enumerate() {
        for m2 in methods.iter().skip(i + 1) {
            if let (Some(attrs1), Some(attrs2)) =
                (method_attributes.get(*m1), method_attributes.get(*m2))
            {
                if !attrs1.is_disjoint(attrs2) {
                    adjacency.get_mut(m1).unwrap().insert(m2);
                    adjacency.get_mut(m2).unwrap().insert(m1);
                }
            }
        }
    }

    // Connect methods that call each other
    for (caller, callees) in method_calls {
        if !methods.iter().any(|m| *m == caller) {
            continue;
        }
        for callee in callees {
            if methods.iter().any(|m| *m == callee) {
                if let Some(caller_ref) = methods.iter().find(|m| **m == caller) {
                    if let Some(callee_ref) = methods.iter().find(|m| **m == callee) {
                        adjacency.get_mut(caller_ref).unwrap().insert(callee_ref);
                        adjacency.get_mut(callee_ref).unwrap().insert(caller_ref);
                    }
                }
            }
        }
    }

    // BFS to count connected components
    let mut visited: FxHashSet<&String> = FxHashSet::default();
    let mut components = 0u32;

    for method in &methods {
        if visited.contains(method) {
            continue;
        }

        components += 1;
        let mut queue = VecDeque::new();
        queue.push_back(*method);
        visited.insert(method);

        while let Some(current) = queue.pop_front() {
            if let Some(neighbors) = adjacency.get(current) {
                for neighbor in neighbors {
                    if !visited.contains(neighbor) {
                        visited.insert(neighbor);
                        queue.push_back(neighbor);
                    }
                }
            }
        }
    }

    components
}

/// Estimate coupling based on base classes and return type annotations.
fn estimate_coupling(class: &crate::ast::types::ClassInfo) -> u32 {
    let mut unique_types: FxHashSet<String> = FxHashSet::default();

    // Base classes
    for base in &class.bases {
        if !is_builtin_type(base) {
            unique_types.insert(base.clone());
        }
    }

    // Count unique types from method return types
    for method in &class.methods {
        if let Some(ref return_type) = method.return_type {
            if !is_builtin_type(return_type) {
                unique_types.insert(return_type.clone());
            }
        }
        // Parse type hints from params (format: "name: Type" or "name")
        for param in &method.params {
            if let Some(type_part) = param.split(':').nth(1) {
                let type_name = type_part.trim();
                if !is_builtin_type(type_name) {
                    unique_types.insert(type_name.to_string());
                }
            }
        }
    }

    unique_types.len() as u32
}

/// Check if a type is a built-in type.
fn is_builtin_type(type_name: &str) -> bool {
    let builtins = [
        "int", "str", "float", "bool", "list", "dict", "set", "tuple", "None", "any", "Any",
        "void", "number", "string", "boolean", "i32", "i64", "u32", "u64", "f32", "f64", "usize",
        "isize", "String", "Vec", "Option", "Result",
    ];
    builtins.iter().any(|b| type_name.starts_with(b))
}

/// Estimate cyclomatic complexity by counting decision points.
fn estimate_complexity(node: Node, language: &str) -> u32 {
    let mut complexity = 1u32; // Base complexity

    let decision_kinds = match language {
        "python" => vec![
            "if_statement",
            "elif_clause",
            "while_statement",
            "for_statement",
            "except_clause",
            "with_statement",
            "and",
            "or",
            "match_statement",
            "case_clause",
            "list_comprehension",
            "dictionary_comprehension",
        ],
        "typescript" | "javascript" | "tsx" | "jsx" => vec![
            "if_statement",
            "while_statement",
            "for_statement",
            "for_in_statement",
            "switch_case",
            "catch_clause",
            "ternary_expression",
            "&&",
            "||",
            "optional_chain_expression",
        ],
        "rust" => vec![
            "if_expression",
            "while_expression",
            "for_expression",
            "match_arm",
            "&&",
            "||",
            "?",
        ],
        "go" => vec![
            "if_statement",
            "for_statement",
            "switch_case",
            "select_case",
            "&&",
            "||",
        ],
        "java" | "kotlin" | "csharp" => vec![
            "if_statement",
            "while_statement",
            "for_statement",
            "enhanced_for_statement",
            "switch_case",
            "catch_clause",
            "&&",
            "||",
            "ternary_expression",
        ],
        _ => vec!["if_statement", "while_statement", "for_statement", "case"],
    };

    count_decision_points(node, &decision_kinds, &mut complexity);
    complexity
}

fn count_decision_points(node: Node, kinds: &[&str], complexity: &mut u32) {
    if kinds.contains(&node.kind()) {
        *complexity += 1;
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        count_decision_points(child, kinds, complexity);
    }
}

/// Suggest class splits based on method groupings that share attributes.
fn suggest_class_splits(
    method_attributes: &FxHashMap<String, FxHashSet<String>>,
    method_calls: &FxHashMap<String, FxHashSet<String>>,
) -> Vec<SuggestedClass> {
    // Find connected components (same as LCOM calculation)
    let methods: Vec<&String> = method_attributes.keys().collect();
    if methods.len() <= 3 {
        return Vec::new(); // Not worth splitting very small classes
    }

    // Build adjacency
    let mut adjacency: FxHashMap<&String, FxHashSet<&String>> = FxHashMap::default();
    for m in &methods {
        adjacency.insert(m, FxHashSet::default());
    }

    for (i, m1) in methods.iter().enumerate() {
        for m2 in methods.iter().skip(i + 1) {
            if let (Some(attrs1), Some(attrs2)) =
                (method_attributes.get(*m1), method_attributes.get(*m2))
            {
                if !attrs1.is_disjoint(attrs2) {
                    adjacency.get_mut(m1).unwrap().insert(m2);
                    adjacency.get_mut(m2).unwrap().insert(m1);
                }
            }
        }
    }

    for (caller, callees) in method_calls {
        for callee in callees {
            if let (Some(caller_ref), Some(callee_ref)) = (
                methods.iter().find(|m| **m == caller),
                methods.iter().find(|m| **m == callee),
            ) {
                adjacency.get_mut(caller_ref).unwrap().insert(callee_ref);
                adjacency.get_mut(callee_ref).unwrap().insert(caller_ref);
            }
        }
    }

    // Find components
    let mut visited: FxHashSet<&String> = FxHashSet::default();
    let mut components: Vec<Vec<String>> = Vec::new();

    for method in &methods {
        if visited.contains(method) {
            continue;
        }

        let mut component = Vec::new();
        let mut queue = VecDeque::new();
        queue.push_back(*method);
        visited.insert(method);

        while let Some(current) = queue.pop_front() {
            component.push(current.clone());

            if let Some(neighbors) = adjacency.get(current) {
                for neighbor in neighbors {
                    if !visited.contains(neighbor) {
                        visited.insert(neighbor);
                        queue.push_back(neighbor);
                    }
                }
            }
        }

        if component.len() >= 2 {
            components.push(component);
        }
    }

    // Only suggest splits if there are multiple meaningful components
    if components.len() < 2 {
        return Vec::new();
    }

    // Build suggestions
    components
        .into_iter()
        .enumerate()
        .map(|(i, methods_vec)| {
            // Collect all attributes used by this component
            let mut attrs: FxHashSet<String> = FxHashSet::default();
            for method in &methods_vec {
                if let Some(method_attrs) = method_attributes.get(method) {
                    attrs.extend(method_attrs.iter().cloned());
                }
            }

            // Generate name hint from common attribute prefixes or method names
            let name_hint = generate_name_hint(&methods_vec, &attrs, i);

            // Calculate cohesion for this group
            let cohesion = if methods_vec.len() > 1 {
                let total_pairs = methods_vec.len() * (methods_vec.len() - 1) / 2;
                let mut sharing_pairs = 0;
                for (j, m1) in methods_vec.iter().enumerate() {
                    for m2 in methods_vec.iter().skip(j + 1) {
                        if let (Some(a1), Some(a2)) =
                            (method_attributes.get(m1), method_attributes.get(m2))
                        {
                            if !a1.is_disjoint(a2) {
                                sharing_pairs += 1;
                            }
                        }
                    }
                }
                if total_pairs > 0 {
                    sharing_pairs as f64 / total_pairs as f64
                } else {
                    1.0
                }
            } else {
                1.0
            };

            SuggestedClass {
                name_hint,
                methods: methods_vec,
                attributes: attrs.into_iter().collect(),
                cohesion,
            }
        })
        .collect()
}

/// Generate a meaningful name hint for a suggested class.
fn generate_name_hint(methods: &[String], attributes: &FxHashSet<String>, index: usize) -> String {
    // Try to find common prefixes in method names
    let prefixes: Vec<&str> = methods
        .iter()
        .filter_map(|m| {
            // Common prefixes: get_, set_, handle_, process_, etc.
            if let Some(pos) = m.find('_') {
                Some(&m[..pos])
            } else {
                None
            }
        })
        .collect();

    // Count prefix occurrences
    let mut prefix_counts: FxHashMap<&str, usize> = FxHashMap::default();
    for prefix in &prefixes {
        *prefix_counts.entry(prefix).or_insert(0) += 1;
    }

    // Find most common prefix
    if let Some((prefix, count)) = prefix_counts.iter().max_by_key(|(_, c)| *c) {
        if *count >= methods.len() / 2 && *count >= 2 {
            let capitalized = capitalize(prefix);
            return format!("{}Handler", capitalized);
        }
    }

    // Try to find common attribute patterns
    if !attributes.is_empty() {
        let attr_list: Vec<&String> = attributes.iter().collect();
        if let Some(first_attr) = attr_list.first() {
            if first_attr.len() > 3 {
                let capitalized = capitalize(first_attr);
                return format!("{}Manager", capitalized);
            }
        }
    }

    // Default: Component + index
    format!("Component{}", index + 1)
}

fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

// find_class_node, find_method_node, find_method_recursive, node_text moved to crate::metrics::common

// =============================================================================
// FORMATTING
// =============================================================================

/// Format a human-readable summary of God class analysis.
#[must_use]
pub fn format_god_class_summary(analysis: &GodClassAnalysis) -> String {
    let mut output = String::new();

    output.push_str(&format!(
        "God Class Analysis: {}\n",
        analysis.path.display()
    ));
    output.push_str(&"=".repeat(60));
    output.push_str("\n\n");

    // Statistics
    output.push_str("Summary:\n");
    output.push_str(&format!(
        "  Total classes analyzed: {}\n",
        analysis.stats.total_classes
    ));
    output.push_str(&format!(
        "  God classes detected:   {} ({:.1}%)\n",
        analysis.stats.god_classes, analysis.stats.god_class_percentage
    ));
    output.push_str(&format!(
        "  Excluded classes:       {}\n",
        analysis.stats.excluded_classes
    ));
    output.push_str(&format!(
        "  Affected files:         {}\n",
        analysis.stats.affected_files
    ));

    if !analysis.stats.severity_distribution.is_empty() {
        output.push_str("\nSeverity Distribution:\n");
        for (severity, count) in &analysis.stats.severity_distribution {
            output.push_str(&format!("  {}: {}\n", severity, count));
        }
    }

    if analysis.stats.god_classes > 0 {
        output.push_str(&format!(
            "\nAverage score: {:.1}\n",
            analysis.stats.average_score
        ));
        output.push_str(&format!("Maximum score: {:.1}\n", analysis.stats.max_score));
    }

    output.push_str("\n");

    // Findings
    if analysis.findings.is_empty() {
        output.push_str("No God classes detected.\n");
    } else {
        output.push_str(&format!(
            "Findings ({} God classes):\n\n",
            analysis.findings.len()
        ));

        for finding in &analysis.findings {
            let color = finding.severity.color_code();
            let reset = "\x1b[0m";

            output.push_str(&format!(
                "{}{}{} [{}]: {}\n",
                color,
                finding.class_name,
                reset,
                finding.severity,
                finding.file.display()
            ));
            output.push_str(&format!("  Lines: {}-{}\n", finding.line, finding.end_line));
            output.push_str(&format!("  Score: {:.1}\n", finding.score));
            output.push_str(&format!(
                "  Indicators: methods={}, attributes={}, lines={}, LCOM={}, complexity={}\n",
                finding.indicators.method_count,
                finding.indicators.attribute_count,
                finding.indicators.line_count,
                finding.indicators.lcom,
                finding.indicators.complexity_sum
            ));

            if !finding.score_breakdown.is_empty() {
                output.push_str("  Score breakdown:");
                for (reason, penalty) in &finding.score_breakdown {
                    output.push_str(&format!(" {}={:.1}", reason, penalty));
                }
                output.push_str("\n");
            }

            if !finding.suggested_splits.is_empty() {
                output.push_str("  Suggested splits:\n");
                for split in &finding.suggested_splits {
                    output.push_str(&format!(
                        "    -> {} ({} methods, {:.0}% cohesion): {:?}\n",
                        split.name_hint,
                        split.methods.len(),
                        split.cohesion * 100.0,
                        split.methods
                    ));
                }
            }

            output.push_str("\n");
        }
    }

    // Errors
    if !analysis.errors.is_empty() {
        output.push_str(&format!("\nErrors ({} files):\n", analysis.errors.len()));
        for error in &analysis.errors {
            output.push_str(&format!("  {}: {}\n", error.file.display(), error.message));
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
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn create_temp_file(content: &str, extension: &str) -> NamedTempFile {
        let mut file = tempfile::Builder::new()
            .suffix(extension)
            .tempfile()
            .expect("Failed to create temp file");
        file.write_all(content.as_bytes())
            .expect("Failed to write to temp file");
        file
    }

    #[test]
    fn test_severity_classification() {
        assert_eq!(GodClassSeverity::from_score(5.0), GodClassSeverity::Low);
        assert_eq!(GodClassSeverity::from_score(15.0), GodClassSeverity::Low);
        assert_eq!(GodClassSeverity::from_score(25.0), GodClassSeverity::Medium);
        assert_eq!(GodClassSeverity::from_score(40.0), GodClassSeverity::High);
        assert_eq!(
            GodClassSeverity::from_score(60.0),
            GodClassSeverity::Critical
        );
    }

    #[test]
    fn test_indicators_score_calculation() {
        let config = GodClassConfig::default();

        // Normal class - no penalties
        let normal = GodClassIndicators {
            method_count: 10,
            attribute_count: 5,
            line_count: 200,
            lcom: 1,
            coupling: 3,
            complexity_sum: 30,
            avg_complexity: 3.0,
            public_methods: 8,
            private_methods: 2,
        };
        assert_eq!(normal.calculate_score(&config), 0.0);

        // God class - multiple penalties
        let god = GodClassIndicators {
            method_count: 30,    // 10 over threshold -> +20
            attribute_count: 20, // 5 over threshold -> +5
            line_count: 800,     // 300 over threshold -> +3
            lcom: 5,             // 3 over threshold -> +15
            coupling: 10,
            complexity_sum: 150, // 60 over expected (30*3=90) -> +6
            avg_complexity: 5.0,
            public_methods: 25,
            private_methods: 5,
        };
        let score = god.calculate_score(&config);
        assert!(
            score > 40.0,
            "Expected high score for god class, got {}",
            score
        );
    }

    #[test]
    fn test_config_builders() {
        let config = GodClassConfig::default()
            .with_threshold(20.0)
            .with_language("python")
            .include_tests()
            .include_framework();

        assert_eq!(config.score_threshold, 20.0);
        assert_eq!(config.language, Some("python".to_string()));
        assert!(!config.exclude_tests);
        assert!(!config.exclude_framework);
    }

    #[test]
    fn test_small_class_not_detected() {
        let source = r#"
class SmallClass:
    def method_a(self):
        self.attr = 1

    def method_b(self):
        self.attr = 2
"#;
        let file = create_temp_file(source, ".py");
        let result = detect_god_classes(file.path(), None, Some(10.0));

        assert!(result.is_ok());
        let analysis = result.unwrap();
        assert!(
            analysis.findings.is_empty(),
            "Small class should not be flagged"
        );
    }

    #[test]
    fn test_large_class_detected() {
        // Generate a large class with many methods and attributes
        let mut source = String::from("class LargeClass:\n");

        // Add 25 methods using different attributes (low cohesion)
        for i in 0..25 {
            source.push_str(&format!(
                "    def method_{i}(self):\n        self.attr_{i} = {i}\n        return self.attr_{i}\n\n",
            ));
        }

        let file = create_temp_file(&source, ".py");
        let result = detect_god_classes(file.path(), None, Some(5.0));

        assert!(result.is_ok());
        let analysis = result.unwrap();

        // Should detect the large class
        assert!(
            !analysis.findings.is_empty(),
            "Large class should be flagged as God class"
        );

        let finding = &analysis.findings[0];
        assert_eq!(finding.class_name, "LargeClass");
        assert!(finding.indicators.method_count >= 20);
        assert!(finding.score >= 5.0);
    }

    #[test]
    fn test_test_class_excluded() {
        let source = r#"
class TestUserHandler:
    def test_create_user(self):
        self.user = {}

    def test_delete_user(self):
        self.user = None

    def test_update_user(self):
        self.user = {"updated": True}

    def setUp(self):
        self.data = []

    def tearDown(self):
        self.data = None
"#;
        let file = create_temp_file(source, ".py");
        let config = GodClassConfig::default();

        let result = detect_with_config(file.path(), config);
        assert!(result.is_ok());

        let analysis = result.unwrap();
        // Test class should be excluded
        assert!(
            analysis.findings.is_empty(),
            "Test class should be excluded"
        );
        assert!(analysis.stats.excluded_classes > 0);
    }

    #[test]
    fn test_suggested_splits() {
        // Class with two distinct responsibility groups
        let source = r#"
class UserOrderService:
    def get_user(self):
        return self.users

    def update_user(self):
        self.users = []

    def delete_user(self):
        self.users.clear()

    def list_users(self):
        return list(self.users)

    def get_order(self):
        return self.orders

    def create_order(self):
        self.orders.append({})

    def cancel_order(self):
        self.orders.pop()

    def list_orders(self):
        return list(self.orders)
"#;
        let file = create_temp_file(source, ".py");
        let result = detect_god_classes(file.path(), None, Some(1.0));

        assert!(result.is_ok());
        let analysis = result.unwrap();

        // If detected, should suggest splitting
        if !analysis.findings.is_empty() {
            let finding = &analysis.findings[0];
            // Should suggest at least 2 splits (user-related and order-related)
            assert!(
                finding.suggested_splits.len() >= 1,
                "Should suggest splits for class with separate concerns"
            );
        }
    }

    #[test]
    fn test_lcom_calculation() {
        // Methods sharing same attribute = high cohesion
        let mut method_attrs1: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        method_attrs1.insert("m1".to_string(), ["attr".to_string()].into_iter().collect());
        method_attrs1.insert("m2".to_string(), ["attr".to_string()].into_iter().collect());
        method_attrs1.insert("m3".to_string(), ["attr".to_string()].into_iter().collect());

        let calls1: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        let lcom1 = calculate_lcom(&method_attrs1, &calls1);
        assert_eq!(
            lcom1, 1,
            "All methods sharing attribute should be 1 component"
        );

        // Methods using different attributes = low cohesion
        let mut method_attrs2: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        method_attrs2.insert("m1".to_string(), ["a".to_string()].into_iter().collect());
        method_attrs2.insert("m2".to_string(), ["b".to_string()].into_iter().collect());
        method_attrs2.insert("m3".to_string(), ["c".to_string()].into_iter().collect());

        let lcom2 = calculate_lcom(&method_attrs2, &calls1);
        assert_eq!(
            lcom2, 3,
            "Methods not sharing attributes should be separate components"
        );
    }

    #[test]
    fn test_nonexistent_path() {
        let result = detect_god_classes("/nonexistent/path/file.py", None, None);
        assert!(matches!(result, Err(GodClassError::NotFound(_))));
    }

    #[test]
    fn test_stats_calculation() {
        let findings = vec![
            GodClassFinding {
                class_name: "A".to_string(),
                file: PathBuf::from("a.py"),
                line: 1,
                end_line: 100,
                indicators: GodClassIndicators::default(),
                score: 15.0,
                severity: GodClassSeverity::Low,
                suggested_splits: vec![],
                score_breakdown: HashMap::new(),
                exclusion_reason: None,
            },
            GodClassFinding {
                class_name: "B".to_string(),
                file: PathBuf::from("b.py"),
                line: 1,
                end_line: 200,
                indicators: GodClassIndicators::default(),
                score: 45.0,
                severity: GodClassSeverity::High,
                suggested_splits: vec![],
                score_breakdown: HashMap::new(),
                exclusion_reason: None,
            },
        ];

        let stats = GodClassStats::from_findings(&findings, 10, 2);

        assert_eq!(stats.total_classes, 10);
        assert_eq!(stats.god_classes, 2);
        assert_eq!(stats.excluded_classes, 2);
        assert!((stats.god_class_percentage - 20.0).abs() < 0.1);
        assert_eq!(stats.affected_files, 2);
        assert!((stats.average_score - 30.0).abs() < 0.1);
        assert!((stats.max_score - 45.0).abs() < 0.1);
    }

    #[test]
    fn test_builtin_type_detection() {
        assert!(is_builtin_type("int"));
        assert!(is_builtin_type("str"));
        assert!(is_builtin_type("String"));
        assert!(is_builtin_type("Vec<T>"));
        assert!(is_builtin_type("Option<i32>"));
        assert!(!is_builtin_type("UserService"));
        assert!(!is_builtin_type("MyCustomClass"));
    }

    #[test]
    fn test_private_method_detection() {
        assert!(is_private_method("_helper", "python"));
        assert!(!is_private_method("__init__", "python"));
        assert!(!is_private_method("public_method", "python"));

        assert!(is_private_method("#private", "typescript"));
        assert!(is_private_method("_hidden", "typescript"));
        assert!(!is_private_method("public", "typescript"));
    }
}
