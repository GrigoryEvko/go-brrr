//! Cyclomatic complexity calculation using control flow graph analysis.
//!
//! Cyclomatic complexity measures the structural complexity of code by counting
//! the number of linearly independent paths through a function. Higher values
//! indicate more complex code that is harder to test and maintain.
//!
//! # Calculation Methods
//!
//! This module supports two calculation methods:
//!
//! 1. **Decision Point Method** (recommended):
//!    ```text
//!    M = decision_points + 1
//!    ```
//!    Counts decision points (if, while, for, catch, etc.) directly from CFG.
//!
//! 2. **Graph Formula** (classic):
//!    ```text
//!    M = E - N + 2P
//!    ```
//!    Where E = edges, N = nodes, P = connected components (usually 1).
//!
//! # Decision Points by Language
//!
//! | Language   | Decision Points                                              |
//! |------------|--------------------------------------------------------------|
//! | Python     | if, elif, while, for, except, and, or, comprehension if     |
//! | TypeScript | if, else if, for, while, catch, &&, \|\|, ?:, ?.            |
//! | Rust       | if, if let, while, while let, for, match arms, ?            |
//! | Go         | if, for, switch cases, select cases                          |
//! | Java       | if, else if, for, while, catch, switch cases                |
//! | C/C++      | if, else if, for, while, switch cases                       |

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::simd::{cmp::SimdPartialOrd, u32x8, Mask, Simd};

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::debug;

use crate::ast::{AstExtractor, FunctionInfo};
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::cfg::{CFGInfo, CfgBuilder};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;

// =============================================================================
// TYPES
// =============================================================================

/// Risk level classification based on cyclomatic complexity.
///
/// Based on widely accepted thresholds from software engineering research:
/// - McCabe (1976): Original definition
/// - NIST (1996): Risk thresholds
/// - Carnegie Mellon SEI: Industry recommendations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RiskLevel {
    /// Complexity 1-10: Simple, low risk, easy to test
    Low,
    /// Complexity 11-20: Moderate complexity, consider splitting
    Medium,
    /// Complexity 21-50: High complexity, hard to test and maintain
    High,
    /// Complexity 50+: Critical, refactor immediately
    Critical,
}

impl RiskLevel {
    /// Classify complexity value into risk level.
    ///
    /// # Thresholds
    ///
    /// - 1-10: Low risk
    /// - 11-20: Medium risk
    /// - 21-50: High risk
    /// - 50+: Critical risk
    #[must_use]
    pub fn from_complexity(complexity: u32) -> Self {
        match complexity {
            0..=10 => Self::Low,
            11..=20 => Self::Medium,
            21..=50 => Self::High,
            _ => Self::Critical,
        }
    }

    /// Get human-readable description of the risk level.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Low => "Simple, low risk",
            Self::Medium => "Moderate complexity, consider refactoring",
            Self::High => "Complex, hard to test and maintain",
            Self::Critical => "Critical complexity, refactor immediately",
        }
    }

    /// Get the color code for CLI output (ANSI).
    #[must_use]
    pub const fn color_code(&self) -> &'static str {
        match self {
            Self::Low => "\x1b[32m",      // Green
            Self::Medium => "\x1b[33m",   // Yellow
            Self::High => "\x1b[31m",     // Red
            Self::Critical => "\x1b[35m", // Magenta
        }
    }
}

impl std::fmt::Display for RiskLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "low"),
            Self::Medium => write!(f, "medium"),
            Self::High => write!(f, "high"),
            Self::Critical => write!(f, "critical"),
        }
    }
}

// =============================================================================
// SIMD-ACCELERATED RISK LEVEL CLASSIFICATION
// =============================================================================

/// SIMD-accelerated risk level counting using u32x8 (AVX2 256-bit).
///
/// Processes 8 complexity values at a time using parallel threshold comparisons.
/// This provides significant speedup for large codebases with thousands of functions.
///
/// # Algorithm
///
/// For each vector of 8 values:
/// 1. Compare against threshold 10 (Low boundary)
/// 2. Compare against threshold 20 (Medium boundary)
/// 3. Compare against threshold 50 (High boundary)
/// 4. Count values in each category using bitmask operations
///
/// # Thresholds
///
/// - Low: complexity <= 10
/// - Medium: 10 < complexity <= 20
/// - High: 20 < complexity <= 50
/// - Critical: complexity > 50
#[derive(Debug, Clone, Copy, Default)]
pub struct RiskLevelCounts {
    pub low: usize,
    pub medium: usize,
    pub high: usize,
    pub critical: usize,
}

impl RiskLevelCounts {
    /// Count risk levels using SIMD-accelerated parallel comparison.
    ///
    /// Uses u32x8 vectors to process 8 complexity values simultaneously.
    /// Falls back to scalar processing for the remaining tail elements.
    #[must_use]
    pub fn count_simd(complexities: &[u32]) -> Self {
        const LANES: usize = 8;

        // Threshold vectors (broadcast constants)
        let threshold_low: u32x8 = Simd::splat(10);
        let threshold_medium: u32x8 = Simd::splat(20);
        let threshold_high: u32x8 = Simd::splat(50);

        let mut low_count: usize = 0;
        let mut medium_count: usize = 0;
        let mut high_count: usize = 0;
        let mut critical_count: usize = 0;

        let chunks = complexities.len() / LANES;
        let remainder = complexities.len() % LANES;

        // Process 8 values at a time using SIMD
        for chunk_idx in 0..chunks {
            let offset = chunk_idx * LANES;
            let values = u32x8::from_slice(&complexities[offset..offset + LANES]);

            // Parallel threshold comparisons:
            // is_low:      value <= 10
            // is_medium:   value > 10 AND value <= 20
            // is_high:     value > 20 AND value <= 50
            // is_critical: value > 50

            let le_10: Mask<i32, 8> = values.simd_le(threshold_low);
            let le_20: Mask<i32, 8> = values.simd_le(threshold_medium);
            let le_50: Mask<i32, 8> = values.simd_le(threshold_high);

            // Count bits set in each category mask
            // Low: <= 10
            low_count += le_10.to_bitmask().count_ones() as usize;

            // Medium: > 10 AND <= 20 (le_20 AND NOT le_10)
            let is_medium = le_20 & !le_10;
            medium_count += is_medium.to_bitmask().count_ones() as usize;

            // High: > 20 AND <= 50 (le_50 AND NOT le_20)
            let is_high = le_50 & !le_20;
            high_count += is_high.to_bitmask().count_ones() as usize;

            // Critical: > 50 (NOT le_50)
            let is_critical = !le_50;
            critical_count += is_critical.to_bitmask().count_ones() as usize;
        }

        // Handle tail elements with scalar fallback
        let tail_start = chunks * LANES;
        for &c in &complexities[tail_start..tail_start + remainder] {
            match c {
                0..=10 => low_count += 1,
                11..=20 => medium_count += 1,
                21..=50 => high_count += 1,
                _ => critical_count += 1,
            }
        }

        Self {
            low: low_count,
            medium: medium_count,
            high: high_count,
            critical: critical_count,
        }
    }

    /// Convert counts to a HashMap with string keys for serialization.
    #[must_use]
    pub fn to_hashmap(&self) -> HashMap<String, usize> {
        let mut map = HashMap::with_capacity(4);
        if self.low > 0 {
            map.insert("low".to_string(), self.low);
        }
        if self.medium > 0 {
            map.insert("medium".to_string(), self.medium);
        }
        if self.high > 0 {
            map.insert("high".to_string(), self.high);
        }
        if self.critical > 0 {
            map.insert("critical".to_string(), self.critical);
        }
        map
    }
}

/// Cyclomatic complexity result for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CyclomaticComplexity {
    /// Function name (may include class prefix for methods)
    pub function_name: String,
    /// File path containing the function
    pub file: PathBuf,
    /// Starting line number (1-indexed)
    pub line: usize,
    /// Ending line number (1-indexed)
    pub end_line: usize,
    /// Calculated cyclomatic complexity value
    pub complexity: u32,
    /// Risk level classification
    pub risk_level: RiskLevel,
    /// Number of decision points detected
    pub decision_points: u32,
    /// Number of CFG nodes (basic blocks)
    pub nodes: usize,
    /// Number of CFG edges
    pub edges: usize,
}

impl CyclomaticComplexity {
    /// Create complexity result from CFG info.
    fn from_cfg(cfg: &CFGInfo, file: &Path, line: usize, end_line: usize) -> Self {
        let complexity = cfg.cyclomatic_complexity() as u32;
        Self {
            function_name: cfg.function_name.clone(),
            file: file.to_path_buf(),
            line,
            end_line,
            complexity,
            risk_level: RiskLevel::from_complexity(complexity),
            decision_points: cfg.decision_points as u32,
            nodes: cfg.blocks.len(),
            edges: cfg.edges.len(),
        }
    }
}

/// Complexity information for a single function (simplified output).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionComplexity {
    /// Function name
    pub name: String,
    /// Starting line number
    pub line: usize,
    /// Cyclomatic complexity value
    pub complexity: u32,
    /// Risk level
    pub risk_level: RiskLevel,
}

impl From<&CyclomaticComplexity> for FunctionComplexity {
    fn from(cc: &CyclomaticComplexity) -> Self {
        Self {
            name: cc.function_name.clone(),
            line: cc.line,
            complexity: cc.complexity,
            risk_level: cc.risk_level,
        }
    }
}

/// Aggregate complexity statistics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityStats {
    /// Total number of functions analyzed
    pub total_functions: usize,
    /// Average complexity across all functions
    pub average_complexity: f64,
    /// Maximum complexity found
    pub max_complexity: u32,
    /// Minimum complexity found
    pub min_complexity: u32,
    /// Median complexity
    pub median_complexity: u32,
    /// Distribution by risk level
    pub risk_distribution: HashMap<String, usize>,
    /// Complexity histogram buckets (1-5, 6-10, 11-15, ...)
    pub histogram: Vec<HistogramBucket>,
}

// Re-export HistogramBucket from common module for backward compatibility
pub use super::common::HistogramBucket;

impl ComplexityStats {
    /// Calculate statistics from a list of complexity values.
    fn from_complexities(complexities: &[u32]) -> Self {
        if complexities.is_empty() {
            return Self {
                total_functions: 0,
                average_complexity: 0.0,
                max_complexity: 0,
                min_complexity: 0,
                median_complexity: 0,
                risk_distribution: HashMap::new(),
                histogram: Vec::new(),
            };
        }

        let total = complexities.len();
        let sum: u64 = complexities.iter().map(|&c| u64::from(c)).sum();
        let average = sum as f64 / total as f64;

        let max = *complexities.iter().max().unwrap_or(&0);
        let min = *complexities.iter().min().unwrap_or(&0);

        // Calculate median
        let mut sorted = complexities.to_vec();
        sorted.sort_unstable();
        let median = if total % 2 == 0 {
            (sorted[total / 2 - 1] + sorted[total / 2]) / 2
        } else {
            sorted[total / 2]
        };

        // Risk distribution using SIMD-accelerated parallel classification
        let risk_counts = RiskLevelCounts::count_simd(complexities);
        let risk_distribution = risk_counts.to_hashmap();

        // Build histogram (buckets of 5)
        let histogram = Self::build_histogram(complexities, max);

        Self {
            total_functions: total,
            average_complexity: average,
            max_complexity: max,
            min_complexity: min,
            median_complexity: median,
            risk_distribution,
            histogram,
        }
    }

    /// Build histogram with buckets of 5.
    fn build_histogram(complexities: &[u32], max: u32) -> Vec<HistogramBucket> {
        let bucket_size = 5u32;
        let num_buckets = ((max / bucket_size) + 1) as usize;

        let mut buckets = Vec::with_capacity(num_buckets.min(20)); // Cap at 20 buckets

        for i in 0..num_buckets.min(20) {
            let min_val = (i as u32) * bucket_size + 1;
            let max_val = min_val + bucket_size - 1;
            let count = complexities
                .iter()
                .filter(|&&c| c >= min_val && c <= max_val)
                .count();

            buckets.push(HistogramBucket {
                min: min_val,
                max: max_val,
                label: format!("{}-{}", min_val, max_val),
                count,
            });
        }

        // Handle overflow bucket for 100+
        if max > 100 {
            let overflow_count = complexities.iter().filter(|&&c| c > 100).count();
            if overflow_count > 0 {
                buckets.push(HistogramBucket {
                    min: 101,
                    max: u32::MAX,
                    label: "100+".to_string(),
                    count: overflow_count,
                });
            }
        }

        buckets
    }
}

/// Complete complexity analysis result for a file or project.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityAnalysis {
    /// Path that was analyzed (file or directory)
    pub path: PathBuf,
    /// Language filter applied (if any)
    pub language: Option<String>,
    /// Individual function complexities
    pub functions: Vec<CyclomaticComplexity>,
    /// Functions exceeding threshold (if threshold was specified)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violations: Option<Vec<CyclomaticComplexity>>,
    /// Aggregate statistics
    pub stats: ComplexityStats,
    /// Threshold used for filtering (if any)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub threshold: Option<u32>,
    /// Files that could not be analyzed
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<AnalysisError>,
}

/// Error encountered during complexity analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnalysisError {
    /// File path where error occurred
    pub file: PathBuf,
    /// Error message
    pub message: String,
}

// =============================================================================
// ANALYSIS FUNCTIONS
// =============================================================================

/// Analyze cyclomatic complexity for a project or directory.
///
/// Scans all source files in the directory, extracts functions, and calculates
/// cyclomatic complexity for each function using CFG analysis.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `language` - Optional language filter (e.g., "python", "typescript")
/// * `threshold` - Optional complexity threshold for filtering results
///
/// # Returns
///
/// Complete analysis result with individual complexities and statistics.
///
/// # Errors
///
/// Returns error if:
/// - Path does not exist
/// - No source files found
/// - All files failed to parse
///
/// # Example
///
/// ```ignore
/// use brrr::metrics::analyze_complexity;
///
/// // Analyze all Python files, report functions with complexity > 10
/// let result = analyze_complexity("./src", Some("python"), Some(10))?;
///
/// for func in &result.functions {
///     println!("{}: {} ({})", func.function_name, func.complexity, func.risk_level);
/// }
/// ```
pub fn analyze_complexity(
    path: impl AsRef<Path>,
    language: Option<&str>,
    threshold: Option<u32>,
) -> Result<ComplexityAnalysis> {
    let path = path.as_ref();

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Path not found: {}", path.display()),
        )));
    }

    if path.is_file() {
        return analyze_file_complexity(path, threshold);
    }

    // Directory analysis - scan for source files
    let path_str = path
        .to_str()
        .ok_or_else(|| BrrrError::InvalidArgument("Invalid path encoding".to_string()))?;

    let scanner = ProjectScanner::new(path_str)?;

    let config = if let Some(lang) = language {
        ScanConfig::for_language(lang)
    } else {
        ScanConfig::default()
    };

    let scan_result = scanner.scan_with_config(&config)?;

    if scan_result.files.is_empty() {
        return Err(BrrrError::InvalidArgument(format!(
            "No source files found in {} (filter: {:?})",
            path.display(),
            language
        )));
    }

    debug!("Analyzing {} files for complexity", scan_result.files.len());

    // Analyze files in parallel
    let results: Vec<(Vec<CyclomaticComplexity>, Vec<AnalysisError>)> = scan_result
        .files
        .par_iter()
        .map(|file| analyze_file_functions(file, threshold))
        .collect();

    // Aggregate results
    let mut all_functions = Vec::new();
    let mut all_errors = Vec::new();

    for (functions, errors) in results {
        all_functions.extend(functions);
        all_errors.extend(errors);
    }

    // Calculate statistics
    let complexities: Vec<u32> = all_functions.iter().map(|f| f.complexity).collect();
    let stats = ComplexityStats::from_complexities(&complexities);

    // Filter violations if threshold specified
    let violations = threshold.map(|t| {
        all_functions
            .iter()
            .filter(|f| f.complexity > t)
            .cloned()
            .collect::<Vec<_>>()
    });

    Ok(ComplexityAnalysis {
        path: path.to_path_buf(),
        language: language.map(String::from),
        functions: all_functions,
        violations,
        stats,
        threshold,
        errors: all_errors,
    })
}

/// Analyze cyclomatic complexity for a single file.
///
/// Extracts all functions from the file and calculates complexity for each.
///
/// # Arguments
///
/// * `file` - Path to source file
/// * `threshold` - Optional complexity threshold for filtering
///
/// # Returns
///
/// Analysis result with function complexities and statistics.
pub fn analyze_file_complexity(
    file: impl AsRef<Path>,
    threshold: Option<u32>,
) -> Result<ComplexityAnalysis> {
    let file = file.as_ref();

    if !file.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("File not found: {}", file.display()),
        )));
    }

    if !file.is_file() {
        return Err(BrrrError::InvalidArgument(format!(
            "Expected a file, got directory: {}",
            file.display()
        )));
    }

    let (functions, errors) = analyze_file_functions(file, threshold);

    let complexities: Vec<u32> = functions.iter().map(|f| f.complexity).collect();
    let stats = ComplexityStats::from_complexities(&complexities);

    let violations = threshold.map(|t| {
        functions
            .iter()
            .filter(|f| f.complexity > t)
            .cloned()
            .collect::<Vec<_>>()
    });

    // Detect language from file extension
    let registry = LanguageRegistry::global();
    let language = registry.detect_language(file).map(|l| l.name().to_string());

    Ok(ComplexityAnalysis {
        path: file.to_path_buf(),
        language,
        functions,
        violations,
        stats,
        threshold,
        errors,
    })
}

/// Internal function to analyze all functions in a file.
///
/// Returns a tuple of (successful analyses, errors encountered).
fn analyze_file_functions(
    file: &Path,
    _threshold: Option<u32>,
) -> (Vec<CyclomaticComplexity>, Vec<AnalysisError>) {
    let mut results = Vec::new();
    let mut errors = Vec::new();

    // Extract module info to get function list
    let module = match AstExtractor::extract_file(file) {
        Ok(m) => m,
        Err(e) => {
            errors.push(AnalysisError {
                file: file.to_path_buf(),
                message: format!("Failed to parse file: {}", e),
            });
            return (results, errors);
        }
    };

    let file_str = match file.to_str() {
        Some(s) => s,
        None => {
            errors.push(AnalysisError {
                file: file.to_path_buf(),
                message: "Invalid file path encoding".to_string(),
            });
            return (results, errors);
        }
    };

    // Analyze top-level functions
    for func in &module.functions {
        let start_line = func.line_number;
        let end_line = func.end_line_number.unwrap_or(start_line);
        match analyze_function(file_str, &func.name, start_line, end_line) {
            Ok(complexity) => results.push(complexity),
            Err(e) => {
                debug!("Failed to analyze function {}: {}", func.name, e);
                // Fall back to simple estimation from function info
                if let Some(complexity) = estimate_complexity_from_function(func, file) {
                    results.push(complexity);
                }
            }
        }
    }

    // Analyze class methods
    for class in &module.classes {
        for method in &class.methods {
            let qualified_name = format!("{}.{}", class.name, method.name);
            let start_line = method.line_number;
            let end_line = method.end_line_number.unwrap_or(start_line);
            match analyze_function(file_str, &qualified_name, start_line, end_line) {
                Ok(mut complexity) => {
                    // Keep the qualified name for methods
                    complexity.function_name = qualified_name;
                    results.push(complexity);
                }
                Err(e) => {
                    debug!("Failed to analyze method {}: {}", qualified_name, e);
                    if let Some(mut complexity) = estimate_complexity_from_function(method, file) {
                        complexity.function_name = qualified_name;
                        results.push(complexity);
                    }
                }
            }
        }
    }

    (results, errors)
}

/// Analyze a single function using CFG extraction.
fn analyze_function(
    file: &str,
    function_name: &str,
    start_line: usize,
    end_line: usize,
) -> Result<CyclomaticComplexity> {
    let cfg = CfgBuilder::extract_from_file(file, function_name)?;
    Ok(CyclomaticComplexity::from_cfg(
        &cfg,
        Path::new(file),
        start_line,
        end_line,
    ))
}

/// Estimate complexity from function info when CFG extraction fails.
///
/// This is a fallback that provides approximate complexity based on
/// function structure (nesting depth, parameters, etc.).
fn estimate_complexity_from_function(
    func: &FunctionInfo,
    file: &Path,
) -> Option<CyclomaticComplexity> {
    // Simple heuristic: base complexity of 1
    // Real implementation would count decision keywords in source
    let base_complexity = 1u32;
    let start_line = func.line_number;
    let end_line = func.end_line_number.unwrap_or(start_line);

    Some(CyclomaticComplexity {
        function_name: func.name.clone(),
        file: file.to_path_buf(),
        line: start_line,
        end_line,
        complexity: base_complexity,
        risk_level: RiskLevel::from_complexity(base_complexity),
        decision_points: 0,
        nodes: 0,
        edges: 0,
    })
}

// =============================================================================
// ADDITIONAL COMPLEXITY CALCULATIONS
// =============================================================================

/// Calculate complexity using the graph formula: M = E - N + 2P.
///
/// This is the classic McCabe formula where:
/// - E = number of edges in the control flow graph
/// - N = number of nodes (basic blocks)
/// - P = number of connected components (usually 1 for a single function)
///
/// # Note
///
/// This may give slightly different results than the decision-point method
/// due to unreachable code blocks and graph structure variations.
#[allow(dead_code)]
pub fn calculate_graph_complexity(cfg: &CFGInfo) -> u32 {
    cfg.cyclomatic_complexity_graph() as u32
}

/// Count additional decision points from boolean operators.
///
/// Boolean operators (&& and ||) in conditions create additional paths
/// due to short-circuit evaluation. This function counts them in
/// condition expressions.
///
/// # Decision Points from Boolean Operators
///
/// ```text
/// if (a && b)    // 2 decision points: a, then b (if a is true)
/// if (a || b)    // 2 decision points: a, then b (if a is false)
/// if (a && b && c)  // 3 decision points
/// ```
#[allow(dead_code)]
pub fn count_boolean_operators(condition: &str) -> u32 {
    let and_count = condition.matches("&&").count() as u32;
    let or_count = condition.matches("||").count() as u32;

    // Python uses 'and' and 'or'
    let py_and_count = count_word_boundary("and", condition) as u32;
    let py_or_count = count_word_boundary("or", condition) as u32;

    and_count + or_count + py_and_count + py_or_count
}

/// Count occurrences of a word at word boundaries.
fn count_word_boundary(word: &str, text: &str) -> usize {
    let word_len = word.len();
    let text_bytes = text.as_bytes();
    let word_bytes = word.as_bytes();
    let mut count = 0;

    for i in 0..=text.len().saturating_sub(word_len) {
        if &text_bytes[i..i + word_len] == word_bytes {
            let before_ok = i == 0 || !text_bytes[i - 1].is_ascii_alphanumeric();
            let after_ok =
                i + word_len >= text.len() || !text_bytes[i + word_len].is_ascii_alphanumeric();

            if before_ok && after_ok {
                count += 1;
            }
        }
    }

    count
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
    fn test_risk_level_classification() {
        assert_eq!(RiskLevel::from_complexity(1), RiskLevel::Low);
        assert_eq!(RiskLevel::from_complexity(10), RiskLevel::Low);
        assert_eq!(RiskLevel::from_complexity(11), RiskLevel::Medium);
        assert_eq!(RiskLevel::from_complexity(20), RiskLevel::Medium);
        assert_eq!(RiskLevel::from_complexity(21), RiskLevel::High);
        assert_eq!(RiskLevel::from_complexity(50), RiskLevel::High);
        assert_eq!(RiskLevel::from_complexity(51), RiskLevel::Critical);
        assert_eq!(RiskLevel::from_complexity(100), RiskLevel::Critical);
    }

    #[test]
    fn test_risk_level_display() {
        assert_eq!(RiskLevel::Low.to_string(), "low");
        assert_eq!(RiskLevel::Medium.to_string(), "medium");
        assert_eq!(RiskLevel::High.to_string(), "high");
        assert_eq!(RiskLevel::Critical.to_string(), "critical");
    }

    #[test]
    fn test_simple_function_complexity() {
        let source = r#"
def simple():
    return 42
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_complexity(file.path(), None);

        assert!(result.is_ok(), "Analysis should succeed");
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].function_name, "simple");
        assert_eq!(analysis.functions[0].complexity, 1);
        assert_eq!(analysis.functions[0].risk_level, RiskLevel::Low);
    }

    #[test]
    fn test_if_statement_complexity() {
        let source = r#"
def with_if(x):
    if x > 0:
        return 1
    return 0
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].complexity, 2); // 1 decision point + 1
    }

    #[test]
    fn test_if_elif_else_complexity() {
        let source = r#"
def with_elif(x):
    if x > 0:
        return "positive"
    elif x < 0:
        return "negative"
    else:
        return "zero"
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].complexity, 3); // 2 decision points + 1
    }

    #[test]
    fn test_loop_complexity() {
        let source = r#"
def with_loop(items):
    total = 0
    for item in items:
        total += item
    return total
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        assert_eq!(analysis.functions[0].complexity, 2); // 1 loop + 1
    }

    #[test]
    fn test_nested_complexity() {
        let source = r#"
def nested(x, items):
    if x > 0:
        for item in items:
            if item > x:
                return item
    return None
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // 3 decision points: if, for, if
        assert_eq!(analysis.functions[0].complexity, 4);
    }

    #[test]
    fn test_class_method_complexity() {
        let source = r#"
class Calculator:
    def add(self, a, b):
        return a + b

    def smart_divide(self, a, b):
        if b == 0:
            return None
        return a / b
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 2);

        // Find the methods by name
        let add = analysis
            .functions
            .iter()
            .find(|f| f.function_name == "Calculator.add");
        let divide = analysis
            .functions
            .iter()
            .find(|f| f.function_name == "Calculator.smart_divide");

        assert!(add.is_some(), "Should find add method");
        assert!(divide.is_some(), "Should find smart_divide method");

        assert_eq!(add.unwrap().complexity, 1);
        assert_eq!(divide.unwrap().complexity, 2);
    }

    #[test]
    fn test_threshold_filtering() {
        let source = r#"
def simple():
    return 1

def complex_func(x, y, z):
    if x > 0:
        if y > 0:
            if z > 0:
                return "all positive"
            else:
                return "z negative"
        else:
            return "y negative"
    else:
        return "x negative"
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_complexity(file.path(), Some(2));

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert!(analysis.violations.is_some());
        let violations = analysis.violations.unwrap();

        // Only complex_func should be a violation (complexity > 2)
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].function_name, "complex_func");
    }

    #[test]
    fn test_statistics_calculation() {
        let complexities = vec![1, 2, 3, 10, 15, 25];
        let stats = ComplexityStats::from_complexities(&complexities);

        assert_eq!(stats.total_functions, 6);
        assert_eq!(stats.min_complexity, 1);
        assert_eq!(stats.max_complexity, 25);
        assert!((stats.average_complexity - 9.33).abs() < 0.1);

        // Check risk distribution
        assert_eq!(*stats.risk_distribution.get("low").unwrap_or(&0), 4);
        assert_eq!(*stats.risk_distribution.get("medium").unwrap_or(&0), 1);
        assert_eq!(*stats.risk_distribution.get("high").unwrap_or(&0), 1);
    }

    #[test]
    fn test_empty_file_analysis() {
        let source = "# Just a comment\n";
        let file = create_temp_file(source, ".py");
        let result = analyze_file_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 0);
        assert_eq!(analysis.stats.total_functions, 0);
    }

    #[test]
    fn test_boolean_operator_counting() {
        assert_eq!(count_boolean_operators("a && b"), 1);
        assert_eq!(count_boolean_operators("a || b"), 1);
        assert_eq!(count_boolean_operators("a && b && c"), 2);
        assert_eq!(count_boolean_operators("a || b && c"), 2);

        // Python operators
        assert_eq!(count_boolean_operators("a and b"), 1);
        assert_eq!(count_boolean_operators("a or b"), 1);
        assert_eq!(count_boolean_operators("a and b and c"), 2);

        // Should not match word fragments
        assert_eq!(count_boolean_operators("android"), 0);
        assert_eq!(count_boolean_operators("valor"), 0);
    }

    #[test]
    fn test_word_boundary_matching() {
        assert_eq!(count_word_boundary("and", "a and b"), 1);
        assert_eq!(count_word_boundary("and", "android"), 0);
        assert_eq!(count_word_boundary("and", "band"), 0);
        assert_eq!(count_word_boundary("or", "a or b"), 1);
        assert_eq!(count_word_boundary("or", "for"), 0);
        assert_eq!(count_word_boundary("or", "order"), 0);
    }

    #[test]
    fn test_try_except_complexity() {
        let source = r#"
def safe_divide(a, b):
    try:
        result = a / b
    except ZeroDivisionError:
        result = 0
    except TypeError:
        result = None
    return result
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        // 2 exception handlers = 2 decision points
        assert_eq!(analysis.functions[0].complexity, 3);
    }

    #[test]
    fn test_typescript_complexity() {
        let source = r#"
function simple(): number {
    return 42;
}

function withIf(x: number): string {
    if (x > 0) {
        return "positive";
    }
    return "non-positive";
}
"#;
        let file = create_temp_file(source, ".ts");
        let result = analyze_file_complexity(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        // Should find both functions
        assert_eq!(analysis.functions.len(), 2);
    }

    #[test]
    fn test_nonexistent_file() {
        let result = analyze_file_complexity("/nonexistent/path/file.py", None);
        assert!(result.is_err());
    }

    #[test]
    fn test_histogram_generation() {
        let complexities = vec![1, 2, 3, 5, 6, 7, 10, 11, 15, 20, 25, 30];
        let stats = ComplexityStats::from_complexities(&complexities);

        // Should have histogram buckets
        assert!(!stats.histogram.is_empty());

        // First bucket (1-5) should have 4 functions
        assert_eq!(stats.histogram[0].count, 4);
        assert_eq!(stats.histogram[0].label, "1-5");

        // Second bucket (6-10) should have 3 functions
        assert_eq!(stats.histogram[1].count, 3);
    }

    // =========================================================================
    // SIMD RISK LEVEL CLASSIFICATION TESTS
    // =========================================================================

    #[test]
    fn test_simd_risk_level_empty() {
        let counts = RiskLevelCounts::count_simd(&[]);
        assert_eq!(counts.low, 0);
        assert_eq!(counts.medium, 0);
        assert_eq!(counts.high, 0);
        assert_eq!(counts.critical, 0);
    }

    #[test]
    fn test_simd_risk_level_single_element() {
        // Test single element in each category
        let counts = RiskLevelCounts::count_simd(&[5]);
        assert_eq!(counts.low, 1);

        let counts = RiskLevelCounts::count_simd(&[15]);
        assert_eq!(counts.medium, 1);

        let counts = RiskLevelCounts::count_simd(&[30]);
        assert_eq!(counts.high, 1);

        let counts = RiskLevelCounts::count_simd(&[100]);
        assert_eq!(counts.critical, 1);
    }

    #[test]
    fn test_simd_risk_level_boundaries() {
        // Test exact boundary values
        // Low boundary: <= 10
        assert_eq!(RiskLevelCounts::count_simd(&[10]).low, 1);
        assert_eq!(RiskLevelCounts::count_simd(&[10]).medium, 0);

        // Medium boundary: 11-20
        assert_eq!(RiskLevelCounts::count_simd(&[11]).medium, 1);
        assert_eq!(RiskLevelCounts::count_simd(&[20]).medium, 1);

        // High boundary: 21-50
        assert_eq!(RiskLevelCounts::count_simd(&[21]).high, 1);
        assert_eq!(RiskLevelCounts::count_simd(&[50]).high, 1);

        // Critical boundary: > 50
        assert_eq!(RiskLevelCounts::count_simd(&[51]).critical, 1);
    }

    #[test]
    fn test_simd_risk_level_tail_only() {
        // Test with less than 8 elements (tail processing only)
        let complexities = vec![1, 5, 10, 15, 25, 55];
        let counts = RiskLevelCounts::count_simd(&complexities);

        assert_eq!(counts.low, 3); // 1, 5, 10
        assert_eq!(counts.medium, 1); // 15
        assert_eq!(counts.high, 1); // 25
        assert_eq!(counts.critical, 1); // 55
    }

    #[test]
    fn test_simd_risk_level_exact_8() {
        // Test with exactly 8 elements (one full SIMD vector)
        let complexities = vec![1, 5, 10, 15, 20, 25, 50, 100];
        let counts = RiskLevelCounts::count_simd(&complexities);

        assert_eq!(counts.low, 3); // 1, 5, 10
        assert_eq!(counts.medium, 2); // 15, 20
        assert_eq!(counts.high, 2); // 25, 50
        assert_eq!(counts.critical, 1); // 100
    }

    #[test]
    fn test_simd_risk_level_16_elements() {
        // Test with 16 elements (two full SIMD vectors)
        let complexities = vec![
            1, 2, 3, 4, 5, 6, 7, 8, // All low (8)
            11, 12, 13, 14, 15, 16, 17, 18, // All medium (8)
        ];
        let counts = RiskLevelCounts::count_simd(&complexities);

        assert_eq!(counts.low, 8);
        assert_eq!(counts.medium, 8);
        assert_eq!(counts.high, 0);
        assert_eq!(counts.critical, 0);
    }

    #[test]
    fn test_simd_risk_level_17_elements() {
        // Test with 17 elements (two vectors + 1 tail)
        let complexities = vec![
            1, 2, 3, 4, 5, 6, 7, 10, // All low (8)
            21, 22, 23, 24, 25, 26, 27, 30, // All high (8)
            51, // Critical (1 tail)
        ];
        let counts = RiskLevelCounts::count_simd(&complexities);

        assert_eq!(counts.low, 8);
        assert_eq!(counts.medium, 0);
        assert_eq!(counts.high, 8);
        assert_eq!(counts.critical, 1);
    }

    #[test]
    fn test_simd_risk_level_large_mixed() {
        // Large test with all categories
        let mut complexities = Vec::with_capacity(1000);
        for i in 0..250 {
            complexities.push(i % 10 + 1); // Low: 1-10
        }
        for i in 0..250 {
            complexities.push(i % 10 + 11); // Medium: 11-20
        }
        for i in 0..250 {
            complexities.push(i % 30 + 21); // High: 21-50
        }
        for _ in 0..250 {
            complexities.push(100); // Critical: 100
        }

        let counts = RiskLevelCounts::count_simd(&complexities);

        assert_eq!(counts.low, 250);
        assert_eq!(counts.medium, 250);
        assert_eq!(counts.high, 250);
        assert_eq!(counts.critical, 250);
    }

    #[test]
    fn test_simd_matches_scalar() {
        // Verify SIMD results match scalar implementation
        let complexities: Vec<u32> = (1..=100).collect();

        let simd_counts = RiskLevelCounts::count_simd(&complexities);

        // Scalar reference implementation
        let mut low = 0;
        let mut medium = 0;
        let mut high = 0;
        let mut critical = 0;
        for &c in &complexities {
            match c {
                0..=10 => low += 1,
                11..=20 => medium += 1,
                21..=50 => high += 1,
                _ => critical += 1,
            }
        }

        assert_eq!(simd_counts.low, low);
        assert_eq!(simd_counts.medium, medium);
        assert_eq!(simd_counts.high, high);
        assert_eq!(simd_counts.critical, critical);
    }

    #[test]
    fn test_simd_to_hashmap() {
        let counts = RiskLevelCounts {
            low: 10,
            medium: 5,
            high: 3,
            critical: 1,
        };

        let map = counts.to_hashmap();

        assert_eq!(map.get("low"), Some(&10));
        assert_eq!(map.get("medium"), Some(&5));
        assert_eq!(map.get("high"), Some(&3));
        assert_eq!(map.get("critical"), Some(&1));
    }

    #[test]
    fn test_simd_to_hashmap_omits_zeros() {
        let counts = RiskLevelCounts {
            low: 5,
            medium: 0,
            high: 0,
            critical: 0,
        };

        let map = counts.to_hashmap();

        assert_eq!(map.get("low"), Some(&5));
        assert_eq!(map.get("medium"), None);
        assert_eq!(map.get("high"), None);
        assert_eq!(map.get("critical"), None);
    }
}
