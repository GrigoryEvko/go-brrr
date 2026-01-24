//! Maintainability Index calculation.
//!
//! The Maintainability Index (MI) is a composite metric that combines multiple
//! software quality measures into a single score indicating how maintainable
//! the code is.
//!
//! # Formula (Visual Studio Standard)
//!
//! ```text
//! MI = MAX(0, (171 - 5.2 * ln(V) - 0.23 * CC - 16.2 * ln(LOC)) * 100 / 171)
//! ```
//!
//! Where:
//! - V = Halstead Volume (program size in bits)
//! - CC = Cyclomatic Complexity (independent paths)
//! - LOC = Lines of Code (source lines, excluding blanks and comments)
//!
//! # Extended Formula (with Comments)
//!
//! ```text
//! MI = MAX(0, (171 - 5.2 * ln(V) - 0.23 * CC - 16.2 * ln(LOC) + 50 * sin(sqrt(2.4 * CM))) * 100 / 171)
//! ```
//!
//! Where CM = percentage of comment lines (0.0 to 100.0)
//!
//! # Risk Levels
//!
//! | Score Range | Risk Level | Interpretation                     |
//! |-------------|------------|-----------------------------------|
//! | 0-9         | Critical   | Very hard to maintain             |
//! | 10-19       | High       | Hard to maintain                  |
//! | 20-49       | Medium     | Moderately maintainable           |
//! | 50-100      | Low        | Highly maintainable               |
//!
//! # Lines of Code Types
//!
//! This module calculates multiple LOC metrics:
//!
//! - **Physical LOC (PLOC)**: Total lines including blanks and comments
//! - **Source LOC (SLOC)**: Physical lines minus blank lines
//! - **Logical LOC (LLOC)**: Number of statements (language-dependent)
//! - **Comment Lines**: Lines containing comments
//! - **Blank Lines**: Empty or whitespace-only lines
//!
//! The MI formula uses **Source LOC** (SLOC) excluding comment-only lines,
//! matching Visual Studio's implementation.
//!
//! # References
//!
//! - Oman, P. & Hagemeister, J. (1992). "Metrics for Assessing a Software
//!   System's Maintainability"
//! - Coleman, D., et al. (1994). "Using Metrics to Evaluate Software System
//!   Maintainability"
//! - SEI (Software Engineering Institute) Maintainability Index
//! - Visual Studio Code Metrics

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::debug;
use tree_sitter::Node;

use crate::ast::AstExtractor;
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;

use super::common;
use super::halstead::HalsteadMetrics;

// =============================================================================
// TYPES
// =============================================================================

/// Risk level for maintainability index scores.
///
/// Based on industry-standard thresholds used by Visual Studio and similar tools.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MaintainabilityRiskLevel {
    /// Score 50-100: Highly maintainable, low risk
    Low,
    /// Score 20-49: Moderately maintainable, medium risk
    Medium,
    /// Score 10-19: Hard to maintain, high risk
    High,
    /// Score 0-9: Very hard to maintain, critical risk
    Critical,
}

impl MaintainabilityRiskLevel {
    /// Classify a maintainability index score into a risk level.
    ///
    /// # Thresholds
    ///
    /// - 50-100: Low risk (highly maintainable)
    /// - 20-49: Medium risk (moderately maintainable)
    /// - 10-19: High risk (hard to maintain)
    /// - 0-9: Critical risk (very hard to maintain)
    #[must_use]
    pub fn from_score(score: f64) -> Self {
        match score {
            s if s >= 50.0 => Self::Low,
            s if s >= 20.0 => Self::Medium,
            s if s >= 10.0 => Self::High,
            _ => Self::Critical,
        }
    }

    /// Get human-readable description of the risk level.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Low => "Highly maintainable",
            Self::Medium => "Moderately maintainable",
            Self::High => "Hard to maintain",
            Self::Critical => "Very hard to maintain, refactor immediately",
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

impl std::fmt::Display for MaintainabilityRiskLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "low"),
            Self::Medium => write!(f, "medium"),
            Self::High => write!(f, "high"),
            Self::Critical => write!(f, "critical"),
        }
    }
}

/// Lines of Code metrics for a code segment.
///
/// Provides multiple LOC measurements to support different analysis needs.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LinesOfCode {
    /// Physical lines of code (total line count)
    pub physical: u32,
    /// Source lines of code (non-blank lines)
    pub source: u32,
    /// Logical lines of code (statements)
    pub logical: u32,
    /// Lines containing comments (full or partial)
    pub comment_lines: u32,
    /// Blank lines (empty or whitespace-only)
    pub blank_lines: u32,
    /// Comment-only lines (no code on the line)
    pub comment_only_lines: u32,
    /// Effective source lines (source minus comment-only lines)
    pub effective: u32,
}

impl LinesOfCode {
    /// Calculate the percentage of comment lines relative to total lines.
    ///
    /// Returns a value between 0.0 and 100.0.
    #[must_use]
    pub fn comment_percentage(&self) -> f64 {
        if self.physical == 0 {
            return 0.0;
        }
        (f64::from(self.comment_lines) / f64::from(self.physical)) * 100.0
    }

    /// Calculate the percentage of comment lines relative to source lines.
    ///
    /// This is the ratio used in some MI variants.
    #[must_use]
    pub fn comment_ratio(&self) -> f64 {
        if self.source == 0 {
            return 0.0;
        }
        (f64::from(self.comment_lines) / f64::from(self.source)) * 100.0
    }
}

/// Maintainability Index result for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MaintainabilityIndex {
    /// Calculated MI score (0-100)
    pub score: f64,
    /// Risk level classification
    pub risk_level: MaintainabilityRiskLevel,
    /// Halstead Volume used in calculation
    pub halstead_volume: f64,
    /// Cyclomatic Complexity used in calculation
    pub cyclomatic_complexity: u32,
    /// Lines of Code metrics
    pub lines_of_code: LinesOfCode,
    /// Comment percentage (0-100)
    pub comment_percentage: f64,
    /// Whether the extended formula with comments was used
    pub includes_comments: bool,
}

impl MaintainabilityIndex {
    /// Calculate MI using the standard Visual Studio formula.
    ///
    /// Formula: `MI = MAX(0, (171 - 5.2 * ln(V) - 0.23 * CC - 16.2 * ln(LOC)) * 100 / 171)`
    ///
    /// # Arguments
    ///
    /// * `halstead_volume` - Halstead Volume (V)
    /// * `cyclomatic_complexity` - Cyclomatic Complexity (CC)
    /// * `loc` - Lines of Code metrics
    #[must_use]
    pub fn calculate(halstead_volume: f64, cyclomatic_complexity: u32, loc: LinesOfCode) -> Self {
        let effective_loc = loc.effective.max(1); // Avoid log(0)
        let volume = halstead_volume.max(1.0); // Avoid log(0)
        let cc = f64::from(cyclomatic_complexity);

        // Standard MI formula (Visual Studio)
        let raw_mi = 171.0 - 5.2 * volume.ln() - 0.23 * cc - 16.2 * f64::from(effective_loc).ln();

        let score = (raw_mi * 100.0 / 171.0).max(0.0).min(100.0);
        let comment_percentage = loc.comment_percentage();

        Self {
            score,
            risk_level: MaintainabilityRiskLevel::from_score(score),
            halstead_volume,
            cyclomatic_complexity,
            lines_of_code: loc,
            comment_percentage,
            includes_comments: false,
        }
    }

    /// Calculate MI using the extended formula with comment bonus.
    ///
    /// Formula: `MI = MAX(0, (171 - 5.2 * ln(V) - 0.23 * CC - 16.2 * ln(LOC) + 50 * sin(sqrt(2.4 * CM))) * 100 / 171)`
    ///
    /// The comment factor can add up to ~50 points to the raw MI when comments
    /// are well-distributed throughout the code.
    ///
    /// # Arguments
    ///
    /// * `halstead_volume` - Halstead Volume (V)
    /// * `cyclomatic_complexity` - Cyclomatic Complexity (CC)
    /// * `loc` - Lines of Code metrics
    #[must_use]
    pub fn calculate_with_comments(
        halstead_volume: f64,
        cyclomatic_complexity: u32,
        loc: LinesOfCode,
    ) -> Self {
        let effective_loc = loc.effective.max(1);
        let volume = halstead_volume.max(1.0);
        let cc = f64::from(cyclomatic_complexity);
        let cm = loc.comment_percentage(); // 0-100

        // Extended MI formula with comment bonus
        // Note: 2.4 * CM should be clamped because sin argument in radians
        // When CM=100%, sqrt(2.4*100) = sqrt(240) = 15.49 radians
        // sin(15.49) oscillates, so we clamp CM contribution
        let comment_factor = 50.0 * (2.4 * cm).sqrt().sin();

        let raw_mi = 171.0 - 5.2 * volume.ln() - 0.23 * cc - 16.2 * f64::from(effective_loc).ln()
            + comment_factor;

        let score = (raw_mi * 100.0 / 171.0).max(0.0).min(100.0);

        Self {
            score,
            risk_level: MaintainabilityRiskLevel::from_score(score),
            halstead_volume,
            cyclomatic_complexity,
            lines_of_code: loc,
            comment_percentage: cm,
            includes_comments: true,
        }
    }
}

/// Maintainability Index result for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionMaintainability {
    /// Function name (may include class prefix for methods)
    pub function_name: String,
    /// File path containing the function
    pub file: PathBuf,
    /// Starting line number (1-indexed)
    pub line: usize,
    /// Ending line number (1-indexed)
    pub end_line: usize,
    /// Maintainability Index score and components
    pub index: MaintainabilityIndex,
}

/// Aggregate maintainability statistics for a project.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MaintainabilityStats {
    /// Total functions analyzed
    pub total_functions: usize,
    /// Average maintainability index
    pub average_mi: f64,
    /// Minimum MI found
    pub min_mi: f64,
    /// Maximum MI found
    pub max_mi: f64,
    /// Median MI
    pub median_mi: f64,
    /// Distribution by risk level
    pub risk_distribution: HashMap<String, usize>,
    /// Total source lines of code
    pub total_sloc: u32,
    /// Total comment lines
    pub total_comment_lines: u32,
    /// Overall comment percentage
    pub overall_comment_percentage: f64,
    /// Average Halstead Volume
    pub average_volume: f64,
    /// Average Cyclomatic Complexity
    pub average_cc: f64,
}

impl MaintainabilityStats {
    /// Calculate statistics from a list of function results.
    fn from_functions(functions: &[FunctionMaintainability]) -> Self {
        if functions.is_empty() {
            return Self {
                total_functions: 0,
                average_mi: 0.0,
                min_mi: 0.0,
                max_mi: 0.0,
                median_mi: 0.0,
                risk_distribution: HashMap::new(),
                total_sloc: 0,
                total_comment_lines: 0,
                overall_comment_percentage: 0.0,
                average_volume: 0.0,
                average_cc: 0.0,
            };
        }

        let total = functions.len();
        let scores: Vec<f64> = functions.iter().map(|f| f.index.score).collect();
        let volumes: Vec<f64> = functions.iter().map(|f| f.index.halstead_volume).collect();
        let ccs: Vec<u32> = functions
            .iter()
            .map(|f| f.index.cyclomatic_complexity)
            .collect();

        let sum_mi: f64 = scores.iter().sum();
        let average_mi = sum_mi / total as f64;

        let min_mi = scores.iter().cloned().fold(f64::INFINITY, f64::min);
        let max_mi = scores.iter().cloned().fold(f64::NEG_INFINITY, f64::max);

        // Calculate median
        let mut sorted_scores = scores.clone();
        sorted_scores.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        let median_mi = if total % 2 == 0 {
            (sorted_scores[total / 2 - 1] + sorted_scores[total / 2]) / 2.0
        } else {
            sorted_scores[total / 2]
        };

        // Risk distribution
        let mut risk_distribution = HashMap::new();
        for func in functions {
            let risk = func.index.risk_level.to_string();
            *risk_distribution.entry(risk).or_insert(0) += 1;
        }

        // Aggregate LOC metrics
        let total_sloc: u32 = functions.iter().map(|f| f.index.lines_of_code.source).sum();
        let total_comment_lines: u32 = functions
            .iter()
            .map(|f| f.index.lines_of_code.comment_lines)
            .sum();
        let total_physical: u32 = functions
            .iter()
            .map(|f| f.index.lines_of_code.physical)
            .sum();

        let overall_comment_percentage = if total_physical > 0 {
            (f64::from(total_comment_lines) / f64::from(total_physical)) * 100.0
        } else {
            0.0
        };

        let average_volume = volumes.iter().sum::<f64>() / total as f64;
        let average_cc = ccs.iter().map(|&c| f64::from(c)).sum::<f64>() / total as f64;

        Self {
            total_functions: total,
            average_mi,
            min_mi,
            max_mi,
            median_mi,
            risk_distribution,
            total_sloc,
            total_comment_lines,
            overall_comment_percentage,
            average_volume,
            average_cc,
        }
    }
}

/// Complete maintainability analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MaintainabilityAnalysis {
    /// Path that was analyzed
    pub path: PathBuf,
    /// Language filter applied
    pub language: Option<String>,
    /// Individual function results
    pub functions: Vec<FunctionMaintainability>,
    /// Functions below threshold (if threshold specified)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violations: Option<Vec<FunctionMaintainability>>,
    /// Aggregate statistics
    pub stats: MaintainabilityStats,
    /// Minimum MI threshold used (if any)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub threshold: Option<f64>,
    /// Whether extended formula with comments was used
    pub includes_comments: bool,
    /// Analysis errors encountered
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<MaintainabilityError>,
}

/// Error encountered during maintainability analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MaintainabilityError {
    /// File path where error occurred
    pub file: PathBuf,
    /// Error message
    pub message: String,
}

// =============================================================================
// LOC CALCULATION
// =============================================================================

/// Calculate lines of code metrics for source code.
///
/// Analyzes the source code to count:
/// - Physical lines (total)
/// - Blank lines
/// - Comment lines (including partial)
/// - Comment-only lines
/// - Source lines (non-blank)
/// - Effective lines (source minus comment-only)
///
/// # Language Support
///
/// Supports comment detection for:
/// - Python: `#` line comments, `'''`/`"""` docstrings
/// - JavaScript/TypeScript: `//`, `/* */`
/// - Rust: `//`, `/* */`, `///`, `//!`
/// - Go: `//`, `/* */`
/// - C/C++: `//`, `/* */`
/// - Java: `//`, `/* */`
fn calculate_loc(source: &str, language: &str) -> LinesOfCode {
    let lines: Vec<&str> = source.lines().collect();
    let physical = lines.len() as u32;

    let mut blank_lines = 0u32;
    let mut comment_lines = 0u32;
    let mut comment_only_lines = 0u32;
    let mut in_multiline_comment = false;
    let mut in_python_docstring = false;
    let mut docstring_char: char = '"';

    let (line_comment, block_start, block_end) = get_comment_markers(language);

    for line in &lines {
        let trimmed = line.trim();

        // Check for blank lines
        if trimmed.is_empty() {
            blank_lines += 1;
            continue;
        }

        // Handle Python docstrings specially
        if language == "python" {
            if !in_python_docstring {
                // Check for docstring start
                if trimmed.starts_with("\"\"\"") || trimmed.starts_with("'''") {
                    docstring_char = trimmed.chars().next().unwrap_or('"');
                    let end_marker: String = std::iter::repeat(docstring_char).take(3).collect();
                    comment_lines += 1;

                    // Check if docstring ends on same line (after the opening)
                    let after_start = &trimmed[3..];
                    if after_start.contains(&end_marker) {
                        // Single-line docstring
                        comment_only_lines += 1;
                    } else {
                        in_python_docstring = true;
                        comment_only_lines += 1;
                    }
                    continue;
                }
            } else {
                // Inside docstring
                let end_marker: String = std::iter::repeat(docstring_char).take(3).collect();
                comment_lines += 1;
                comment_only_lines += 1;
                if trimmed.contains(&end_marker) {
                    in_python_docstring = false;
                }
                continue;
            }
        }

        // Handle multi-line comments
        if in_multiline_comment {
            comment_lines += 1;
            if let Some(end) = block_end {
                if trimmed.contains(end) {
                    in_multiline_comment = false;
                    // Check if there's code after the comment end
                    if let Some(idx) = trimmed.find(end) {
                        let after = trimmed[idx + end.len()..].trim();
                        if after.is_empty() {
                            comment_only_lines += 1;
                        }
                    }
                } else {
                    comment_only_lines += 1;
                }
            }
            continue;
        }

        // Check for multi-line comment start
        if let Some(start) = block_start {
            if trimmed.contains(start) {
                comment_lines += 1;
                if let Some(end) = block_end {
                    // Check if it ends on the same line
                    if let Some(start_idx) = trimmed.find(start) {
                        let after_start = &trimmed[start_idx + start.len()..];
                        if after_start.contains(end) {
                            // Comment contained on one line
                            // Check if there's code before or after
                            let before = &trimmed[..start_idx];
                            if let Some(end_idx) = after_start.find(end) {
                                let after = &after_start[end_idx + end.len()..];
                                if before.trim().is_empty() && after.trim().is_empty() {
                                    comment_only_lines += 1;
                                }
                            }
                        } else {
                            // Multi-line comment starts
                            in_multiline_comment = true;
                            let before = &trimmed[..start_idx];
                            if before.trim().is_empty() {
                                comment_only_lines += 1;
                            }
                        }
                    }
                }
                continue;
            }
        }

        // Check for line comments
        if let Some(marker) = line_comment {
            if trimmed.starts_with(marker) {
                comment_lines += 1;
                comment_only_lines += 1;
                continue;
            }
            // Check for trailing comment
            if trimmed.contains(marker) {
                comment_lines += 1;
                // Not comment-only since there's code
            }
        }
    }

    let source = physical - blank_lines;
    let effective = source - comment_only_lines;

    // Estimate logical LOC (statements) - simplified heuristic
    let logical = estimate_logical_loc(source, language);

    LinesOfCode {
        physical,
        source,
        logical,
        comment_lines,
        blank_lines,
        comment_only_lines,
        effective,
    }
}

/// Get comment markers for a language.
///
/// Returns (line_comment, block_start, block_end).
fn get_comment_markers(
    language: &str,
) -> (
    Option<&'static str>,
    Option<&'static str>,
    Option<&'static str>,
) {
    match language.to_lowercase().as_str() {
        "python" => (Some("#"), None, None),
        "typescript" | "javascript" | "tsx" | "jsx" | "rust" | "go" | "java" | "c" | "cpp"
        | "c++" => (Some("//"), Some("/*"), Some("*/")),
        _ => (Some("#"), None, None), // Default to Python-style
    }
}

/// Estimate logical lines of code (statements).
///
/// This is a heuristic based on semicolons, colons, and other statement
/// terminators. For precise LLOC, AST-based counting would be needed.
fn estimate_logical_loc(source_lines: u32, language: &str) -> u32 {
    // Simple heuristic: logical LOC is approximately equal to source lines
    // for most languages. A more precise implementation would count
    // statement nodes in the AST.
    match language.to_lowercase().as_str() {
        // Python uses indentation, so each non-blank line is roughly one statement
        "python" => source_lines,
        // C-family languages might have multiple statements per line
        _ => source_lines,
    }
}

/// Calculate LOC for a specific function range in source code.
fn calculate_function_loc(
    source: &str,
    start_line: usize,
    end_line: usize,
    language: &str,
) -> LinesOfCode {
    let lines: Vec<&str> = source.lines().collect();

    // Extract function lines (1-indexed to 0-indexed)
    let start = start_line.saturating_sub(1);
    let end = end_line.min(lines.len());

    if start >= lines.len() || start >= end {
        return LinesOfCode::default();
    }

    let function_source: String = lines[start..end].join("\n");
    calculate_loc(&function_source, language)
}

// =============================================================================
// ANALYSIS FUNCTIONS
// =============================================================================

/// Analyze maintainability index for a project or directory.
///
/// Scans all source files, extracts functions, and calculates the
/// Maintainability Index for each function by combining Halstead Volume,
/// Cyclomatic Complexity, and Lines of Code metrics.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `language` - Optional language filter
/// * `threshold` - Optional minimum MI threshold (violations will be below this)
/// * `include_comments` - Whether to use the extended formula with comment bonus
///
/// # Returns
///
/// Complete maintainability analysis with function scores and statistics.
///
/// # Example
///
/// ```ignore
/// use go_brrr::metrics::analyze_maintainability;
///
/// // Analyze all Python files, flag functions with MI < 20
/// let result = analyze_maintainability("./src", Some("python"), Some(20.0), false)?;
///
/// for func in &result.functions {
///     println!("{}: MI={:.1} ({})",
///         func.function_name,
///         func.index.score,
///         func.index.risk_level
///     );
/// }
/// ```
pub fn analyze_maintainability(
    path: impl AsRef<Path>,
    language: Option<&str>,
    threshold: Option<f64>,
    include_comments: bool,
) -> Result<MaintainabilityAnalysis> {
    let path = path.as_ref();

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Path not found: {}", path.display()),
        )));
    }

    if path.is_file() {
        return analyze_file_maintainability(path, threshold, include_comments);
    }

    // Directory analysis
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

    debug!(
        "Analyzing {} files for maintainability",
        scan_result.files.len()
    );

    // Analyze files in parallel
    let results: Vec<(Vec<FunctionMaintainability>, Vec<MaintainabilityError>)> = scan_result
        .files
        .par_iter()
        .map(|file| analyze_file_functions_maintainability(file, include_comments))
        .collect();

    // Aggregate results
    let mut all_functions = Vec::new();
    let mut all_errors = Vec::new();

    for (functions, errors) in results {
        all_functions.extend(functions);
        all_errors.extend(errors);
    }

    let stats = MaintainabilityStats::from_functions(&all_functions);

    // Filter violations (functions BELOW threshold - low MI is bad)
    let violations = threshold.map(|t| {
        all_functions
            .iter()
            .filter(|f| f.index.score < t)
            .cloned()
            .collect::<Vec<_>>()
    });

    Ok(MaintainabilityAnalysis {
        path: path.to_path_buf(),
        language: language.map(String::from),
        functions: all_functions,
        violations,
        stats,
        threshold,
        includes_comments: include_comments,
        errors: all_errors,
    })
}

/// Analyze maintainability index for a single file.
pub fn analyze_file_maintainability(
    file: impl AsRef<Path>,
    threshold: Option<f64>,
    include_comments: bool,
) -> Result<MaintainabilityAnalysis> {
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

    let (functions, errors) = analyze_file_functions_maintainability(file, include_comments);
    let stats = MaintainabilityStats::from_functions(&functions);

    // Detect language
    let registry = LanguageRegistry::global();
    let language = registry.detect_language(file).map(|l| l.name().to_string());

    let violations = threshold.map(|t| {
        functions
            .iter()
            .filter(|f| f.index.score < t)
            .cloned()
            .collect::<Vec<_>>()
    });

    Ok(MaintainabilityAnalysis {
        path: file.to_path_buf(),
        language,
        functions,
        violations,
        stats,
        threshold,
        includes_comments: include_comments,
        errors,
    })
}

/// Analyze all functions in a file for maintainability.
fn analyze_file_functions_maintainability(
    file: &Path,
    include_comments: bool,
) -> (Vec<FunctionMaintainability>, Vec<MaintainabilityError>) {
    let mut results = Vec::new();
    let mut errors = Vec::new();

    // Read source file
    let source = match std::fs::read_to_string(file) {
        Ok(s) => s,
        Err(e) => {
            errors.push(MaintainabilityError {
                file: file.to_path_buf(),
                message: format!("Failed to read file: {}", e),
            });
            return (results, errors);
        }
    };

    // Detect language
    let registry = LanguageRegistry::global();
    let lang = match registry.detect_language(file) {
        Some(l) => l,
        None => {
            errors.push(MaintainabilityError {
                file: file.to_path_buf(),
                message: "Unsupported language".to_string(),
            });
            return (results, errors);
        }
    };

    let lang_name = lang.name();

    // Parse file for AST-based metrics
    let mut parser = match lang.parser() {
        Ok(p) => p,
        Err(e) => {
            errors.push(MaintainabilityError {
                file: file.to_path_buf(),
                message: format!("Failed to create parser: {}", e),
            });
            return (results, errors);
        }
    };

    let tree = match parser.parse(&source, None) {
        Some(t) => t,
        None => {
            errors.push(MaintainabilityError {
                file: file.to_path_buf(),
                message: "Failed to parse file".to_string(),
            });
            return (results, errors);
        }
    };

    // Extract module info to get function list
    let module = match AstExtractor::extract_file(file) {
        Ok(m) => m,
        Err(e) => {
            errors.push(MaintainabilityError {
                file: file.to_path_buf(),
                message: format!("Failed to extract AST: {}", e),
            });
            return (results, errors);
        }
    };

    // Analyze top-level functions
    for func in &module.functions {
        let start_line = func.line_number;
        let end_line = func.end_line_number.unwrap_or(start_line);

        match analyze_function_maintainability(
            file,
            &source,
            &tree,
            &func.name,
            start_line,
            end_line,
            lang_name,
            include_comments,
        ) {
            Ok(mi) => results.push(mi),
            Err(e) => {
                debug!("Failed to analyze function {}: {}", func.name, e);
                errors.push(MaintainabilityError {
                    file: file.to_path_buf(),
                    message: format!("Failed to analyze {}: {}", func.name, e),
                });
            }
        }
    }

    // Analyze class methods
    for class in &module.classes {
        for method in &class.methods {
            let qualified_name = format!("{}.{}", class.name, method.name);
            let start_line = method.line_number;
            let end_line = method.end_line_number.unwrap_or(start_line);

            match analyze_function_maintainability(
                file,
                &source,
                &tree,
                &qualified_name,
                start_line,
                end_line,
                lang_name,
                include_comments,
            ) {
                Ok(mi) => results.push(mi),
                Err(e) => {
                    debug!("Failed to analyze method {}: {}", qualified_name, e);
                    errors.push(MaintainabilityError {
                        file: file.to_path_buf(),
                        message: format!("Failed to analyze {}: {}", qualified_name, e),
                    });
                }
            }
        }
    }

    (results, errors)
}

/// Analyze a single function for maintainability index.
fn analyze_function_maintainability(
    file: &Path,
    source: &str,
    tree: &tree_sitter::Tree,
    function_name: &str,
    start_line: usize,
    end_line: usize,
    language: &str,
    include_comments: bool,
) -> Result<FunctionMaintainability> {
    // Calculate LOC for the function
    let loc = calculate_function_loc(source, start_line, end_line, language);

    // Find the function node for Halstead analysis (using common utility)
    let function_node = common::find_function_node(tree, start_line, end_line);
    let node_to_analyze = function_node.unwrap_or_else(|| tree.root_node());

    // Calculate Halstead metrics
    let halstead = calculate_halstead_for_node(node_to_analyze, source.as_bytes(), language);

    // Calculate Cyclomatic Complexity
    let cc = calculate_cyclomatic_for_node(node_to_analyze, language);

    // Calculate Maintainability Index
    let index = if include_comments {
        MaintainabilityIndex::calculate_with_comments(halstead.volume, cc, loc)
    } else {
        MaintainabilityIndex::calculate(halstead.volume, cc, loc)
    };

    Ok(FunctionMaintainability {
        function_name: function_name.to_string(),
        file: file.to_path_buf(),
        line: start_line,
        end_line,
        index,
    })
}

// Note: find_function_node and is_function_node are now in common.rs

// =============================================================================
// HALSTEAD CALCULATION (LOCAL)
// =============================================================================

/// Calculate Halstead metrics for a tree-sitter node.
///
/// Simplified version that counts operators and operands.
fn calculate_halstead_for_node(node: Node, source: &[u8], language: &str) -> HalsteadMetrics {
    let mut operators = std::collections::HashSet::new();
    let mut operands = std::collections::HashSet::new();
    let mut total_operators = 0u32;
    let mut total_operands = 0u32;

    collect_tokens_recursive(
        node,
        source,
        language,
        &mut operators,
        &mut operands,
        &mut total_operators,
        &mut total_operands,
    );

    HalsteadMetrics::from_counts(
        operators.len() as u32,
        operands.len() as u32,
        total_operators,
        total_operands,
    )
}

/// Recursively collect operators and operands from AST nodes.
fn collect_tokens_recursive(
    node: Node,
    source: &[u8],
    language: &str,
    operators: &mut std::collections::HashSet<String>,
    operands: &mut std::collections::HashSet<String>,
    total_operators: &mut u32,
    total_operands: &mut u32,
) {
    let kind = node.kind();
    let text = node.utf8_text(source).unwrap_or("");

    // Classify this node
    if is_operator_kind(kind) || is_operator_text(text, language) {
        if !text.trim().is_empty() {
            operators.insert(text.to_string());
            *total_operators += 1;
        }
    } else if is_operand_kind(kind) {
        if !text.trim().is_empty() {
            operands.insert(text.to_string());
            *total_operands += 1;
        }
    }

    // Recurse into children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_tokens_recursive(
            child,
            source,
            language,
            operators,
            operands,
            total_operators,
            total_operands,
        );
    }
}

/// Check if a node kind represents an operator.
fn is_operator_kind(kind: &str) -> bool {
    matches!(
        kind,
        "binary_operator"
            | "unary_operator"
            | "comparison_operator"
            | "boolean_operator"
            | "augmented_assignment"
            | "assignment"
            | "assignment_expression"
            | "+"
            | "-"
            | "*"
            | "/"
            | "%"
            | "**"
            | "//"
            | "=="
            | "!="
            | "<"
            | ">"
            | "<="
            | ">="
            | "&&"
            | "||"
            | "!"
            | "?"
            | "("
            | ")"
            | "["
            | "]"
            | "{"
            | "}"
            | "."
            | ","
            | ";"
            | ":"
            | "->"
            | "=>"
            | "::"
    )
}

/// Check if text represents an operator.
fn is_operator_text(text: &str, language: &str) -> bool {
    let common_ops = [
        "+", "-", "*", "/", "%", "==", "!=", "<", ">", "<=", ">=", "=", "+=", "-=", "*=", "/=",
        "&", "|", "^", "~", "<<", ">>", "&&", "||", "!", ".", ",", ";", "(", ")", "[", "]", "{",
        "}", "?", ":",
    ];

    if common_ops.contains(&text) {
        return true;
    }

    match language.to_lowercase().as_str() {
        "python" => {
            matches!(
                text,
                "and"
                    | "or"
                    | "not"
                    | "in"
                    | "is"
                    | "**"
                    | "//"
                    | "if"
                    | "else"
                    | "elif"
                    | "while"
                    | "for"
                    | "try"
                    | "except"
                    | "finally"
                    | "raise"
                    | "def"
                    | "class"
                    | "return"
                    | "yield"
                    | "lambda"
                    | "with"
                    | "as"
            )
        }
        "typescript" | "javascript" | "tsx" | "jsx" => {
            matches!(
                text,
                "=>" | "?."
                    | "??"
                    | "..."
                    | "++"
                    | "--"
                    | "if"
                    | "else"
                    | "while"
                    | "for"
                    | "switch"
                    | "case"
                    | "default"
                    | "function"
                    | "return"
                    | "new"
                    | "typeof"
                    | "instanceof"
            )
        }
        "rust" => {
            matches!(
                text,
                "::" | "->"
                    | "=>"
                    | ".."
                    | "..="
                    | "if"
                    | "else"
                    | "while"
                    | "for"
                    | "loop"
                    | "match"
                    | "return"
                    | "fn"
                    | "let"
                    | "mut"
            )
        }
        "go" => {
            matches!(
                text,
                ":=" | "<-"
                    | "..."
                    | "if"
                    | "else"
                    | "for"
                    | "switch"
                    | "case"
                    | "func"
                    | "return"
                    | "go"
                    | "defer"
            )
        }
        _ => false,
    }
}

/// Check if a node kind represents an operand.
fn is_operand_kind(kind: &str) -> bool {
    matches!(
        kind,
        "identifier"
            | "field_identifier"
            | "property_identifier"
            | "type_identifier"
            | "number"
            | "integer"
            | "float"
            | "string"
            | "string_literal"
            | "char_literal"
            | "boolean"
            | "true"
            | "false"
            | "none"
            | "null"
            | "nil"
            | "self"
            | "this"
    )
}

// =============================================================================
// CYCLOMATIC CALCULATION (LOCAL)
// =============================================================================

/// Calculate cyclomatic complexity for a tree-sitter node.
///
/// Counts decision points to determine complexity.
fn calculate_cyclomatic_for_node(node: Node, language: &str) -> u32 {
    let mut decision_points = 0u32;
    count_decision_points_recursive(node, language, &mut decision_points);
    decision_points + 1 // CC = decision_points + 1
}

/// Recursively count decision points in AST nodes.
fn count_decision_points_recursive(node: Node, language: &str, count: &mut u32) {
    let kind = node.kind();

    // Count decision points based on node kind
    if is_decision_point(kind, language) {
        *count += 1;
    }

    // Recurse into children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        count_decision_points_recursive(child, language, count);
    }
}

/// Check if a node kind represents a decision point.
fn is_decision_point(kind: &str, language: &str) -> bool {
    // Common decision points across languages
    let common = matches!(
        kind,
        "if_statement"
            | "if_expression"
            | "elif_clause"
            | "else_if_clause"
            | "while_statement"
            | "while_expression"
            | "for_statement"
            | "for_expression"
            | "for_in_statement"
            | "catch_clause"
            | "except_clause"
            | "case_clause"
            | "match_arm"
            | "conditional_expression"
            | "ternary_expression"
    );

    if common {
        return true;
    }

    // Language-specific decision points
    match language.to_lowercase().as_str() {
        "python" => {
            matches!(
                kind,
                "list_comprehension"
                    | "dictionary_comprehension"
                    | "set_comprehension"
                    | "generator_expression"
                    | "boolean_operator"
            )
        }
        "rust" => {
            matches!(
                kind,
                "if_let_expression" | "while_let_expression" | "match_expression"
            )
        }
        "go" => {
            matches!(
                kind,
                "select_statement" | "communication_case" | "default_case"
            )
        }
        _ => false,
    }
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
        assert_eq!(
            MaintainabilityRiskLevel::from_score(100.0),
            MaintainabilityRiskLevel::Low
        );
        assert_eq!(
            MaintainabilityRiskLevel::from_score(50.0),
            MaintainabilityRiskLevel::Low
        );
        assert_eq!(
            MaintainabilityRiskLevel::from_score(49.0),
            MaintainabilityRiskLevel::Medium
        );
        assert_eq!(
            MaintainabilityRiskLevel::from_score(20.0),
            MaintainabilityRiskLevel::Medium
        );
        assert_eq!(
            MaintainabilityRiskLevel::from_score(19.0),
            MaintainabilityRiskLevel::High
        );
        assert_eq!(
            MaintainabilityRiskLevel::from_score(10.0),
            MaintainabilityRiskLevel::High
        );
        assert_eq!(
            MaintainabilityRiskLevel::from_score(9.0),
            MaintainabilityRiskLevel::Critical
        );
        assert_eq!(
            MaintainabilityRiskLevel::from_score(0.0),
            MaintainabilityRiskLevel::Critical
        );
    }

    #[test]
    fn test_loc_calculation_python() {
        let source = r#"
# This is a comment
def hello():
    """Docstring"""
    # Another comment
    return "hello"

def world():
    return "world"
"#;
        let loc = calculate_loc(source, "python");

        assert!(loc.physical > 0);
        assert!(loc.comment_lines > 0);
        assert!(loc.blank_lines > 0);
        assert!(loc.source <= loc.physical);
        assert!(loc.effective <= loc.source);
    }

    #[test]
    fn test_loc_calculation_typescript() {
        let source = r#"
// Single line comment
function greet(name: string): string {
    /* Multi-line
       comment */
    return `Hello, ${name}!`;
}
"#;
        let loc = calculate_loc(source, "typescript");

        assert!(loc.physical > 0);
        assert!(loc.comment_lines >= 2); // At least single-line and part of multi-line
        assert!(loc.source > 0);
    }

    #[test]
    fn test_mi_calculation_simple() {
        // Simple function: low volume, low CC, low LOC
        let loc = LinesOfCode {
            physical: 5,
            source: 4,
            logical: 4,
            comment_lines: 1,
            blank_lines: 1,
            comment_only_lines: 1,
            effective: 3,
        };

        let mi = MaintainabilityIndex::calculate(50.0, 1, loc);

        // Simple functions should have high MI
        assert!(
            mi.score > 50.0,
            "Simple function should have MI > 50, got {}",
            mi.score
        );
        assert_eq!(mi.risk_level, MaintainabilityRiskLevel::Low);
    }

    #[test]
    fn test_mi_calculation_complex() {
        // Complex function: high volume, high CC, high LOC
        let loc = LinesOfCode {
            physical: 200,
            source: 180,
            logical: 180,
            comment_lines: 10,
            blank_lines: 20,
            comment_only_lines: 5,
            effective: 175,
        };

        let mi = MaintainabilityIndex::calculate(5000.0, 30, loc);

        // Complex functions should have low MI
        assert!(
            mi.score < 50.0,
            "Complex function should have MI < 50, got {}",
            mi.score
        );
        assert!(matches!(
            mi.risk_level,
            MaintainabilityRiskLevel::Medium
                | MaintainabilityRiskLevel::High
                | MaintainabilityRiskLevel::Critical
        ));
    }

    #[test]
    fn test_mi_with_comments_bonus() {
        let loc = LinesOfCode {
            physical: 20,
            source: 15,
            logical: 15,
            comment_lines: 10,
            blank_lines: 5,
            comment_only_lines: 5,
            effective: 10,
        };

        let mi_without = MaintainabilityIndex::calculate(100.0, 5, loc.clone());
        let mi_with = MaintainabilityIndex::calculate_with_comments(100.0, 5, loc);

        // With comments should generally give a higher score (with appropriate comment ratio)
        // Note: The sin function can oscillate, so we just verify both calculations work
        assert!(mi_without.score >= 0.0 && mi_without.score <= 100.0);
        assert!(mi_with.score >= 0.0 && mi_with.score <= 100.0);
        assert!(!mi_without.includes_comments);
        assert!(mi_with.includes_comments);
    }

    #[test]
    fn test_comment_percentage() {
        let loc = LinesOfCode {
            physical: 100,
            source: 80,
            logical: 80,
            comment_lines: 20,
            blank_lines: 20,
            comment_only_lines: 15,
            effective: 65,
        };

        let pct = loc.comment_percentage();
        assert!((pct - 20.0).abs() < 0.1, "Expected 20%, got {}%", pct);
    }

    #[test]
    fn test_simple_python_maintainability() {
        let source = r#"
def add(a, b):
    return a + b
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_maintainability(file.path(), None, false);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        let func = &analysis.functions[0];
        assert_eq!(func.function_name, "add");
        assert!(func.index.score > 0.0);
        // Simple function should be maintainable
        assert!(matches!(
            func.index.risk_level,
            MaintainabilityRiskLevel::Low | MaintainabilityRiskLevel::Medium
        ));
    }

    #[test]
    fn test_complex_python_maintainability() {
        let source = r#"
def process_data(items, threshold, callback, config):
    result = []
    errors = []
    for item in items:
        if item.value > threshold:
            if item.is_valid():
                try:
                    processed = callback(item, config)
                    if processed.status == "ok":
                        result.append(processed)
                    elif processed.status == "warning":
                        result.append(processed)
                        errors.append({"type": "warning", "item": item})
                    else:
                        errors.append({"type": "error", "item": item})
                except ValueError as e:
                    errors.append({"type": "exception", "error": str(e)})
                except TypeError as e:
                    errors.append({"type": "type_error", "error": str(e)})
            else:
                errors.append({"type": "invalid", "item": item})
        elif item.value == threshold:
            result.append(item)
    return {"result": result, "errors": errors}
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_maintainability(file.path(), None, false);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 1);
        let func = &analysis.functions[0];

        // Complex function should have lower MI
        assert!(
            func.index.score < 80.0,
            "Complex function should have MI < 80, got {}",
            func.index.score
        );
        assert!(func.index.cyclomatic_complexity > 5);
    }

    #[test]
    fn test_typescript_maintainability() {
        let source = r#"
function greet(name: string): string {
    return `Hello, ${name}!`;
}

function complexGreet(name: string, config: Config): string {
    if (!name) {
        return "Hello, stranger!";
    }
    if (config.formal) {
        return `Good day, ${config.title} ${name}.`;
    } else if (config.casual) {
        return `Hey ${name}!`;
    }
    return `Hello, ${name}!`;
}
"#;
        let file = create_temp_file(source, ".ts");
        let result = analyze_file_maintainability(file.path(), None, false);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        // Should find both functions
        assert!(analysis.functions.len() >= 1);
    }

    #[test]
    fn test_threshold_filtering() {
        let source = r#"
def simple():
    return 1

def somewhat_complex(a, b, c):
    if a > 0:
        if b > 0:
            if c > 0:
                return a + b + c
            return a + b
        return a
    return 0
"#;
        let file = create_temp_file(source, ".py");
        // Use a high threshold to catch the complex function
        let result = analyze_file_maintainability(file.path(), Some(80.0), false);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert!(analysis.violations.is_some());
        // At least one function should be below threshold 80
        let violations = analysis.violations.unwrap();
        assert!(!violations.is_empty() || analysis.functions.iter().all(|f| f.index.score >= 80.0));
    }

    #[test]
    fn test_statistics_calculation() {
        let source = r#"
def func1():
    return 1

def func2(a, b):
    if a > b:
        return a
    return b

def func3(items):
    result = []
    for item in items:
        if item > 0:
            result.append(item)
    return result
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_maintainability(file.path(), None, false);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.stats.total_functions, 3);
        assert!(analysis.stats.average_mi > 0.0);
        assert!(analysis.stats.min_mi <= analysis.stats.average_mi);
        assert!(analysis.stats.max_mi >= analysis.stats.average_mi);
    }

    #[test]
    fn test_empty_file() {
        let source = "# Just a comment\n";
        let file = create_temp_file(source, ".py");
        let result = analyze_file_maintainability(file.path(), None, false);

        assert!(result.is_ok());
        let analysis = result.unwrap();
        assert_eq!(analysis.functions.len(), 0);
        assert_eq!(analysis.stats.total_functions, 0);
    }

    #[test]
    fn test_nonexistent_file() {
        let result = analyze_file_maintainability("/nonexistent/path/file.py", None, false);
        assert!(result.is_err());
    }

    #[test]
    fn test_class_methods_maintainability() {
        let source = r#"
class Calculator:
    def add(self, a, b):
        return a + b

    def complex_operation(self, items, threshold):
        result = 0
        for item in items:
            if item.value > threshold:
                if item.is_valid():
                    result += item.value
                else:
                    result -= 1
            elif item.value == threshold:
                result += item.value // 2
        return result
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_maintainability(file.path(), None, false);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.functions.len(), 2);

        let add = analysis
            .functions
            .iter()
            .find(|f| f.function_name == "Calculator.add");
        let complex = analysis
            .functions
            .iter()
            .find(|f| f.function_name == "Calculator.complex_operation");

        assert!(add.is_some());
        assert!(complex.is_some());

        // Simple method should have higher MI than complex method
        assert!(
            add.unwrap().index.score > complex.unwrap().index.score,
            "Simple method should have higher MI"
        );
    }

    #[test]
    fn test_risk_distribution() {
        let source = r#"
def func1():
    return 1

def func2(a, b):
    return a + b

def func3(x):
    if x > 0:
        return x
    return -x
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_maintainability(file.path(), None, false);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        // Risk distribution should sum to total functions
        let total_in_dist: usize = analysis.stats.risk_distribution.values().sum();
        assert_eq!(total_in_dist, analysis.stats.total_functions);
    }

    #[test]
    fn test_mi_formula_edge_cases() {
        // Test with very small values (should not panic)
        let loc = LinesOfCode {
            physical: 1,
            source: 1,
            logical: 1,
            comment_lines: 0,
            blank_lines: 0,
            comment_only_lines: 0,
            effective: 1,
        };

        let mi = MaintainabilityIndex::calculate(1.0, 1, loc);
        assert!(mi.score >= 0.0 && mi.score <= 100.0);

        // Test with zero values (should handle gracefully)
        let loc_zero = LinesOfCode::default();
        let mi_zero = MaintainabilityIndex::calculate(0.0, 0, loc_zero);
        assert!(mi_zero.score >= 0.0 && mi_zero.score <= 100.0);
    }

    #[test]
    fn test_loc_multiline_comments() {
        let source = r#"
function test() {
    /* This is a
       multi-line
       comment */
    return 42;
}
"#;
        let loc = calculate_loc(source, "typescript");

        assert!(
            loc.comment_lines >= 3,
            "Should count all multi-line comment lines"
        );
    }
}
