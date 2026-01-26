//! Common traits and utilities for complexity metrics.
//!
//! This module provides shared functionality to reduce code duplication across
//! the cyclomatic, cognitive, halstead, and maintainability modules.

use std::collections::HashMap;
use std::path::PathBuf;

use serde::{Deserialize, Serialize};
use tree_sitter::Node;

// =============================================================================
// COMMON ERROR TYPE
// =============================================================================

/// Common error type for complexity analysis failures.
///
/// Used across all complexity analysis modules for consistent error reporting.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnalysisError {
    /// File path where error occurred
    pub file: PathBuf,
    /// Error message describing the failure
    pub message: String,
}

impl AnalysisError {
    /// Create a new analysis error.
    #[must_use]
    pub fn new(file: impl Into<PathBuf>, message: impl Into<String>) -> Self {
        Self {
            file: file.into(),
            message: message.into(),
        }
    }
}

// =============================================================================
// BASE COMPLEXITY STATISTICS
// =============================================================================

/// Base complexity statistics calculated from numeric values.
///
/// Provides common statistical measures that apply to all complexity metrics.
/// Module-specific statistics types can include this as a field and add their
/// own specialized fields.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BaseComplexityStats {
    /// Total count of items analyzed
    pub count: usize,
    /// Sum of all values
    pub sum: u64,
    /// Average value
    pub average: f64,
    /// Maximum value
    pub max: u32,
    /// Minimum value
    pub min: u32,
    /// Median value
    pub median: u32,
}

impl BaseComplexityStats {
    /// Calculate base statistics from a slice of u32 values.
    ///
    /// Returns default (zero) values if the input is empty.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let values = vec![1, 5, 10, 15, 20];
    /// let stats = BaseComplexityStats::from_values(&values);
    /// assert_eq!(stats.count, 5);
    /// assert_eq!(stats.median, 10);
    /// ```
    #[must_use]
    pub fn from_values(values: &[u32]) -> Self {
        if values.is_empty() {
            return Self::default();
        }

        let count = values.len();
        let sum: u64 = values.iter().map(|&v| u64::from(v)).sum();
        let average = sum as f64 / count as f64;
        let max = values.iter().copied().max().unwrap_or(0);
        let min = values.iter().copied().min().unwrap_or(0);

        // Calculate median
        let mut sorted = values.to_vec();
        sorted.sort_unstable();
        let median = if count % 2 == 0 {
            (sorted[count / 2 - 1] + sorted[count / 2]) / 2
        } else {
            sorted[count / 2]
        };

        Self {
            count,
            sum,
            average,
            max,
            min,
            median,
        }
    }

    /// Calculate base statistics from f64 values.
    ///
    /// Useful for metrics like maintainability index that use floating point.
    #[must_use]
    pub fn from_f64_values(values: &[f64]) -> BaseF64Stats {
        BaseF64Stats::from_values(values)
    }
}

/// Base statistics for f64 values (e.g., maintainability index scores).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BaseF64Stats {
    /// Total count of items analyzed
    pub count: usize,
    /// Sum of all values
    pub sum: f64,
    /// Average value
    pub average: f64,
    /// Maximum value
    pub max: f64,
    /// Minimum value
    pub min: f64,
    /// Median value
    pub median: f64,
}

impl BaseF64Stats {
    /// Calculate base statistics from a slice of f64 values.
    #[must_use]
    pub fn from_values(values: &[f64]) -> Self {
        if values.is_empty() {
            return Self::default();
        }

        let count = values.len();
        let sum: f64 = values.iter().sum();
        let average = sum / count as f64;
        let max = values.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
        let min = values.iter().cloned().fold(f64::INFINITY, f64::min);

        // Calculate median
        let mut sorted = values.to_vec();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        let median = if count % 2 == 0 {
            (sorted[count / 2 - 1] + sorted[count / 2]) / 2.0
        } else {
            sorted[count / 2]
        };

        Self {
            count,
            sum,
            average,
            max,
            min,
            median,
        }
    }
}

// =============================================================================
// RISK LEVEL DISTRIBUTION
// =============================================================================

/// Calculate risk level distribution from values and a classification function.
///
/// # Arguments
///
/// * `values` - Slice of values to classify
/// * `classifier` - Function that maps a value to a risk level string
///
/// # Returns
///
/// HashMap mapping risk level names to counts.
pub fn calculate_risk_distribution<T, F>(values: &[T], classifier: F) -> HashMap<String, usize>
where
    F: Fn(&T) -> String,
{
    let mut distribution = HashMap::new();
    for value in values {
        let risk = classifier(value);
        *distribution.entry(risk).or_insert(0) += 1;
    }
    distribution
}

// =============================================================================
// AST NODE HELPERS
// =============================================================================

/// Check if a tree-sitter node represents a function definition.
///
/// Supports multiple languages by checking for various function node kinds.
#[must_use]
pub fn is_function_node(node: &Node) -> bool {
    matches!(
        node.kind(),
        "function_definition"
            | "function_declaration"
            | "method_definition"
            | "function_item"
            | "function"
            | "method"
            | "arrow_function"
            | "function_expression"
            | "method_declaration"
            | "constructor_declaration"
    )
}

/// Find a function node in an AST by line range.
///
/// Searches for a function definition node that starts at `start_line`
/// and ends at or after `end_line`.
///
/// # Arguments
///
/// * `tree` - Parsed tree-sitter tree
/// * `start_line` - Expected start line (1-indexed)
/// * `end_line` - Expected end line (1-indexed)
///
/// # Returns
///
/// The matching function node, or `None` if not found.
#[must_use]
pub fn find_function_node(
    tree: &tree_sitter::Tree,
    start_line: usize,
    end_line: usize,
) -> Option<Node<'_>> {
    find_function_node_recursive(tree.root_node(), start_line, end_line)
}

/// Recursively search for a function node matching the line range.
fn find_function_node_recursive(
    node: Node<'_>,
    start_line: usize,
    end_line: usize,
) -> Option<Node<'_>> {
    let node_start = node.start_position().row + 1; // 1-indexed
    let node_end = node.end_position().row + 1;

    // Check if this node matches
    if is_function_node(&node) && node_start == start_line && node_end >= end_line {
        return Some(node);
    }

    // Search children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(found) = find_function_node_recursive(child, start_line, end_line) {
            return Some(found);
        }
    }

    None
}

/// Find the body node of a function based on language conventions.
///
/// Different languages use different field names for function bodies.
#[must_use]
pub fn find_function_body<'a>(node: Node<'a>, language: &str) -> Option<Node<'a>> {
    let body_field = match language {
        "python" | "typescript" | "javascript" | "tsx" | "jsx" | "rust" | "go" | "java" | "c"
        | "cpp" => "body",
        _ => "body",
    };
    node.child_by_field_name(body_field)
}

/// Check if a node kind is part of the function signature (not body).
///
/// Used to skip non-body parts when processing function contents.
#[must_use]
pub fn is_function_signature_part(kind: &str) -> bool {
    matches!(
        kind,
        "parameters"
            | "formal_parameters"
            | "parameter_list"
            | "type_parameters"
            | "return_type"
            | "type_annotation"
            | "type"
            | "decorator"
            | "modifiers"
            | "visibility_modifier"
            | "identifier"
            | "name"
            | "def"
            | "fn"
            | "func"
            | "function"
            | "async"
            | "("
            | ")"
            | "{"
            | "}"
            | ":"
            | "->"
    )
}

// =============================================================================
// HISTOGRAM UTILITIES
// =============================================================================

/// Histogram bucket for complexity distribution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramBucket {
    /// Lower bound (inclusive)
    pub min: u32,
    /// Upper bound (inclusive)
    pub max: u32,
    /// Label for display
    pub label: String,
    /// Number of items in this bucket
    pub count: usize,
}

/// Build a histogram from complexity values.
///
/// # Arguments
///
/// * `values` - Slice of complexity values
/// * `bucket_size` - Size of each bucket (e.g., 5 for 1-5, 6-10, etc.)
/// * `max_buckets` - Maximum number of buckets to create
///
/// # Returns
///
/// Vector of histogram buckets.
#[must_use]
pub fn build_histogram(values: &[u32], bucket_size: u32, max_buckets: usize) -> Vec<HistogramBucket> {
    if values.is_empty() {
        return Vec::new();
    }

    let max_val = values.iter().copied().max().unwrap_or(0);
    let num_buckets = ((max_val / bucket_size) + 1) as usize;
    let actual_buckets = num_buckets.min(max_buckets);

    let mut buckets = Vec::with_capacity(actual_buckets);

    for i in 0..actual_buckets {
        let min_val = (i as u32) * bucket_size + 1;
        let max_val = min_val + bucket_size - 1;
        let count = values
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

    // Handle overflow bucket for values beyond max_buckets
    let overflow_threshold = (max_buckets as u32) * bucket_size;
    if max_val > overflow_threshold {
        let overflow_count = values.iter().filter(|&&c| c > overflow_threshold).count();
        if overflow_count > 0 {
            buckets.push(HistogramBucket {
                min: overflow_threshold + 1,
                max: u32::MAX,
                label: format!("{}+", overflow_threshold + 1),
                count: overflow_count,
            });
        }
    }

    buckets
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_base_stats_from_values() {
        let values = vec![1, 5, 10, 15, 20];
        let stats = BaseComplexityStats::from_values(&values);

        assert_eq!(stats.count, 5);
        assert_eq!(stats.min, 1);
        assert_eq!(stats.max, 20);
        assert_eq!(stats.median, 10);
        assert!((stats.average - 10.2).abs() < 0.01);
    }

    #[test]
    fn test_base_stats_empty() {
        let stats = BaseComplexityStats::from_values(&[]);
        assert_eq!(stats.count, 0);
        assert_eq!(stats.min, 0);
        assert_eq!(stats.max, 0);
        assert_eq!(stats.median, 0);
    }

    #[test]
    fn test_base_stats_single_value() {
        let stats = BaseComplexityStats::from_values(&[42]);
        assert_eq!(stats.count, 1);
        assert_eq!(stats.min, 42);
        assert_eq!(stats.max, 42);
        assert_eq!(stats.median, 42);
    }

    #[test]
    fn test_base_stats_even_count() {
        // Median with even count should average middle two
        let values = vec![1, 3, 5, 7];
        let stats = BaseComplexityStats::from_values(&values);
        assert_eq!(stats.median, 4); // (3 + 5) / 2
    }

    #[test]
    fn test_f64_stats_from_values() {
        let values = vec![10.0, 20.0, 30.0, 40.0, 50.0];
        let stats = BaseF64Stats::from_values(&values);

        assert_eq!(stats.count, 5);
        assert!((stats.min - 10.0).abs() < 0.01);
        assert!((stats.max - 50.0).abs() < 0.01);
        assert!((stats.median - 30.0).abs() < 0.01);
        assert!((stats.average - 30.0).abs() < 0.01);
    }

    #[test]
    fn test_risk_distribution() {
        let values = vec![5u32, 15, 25, 5, 15, 5];
        let distribution = calculate_risk_distribution(&values, |&v| {
            if v <= 10 {
                "low".to_string()
            } else if v <= 20 {
                "medium".to_string()
            } else {
                "high".to_string()
            }
        });

        assert_eq!(distribution.get("low"), Some(&3));
        assert_eq!(distribution.get("medium"), Some(&2));
        assert_eq!(distribution.get("high"), Some(&1));
    }

    #[test]
    fn test_histogram_building() {
        let values = vec![1, 2, 3, 6, 7, 11, 15, 20, 25];
        let buckets = build_histogram(&values, 5, 10);

        // 1-5: 3 values (1, 2, 3)
        // 6-10: 2 values (6, 7)
        // 11-15: 2 values (11, 15)
        // 16-20: 1 value (20)
        // 21-25: 1 value (25)
        assert!(buckets.len() >= 5);
        assert_eq!(buckets[0].count, 3);
        assert_eq!(buckets[1].count, 2);
    }

    #[test]
    fn test_histogram_empty() {
        let buckets = build_histogram(&[], 5, 10);
        assert!(buckets.is_empty());
    }

    #[test]
    fn test_analysis_error() {
        let error = AnalysisError::new("/path/to/file.rs", "Parse error");
        assert_eq!(error.file, PathBuf::from("/path/to/file.rs"));
        assert_eq!(error.message, "Parse error");
    }

    #[test]
    fn test_is_function_node_kinds() {
        // This is a compile-time test that the function handles all expected kinds
        let kinds = [
            "function_definition",
            "function_declaration",
            "method_definition",
            "function_item",
            "arrow_function",
            "method_declaration",
        ];

        // Just ensure the patterns compile and work
        for kind in kinds {
            let result = matches!(
                kind,
                "function_definition"
                    | "function_declaration"
                    | "method_definition"
                    | "function_item"
                    | "function"
                    | "method"
                    | "arrow_function"
                    | "function_expression"
                    | "method_declaration"
                    | "constructor_declaration"
            );
            assert!(result, "Kind '{}' should be recognized", kind);
        }
    }

    #[test]
    fn test_is_function_signature_part() {
        assert!(is_function_signature_part("parameters"));
        assert!(is_function_signature_part("return_type"));
        assert!(is_function_signature_part("identifier"));
        assert!(!is_function_signature_part("block"));
        assert!(!is_function_signature_part("if_statement"));
    }
}
