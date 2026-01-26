//! Base trait and utilities for security scanners.
//!
//! This module provides a common interface for all injection detection scanners,
//! reducing code duplication and establishing consistent patterns.
//!
//! # Architecture
//!
//! Security scanners follow a three-phase approach:
//! 1. **Sink Detection**: Find dangerous function calls (execute, query, render, etc.)
//! 2. **Pattern Analysis**: Check if arguments use unsafe patterns (concatenation, interpolation)
//! 3. **Taint Tracking**: Trace data flow from user inputs to sinks
//!
//! # Usage
//!
//! Implement `SecurityScanner` for your scanner type:
//!
//! ```ignore
//! impl SecurityScanner for SqlInjectionDetector {
//!     type Finding = SQLInjectionFinding;
//!     type Config = SqlScanConfig;
//!
//!     fn scan_tree(&self, tree: &Tree, source: &[u8], path: &str) -> Result<Vec<Self::Finding>> {
//!         // Implementation
//!     }
//! }
//! ```

use std::path::Path;

use rustc_hash::FxHashMap;
use tree_sitter::{Node, Tree};

use crate::error::Result;
use crate::lang::LanguageRegistry;

// Re-export common types for scanner implementations
pub use crate::security::common::{Confidence, Severity, SourceLocation};

// =============================================================================
// Scanner Trait
// =============================================================================

/// Base trait for security vulnerability scanners.
///
/// Provides a consistent interface for scanning files and directories
/// for injection vulnerabilities. Implementations should focus on the
/// `scan_tree` method which analyzes a parsed AST.
pub trait SecurityScanner: Send + Sync {
    /// The type of finding this scanner produces.
    type Finding: Clone + Send;

    /// Optional configuration type for the scanner.
    type Config: Default + Clone + Send;

    /// Scan a parsed syntax tree for vulnerabilities.
    ///
    /// This is the core analysis method that implementations must provide.
    /// The tree has already been parsed by tree-sitter.
    ///
    /// # Arguments
    ///
    /// * `tree` - Parsed syntax tree from tree-sitter
    /// * `source` - Original source code bytes
    /// * `file_path` - Path to the file being scanned
    /// * `config` - Scanner-specific configuration
    ///
    /// # Returns
    ///
    /// Vector of findings detected in this file.
    fn scan_tree(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
        config: &Self::Config,
    ) -> Result<Vec<Self::Finding>>;

    /// Scan a single file for vulnerabilities.
    ///
    /// Default implementation handles file reading and parsing,
    /// then delegates to `scan_tree`.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to the source file
    /// * `config` - Scanner-specific configuration
    ///
    /// # Returns
    ///
    /// Vector of findings in this file.
    fn scan_file(&self, path: &Path, config: &Self::Config) -> Result<Vec<Self::Finding>> {
        let registry = LanguageRegistry::global();

        let lang = registry.detect_language(path).ok_or_else(|| {
            crate::error::BrrrError::UnsupportedLanguage(
                path.extension()
                    .and_then(|e| e.to_str())
                    .unwrap_or("unknown")
                    .to_string(),
            )
        })?;

        let source =
            std::fs::read(path).map_err(|e| crate::error::BrrrError::io_with_path(e, path))?;
        let mut parser = lang.parser_for_path(path)?;
        let tree = parser
            .parse(&source, None)
            .ok_or_else(|| crate::error::BrrrError::Parse {
                file: path.display().to_string(),
                message: "Failed to parse file".to_string(),
            })?;

        let file_path = path.display().to_string();
        self.scan_tree(&tree, &source, &file_path, config)
    }

    /// Get the scanner name for logging and reporting.
    fn name(&self) -> &'static str;

    /// Get the CWE IDs this scanner detects.
    fn cwe_ids(&self) -> &[u32] {
        &[]
    }

    /// Get supported language names.
    fn supported_languages(&self) -> &[&'static str];
}

// =============================================================================
// Scan Result Aggregator
// =============================================================================

/// Generic scan result that can be used by any scanner.
///
/// Provides common aggregation for findings, file counts, and severity breakdown.
#[derive(Debug, Clone)]
pub struct ScanResultSummary<F> {
    /// All findings from the scan
    pub findings: Vec<F>,
    /// Number of files scanned
    pub files_scanned: usize,
    /// Number of sinks/vulnerabilities found
    pub sinks_found: usize,
    /// Count of findings by severity level
    pub severity_counts: FxHashMap<String, usize>,
    /// Primary language detected
    pub language: String,
}

impl<F> Default for ScanResultSummary<F> {
    fn default() -> Self {
        Self {
            findings: Vec::new(),
            files_scanned: 0,
            sinks_found: 0,
            severity_counts: FxHashMap::default(),
            language: String::new(),
        }
    }
}

impl<F> ScanResultSummary<F> {
    /// Create a new empty scan result.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a finding and increment counts.
    pub fn add_finding(&mut self, finding: F, severity: Severity) {
        self.findings.push(finding);
        self.sinks_found += 1;
        *self
            .severity_counts
            .entry(severity.to_string())
            .or_insert(0) += 1;
    }

    /// Merge another result into this one.
    pub fn merge(&mut self, other: Self) {
        self.findings.extend(other.findings);
        self.files_scanned += other.files_scanned;
        self.sinks_found += other.sinks_found;
        for (severity, count) in other.severity_counts {
            *self.severity_counts.entry(severity).or_insert(0) += count;
        }
    }

    /// Get total number of findings.
    #[must_use]
    pub fn total_findings(&self) -> usize {
        self.findings.len()
    }

    /// Check if any critical findings exist.
    #[must_use]
    pub fn has_critical(&self) -> bool {
        self.severity_counts
            .get("CRITICAL")
            .copied()
            .unwrap_or(0)
            > 0
    }
}

// =============================================================================
// Node Utilities
// =============================================================================

/// Extract text from a tree-sitter node.
///
/// Safely converts the byte range to a UTF-8 string, returning empty string
/// if the conversion fails.
///
/// # Arguments
///
/// * `node` - The tree-sitter node
/// * `source` - The full source code bytes
///
/// # Returns
///
/// The text content of the node, or empty string if invalid UTF-8.
#[inline]
pub fn node_text<'a>(node: Node<'a>, source: &'a [u8]) -> &'a str {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
}

/// Create a SourceLocation from a tree-sitter node.
///
/// Converts tree-sitter's 0-indexed positions to 1-indexed for display.
///
/// # Arguments
///
/// * `node` - The tree-sitter node
/// * `file_path` - Path to the source file
///
/// # Returns
///
/// A `SourceLocation` with 1-indexed line and column numbers.
#[must_use]
pub fn location_from_node(node: Node, file_path: &str) -> SourceLocation {
    let start = node.start_position();
    let end = node.end_position();

    SourceLocation {
        file: file_path.to_string(),
        line: start.row + 1,
        column: start.column + 1,
        end_line: end.row + 1,
        end_column: end.column + 1,
        snippet: None,
    }
}

/// Create a SourceLocation from a tree-sitter node with a code snippet.
///
/// # Arguments
///
/// * `node` - The tree-sitter node
/// * `file_path` - Path to the source file
/// * `snippet` - Code snippet for context
///
/// # Returns
///
/// A `SourceLocation` with line numbers and snippet.
#[must_use]
pub fn location_from_node_with_snippet(
    node: Node,
    file_path: &str,
    snippet: String,
) -> SourceLocation {
    let start = node.start_position();
    let end = node.end_position();

    SourceLocation {
        file: file_path.to_string(),
        line: start.row + 1,
        column: start.column + 1,
        end_line: end.row + 1,
        end_column: end.column + 1,
        snippet: Some(snippet),
    }
}

/// Get the first child of a node that matches a predicate.
///
/// Useful for extracting specific parts of an AST node.
///
/// # Arguments
///
/// * `node` - Parent node to search
/// * `predicate` - Function returning true for the desired child
///
/// # Returns
///
/// The first matching child node, if any.
pub fn find_child<'a, F>(node: Node<'a>, predicate: F) -> Option<Node<'a>>
where
    F: Fn(&Node<'a>) -> bool,
{
    let mut cursor = node.walk();
    let children: Vec<_> = node.children(&mut cursor).collect();
    children.into_iter().find(|n| predicate(n))
}

/// Get all children of a node that match a predicate.
///
/// # Arguments
///
/// * `node` - Parent node to search
/// * `predicate` - Function returning true for desired children
///
/// # Returns
///
/// Vector of matching child nodes.
pub fn filter_children<'a, F>(node: Node<'a>, predicate: F) -> Vec<Node<'a>>
where
    F: Fn(&Node<'a>) -> bool,
{
    let mut cursor = node.walk();
    let children: Vec<_> = node.children(&mut cursor).collect();
    children.into_iter().filter(|n| predicate(n)).collect()
}

/// Check if a node is a string literal.
///
/// Works across multiple languages by checking common string node kinds.
///
/// # Arguments
///
/// * `node` - The node to check
///
/// # Returns
///
/// True if the node represents a string literal.
#[must_use]
pub fn is_string_literal(node: Node) -> bool {
    matches!(
        node.kind(),
        "string"
            | "string_literal"
            | "template_string"
            | "raw_string_literal"
            | "interpreted_string_literal"
    )
}

/// Check if a node is an identifier.
///
/// # Arguments
///
/// * `node` - The node to check
///
/// # Returns
///
/// True if the node represents an identifier/variable name.
#[must_use]
pub fn is_identifier(node: Node) -> bool {
    matches!(node.kind(), "identifier" | "property_identifier" | "name")
}

// =============================================================================
// Capture Extraction Utilities
// =============================================================================

/// Helper for extracting captures from tree-sitter query matches.
///
/// Provides convenient access to captured nodes by name.
pub struct CaptureExtractor<'a, 'b> {
    captures: &'a [tree_sitter::QueryCapture<'b>],
    query: &'a tree_sitter::Query,
}

impl<'a, 'b> CaptureExtractor<'a, 'b> {
    /// Create a new capture extractor.
    #[must_use]
    pub fn new(
        captures: &'a [tree_sitter::QueryCapture<'b>],
        query: &'a tree_sitter::Query,
    ) -> Self {
        Self { captures, query }
    }

    /// Get a captured node by name.
    pub fn get_node(&self, name: &str) -> Option<Node<'b>> {
        let idx = self.query.capture_index_for_name(name)?;
        self.captures
            .iter()
            .find(|c| c.index == idx)
            .map(|c| c.node)
    }

    /// Get the text of a captured node.
    pub fn get_text(&self, name: &str, source: &'a [u8]) -> Option<&'a str> {
        self.get_node(name).map(|n| node_text(n, source))
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scan_result_summary_add_finding() {
        let mut result: ScanResultSummary<String> = ScanResultSummary::new();
        result.add_finding("finding1".to_string(), Severity::Critical);
        result.add_finding("finding2".to_string(), Severity::High);
        result.add_finding("finding3".to_string(), Severity::Critical);

        assert_eq!(result.total_findings(), 3);
        assert_eq!(result.sinks_found, 3);
        assert_eq!(result.severity_counts.get("CRITICAL"), Some(&2));
        assert_eq!(result.severity_counts.get("HIGH"), Some(&1));
        assert!(result.has_critical());
    }

    #[test]
    fn test_scan_result_summary_merge() {
        let mut result1: ScanResultSummary<String> = ScanResultSummary::new();
        result1.add_finding("a".to_string(), Severity::High);
        result1.files_scanned = 5;

        let mut result2: ScanResultSummary<String> = ScanResultSummary::new();
        result2.add_finding("b".to_string(), Severity::Critical);
        result2.files_scanned = 3;

        result1.merge(result2);

        assert_eq!(result1.total_findings(), 2);
        assert_eq!(result1.files_scanned, 8);
        assert!(result1.has_critical());
    }

    #[test]
    fn test_severity_display() {
        assert_eq!(Severity::Critical.to_string(), "CRITICAL");
        assert_eq!(Severity::High.to_string(), "HIGH");
        assert_eq!(Severity::Medium.to_string(), "MEDIUM");
        assert_eq!(Severity::Low.to_string(), "LOW");
    }

    #[test]
    fn test_confidence_ordering() {
        assert!(Confidence::High > Confidence::Medium);
        assert!(Confidence::Medium > Confidence::Low);
    }
}
