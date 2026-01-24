//! Cohesion metrics (LCOM variants) for class quality analysis.
//!
//! Lack of Cohesion of Methods (LCOM) measures how tightly related the methods
//! of a class are. High LCOM indicates a class that might be doing too many things
//! and should potentially be split into multiple classes.
//!
//! # LCOM Variants
//!
//! ## LCOM1 (Chidamber-Kemerer Original)
//! ```text
//! P = number of method pairs that DON'T share instance variables
//! Q = number of method pairs that DO share instance variables
//! LCOM1 = max(0, P - Q)
//! ```
//! - LCOM1 = 0: All methods share at least one attribute (cohesive)
//! - LCOM1 > 0: Some methods don't share attributes (less cohesive)
//!
//! ## LCOM2 (Chidamber-Kemerer Simplified)
//! ```text
//! LCOM2 = P - Q (can be negative = good cohesion)
//! ```
//! - LCOM2 < 0: More method pairs share attributes than not
//! - LCOM2 = 0: Equal sharing
//! - LCOM2 > 0: Poor cohesion
//!
//! ## LCOM3 (Henderson-Sellers)
//! Number of connected components in the method-attribute graph.
//! ```text
//! Graph: nodes = methods + attributes
//! Edges: method -> attribute (if method uses attribute)
//! LCOM3 = number of connected components
//! ```
//! - LCOM3 = 1: Perfectly cohesive class
//! - LCOM3 > 1: Class might be N separate classes
//!
//! ## LCOM4 (Extends LCOM3 with method calls)
//! Same as LCOM3 but also connects methods that call each other.
//! ```text
//! Additional edges: method -> method (if one calls the other)
//! LCOM4 = number of connected components
//! ```
//! - LCOM4 = 1: Perfectly cohesive
//! - LCOM4 > 1: Consider splitting into LCOM4 classes
//!
//! # Interpretation Guidelines
//!
//! - Classes with LCOM3/4 = 1 are well-designed
//! - Classes with LCOM3/4 > 1 might violate Single Responsibility Principle
//! - Static methods should be excluded (they don't use instance state)
//! - Constructors may have artificially low cohesion (initialize all fields)
//! - Utility classes may have low cohesion by design

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::debug;

use crate::ast::AstExtractor;
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;
use crate::metrics::common::{
    extract_attribute_accesses, extract_method_calls, find_class_node, find_method_node,
    MetricStats,
};

// =============================================================================
// TYPES
// =============================================================================

/// Cohesion level based on LCOM3 value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CohesionLevel {
    /// LCOM3 = 1: Perfectly cohesive
    High,
    /// LCOM3 = 2: Minor cohesion issue
    Medium,
    /// LCOM3 = 3-4: Moderate cohesion problem
    Low,
    /// LCOM3 >= 5: Severe cohesion problem
    VeryLow,
}

impl CohesionLevel {
    /// Classify LCOM3 value into cohesion level.
    #[must_use]
    pub fn from_lcom3(lcom3: u32) -> Self {
        match lcom3 {
            0 | 1 => Self::High,
            2 => Self::Medium,
            3 | 4 => Self::Low,
            _ => Self::VeryLow,
        }
    }

    /// Get human-readable description.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::High => "Cohesive class, well-designed",
            Self::Medium => "Minor cohesion issue, consider reviewing",
            Self::Low => "Low cohesion, consider splitting class",
            Self::VeryLow => "Very low cohesion, strongly recommend splitting",
        }
    }

    /// Get ANSI color code for CLI output.
    #[must_use]
    pub const fn color_code(&self) -> &'static str {
        match self {
            Self::High => "\x1b[32m",    // Green
            Self::Medium => "\x1b[33m",  // Yellow
            Self::Low => "\x1b[31m",     // Red
            Self::VeryLow => "\x1b[35m", // Magenta
        }
    }
}

impl std::fmt::Display for CohesionLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::High => write!(f, "high"),
            Self::Medium => write!(f, "medium"),
            Self::Low => write!(f, "low"),
            Self::VeryLow => write!(f, "very_low"),
        }
    }
}

/// Cohesion metrics for a single class.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CohesionMetrics {
    /// Class name (may include module prefix for nested classes)
    pub class_name: String,
    /// File path containing the class
    pub file: PathBuf,
    /// Starting line number (1-indexed)
    pub line: usize,
    /// Ending line number (1-indexed)
    pub end_line: usize,
    /// LCOM1 value: max(0, P - Q) where P = non-sharing pairs, Q = sharing pairs
    pub lcom1: u32,
    /// LCOM2 value: P - Q (can be negative)
    pub lcom2: i32,
    /// LCOM3 value: number of connected components in method-attribute graph
    pub lcom3: u32,
    /// LCOM4 value: LCOM3 extended with method-to-method call edges
    pub lcom4: u32,
    /// Number of instance methods analyzed
    pub methods: u32,
    /// Number of instance attributes detected
    pub attributes: u32,
    /// Cohesion level based on LCOM3
    pub cohesion_level: CohesionLevel,
    /// Whether class has low cohesion (LCOM3 > 1)
    pub is_low_cohesion: bool,
    /// Suggestion for improvement (if LCOM3 > 1)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggestion: Option<String>,
    /// Names of methods in each connected component (for LCOM4)
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub components: Vec<Vec<String>>,
}

/// Aggregate cohesion statistics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CohesionStats {
    /// Total number of classes analyzed
    pub total_classes: usize,
    /// Number of classes with LCOM3 = 1 (cohesive)
    pub cohesive_classes: usize,
    /// Number of classes with LCOM3 > 1 (potential issues)
    pub low_cohesion_classes: usize,
    /// Average LCOM3 across all classes
    pub average_lcom3: f64,
    /// Maximum LCOM3 found
    pub max_lcom3: u32,
    /// Distribution by cohesion level
    pub cohesion_distribution: HashMap<String, usize>,
    /// Average methods per class
    pub average_methods: f64,
    /// Average attributes per class
    pub average_attributes: f64,
}

impl CohesionStats {
    /// Calculate statistics from a list of cohesion metrics.
    fn from_metrics(metrics: &[CohesionMetrics]) -> Self {
        if metrics.is_empty() {
            return Self {
                total_classes: 0,
                cohesive_classes: 0,
                low_cohesion_classes: 0,
                average_lcom3: 0.0,
                max_lcom3: 0,
                cohesion_distribution: HashMap::new(),
                average_methods: 0.0,
                average_attributes: 0.0,
            };
        }

        let total = metrics.len();
        let cohesive = metrics.iter().filter(|m| m.lcom3 <= 1).count();
        let low_cohesion = metrics.iter().filter(|m| m.lcom3 > 1).count();

        let lcom3_sum: u64 = metrics.iter().map(|m| u64::from(m.lcom3)).sum();
        let average_lcom3 = lcom3_sum as f64 / total as f64;

        let max_lcom3 = metrics.iter().map(|m| m.lcom3).max().unwrap_or(0);

        let methods_sum: u64 = metrics.iter().map(|m| u64::from(m.methods)).sum();
        let attrs_sum: u64 = metrics.iter().map(|m| u64::from(m.attributes)).sum();

        let mut cohesion_distribution = HashMap::new();
        for m in metrics {
            *cohesion_distribution
                .entry(m.cohesion_level.to_string())
                .or_insert(0) += 1;
        }

        Self {
            total_classes: total,
            cohesive_classes: cohesive,
            low_cohesion_classes: low_cohesion,
            average_lcom3,
            max_lcom3,
            cohesion_distribution,
            average_methods: methods_sum as f64 / total as f64,
            average_attributes: attrs_sum as f64 / total as f64,
        }
    }
}

impl MetricStats for CohesionStats {
    fn count(&self) -> usize {
        self.total_classes
    }

    fn total(&self) -> f64 {
        // Total is sum of all LCOM3 values; approximated from average * count
        self.average_lcom3 * self.total_classes as f64
    }

    fn average(&self) -> f64 {
        self.average_lcom3
    }

    fn max(&self) -> f64 {
        f64::from(self.max_lcom3)
    }

    fn min(&self) -> f64 {
        // LCOM3 minimum is always 0 or 1 for analyzed classes
        0.0
    }
}

/// Complete cohesion analysis result for a file or project.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CohesionAnalysis {
    /// Path that was analyzed (file or directory)
    pub path: PathBuf,
    /// Language filter applied (if any)
    pub language: Option<String>,
    /// Individual class cohesion metrics
    pub classes: Vec<CohesionMetrics>,
    /// Classes with LCOM3 > threshold (if threshold specified)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violations: Option<Vec<CohesionMetrics>>,
    /// Aggregate statistics
    pub stats: CohesionStats,
    /// Threshold used for filtering (if any)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub threshold: Option<u32>,
    /// Files that could not be analyzed
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<CohesionError>,
}

/// Error encountered during cohesion analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CohesionError {
    /// File path where error occurred
    pub file: PathBuf,
    /// Error message
    pub message: String,
}

// =============================================================================
// METHOD-ATTRIBUTE GRAPH
// =============================================================================

/// Represents the method-attribute graph for LCOM calculation.
#[derive(Debug, Default)]
struct MethodAttributeGraph {
    /// Method names
    methods: Vec<String>,
    /// Attribute names
    attributes: HashSet<String>,
    /// Which attributes each method accesses: method_name -> set of attribute names
    method_attributes: HashMap<String, HashSet<String>>,
    /// Which methods each method calls: caller -> set of callee names
    method_calls: HashMap<String, HashSet<String>>,
}

impl MethodAttributeGraph {
    fn new() -> Self {
        Self::default()
    }

    /// Add a method to the graph.
    fn add_method(&mut self, name: &str) {
        if !self.methods.contains(&name.to_string()) {
            self.methods.push(name.to_string());
        }
    }

    /// Record that a method accesses an attribute.
    fn add_attribute_access(&mut self, method: &str, attribute: &str) {
        self.attributes.insert(attribute.to_string());
        self.method_attributes
            .entry(method.to_string())
            .or_default()
            .insert(attribute.to_string());
    }

    /// Record that one method calls another.
    fn add_method_call(&mut self, caller: &str, callee: &str) {
        self.method_calls
            .entry(caller.to_string())
            .or_default()
            .insert(callee.to_string());
    }

    /// Calculate LCOM1: max(0, P - Q)
    /// P = pairs that don't share attributes
    /// Q = pairs that share at least one attribute
    fn calculate_lcom1(&self) -> u32 {
        let (p, q) = self.count_sharing_pairs();
        if p > q {
            (p - q) as u32
        } else {
            0
        }
    }

    /// Calculate LCOM2: P - Q (can be negative)
    fn calculate_lcom2(&self) -> i32 {
        let (p, q) = self.count_sharing_pairs();
        (p as i32) - (q as i32)
    }

    /// Count method pairs that share/don't share attributes.
    /// Returns (non_sharing_pairs, sharing_pairs)
    fn count_sharing_pairs(&self) -> (usize, usize) {
        let n = self.methods.len();
        if n < 2 {
            return (0, 0);
        }

        let mut p = 0; // non-sharing pairs
        let mut q = 0; // sharing pairs

        for i in 0..n {
            for j in (i + 1)..n {
                let m1 = &self.methods[i];
                let m2 = &self.methods[j];

                let attrs1 = self.method_attributes.get(m1);
                let attrs2 = self.method_attributes.get(m2);

                let shares = match (attrs1, attrs2) {
                    (Some(a1), Some(a2)) => !a1.is_disjoint(a2),
                    _ => false,
                };

                if shares {
                    q += 1;
                } else {
                    p += 1;
                }
            }
        }

        (p, q)
    }

    /// Calculate LCOM3: number of connected components (method-attribute graph only)
    fn calculate_lcom3(&self) -> (u32, Vec<Vec<String>>) {
        self.find_connected_components(false)
    }

    /// Calculate LCOM4: number of connected components (including method calls)
    fn calculate_lcom4(&self) -> (u32, Vec<Vec<String>>) {
        self.find_connected_components(true)
    }

    /// Find connected components in the method-attribute graph.
    /// If include_method_calls is true, also connects methods that call each other.
    fn find_connected_components(&self, include_method_calls: bool) -> (u32, Vec<Vec<String>>) {
        if self.methods.is_empty() {
            return (0, Vec::new());
        }

        // Build adjacency list for methods
        // Two methods are adjacent if they share an attribute or (optionally) call each other
        let mut adjacency: HashMap<&str, HashSet<&str>> = HashMap::new();

        for method in &self.methods {
            adjacency.insert(method.as_str(), HashSet::new());
        }

        // Connect methods that share attributes
        for i in 0..self.methods.len() {
            for j in (i + 1)..self.methods.len() {
                let m1 = &self.methods[i];
                let m2 = &self.methods[j];

                let attrs1 = self.method_attributes.get(m1);
                let attrs2 = self.method_attributes.get(m2);

                let shares_attribute = match (attrs1, attrs2) {
                    (Some(a1), Some(a2)) => !a1.is_disjoint(a2),
                    _ => false,
                };

                if shares_attribute {
                    adjacency.get_mut(m1.as_str()).unwrap().insert(m2.as_str());
                    adjacency.get_mut(m2.as_str()).unwrap().insert(m1.as_str());
                }
            }
        }

        // Connect methods that call each other (for LCOM4)
        if include_method_calls {
            for (caller, callees) in &self.method_calls {
                if !self.methods.contains(caller) {
                    continue;
                }
                for callee in callees {
                    if self.methods.contains(callee) {
                        adjacency
                            .get_mut(caller.as_str())
                            .unwrap()
                            .insert(callee.as_str());
                        adjacency
                            .get_mut(callee.as_str())
                            .unwrap()
                            .insert(caller.as_str());
                    }
                }
            }
        }

        // BFS to find connected components
        let mut visited: HashSet<&str> = HashSet::new();
        let mut components: Vec<Vec<String>> = Vec::new();

        for method in &self.methods {
            if visited.contains(method.as_str()) {
                continue;
            }

            let mut component = Vec::new();
            let mut queue = VecDeque::new();
            queue.push_back(method.as_str());
            visited.insert(method.as_str());

            while let Some(current) = queue.pop_front() {
                component.push(current.to_string());

                if let Some(neighbors) = adjacency.get(current) {
                    for &neighbor in neighbors {
                        if !visited.contains(neighbor) {
                            visited.insert(neighbor);
                            queue.push_back(neighbor);
                        }
                    }
                }
            }

            components.push(component);
        }

        (components.len() as u32, components)
    }
}

// Attribute extraction and method call extraction moved to crate::metrics::common

// =============================================================================
// ANALYSIS FUNCTIONS
// =============================================================================

/// Analyze cohesion for a project or directory.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `language` - Optional language filter
/// * `threshold` - Optional LCOM3 threshold for filtering (default: show all classes)
///
/// # Returns
///
/// Complete analysis with individual class metrics and statistics.
pub fn analyze_cohesion(
    path: impl AsRef<Path>,
    language: Option<&str>,
    threshold: Option<u32>,
) -> Result<CohesionAnalysis> {
    let path = path.as_ref();

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Path not found: {}", path.display()),
        )));
    }

    if path.is_file() {
        return analyze_file_cohesion(path, threshold);
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

    debug!("Analyzing {} files for cohesion", scan_result.files.len());

    // Analyze files in parallel
    let results: Vec<(Vec<CohesionMetrics>, Vec<CohesionError>)> = scan_result
        .files
        .par_iter()
        .map(|file| analyze_file_classes(file, threshold))
        .collect();

    // Aggregate results
    let mut all_classes = Vec::new();
    let mut all_errors = Vec::new();

    for (classes, errors) in results {
        all_classes.extend(classes);
        all_errors.extend(errors);
    }

    // Calculate statistics
    let stats = CohesionStats::from_metrics(&all_classes);

    // Filter violations if threshold specified
    let violations = threshold.map(|t| {
        all_classes
            .iter()
            .filter(|c| c.lcom3 > t)
            .cloned()
            .collect::<Vec<_>>()
    });

    Ok(CohesionAnalysis {
        path: path.to_path_buf(),
        language: language.map(String::from),
        classes: all_classes,
        violations,
        stats,
        threshold,
        errors: all_errors,
    })
}

/// Analyze cohesion for a single file.
pub fn analyze_file_cohesion(
    file: impl AsRef<Path>,
    threshold: Option<u32>,
) -> Result<CohesionAnalysis> {
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

    let (classes, errors) = analyze_file_classes(file, threshold);
    let stats = CohesionStats::from_metrics(&classes);

    let violations = threshold.map(|t| {
        classes
            .iter()
            .filter(|c| c.lcom3 > t)
            .cloned()
            .collect::<Vec<_>>()
    });

    // Detect language
    let registry = LanguageRegistry::global();
    let language = registry.detect_language(file).map(|l| l.name().to_string());

    Ok(CohesionAnalysis {
        path: file.to_path_buf(),
        language,
        classes,
        violations,
        stats,
        threshold,
        errors,
    })
}

/// Internal function to analyze all classes in a file.
fn analyze_file_classes(
    file: &Path,
    _threshold: Option<u32>,
) -> (Vec<CohesionMetrics>, Vec<CohesionError>) {
    let mut results = Vec::new();
    let mut errors = Vec::new();

    // Extract module info
    let module = match AstExtractor::extract_file(file) {
        Ok(m) => m,
        Err(e) => {
            errors.push(CohesionError {
                file: file.to_path_buf(),
                message: format!("Failed to parse file: {}", e),
            });
            return (results, errors);
        }
    };

    // Read file content for AST traversal
    let source = match std::fs::read(file) {
        Ok(s) => s,
        Err(e) => {
            errors.push(CohesionError {
                file: file.to_path_buf(),
                message: format!("Failed to read file: {}", e),
            });
            return (results, errors);
        }
    };

    let language = &module.language;

    // Get parser for this language
    let registry = LanguageRegistry::global();
    let lang_impl = match registry.detect_language(file) {
        Some(l) => l,
        None => {
            errors.push(CohesionError {
                file: file.to_path_buf(),
                message: "Unsupported language".to_string(),
            });
            return (results, errors);
        }
    };

    let mut parser = match lang_impl.parser() {
        Ok(p) => p,
        Err(e) => {
            errors.push(CohesionError {
                file: file.to_path_buf(),
                message: format!("Failed to create parser: {}", e),
            });
            return (results, errors);
        }
    };

    let tree = match parser.parse(&source, None) {
        Some(t) => t,
        None => {
            errors.push(CohesionError {
                file: file.to_path_buf(),
                message: "Failed to parse file".to_string(),
            });
            return (results, errors);
        }
    };

    // Analyze each class
    for class in &module.classes {
        if let Some(metrics) = analyze_class_cohesion(file, class, &tree, &source, language) {
            results.push(metrics);
        }

        // Also analyze nested classes
        for inner in &class.inner_classes {
            if let Some(metrics) = analyze_class_cohesion(file, inner, &tree, &source, language) {
                results.push(metrics);
            }
        }
    }

    (results, errors)
}

/// Analyze cohesion for a single class.
fn analyze_class_cohesion(
    file: &Path,
    class: &crate::ast::types::ClassInfo,
    tree: &tree_sitter::Tree,
    source: &[u8],
    language: &str,
) -> Option<CohesionMetrics> {
    // Skip classes with no methods
    if class.methods.is_empty() {
        return None;
    }

    // Build method-attribute graph
    let mut graph = MethodAttributeGraph::new();

    // Collect method names (excluding static methods and dunder methods for Python)
    let mut class_method_names: HashSet<String> = HashSet::new();

    for method in &class.methods {
        // Skip static methods (they don't use instance state)
        let is_static = method
            .decorators
            .iter()
            .any(|d| d == "staticmethod" || d == "static" || d.contains("@staticmethod"));

        // For Python, skip if first param is not self/cls
        let is_class_method = method
            .decorators
            .iter()
            .any(|d| d == "classmethod" || d.contains("@classmethod"));

        if is_static || is_class_method {
            continue;
        }

        // Skip Python dunder methods except __init__
        if language == "python" && method.name.starts_with("__") && method.name.ends_with("__") {
            if method.name != "__init__" {
                continue;
            }
        }

        class_method_names.insert(method.name.clone());
        graph.add_method(&method.name);
    }

    // Skip classes with 0 or 1 instance methods (trivially cohesive)
    if graph.methods.len() <= 1 {
        return None;
    }

    // Find class node in AST and extract attribute accesses per method
    let root = tree.root_node();
    if let Some(class_node) = find_class_node(root, &class.name, class.line_number) {
        for method in &class.methods {
            if !class_method_names.contains(&method.name) {
                continue;
            }

            // Find method node within class
            if let Some(method_node) =
                find_method_node(class_node, &method.name, method.line_number, language)
            {
                // Extract attribute accesses
                let attrs = extract_attribute_accesses(method_node, source, language);
                for attr in &attrs {
                    graph.add_attribute_access(&method.name, attr);
                }

                // Extract method calls for LCOM4
                let calls =
                    extract_method_calls(method_node, source, language, &class_method_names);
                for callee in &calls {
                    graph.add_method_call(&method.name, callee);
                }
            }
        }
    }

    // Calculate LCOM metrics
    let lcom1 = graph.calculate_lcom1();
    let lcom2 = graph.calculate_lcom2();
    let (lcom3, _) = graph.calculate_lcom3();
    let (lcom4, components) = graph.calculate_lcom4();

    let cohesion_level = CohesionLevel::from_lcom3(lcom3);
    let is_low_cohesion = lcom3 > 1;

    let suggestion = if lcom4 > 1 {
        Some(format!(
            "Consider splitting into {} classes based on connected components",
            lcom4
        ))
    } else {
        None
    };

    Some(CohesionMetrics {
        class_name: class.name.clone(),
        file: file.to_path_buf(),
        line: class.line_number,
        end_line: class.end_line_number.unwrap_or(class.line_number),
        lcom1,
        lcom2,
        lcom3,
        lcom4,
        methods: graph.methods.len() as u32,
        attributes: graph.attributes.len() as u32,
        cohesion_level,
        is_low_cohesion,
        suggestion,
        components,
    })
}

// find_class_node, find_method_node, find_method_recursive moved to crate::metrics::common

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
    fn test_cohesion_level_classification() {
        assert_eq!(CohesionLevel::from_lcom3(0), CohesionLevel::High);
        assert_eq!(CohesionLevel::from_lcom3(1), CohesionLevel::High);
        assert_eq!(CohesionLevel::from_lcom3(2), CohesionLevel::Medium);
        assert_eq!(CohesionLevel::from_lcom3(3), CohesionLevel::Low);
        assert_eq!(CohesionLevel::from_lcom3(4), CohesionLevel::Low);
        assert_eq!(CohesionLevel::from_lcom3(5), CohesionLevel::VeryLow);
        assert_eq!(CohesionLevel::from_lcom3(10), CohesionLevel::VeryLow);
    }

    #[test]
    fn test_cohesion_level_display() {
        assert_eq!(CohesionLevel::High.to_string(), "high");
        assert_eq!(CohesionLevel::Medium.to_string(), "medium");
        assert_eq!(CohesionLevel::Low.to_string(), "low");
        assert_eq!(CohesionLevel::VeryLow.to_string(), "very_low");
    }

    #[test]
    fn test_method_attribute_graph_lcom1() {
        let mut graph = MethodAttributeGraph::new();

        // Two methods sharing an attribute
        graph.add_method("method_a");
        graph.add_method("method_b");
        graph.add_attribute_access("method_a", "attr1");
        graph.add_attribute_access("method_b", "attr1");

        // LCOM1 should be 0 (all pairs share)
        assert_eq!(graph.calculate_lcom1(), 0);

        // Add third method not sharing
        graph.add_method("method_c");
        graph.add_attribute_access("method_c", "attr2");

        // Now: (a,b) share, (a,c) don't, (b,c) don't
        // P = 2, Q = 1, LCOM1 = max(0, 2-1) = 1
        assert_eq!(graph.calculate_lcom1(), 1);
    }

    #[test]
    fn test_method_attribute_graph_lcom2() {
        let mut graph = MethodAttributeGraph::new();

        // All methods share attributes - negative LCOM2 (good)
        graph.add_method("m1");
        graph.add_method("m2");
        graph.add_method("m3");
        graph.add_attribute_access("m1", "a");
        graph.add_attribute_access("m2", "a");
        graph.add_attribute_access("m3", "a");

        // All 3 pairs share attribute 'a'
        // P = 0, Q = 3, LCOM2 = 0 - 3 = -3
        assert_eq!(graph.calculate_lcom2(), -3);
    }

    #[test]
    fn test_method_attribute_graph_connected_components() {
        let mut graph = MethodAttributeGraph::new();

        // Two separate clusters
        // Cluster 1: m1, m2 share attr1
        graph.add_method("m1");
        graph.add_method("m2");
        graph.add_attribute_access("m1", "attr1");
        graph.add_attribute_access("m2", "attr1");

        // Cluster 2: m3, m4 share attr2
        graph.add_method("m3");
        graph.add_method("m4");
        graph.add_attribute_access("m3", "attr2");
        graph.add_attribute_access("m4", "attr2");

        let (lcom3, components) = graph.calculate_lcom3();
        assert_eq!(lcom3, 2);
        assert_eq!(components.len(), 2);
    }

    #[test]
    fn test_method_attribute_graph_lcom4_with_calls() {
        let mut graph = MethodAttributeGraph::new();

        // Two separate attribute clusters
        graph.add_method("m1");
        graph.add_method("m2");
        graph.add_method("m3");
        graph.add_attribute_access("m1", "attr1");
        graph.add_attribute_access("m2", "attr1");
        graph.add_attribute_access("m3", "attr2");

        // Without method calls: 2 components (m1,m2) and (m3)
        let (lcom3, _) = graph.calculate_lcom3();
        assert_eq!(lcom3, 2);

        // With method call connecting them
        graph.add_method_call("m2", "m3");
        let (lcom4, _) = graph.calculate_lcom4();
        assert_eq!(lcom4, 1); // Now all connected
    }

    #[test]
    fn test_cohesive_python_class() {
        let source = r#"
class Calculator:
    def __init__(self):
        self.value = 0
        self.history = []

    def add(self, x):
        self.value += x
        self.history.append(('add', x))

    def subtract(self, x):
        self.value -= x
        self.history.append(('sub', x))

    def get_value(self):
        return self.value

    def get_history(self):
        return self.history
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cohesion(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.classes.len(), 1);
        let metrics = &analysis.classes[0];
        assert_eq!(metrics.class_name, "Calculator");
        // All methods share 'value' or 'history' attributes
        assert!(
            metrics.lcom3 <= 2,
            "Expected cohesive class, got LCOM3 = {}",
            metrics.lcom3
        );
    }

    #[test]
    fn test_low_cohesion_python_class() {
        let source = r#"
class GodObject:
    def process_users(self):
        self.users = []
        return self.users

    def handle_payments(self):
        self.payments = []
        return self.payments

    def send_emails(self):
        self.emails = []
        return self.emails

    def generate_reports(self):
        self.reports = []
        return self.reports
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cohesion(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.classes.len(), 1);
        let metrics = &analysis.classes[0];
        assert_eq!(metrics.class_name, "GodObject");
        // Each method uses different attributes - no sharing
        assert!(
            metrics.lcom3 >= 3,
            "Expected low cohesion, got LCOM3 = {}",
            metrics.lcom3
        );
        assert!(metrics.is_low_cohesion);
    }

    #[test]
    fn test_statistics_calculation() {
        let metrics = vec![
            CohesionMetrics {
                class_name: "A".to_string(),
                file: PathBuf::from("a.py"),
                line: 1,
                end_line: 10,
                lcom1: 0,
                lcom2: -2,
                lcom3: 1,
                lcom4: 1,
                methods: 3,
                attributes: 2,
                cohesion_level: CohesionLevel::High,
                is_low_cohesion: false,
                suggestion: None,
                components: vec![],
            },
            CohesionMetrics {
                class_name: "B".to_string(),
                file: PathBuf::from("b.py"),
                line: 1,
                end_line: 20,
                lcom1: 5,
                lcom2: 3,
                lcom3: 3,
                lcom4: 2,
                methods: 4,
                attributes: 4,
                cohesion_level: CohesionLevel::Low,
                is_low_cohesion: true,
                suggestion: Some("Consider splitting".to_string()),
                components: vec![],
            },
        ];

        let stats = CohesionStats::from_metrics(&metrics);

        assert_eq!(stats.total_classes, 2);
        assert_eq!(stats.cohesive_classes, 1);
        assert_eq!(stats.low_cohesion_classes, 1);
        assert_eq!(stats.max_lcom3, 3);
        assert!((stats.average_lcom3 - 2.0).abs() < 0.01);
    }

    #[test]
    fn test_empty_class_skipped() {
        let source = r#"
class Empty:
    pass
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cohesion(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();
        // Empty class should be skipped
        assert_eq!(analysis.classes.len(), 0);
    }

    #[test]
    fn test_single_method_class_skipped() {
        let source = r#"
class SingleMethod:
    def only_method(self):
        self.attr = 1
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cohesion(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();
        // Single-method classes are trivially cohesive, skip them
        assert_eq!(analysis.classes.len(), 0);
    }

    #[test]
    fn test_static_methods_excluded() {
        let source = r#"
class WithStatic:
    @staticmethod
    def static_helper():
        return 42

    def instance_method(self):
        self.value = 1

    def another_instance(self):
        self.value = 2
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cohesion(file.path(), None);

        assert!(result.is_ok());
        let analysis = result.unwrap();

        assert_eq!(analysis.classes.len(), 1);
        let metrics = &analysis.classes[0];
        // Only 2 instance methods, static method excluded
        assert_eq!(metrics.methods, 2);
    }

    #[test]
    fn test_nonexistent_file() {
        let result = analyze_file_cohesion("/nonexistent/path/file.py", None);
        assert!(result.is_err());
    }

    #[test]
    fn test_threshold_filtering() {
        let source = r#"
class Cohesive:
    def method_a(self):
        self.shared = 1
    def method_b(self):
        self.shared = 2

class NotCohesive:
    def isolated_a(self):
        self.a = 1
    def isolated_b(self):
        self.b = 1
    def isolated_c(self):
        self.c = 1
"#;
        let file = create_temp_file(source, ".py");
        let result = analyze_file_cohesion(file.path(), Some(1));

        assert!(result.is_ok());
        let analysis = result.unwrap();

        // Should have violations (classes with LCOM3 > 1)
        assert!(analysis.violations.is_some());
        let violations = analysis.violations.unwrap();
        // NotCohesive should be a violation
        assert!(violations.iter().any(|v| v.class_name == "NotCohesive"));
    }
}
