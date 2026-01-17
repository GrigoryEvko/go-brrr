//! Core taint analysis types.
//!
//! This module defines the fundamental types for taint tracking:
//! - `TaintLabel`: Categories of taint sources (user input, file, network, etc.)
//! - `TaintedValue`: A value with its taint metadata and propagation history
//! - `TaintPropagation`: Rules for how taint flows through operations
//! - `TaintState`: Aggregated taint state for a variable or expression
//!
//! # Taint Propagation Semantics
//!
//! The taint analysis uses dataflow semantics where:
//! - **Copy**: `taint(x) = taint(y)` for simple assignment `x = y`
//! - **Merge**: `taint(x) = taint(a) ∪ taint(b)` for operations like `x = a + b`
//! - **Sanitize**: Removes taint when data passes through sanitization functions
//! - **Transform**: Preserves taint but tracks the transformation applied
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::security::taint::{TaintLabel, TaintedValue, TaintPropagation};
//!
//! // User input is tainted
//! let user_input = TaintedValue::new(TaintLabel::UserInput, location);
//!
//! // Taint propagates through concatenation
//! let merged = TaintedValue::merge(&[user_input], location);
//!
//! // Sanitization removes taint
//! let sanitized = TaintedValue::sanitize(&merged, "html_escape", location);
//! assert!(!sanitized.is_tainted());
//! ```

use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};

// =============================================================================
// Location Types
// =============================================================================

/// A source code location with file, line, and column information.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Location {
    /// File path (relative or absolute)
    pub file: String,
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed)
    pub column: usize,
    /// Optional end line for multi-line spans
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_line: Option<usize>,
    /// Optional end column
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_column: Option<usize>,
}

impl Location {
    /// Create a new location.
    #[inline]
    pub fn new(file: impl Into<String>, line: usize, column: usize) -> Self {
        Self {
            file: file.into(),
            line,
            column,
            end_line: None,
            end_column: None,
        }
    }

    /// Create a location with a span.
    #[inline]
    pub fn with_span(
        file: impl Into<String>,
        line: usize,
        column: usize,
        end_line: usize,
        end_column: usize,
    ) -> Self {
        Self {
            file: file.into(),
            line,
            column,
            end_line: Some(end_line),
            end_column: Some(end_column),
        }
    }

    /// Create an unknown/synthetic location.
    #[inline]
    pub fn unknown() -> Self {
        Self {
            file: "<unknown>".to_string(),
            line: 0,
            column: 0,
            end_line: None,
            end_column: None,
        }
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let (Some(end_line), Some(end_col)) = (self.end_line, self.end_column) {
            write!(
                f,
                "{}:{}:{}-{}:{}",
                self.file, self.line, self.column, end_line, end_col
            )
        } else {
            write!(f, "{}:{}:{}", self.file, self.line, self.column)
        }
    }
}

impl Hash for Location {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.file.hash(state);
        self.line.hash(state);
        self.column.hash(state);
    }
}

// =============================================================================
// Taint Label
// =============================================================================

/// Categories of taint sources.
///
/// Each label represents a distinct source of potentially untrusted data.
/// Values can have multiple labels if they combine data from different sources.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TaintLabel {
    /// Direct user input (request params, form data, CLI args)
    UserInput,
    /// File content read from filesystem
    FileContent,
    /// Network response data (HTTP, WebSocket, etc.)
    NetworkData,
    /// Database query results
    DatabaseQuery,
    /// Environment variables
    Environment,
    /// URL components (path, query string, fragment)
    UrlData,
    /// HTTP headers (may contain user-controlled data)
    HttpHeader,
    /// Cookie values
    Cookie,
    /// Deserialized data (JSON, XML, YAML, pickle, etc.)
    DeserializedData,
    /// Process arguments (sys.argv, process.argv)
    ProcessArgs,
    /// Standard input
    Stdin,
    /// External API response
    ExternalApi,
    /// Configuration values (may be user-editable)
    Config,
    /// Custom taint label for domain-specific analysis
    Custom(String),
}

impl TaintLabel {
    /// Returns the severity weight of this taint label.
    ///
    /// Higher values indicate higher risk when flowing to sensitive sinks.
    /// This is used for prioritizing findings.
    #[inline]
    pub fn severity_weight(&self) -> u8 {
        match self {
            TaintLabel::UserInput => 10,
            TaintLabel::ProcessArgs => 9,
            TaintLabel::Stdin => 9,
            TaintLabel::Cookie => 8,
            TaintLabel::UrlData => 8,
            TaintLabel::HttpHeader => 7,
            TaintLabel::NetworkData => 7,
            TaintLabel::FileContent => 6,
            TaintLabel::ExternalApi => 6,
            TaintLabel::DeserializedData => 8,
            TaintLabel::DatabaseQuery => 5,
            TaintLabel::Environment => 4,
            TaintLabel::Config => 3,
            TaintLabel::Custom(_) => 5,
        }
    }

    /// Returns a human-readable description of this taint source.
    #[inline]
    pub fn description(&self) -> &str {
        match self {
            TaintLabel::UserInput => "user input (form data, request params)",
            TaintLabel::FileContent => "file content",
            TaintLabel::NetworkData => "network response data",
            TaintLabel::DatabaseQuery => "database query result",
            TaintLabel::Environment => "environment variable",
            TaintLabel::UrlData => "URL component",
            TaintLabel::HttpHeader => "HTTP header",
            TaintLabel::Cookie => "cookie value",
            TaintLabel::DeserializedData => "deserialized data",
            TaintLabel::ProcessArgs => "command line argument",
            TaintLabel::Stdin => "standard input",
            TaintLabel::ExternalApi => "external API response",
            TaintLabel::Config => "configuration value",
            TaintLabel::Custom(name) => name.as_str(),
        }
    }
}

impl fmt::Display for TaintLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TaintLabel::UserInput => write!(f, "UserInput"),
            TaintLabel::FileContent => write!(f, "FileContent"),
            TaintLabel::NetworkData => write!(f, "NetworkData"),
            TaintLabel::DatabaseQuery => write!(f, "DatabaseQuery"),
            TaintLabel::Environment => write!(f, "Environment"),
            TaintLabel::UrlData => write!(f, "UrlData"),
            TaintLabel::HttpHeader => write!(f, "HttpHeader"),
            TaintLabel::Cookie => write!(f, "Cookie"),
            TaintLabel::DeserializedData => write!(f, "DeserializedData"),
            TaintLabel::ProcessArgs => write!(f, "ProcessArgs"),
            TaintLabel::Stdin => write!(f, "Stdin"),
            TaintLabel::ExternalApi => write!(f, "ExternalApi"),
            TaintLabel::Config => write!(f, "Config"),
            TaintLabel::Custom(name) => write!(f, "Custom({})", name),
        }
    }
}

// =============================================================================
// Taint Propagation Rules
// =============================================================================

/// Rules for how taint propagates through operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TaintPropagation {
    /// Direct copy: `taint(result) = taint(source)`
    /// Used for simple assignments: `x = y`
    Copy,
    /// Union merge: `taint(result) = taint(a) ∪ taint(b)`
    /// Used for binary operations: `x = a + b`, `x = a.concat(b)`
    Merge,
    /// Sanitization: removes taint from the value
    /// Used when data passes through known sanitizers
    Sanitize,
    /// Transform: preserves taint with metadata about the transformation
    /// Used for string operations that don't sanitize: `x = y.upper()`
    Transform,
    /// Conditional: taint propagates only under certain conditions
    /// Used for operations like `x = a if cond else b`
    Conditional,
    /// Collection access: taint of collection propagates to accessed element
    /// Used for: `x = arr[i]`, `x = obj.prop`, `x = dict[key]`
    CollectionAccess,
    /// Collection store: taint of value propagates to collection
    /// Used for: `arr[i] = x`, `obj.prop = x`, `dict[key] = x`
    CollectionStore,
    /// Function call: taint propagates from arguments to return value
    /// Used for non-sanitizing function calls
    CallReturn,
    /// Implicit flow: taint propagates through control flow
    /// Used for: `if (tainted) { x = secret; }` - x is implicitly tainted
    ImplicitFlow,
}

impl TaintPropagation {
    /// Returns whether this propagation rule preserves taint.
    #[inline]
    pub fn preserves_taint(&self) -> bool {
        !matches!(self, TaintPropagation::Sanitize)
    }

    /// Returns whether this is an explicit data flow.
    #[inline]
    pub fn is_explicit_flow(&self) -> bool {
        !matches!(self, TaintPropagation::ImplicitFlow)
    }
}

impl fmt::Display for TaintPropagation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TaintPropagation::Copy => write!(f, "copy"),
            TaintPropagation::Merge => write!(f, "merge"),
            TaintPropagation::Sanitize => write!(f, "sanitize"),
            TaintPropagation::Transform => write!(f, "transform"),
            TaintPropagation::Conditional => write!(f, "conditional"),
            TaintPropagation::CollectionAccess => write!(f, "collection_access"),
            TaintPropagation::CollectionStore => write!(f, "collection_store"),
            TaintPropagation::CallReturn => write!(f, "call_return"),
            TaintPropagation::ImplicitFlow => write!(f, "implicit_flow"),
        }
    }
}

// =============================================================================
// Tainted Value
// =============================================================================

/// A value with taint tracking metadata.
///
/// Tracks the origin of taint, the propagation path through the program,
/// and any transformations or sanitization applied.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintedValue {
    /// Set of taint labels (a value can have multiple sources)
    pub labels: HashSet<TaintLabel>,
    /// Where this taint originated
    pub source_location: Location,
    /// The path taint took through the program
    pub propagation_path: Vec<PropagationStep>,
    /// Whether this value has been sanitized
    pub sanitized: bool,
    /// Sanitization method used (if sanitized)
    pub sanitization_method: Option<String>,
    /// Original expression that introduced the taint
    pub source_expression: Option<String>,
    /// Confidence level (0.0-1.0) for uncertain taint
    pub confidence: f64,
}

impl TaintedValue {
    /// Create a new tainted value with a single label.
    pub fn new(label: TaintLabel, source_location: Location) -> Self {
        let mut labels = HashSet::new();
        labels.insert(label);
        Self {
            labels,
            source_location,
            propagation_path: Vec::new(),
            sanitized: false,
            sanitization_method: None,
            source_expression: None,
            confidence: 1.0,
        }
    }

    /// Create a tainted value with multiple labels.
    pub fn with_labels(labels: HashSet<TaintLabel>, source_location: Location) -> Self {
        Self {
            labels,
            source_location,
            propagation_path: Vec::new(),
            sanitized: false,
            sanitization_method: None,
            source_expression: None,
            confidence: 1.0,
        }
    }

    /// Create a clean (untainted) value.
    #[inline]
    pub fn clean() -> Self {
        Self {
            labels: HashSet::new(),
            source_location: Location::unknown(),
            propagation_path: Vec::new(),
            sanitized: false,
            sanitization_method: None,
            source_expression: None,
            confidence: 1.0,
        }
    }

    /// Check if this value is tainted (has any taint labels and not sanitized).
    #[inline]
    pub fn is_tainted(&self) -> bool {
        !self.labels.is_empty() && !self.sanitized
    }

    /// Check if this value has a specific taint label.
    #[inline]
    pub fn has_label(&self, label: &TaintLabel) -> bool {
        self.labels.contains(label)
    }

    /// Get the highest severity weight among all labels.
    pub fn max_severity(&self) -> u8 {
        self.labels
            .iter()
            .map(TaintLabel::severity_weight)
            .max()
            .unwrap_or(0)
    }

    /// Add a propagation step to track the taint flow.
    pub fn add_step(&mut self, step: PropagationStep) {
        self.propagation_path.push(step);
    }

    /// Copy taint from source, adding a propagation step.
    pub fn propagate_copy(&self, location: Location) -> Self {
        let mut result = self.clone();
        result.add_step(PropagationStep {
            location,
            propagation: TaintPropagation::Copy,
            operation: None,
        });
        result
    }

    /// Merge taint from multiple sources.
    pub fn merge(sources: &[&TaintedValue], location: Location) -> Self {
        let mut labels = HashSet::new();
        let mut confidence = 1.0_f64;
        let mut path = Vec::new();

        // Collect all labels from non-sanitized sources
        for source in sources {
            if !source.sanitized {
                labels.extend(source.labels.iter().cloned());
                confidence = confidence.min(source.confidence);
            }
        }

        // Take the first source's path and add merge step
        if let Some(first) = sources.first() {
            path = first.propagation_path.clone();
        }
        path.push(PropagationStep {
            location: location.clone(),
            propagation: TaintPropagation::Merge,
            operation: None,
        });

        Self {
            labels,
            source_location: sources
                .first()
                .map_or_else(Location::unknown, |s| s.source_location.clone()),
            propagation_path: path,
            sanitized: false,
            sanitization_method: None,
            source_expression: None,
            confidence,
        }
    }

    /// Create a sanitized version of this value.
    pub fn sanitize(&self, method: &str, location: Location) -> Self {
        let mut result = self.clone();
        result.sanitized = true;
        result.sanitization_method = Some(method.to_string());
        result.add_step(PropagationStep {
            location,
            propagation: TaintPropagation::Sanitize,
            operation: Some(method.to_string()),
        });
        result
    }

    /// Create a transformed version preserving taint.
    pub fn transform(&self, operation: &str, location: Location) -> Self {
        let mut result = self.clone();
        result.add_step(PropagationStep {
            location,
            propagation: TaintPropagation::Transform,
            operation: Some(operation.to_string()),
        });
        result
    }

    /// Propagate taint through collection access (array index, object property).
    pub fn collection_access(&self, access_expr: &str, location: Location) -> Self {
        let mut result = self.clone();
        result.add_step(PropagationStep {
            location,
            propagation: TaintPropagation::CollectionAccess,
            operation: Some(access_expr.to_string()),
        });
        result
    }

    /// Propagate taint through function call return.
    pub fn call_return(&self, function_name: &str, location: Location) -> Self {
        let mut result = self.clone();
        result.add_step(PropagationStep {
            location,
            propagation: TaintPropagation::CallReturn,
            operation: Some(function_name.to_string()),
        });
        result
    }

    /// Set the source expression for debugging.
    pub fn with_source_expression(mut self, expr: impl Into<String>) -> Self {
        self.source_expression = Some(expr.into());
        self
    }

    /// Set confidence level (0.0-1.0).
    pub fn with_confidence(mut self, confidence: f64) -> Self {
        self.confidence = confidence.clamp(0.0, 1.0);
        self
    }
}

impl Default for TaintedValue {
    fn default() -> Self {
        Self::clean()
    }
}

// =============================================================================
// Propagation Step
// =============================================================================

/// A single step in the taint propagation path.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PropagationStep {
    /// Location where this propagation occurred
    pub location: Location,
    /// Type of propagation
    pub propagation: TaintPropagation,
    /// Operation that caused the propagation (if applicable)
    pub operation: Option<String>,
}

impl fmt::Display for PropagationStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref op) = self.operation {
            write!(f, "{} via {} at {}", self.propagation, op, self.location)
        } else {
            write!(f, "{} at {}", self.propagation, self.location)
        }
    }
}

// =============================================================================
// Taint State (Aggregated State for Analysis)
// =============================================================================

/// Aggregated taint state for a variable or expression in the analysis.
///
/// This represents the combined taint information at a program point,
/// which may include taint from multiple control flow paths.
#[derive(Debug, Clone, Default)]
pub struct TaintState {
    /// Map from variable name to its taint value
    variables: fxhash::FxHashMap<String, TaintedValue>,
    /// Taint for object properties: (object, property) -> taint
    properties: fxhash::FxHashMap<(String, String), TaintedValue>,
    /// Taint for collection elements: collection -> taint (conservative)
    /// If any element is tainted, the whole collection is considered tainted
    collections: fxhash::FxHashMap<String, TaintedValue>,
}

impl TaintState {
    /// Create an empty taint state.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set taint for a variable.
    pub fn set_variable(&mut self, name: impl Into<String>, taint: TaintedValue) {
        self.variables.insert(name.into(), taint);
    }

    /// Get taint for a variable.
    pub fn get_variable(&self, name: &str) -> Option<&TaintedValue> {
        self.variables.get(name)
    }

    /// Check if a variable is tainted.
    pub fn is_variable_tainted(&self, name: &str) -> bool {
        self.variables
            .get(name)
            .map_or(false, TaintedValue::is_tainted)
    }

    /// Set taint for an object property.
    pub fn set_property(
        &mut self,
        object: impl Into<String>,
        property: impl Into<String>,
        taint: TaintedValue,
    ) {
        self.properties
            .insert((object.into(), property.into()), taint);
    }

    /// Get taint for an object property.
    ///
    /// Returns the property-specific taint if set, otherwise returns
    /// the object's overall taint (conservative approximation).
    pub fn get_property(&self, object: &str, property: &str) -> Option<&TaintedValue> {
        self.properties
            .get(&(object.to_string(), property.to_string()))
            .or_else(|| self.variables.get(object))
    }

    /// Set taint for a collection (conservative: whole collection tainted).
    pub fn set_collection(&mut self, collection: impl Into<String>, taint: TaintedValue) {
        self.collections.insert(collection.into(), taint);
    }

    /// Get taint for a collection or its element.
    pub fn get_collection(&self, collection: &str) -> Option<&TaintedValue> {
        self.collections
            .get(collection)
            .or_else(|| self.variables.get(collection))
    }

    /// Merge another taint state into this one (for control flow merge points).
    pub fn merge(&mut self, other: &TaintState, location: &Location) {
        // Merge variables
        for (name, other_taint) in &other.variables {
            if let Some(existing) = self.variables.get(name) {
                // Both paths have this variable - merge taints
                let merged = TaintedValue::merge(&[existing, other_taint], location.clone());
                self.variables.insert(name.clone(), merged);
            } else {
                // Only other path has this variable
                self.variables.insert(name.clone(), other_taint.clone());
            }
        }

        // Merge properties
        for (key, other_taint) in &other.properties {
            if let Some(existing) = self.properties.get(key) {
                let merged = TaintedValue::merge(&[existing, other_taint], location.clone());
                self.properties.insert(key.clone(), merged);
            } else {
                self.properties.insert(key.clone(), other_taint.clone());
            }
        }

        // Merge collections
        for (name, other_taint) in &other.collections {
            if let Some(existing) = self.collections.get(name) {
                let merged = TaintedValue::merge(&[existing, other_taint], location.clone());
                self.collections.insert(name.clone(), merged);
            } else {
                self.collections.insert(name.clone(), other_taint.clone());
            }
        }
    }

    /// Get all tainted variables.
    pub fn tainted_variables(&self) -> Vec<(&String, &TaintedValue)> {
        self.variables
            .iter()
            .filter(|(_, v)| v.is_tainted())
            .collect()
    }

    /// Clear all taint information.
    pub fn clear(&mut self) {
        self.variables.clear();
        self.properties.clear();
        self.collections.clear();
    }

    /// Check if any variable is tainted.
    pub fn has_any_taint(&self) -> bool {
        self.variables.values().any(TaintedValue::is_tainted)
            || self.properties.values().any(TaintedValue::is_tainted)
            || self.collections.values().any(TaintedValue::is_tainted)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_taint_label_severity() {
        assert!(TaintLabel::UserInput.severity_weight() > TaintLabel::Config.severity_weight());
        assert!(TaintLabel::ProcessArgs.severity_weight() > TaintLabel::FileContent.severity_weight());
    }

    #[test]
    fn test_tainted_value_creation() {
        let loc = Location::new("test.py", 10, 5);
        let taint = TaintedValue::new(TaintLabel::UserInput, loc);

        assert!(taint.is_tainted());
        assert!(taint.has_label(&TaintLabel::UserInput));
        assert!(!taint.has_label(&TaintLabel::FileContent));
        assert_eq!(taint.max_severity(), 10);
    }

    #[test]
    fn test_tainted_value_clean() {
        let clean = TaintedValue::clean();
        assert!(!clean.is_tainted());
        assert!(clean.labels.is_empty());
    }

    #[test]
    fn test_taint_propagation_copy() {
        let loc1 = Location::new("test.py", 10, 5);
        let loc2 = Location::new("test.py", 15, 5);
        let original = TaintedValue::new(TaintLabel::UserInput, loc1);

        let copied = original.propagate_copy(loc2);

        assert!(copied.is_tainted());
        assert!(copied.has_label(&TaintLabel::UserInput));
        assert_eq!(copied.propagation_path.len(), 1);
        assert_eq!(copied.propagation_path[0].propagation, TaintPropagation::Copy);
    }

    #[test]
    fn test_taint_merge() {
        let loc1 = Location::new("test.py", 10, 5);
        let loc2 = Location::new("test.py", 11, 5);
        let loc3 = Location::new("test.py", 12, 5);

        let taint1 = TaintedValue::new(TaintLabel::UserInput, loc1);
        let taint2 = TaintedValue::new(TaintLabel::FileContent, loc2);

        let merged = TaintedValue::merge(&[&taint1, &taint2], loc3);

        assert!(merged.is_tainted());
        assert!(merged.has_label(&TaintLabel::UserInput));
        assert!(merged.has_label(&TaintLabel::FileContent));
        assert_eq!(merged.labels.len(), 2);
    }

    #[test]
    fn test_taint_sanitize() {
        let loc1 = Location::new("test.py", 10, 5);
        let loc2 = Location::new("test.py", 15, 5);
        let taint = TaintedValue::new(TaintLabel::UserInput, loc1);

        let sanitized = taint.sanitize("html_escape", loc2);

        assert!(!sanitized.is_tainted());
        assert!(sanitized.sanitized);
        assert_eq!(sanitized.sanitization_method, Some("html_escape".to_string()));
    }

    #[test]
    fn test_taint_transform() {
        let loc1 = Location::new("test.py", 10, 5);
        let loc2 = Location::new("test.py", 15, 5);
        let taint = TaintedValue::new(TaintLabel::UserInput, loc1);

        let transformed = taint.transform("upper()", loc2);

        assert!(transformed.is_tainted());
        assert_eq!(transformed.propagation_path.len(), 1);
        assert_eq!(
            transformed.propagation_path[0].operation,
            Some("upper()".to_string())
        );
    }

    #[test]
    fn test_taint_collection_access() {
        let loc1 = Location::new("test.py", 10, 5);
        let loc2 = Location::new("test.py", 15, 5);
        let taint = TaintedValue::new(TaintLabel::UserInput, loc1);

        let accessed = taint.collection_access("[0]", loc2);

        assert!(accessed.is_tainted());
        assert_eq!(
            accessed.propagation_path[0].propagation,
            TaintPropagation::CollectionAccess
        );
    }

    #[test]
    fn test_taint_state() {
        let loc = Location::new("test.py", 10, 5);
        let mut state = TaintState::new();

        let taint = TaintedValue::new(TaintLabel::UserInput, loc);
        state.set_variable("user_input", taint);

        assert!(state.is_variable_tainted("user_input"));
        assert!(!state.is_variable_tainted("other_var"));

        let tainted = state.tainted_variables();
        assert_eq!(tainted.len(), 1);
        assert_eq!(tainted[0].0, "user_input");
    }

    #[test]
    fn test_taint_state_merge() {
        let loc1 = Location::new("test.py", 10, 5);
        let loc2 = Location::new("test.py", 20, 5);
        let merge_loc = Location::new("test.py", 25, 5);

        let mut state1 = TaintState::new();
        state1.set_variable("x", TaintedValue::new(TaintLabel::UserInput, loc1.clone()));

        let mut state2 = TaintState::new();
        state2.set_variable("x", TaintedValue::new(TaintLabel::FileContent, loc2));
        state2.set_variable("y", TaintedValue::new(TaintLabel::NetworkData, loc1));

        state1.merge(&state2, &merge_loc);

        // x should have merged taint (both labels)
        let x_taint = state1.get_variable("x").unwrap();
        assert!(x_taint.has_label(&TaintLabel::UserInput));
        assert!(x_taint.has_label(&TaintLabel::FileContent));

        // y should be present from state2
        assert!(state1.is_variable_tainted("y"));
    }

    #[test]
    fn test_location_display() {
        let loc = Location::new("test.py", 10, 5);
        assert_eq!(format!("{}", loc), "test.py:10:5");

        let span = Location::with_span("test.py", 10, 5, 12, 20);
        assert_eq!(format!("{}", span), "test.py:10:5-12:20");
    }

    #[test]
    fn test_propagation_step_display() {
        let loc = Location::new("test.py", 10, 5);
        let step = PropagationStep {
            location: loc,
            propagation: TaintPropagation::Transform,
            operation: Some("upper()".to_string()),
        };
        assert!(format!("{}", step).contains("transform"));
        assert!(format!("{}", step).contains("upper()"));
    }

    #[test]
    fn test_taint_confidence() {
        let loc = Location::new("test.py", 10, 5);
        let taint = TaintedValue::new(TaintLabel::UserInput, loc).with_confidence(0.8);

        assert!((taint.confidence - 0.8).abs() < f64::EPSILON);
    }

    #[test]
    fn test_taint_merge_confidence() {
        let loc1 = Location::new("test.py", 10, 5);
        let loc2 = Location::new("test.py", 11, 5);
        let loc3 = Location::new("test.py", 12, 5);

        let taint1 = TaintedValue::new(TaintLabel::UserInput, loc1).with_confidence(0.9);
        let taint2 = TaintedValue::new(TaintLabel::FileContent, loc2).with_confidence(0.7);

        let merged = TaintedValue::merge(&[&taint1, &taint2], loc3);

        // Merged confidence should be the minimum
        assert!((merged.confidence - 0.7).abs() < f64::EPSILON);
    }
}
