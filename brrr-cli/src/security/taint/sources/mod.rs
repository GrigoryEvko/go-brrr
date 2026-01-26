//! Taint source identification for multiple languages.
//!
//! This module provides two complementary approaches to identifying taint sources:
//!
//! 1. **Pattern-based matching** ([`registry`]): Fast string pattern matching for
//!    common source patterns. Used for quick lookups during analysis.
//!
//! 2. **AST-based detection** ([`python`], [`typescript`], [`go`], [`rust`]): Deep AST
//!    analysis using tree-sitter for precise source identification including decorator
//!    analysis, handler parameter detection, and language-specific patterns.
//!
//! # Pattern-Based Usage
//!
//! For quick pattern matching against code snippets:
//!
//! ```ignore
//! use brrr::security::taint::sources::{get_python_sources, SourceRegistry};
//!
//! let registry = get_python_sources();
//! let matches = registry.find_matches("request.args.get('id')");
//! assert!(matches.iter().any(|s| s.label == TaintLabel::UserInput));
//! ```
//!
//! # AST-Based Usage
//!
//! For comprehensive analysis of source files:
//!
//! ```ignore
//! use brrr::security::taint::sources::python::PythonSourceDetector;
//! use brrr::security::taint::sources::go::GoSourceDetector;
//! use brrr::security::taint::sources::rust::RustSourceDetector;
//!
//! // Python
//! let detector = PythonSourceDetector::new();
//! let result = detector.scan_file("app.py")?;
//!
//! // Go
//! let detector = GoSourceDetector::new();
//! let result = detector.scan_file("handler.go")?;
//!
//! // Rust
//! let detector = RustSourceDetector::new();
//! let result = detector.scan_file("handler.rs")?;
//!
//! for source in &result.sources {
//!     println!("{}: {} at line {}", source.kind, source.expression, source.location.line);
//! }
//! ```

// Common types and infrastructure for taint source detection
pub mod common;

// Pattern-based source registry (original implementation)
pub mod registry;

// AST-based Python source detector
pub mod python;

// AST-based TypeScript/JavaScript source detector
pub mod typescript;

// AST-based Go source detector
pub mod go;

// AST-based Rust source detector
pub mod rust;

// Re-export everything from registry for backward compatibility
pub use registry::{
    get_go_sources, get_python_sources, get_rust_sources, get_sources_for_language,
    get_typescript_sources, MatchStrategy, SourceRegistry, TaintSource,
};

// Re-export AST-based detectors
pub use python::PythonSourceDetector;
pub use typescript::TypeScriptSourceDetector;

// Re-export common types for use in language-specific detectors
pub use common::{
    AstHelpers, ImportAliases, ParameterTypeMap, ResponseMethodPatterns, ScanContextBase,
    SourceCategory, TaintSourceDef, TaintedVariables,
};

use crate::security::taint::types::{Location, TaintLabel};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

// =============================================================================
// AST-Based Source Detection Types
// =============================================================================

/// Category of taint source for AST-based detection.
///
/// This provides more granular classification than TaintLabel for
/// precise source identification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SourceKind {
    /// Web request parameters (GET/POST/query string)
    RequestParam,
    /// Request body (JSON, form data)
    RequestBody,
    /// HTTP headers
    HttpHeader,
    /// Cookie values
    Cookie,
    /// Uploaded files
    FileUpload,
    /// URL path segments
    UrlPath,
    /// Standard input (input(), stdin)
    Stdin,
    /// Command line arguments (sys.argv, process.argv)
    ProcessArgs,
    /// Environment variables
    Environment,
    /// File content from user-controlled path
    FileRead,
    /// HTTP response from external URL
    HttpResponse,
    /// Socket receive
    SocketRecv,
    /// Database query result
    DatabaseResult,
    /// Deserialized data (JSON, YAML, pickle)
    Deserialized,
    /// External API response
    ExternalApi,
    /// WebSocket message
    WebSocketMessage,
    /// Generic user input (unclassified)
    GenericUserInput,
}

impl SourceKind {
    /// Convert source kind to corresponding taint labels.
    pub fn to_taint_labels(&self) -> HashSet<TaintLabel> {
        let mut labels = HashSet::new();
        match self {
            SourceKind::RequestParam | SourceKind::RequestBody => {
                labels.insert(TaintLabel::UserInput);
            }
            SourceKind::HttpHeader => {
                labels.insert(TaintLabel::HttpHeader);
            }
            SourceKind::Cookie => {
                labels.insert(TaintLabel::Cookie);
            }
            SourceKind::FileUpload => {
                labels.insert(TaintLabel::UserInput);
                labels.insert(TaintLabel::FileContent);
            }
            SourceKind::UrlPath => {
                labels.insert(TaintLabel::UrlData);
            }
            SourceKind::Stdin => {
                labels.insert(TaintLabel::Stdin);
            }
            SourceKind::ProcessArgs => {
                labels.insert(TaintLabel::ProcessArgs);
            }
            SourceKind::Environment => {
                labels.insert(TaintLabel::Environment);
            }
            SourceKind::FileRead => {
                labels.insert(TaintLabel::FileContent);
            }
            SourceKind::HttpResponse | SourceKind::ExternalApi => {
                labels.insert(TaintLabel::NetworkData);
                labels.insert(TaintLabel::ExternalApi);
            }
            SourceKind::SocketRecv => {
                labels.insert(TaintLabel::NetworkData);
            }
            SourceKind::DatabaseResult => {
                labels.insert(TaintLabel::DatabaseQuery);
            }
            SourceKind::Deserialized => {
                labels.insert(TaintLabel::DeserializedData);
            }
            SourceKind::WebSocketMessage => {
                labels.insert(TaintLabel::NetworkData);
                labels.insert(TaintLabel::UserInput);
            }
            SourceKind::GenericUserInput => {
                labels.insert(TaintLabel::UserInput);
            }
        }
        labels
    }

    /// Get severity weight for prioritizing findings.
    pub fn severity_weight(&self) -> u8 {
        match self {
            SourceKind::RequestParam | SourceKind::RequestBody => 10,
            SourceKind::ProcessArgs | SourceKind::Stdin => 9,
            SourceKind::Cookie | SourceKind::UrlPath => 8,
            SourceKind::HttpHeader | SourceKind::WebSocketMessage => 7,
            SourceKind::HttpResponse | SourceKind::ExternalApi => 7,
            SourceKind::Deserialized => 8,
            SourceKind::FileUpload | SourceKind::FileRead => 6,
            SourceKind::SocketRecv => 6,
            SourceKind::DatabaseResult => 5,
            SourceKind::Environment => 4,
            SourceKind::GenericUserInput => 5,
        }
    }

    /// Get human-readable description.
    pub fn description(&self) -> &'static str {
        match self {
            SourceKind::RequestParam => "HTTP request parameter",
            SourceKind::RequestBody => "HTTP request body",
            SourceKind::HttpHeader => "HTTP header",
            SourceKind::Cookie => "HTTP cookie",
            SourceKind::FileUpload => "uploaded file",
            SourceKind::UrlPath => "URL path segment",
            SourceKind::Stdin => "standard input",
            SourceKind::ProcessArgs => "command line argument",
            SourceKind::Environment => "environment variable",
            SourceKind::FileRead => "file content",
            SourceKind::HttpResponse => "HTTP response",
            SourceKind::SocketRecv => "socket data",
            SourceKind::DatabaseResult => "database query result",
            SourceKind::Deserialized => "deserialized data",
            SourceKind::ExternalApi => "external API response",
            SourceKind::WebSocketMessage => "WebSocket message",
            SourceKind::GenericUserInput => "user input",
        }
    }
}

impl std::fmt::Display for SourceKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description())
    }
}

// =============================================================================
// Detected Taint Source
// =============================================================================

/// A detected taint source in source code (AST-based).
///
/// Represents a location where untrusted data enters the program.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectedSource {
    /// Kind of taint source
    pub kind: SourceKind,
    /// Location in source code
    pub location: Location,
    /// The expression that introduces taint (e.g., "request.args.get('id')")
    pub expression: String,
    /// Variable name the tainted value is assigned to (if applicable)
    pub assigned_to: Option<String>,
    /// Confidence score (0.0 to 1.0)
    pub confidence: f64,
    /// Framework or library this source belongs to (e.g., "flask", "django")
    pub framework: Option<String>,
    /// Additional context (e.g., parameter name, header name)
    pub context: Option<String>,
    /// Whether this source is in a handler function (e.g., Flask route)
    pub in_handler: bool,
    /// Name of the enclosing function
    pub enclosing_function: Option<String>,
}

impl DetectedSource {
    /// Create a new detected source.
    pub fn new(kind: SourceKind, location: Location, expression: impl Into<String>) -> Self {
        Self {
            kind,
            location,
            expression: expression.into(),
            assigned_to: None,
            confidence: 1.0,
            framework: None,
            context: None,
            in_handler: false,
            enclosing_function: None,
        }
    }

    /// Set the variable this source is assigned to.
    pub fn with_assignment(mut self, var: impl Into<String>) -> Self {
        self.assigned_to = Some(var.into());
        self
    }

    /// Set confidence score.
    pub fn with_confidence(mut self, confidence: f64) -> Self {
        self.confidence = confidence.clamp(0.0, 1.0);
        self
    }

    /// Set the framework context.
    pub fn with_framework(mut self, framework: impl Into<String>) -> Self {
        self.framework = Some(framework.into());
        self
    }

    /// Set additional context.
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    /// Mark as being in a handler function.
    pub fn in_handler_function(mut self, func_name: impl Into<String>) -> Self {
        self.in_handler = true;
        self.enclosing_function = Some(func_name.into());
        self
    }

    /// Get taint labels for this source.
    pub fn taint_labels(&self) -> HashSet<TaintLabel> {
        self.kind.to_taint_labels()
    }
}

// =============================================================================
// Source Pattern Definition (for AST detector)
// =============================================================================

/// A pattern for detecting taint sources in AST analysis.
#[derive(Debug, Clone)]
pub struct SourcePattern {
    /// Pattern name for identification
    pub name: &'static str,
    /// Kind of source this pattern detects
    pub kind: SourceKind,
    /// Object/module the method is called on (e.g., "request", "os")
    pub object: Option<&'static str>,
    /// Method/attribute name (e.g., "args", "environ")
    pub method: &'static str,
    /// Whether this is a property access (vs method call)
    pub is_property: bool,
    /// Confidence score for matches
    pub confidence: f64,
    /// Framework/library this belongs to
    pub framework: Option<&'static str>,
}

impl SourcePattern {
    /// Create a method call pattern.
    pub const fn method_call(
        name: &'static str,
        kind: SourceKind,
        object: &'static str,
        method: &'static str,
        framework: Option<&'static str>,
    ) -> Self {
        Self {
            name,
            kind,
            object: Some(object),
            method,
            is_property: false,
            confidence: 0.95,
            framework,
        }
    }

    /// Create a property access pattern.
    pub const fn property_access(
        name: &'static str,
        kind: SourceKind,
        object: &'static str,
        property: &'static str,
        framework: Option<&'static str>,
    ) -> Self {
        Self {
            name,
            kind,
            object: Some(object),
            method: property,
            is_property: true,
            confidence: 0.95,
            framework,
        }
    }

    /// Create a function call pattern (no object).
    pub const fn function_call(
        name: &'static str,
        kind: SourceKind,
        function: &'static str,
        confidence: f64,
    ) -> Self {
        Self {
            name,
            kind,
            object: None,
            method: function,
            is_property: false,
            confidence,
            framework: None,
        }
    }
}

// =============================================================================
// Handler Context (for web framework detection)
// =============================================================================

/// Information about a web handler function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandlerInfo {
    /// Function name
    pub name: String,
    /// Start line of the function
    pub start_line: usize,
    /// End line of the function
    pub end_line: usize,
    /// Route path (e.g., "/users/<id>")
    pub route: Option<String>,
    /// HTTP methods (GET, POST, etc.)
    pub methods: Vec<String>,
    /// Framework (flask, django, fastapi)
    pub framework: String,
    /// Parameters that are tainted (from URL path, query, body)
    pub tainted_params: Vec<TaintedParameter>,
}

/// A tainted parameter in a handler function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintedParameter {
    /// Parameter name
    pub name: String,
    /// Source kind
    pub kind: SourceKind,
    /// Parameter index in function signature
    pub index: usize,
    /// FastAPI annotation type (Body, Query, Path, Header, etc.)
    pub annotation: Option<String>,
}

// =============================================================================
// Scan Results
// =============================================================================

/// Results from scanning a file for taint sources (AST-based).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceScanResult {
    /// Path to the scanned file
    pub file: String,
    /// Detected taint sources
    pub sources: Vec<DetectedSource>,
    /// Detected handler functions
    pub handlers: Vec<HandlerInfo>,
    /// Language of the file
    pub language: String,
    /// Errors encountered during scanning
    pub errors: Vec<String>,
}

impl SourceScanResult {
    /// Create an empty result for a file.
    pub fn new(file: impl Into<String>, language: impl Into<String>) -> Self {
        Self {
            file: file.into(),
            sources: Vec::new(),
            handlers: Vec::new(),
            language: language.into(),
            errors: Vec::new(),
        }
    }

    /// Add a detected source.
    pub fn add_source(&mut self, source: DetectedSource) {
        self.sources.push(source);
    }

    /// Add a handler.
    pub fn add_handler(&mut self, handler: HandlerInfo) {
        self.handlers.push(handler);
    }

    /// Add an error.
    pub fn add_error(&mut self, error: impl Into<String>) {
        self.errors.push(error.into());
    }

    /// Check if any sources were found.
    pub fn has_sources(&self) -> bool {
        !self.sources.is_empty()
    }

    /// Get sources by kind.
    pub fn sources_by_kind(&self, kind: SourceKind) -> Vec<&DetectedSource> {
        self.sources.iter().filter(|s| s.kind == kind).collect()
    }

    /// Get all sources in handler functions.
    pub fn handler_sources(&self) -> Vec<&DetectedSource> {
        self.sources.iter().filter(|s| s.in_handler).collect()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_source_kind_to_labels() {
        let labels = SourceKind::RequestParam.to_taint_labels();
        assert!(labels.contains(&TaintLabel::UserInput));

        let labels = SourceKind::Cookie.to_taint_labels();
        assert!(labels.contains(&TaintLabel::Cookie));

        let labels = SourceKind::FileUpload.to_taint_labels();
        assert!(labels.contains(&TaintLabel::UserInput));
        assert!(labels.contains(&TaintLabel::FileContent));
    }

    #[test]
    fn test_source_kind_severity() {
        assert!(
            SourceKind::RequestParam.severity_weight() > SourceKind::Environment.severity_weight()
        );
        assert!(
            SourceKind::ProcessArgs.severity_weight()
                > SourceKind::DatabaseResult.severity_weight()
        );
    }

    #[test]
    fn test_detected_source_builder() {
        let loc = Location::new("test.py", 10, 5);
        let source = DetectedSource::new(SourceKind::RequestParam, loc, "request.args.get('id')")
            .with_assignment("user_id")
            .with_confidence(0.9)
            .with_framework("flask")
            .with_context("id parameter")
            .in_handler_function("get_user");

        assert_eq!(source.kind, SourceKind::RequestParam);
        assert_eq!(source.assigned_to, Some("user_id".to_string()));
        assert!((source.confidence - 0.9).abs() < f64::EPSILON);
        assert_eq!(source.framework, Some("flask".to_string()));
        assert!(source.in_handler);
        assert_eq!(source.enclosing_function, Some("get_user".to_string()));
    }

    #[test]
    fn test_source_pattern() {
        let pattern = SourcePattern::method_call(
            "flask_request_args",
            SourceKind::RequestParam,
            "request",
            "args",
            Some("flask"),
        );

        assert_eq!(pattern.object, Some("request"));
        assert_eq!(pattern.method, "args");
        assert!(!pattern.is_property);

        let prop_pattern = SourcePattern::property_access(
            "django_request_GET",
            SourceKind::RequestParam,
            "request",
            "GET",
            Some("django"),
        );

        assert!(prop_pattern.is_property);
    }

    #[test]
    fn test_scan_result() {
        let mut result = SourceScanResult::new("test.py", "python");

        let loc = Location::new("test.py", 10, 5);
        let source = DetectedSource::new(SourceKind::RequestParam, loc, "request.args");
        result.add_source(source);

        assert!(result.has_sources());
        assert_eq!(result.sources_by_kind(SourceKind::RequestParam).len(), 1);
        assert!(result.sources_by_kind(SourceKind::Cookie).is_empty());
    }

    #[test]
    fn test_handler_info() {
        let handler = HandlerInfo {
            name: "get_user".to_string(),
            start_line: 10,
            end_line: 20,
            route: Some("/users/<int:id>".to_string()),
            methods: vec!["GET".to_string()],
            framework: "flask".to_string(),
            tainted_params: vec![TaintedParameter {
                name: "id".to_string(),
                kind: SourceKind::UrlPath,
                index: 0,
                annotation: None,
            }],
        };

        assert_eq!(handler.name, "get_user");
        assert_eq!(handler.tainted_params.len(), 1);
        assert_eq!(handler.tainted_params[0].kind, SourceKind::UrlPath);
    }

    #[test]
    fn test_registry_reexport() {
        // Test that the pattern-based registry is properly re-exported
        let registry = get_python_sources();
        assert!(!registry.is_empty());

        let matches = registry.find_matches("request.args.get('id')");
        assert!(!matches.is_empty());
    }
}
