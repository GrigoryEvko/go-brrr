//! Common taint source definitions and infrastructure.
//!
//! This module provides shared types and utilities for language-specific
//! taint source detectors, reducing code duplication across Python, TypeScript,
//! Go, and Rust implementations.
//!
//! # Organization
//!
//! - [`SourceCategory`]: High-level categorization of taint sources
//! - [`TaintSourceDef`]: Declarative source definition for building registries
//! - [`ResponseMethodPatterns`]: Common response method detection patterns
//! - [`ScanContextBase`]: Shared fields for scanning context
//! - [`AstHelpers`]: Trait for common AST operations

use rustc_hash::{FxHashMap, FxHashSet};

use super::{HandlerInfo, SourceKind};

// =============================================================================
// Source Categories
// =============================================================================

/// High-level category of taint sources.
///
/// This provides a coarser classification than [`SourceKind`] for organizing
/// source patterns by their origin type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SourceCategory {
    /// User input from HTTP requests (GET/POST params, form data, body)
    UserInput,
    /// HTTP headers (authorization, content-type, custom headers)
    HttpHeaders,
    /// HTTP cookies
    Cookies,
    /// URL-derived data (path segments, query strings, fragments)
    UrlData,
    /// File uploads (multipart form data)
    FileUpload,
    /// Environment variables and configuration
    Environment,
    /// Command line arguments
    ProcessArgs,
    /// Standard input (stdin)
    Stdin,
    /// File system reads
    FileSystem,
    /// Network responses (HTTP clients, sockets)
    Network,
    /// Database query results
    Database,
    /// Deserialized data (JSON, YAML, XML, binary formats)
    Deserialization,
    /// WebSocket messages
    WebSocket,
    /// External API responses
    ExternalApi,
}

impl SourceCategory {
    /// Get the default [`SourceKind`] for this category.
    #[must_use]
    pub fn default_source_kind(&self) -> SourceKind {
        match self {
            SourceCategory::UserInput => SourceKind::RequestParam,
            SourceCategory::HttpHeaders => SourceKind::HttpHeader,
            SourceCategory::Cookies => SourceKind::Cookie,
            SourceCategory::UrlData => SourceKind::UrlPath,
            SourceCategory::FileUpload => SourceKind::FileUpload,
            SourceCategory::Environment => SourceKind::Environment,
            SourceCategory::ProcessArgs => SourceKind::ProcessArgs,
            SourceCategory::Stdin => SourceKind::Stdin,
            SourceCategory::FileSystem => SourceKind::FileRead,
            SourceCategory::Network => SourceKind::HttpResponse,
            SourceCategory::Database => SourceKind::DatabaseResult,
            SourceCategory::Deserialization => SourceKind::Deserialized,
            SourceCategory::WebSocket => SourceKind::WebSocketMessage,
            SourceCategory::ExternalApi => SourceKind::ExternalApi,
        }
    }

    /// Get a human-readable description.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            SourceCategory::UserInput => "HTTP request input",
            SourceCategory::HttpHeaders => "HTTP headers",
            SourceCategory::Cookies => "HTTP cookies",
            SourceCategory::UrlData => "URL data",
            SourceCategory::FileUpload => "file upload",
            SourceCategory::Environment => "environment variable",
            SourceCategory::ProcessArgs => "command line argument",
            SourceCategory::Stdin => "standard input",
            SourceCategory::FileSystem => "file content",
            SourceCategory::Network => "network response",
            SourceCategory::Database => "database result",
            SourceCategory::Deserialization => "deserialized data",
            SourceCategory::WebSocket => "WebSocket message",
            SourceCategory::ExternalApi => "external API response",
        }
    }
}

// =============================================================================
// Base Source Definition
// =============================================================================

/// Declarative definition of a taint source.
///
/// Used to define source patterns in a language-agnostic way that can be
/// converted to language-specific [`SourcePattern`] instances.
#[derive(Debug, Clone)]
pub struct TaintSourceDef {
    /// Identifier name for this source pattern
    pub name: &'static str,
    /// High-level category
    pub category: SourceCategory,
    /// Specific source kind (if different from category default)
    pub kind: Option<SourceKind>,
    /// Object/module the method is called on (e.g., "request", "os")
    pub object: Option<&'static str>,
    /// Method/attribute/function name (e.g., "args", "environ", "getenv")
    pub member: &'static str,
    /// Whether this is a property access (vs method call)
    pub is_property: bool,
    /// Whether this pattern indicates sensitive data
    pub is_sensitive: bool,
    /// Base confidence score (0.0-1.0)
    pub confidence: f64,
    /// Framework this belongs to (e.g., "flask", "express", "actix-web")
    pub framework: Option<&'static str>,
}

impl TaintSourceDef {
    /// Create a method call source definition.
    #[must_use]
    pub const fn method(
        name: &'static str,
        category: SourceCategory,
        object: &'static str,
        method: &'static str,
    ) -> Self {
        Self {
            name,
            category,
            kind: None,
            object: Some(object),
            member: method,
            is_property: false,
            is_sensitive: false,
            confidence: 0.95,
            framework: None,
        }
    }

    /// Create a property access source definition.
    #[must_use]
    pub const fn property(
        name: &'static str,
        category: SourceCategory,
        object: &'static str,
        property: &'static str,
    ) -> Self {
        Self {
            name,
            category,
            kind: None,
            object: Some(object),
            member: property,
            is_property: true,
            is_sensitive: false,
            confidence: 0.95,
            framework: None,
        }
    }

    /// Create a standalone function call source definition.
    #[must_use]
    pub const fn function(name: &'static str, category: SourceCategory, func: &'static str) -> Self {
        Self {
            name,
            category,
            kind: None,
            object: None,
            member: func,
            is_property: false,
            is_sensitive: false,
            confidence: 0.90,
            framework: None,
        }
    }

    /// Set a specific source kind (overrides category default).
    #[must_use]
    pub const fn with_kind(mut self, kind: SourceKind) -> Self {
        self.kind = Some(kind);
        self
    }

    /// Set framework context.
    #[must_use]
    pub const fn with_framework(mut self, framework: &'static str) -> Self {
        self.framework = Some(framework);
        self
    }

    /// Set confidence level.
    #[must_use]
    pub const fn with_confidence(mut self, confidence: f64) -> Self {
        self.confidence = confidence;
        self
    }

    /// Mark as sensitive data source.
    #[must_use]
    pub const fn sensitive(mut self) -> Self {
        self.is_sensitive = true;
        self
    }

    /// Get the effective source kind.
    #[must_use]
    pub fn source_kind(&self) -> SourceKind {
        self.kind.unwrap_or_else(|| self.category.default_source_kind())
    }
}

// =============================================================================
// Response Method Patterns
// =============================================================================

/// Common patterns for detecting response methods that return tainted data.
///
/// These patterns are shared across languages for identifying HTTP response
/// processing methods.
#[derive(Debug, Clone, Default)]
pub struct ResponseMethodPatterns {
    /// Object names that typically represent HTTP responses
    pub response_objects: FxHashSet<&'static str>,
    /// Method names that extract data from responses
    pub data_methods: FxHashSet<&'static str>,
}

impl ResponseMethodPatterns {
    /// Create with default patterns.
    #[must_use]
    pub fn new() -> Self {
        let mut response_objects = FxHashSet::default();
        response_objects.insert("response");
        response_objects.insert("resp");
        response_objects.insert("res");
        response_objects.insert("r");
        response_objects.insert("result");
        response_objects.insert("Response");

        let mut data_methods = FxHashSet::default();
        data_methods.insert("text");
        data_methods.insert("json");
        data_methods.insert("bytes");
        data_methods.insert("body");
        data_methods.insert("content");
        data_methods.insert("read");
        data_methods.insert("chunk");
        data_methods.insert("iter_content");
        data_methods.insert("iter_lines");

        Self {
            response_objects,
            data_methods,
        }
    }

    /// Check if object and method combination indicates a response data access.
    #[must_use]
    pub fn is_response_method(&self, object_name: &str, method: &str) -> bool {
        (self.response_objects.contains(object_name) || object_name.ends_with("Response"))
            && self.data_methods.contains(method)
    }

    /// Add a response object pattern.
    pub fn add_response_object(&mut self, name: &'static str) {
        self.response_objects.insert(name);
    }

    /// Add a data extraction method.
    pub fn add_data_method(&mut self, name: &'static str) {
        self.data_methods.insert(name);
    }
}

// =============================================================================
// Common Handler Parameter Types
// =============================================================================

/// Common parameter type patterns that indicate taint sources.
///
/// Maps type annotation patterns to source kinds, shared across frameworks.
#[derive(Debug, Clone)]
pub struct ParameterTypeMap {
    /// Type pattern -> Source kind mappings
    pub mappings: Vec<(&'static str, SourceKind)>,
}

impl ParameterTypeMap {
    /// Create an empty map.
    #[must_use]
    pub fn new() -> Self {
        Self {
            mappings: Vec::new(),
        }
    }

    /// Add a type mapping.
    pub fn add(&mut self, pattern: &'static str, kind: SourceKind) {
        self.mappings.push((pattern, kind));
    }

    /// Look up source kind for a type annotation.
    #[must_use]
    pub fn get_kind(&self, type_annotation: &str) -> Option<(&'static str, SourceKind)> {
        for (pattern, kind) in &self.mappings {
            if type_annotation.contains(pattern) {
                return Some((pattern, *kind));
            }
        }
        None
    }

    /// Create web framework parameter type mappings.
    #[must_use]
    pub fn web_framework() -> Self {
        let mut map = Self::new();
        // Common across frameworks
        map.add("Path", SourceKind::UrlPath);
        map.add("Query", SourceKind::RequestParam);
        map.add("Body", SourceKind::RequestBody);
        map.add("Json", SourceKind::RequestBody);
        map.add("Form", SourceKind::RequestBody);
        map.add("Header", SourceKind::HttpHeader);
        map.add("Cookie", SourceKind::Cookie);
        map.add("File", SourceKind::FileUpload);
        map.add("Multipart", SourceKind::FileUpload);
        map
    }
}

impl Default for ParameterTypeMap {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Common Scan Context Fields
// =============================================================================

/// Base fields for scan context that are common across all language detectors.
///
/// Language-specific detectors can embed this struct and add their own fields.
#[derive(Debug)]
pub struct ScanContextBase<'a> {
    /// Source bytes being scanned
    pub source: &'a [u8],
    /// File name for location reporting
    pub file_name: &'a str,
    /// Current function name being scanned
    pub current_function: Option<String>,
    /// Current handler info (if in a web handler)
    pub current_handler: Option<HandlerInfo>,
    /// Whether currently inside a handler scope
    pub in_handler_scope: bool,
}

impl<'a> ScanContextBase<'a> {
    /// Create a new base context.
    #[must_use]
    pub fn new(source: &'a [u8], file_name: &'a str) -> Self {
        Self {
            source,
            file_name,
            current_function: None,
            current_handler: None,
            in_handler_scope: false,
        }
    }

    /// Set the current function.
    pub fn set_function(&mut self, name: impl Into<String>) {
        self.current_function = Some(name.into());
    }

    /// Clear the current function.
    pub fn clear_function(&mut self) {
        self.current_function = None;
    }

    /// Enter a handler scope.
    pub fn enter_handler(&mut self, handler: HandlerInfo) {
        self.current_handler = Some(handler);
        self.in_handler_scope = true;
    }

    /// Exit the handler scope.
    pub fn exit_handler(&mut self) {
        self.current_handler = None;
        self.in_handler_scope = false;
    }
}

// =============================================================================
// Import Alias Tracking
// =============================================================================

/// Common import alias tracking across languages.
///
/// Tracks aliases created by import statements like:
/// - Python: `from flask import request as req`
/// - TypeScript: `import { Request as Req } from 'express'`
/// - Rust: `use std::env as environment;`
#[derive(Debug, Clone, Default)]
pub struct ImportAliases {
    /// Alias -> Original name/path mappings
    pub aliases: FxHashMap<String, String>,
    /// Known request-like variable names
    pub request_aliases: FxHashSet<String>,
}

impl ImportAliases {
    /// Create with common request aliases.
    #[must_use]
    pub fn new() -> Self {
        let mut request_aliases = FxHashSet::default();
        request_aliases.insert("req".to_string());
        request_aliases.insert("request".to_string());
        request_aliases.insert("r".to_string());
        request_aliases.insert("ctx".to_string());
        request_aliases.insert("context".to_string());

        Self {
            aliases: FxHashMap::default(),
            request_aliases,
        }
    }

    /// Add an alias mapping.
    pub fn add_alias(&mut self, alias: impl Into<String>, original: impl Into<String>) {
        self.aliases.insert(alias.into(), original.into());
    }

    /// Add a request alias.
    pub fn add_request_alias(&mut self, alias: impl Into<String>) {
        self.request_aliases.insert(alias.into());
    }

    /// Resolve an alias to its original name.
    #[must_use]
    pub fn resolve(&self, name: &str) -> Option<&String> {
        self.aliases.get(name)
    }

    /// Check if a name is a known request alias.
    #[must_use]
    pub fn is_request_alias(&self, name: &str) -> bool {
        self.request_aliases.contains(name)
    }
}

// =============================================================================
// AST Helper Trait
// =============================================================================

/// Common AST operations used across all language detectors.
///
/// This trait provides a uniform interface for AST node manipulation,
/// reducing code duplication in language-specific implementations.
pub trait AstHelpers {
    /// Get text content from a node.
    fn node_text<'a>(&self, node: tree_sitter::Node<'a>, source: &'a [u8]) -> &'a str {
        std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }

    /// Find a child node by field name.
    fn child_by_field<'a>(
        &self,
        node: tree_sitter::Node<'a>,
        field: &str,
    ) -> Option<tree_sitter::Node<'a>> {
        node.child_by_field_name(field)
    }

    /// Find the first child with a specific kind.
    fn child_by_kind<'a>(
        &self,
        node: tree_sitter::Node<'a>,
        kind: &str,
    ) -> Option<tree_sitter::Node<'a>> {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == kind {
                return Some(child);
            }
        }
        None
    }

    /// Find all children with a specific kind.
    fn children_by_kind<'a>(
        &self,
        node: tree_sitter::Node<'a>,
        kind: &str,
    ) -> Vec<tree_sitter::Node<'a>> {
        let mut results = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == kind {
                results.push(child);
            }
        }
        results
    }

    /// Get the location (line, column) for a node.
    fn node_location(&self, node: tree_sitter::Node, file_name: &str) -> crate::security::taint::types::Location {
        crate::security::taint::types::Location::new(
            file_name,
            node.start_position().row + 1,
            node.start_position().column,
        )
    }
}

// =============================================================================
// Tainted Variable Tracking
// =============================================================================

/// Tracks variables that have been assigned tainted values.
///
/// Used for intra-procedural taint propagation during scanning.
#[derive(Debug, Clone, Default)]
pub struct TaintedVariables {
    /// Variable name -> Source kind that tainted it
    vars: FxHashMap<String, SourceKind>,
}

impl TaintedVariables {
    /// Create empty tracking.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Mark a variable as tainted with a specific kind.
    pub fn add(&mut self, name: impl Into<String>, kind: SourceKind) {
        self.vars.insert(name.into(), kind);
    }

    /// Check if a variable is tainted.
    #[must_use]
    pub fn is_tainted(&self, name: &str) -> bool {
        self.vars.contains_key(name)
    }

    /// Get the taint kind for a variable.
    #[must_use]
    pub fn get_kind(&self, name: &str) -> Option<SourceKind> {
        self.vars.get(name).copied()
    }

    /// Remove a variable from tracking.
    pub fn remove(&mut self, name: &str) {
        self.vars.remove(name);
    }

    /// Clear all tracked variables.
    pub fn clear(&mut self) {
        self.vars.clear();
    }

    /// Get all tainted variable names.
    pub fn names(&self) -> impl Iterator<Item = &String> {
        self.vars.keys()
    }
}

// =============================================================================
// Common Source Patterns
// =============================================================================

/// Pre-defined source patterns that are common across multiple languages.
pub mod patterns {
    use super::{SourceCategory, TaintSourceDef};

    /// Standard input sources (stdin, input functions).
    pub const STDIN_PATTERNS: &[TaintSourceDef] = &[
        TaintSourceDef::function("stdin", SourceCategory::Stdin, "stdin"),
        TaintSourceDef::function("input", SourceCategory::Stdin, "input"),
    ];

    /// Environment variable sources.
    pub const ENV_PATTERNS: &[TaintSourceDef] = &[
        TaintSourceDef::method("env_var", SourceCategory::Environment, "env", "var"),
        TaintSourceDef::method("getenv", SourceCategory::Environment, "os", "getenv"),
        TaintSourceDef::property("environ", SourceCategory::Environment, "os", "environ"),
    ];

    /// Process argument sources.
    pub const ARGS_PATTERNS: &[TaintSourceDef] = &[
        TaintSourceDef::property("args", SourceCategory::ProcessArgs, "sys", "argv"),
        TaintSourceDef::function("args", SourceCategory::ProcessArgs, "args"),
    ];

    /// Common deserialization method names.
    pub const DESER_METHODS: &[&str] = &[
        "from_str",
        "from_slice",
        "from_reader",
        "from_value",
        "loads",
        "load",
        "parse",
        "decode",
        "unmarshal",
        "deserialize",
    ];

    /// Common database fetch method names.
    pub const DB_FETCH_METHODS: &[&str] = &[
        "fetchone",
        "fetchall",
        "fetchmany",
        "fetch_one",
        "fetch_all",
        "fetch_optional",
        "fetch",
        "get_result",
        "get_results",
        "first",
        "load",
        "Scan",
        "QueryRow",
    ];

    /// Common file read method names.
    pub const FILE_READ_METHODS: &[&str] = &[
        "read",
        "readFile",
        "read_to_string",
        "read_to_end",
        "read_line",
        "read_lines",
        "readlines",
        "readline",
        "ReadFile",
        "ReadAll",
    ];

    /// HTTP request property names that typically contain user input.
    pub const REQUEST_PROPERTIES: &[&str] = &[
        "body",
        "params",
        "query",
        "form",
        "args",
        "json",
        "data",
        "files",
        "values",
        "GET",
        "POST",
        "FILES",
        "Body",
        "Query",
        "Param",
        "Form",
        "Json",
        "Path",
    ];

    /// HTTP header-related property names.
    pub const HEADER_PROPERTIES: &[&str] = &[
        "headers",
        "Headers",
        "header",
        "Header",
        "META",
        "cookies",
        "Cookies",
        "COOKIES",
        "cookie",
        "Cookie",
    ];
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_source_category_default_kind() {
        assert_eq!(
            SourceCategory::UserInput.default_source_kind(),
            SourceKind::RequestParam
        );
        assert_eq!(
            SourceCategory::Database.default_source_kind(),
            SourceKind::DatabaseResult
        );
        assert_eq!(
            SourceCategory::FileSystem.default_source_kind(),
            SourceKind::FileRead
        );
    }

    #[test]
    fn test_taint_source_def() {
        let def = TaintSourceDef::method("test", SourceCategory::UserInput, "request", "args")
            .with_framework("flask")
            .with_confidence(0.9);

        assert_eq!(def.name, "test");
        assert_eq!(def.object, Some("request"));
        assert_eq!(def.member, "args");
        assert_eq!(def.framework, Some("flask"));
        assert!((def.confidence - 0.9).abs() < f64::EPSILON);
    }

    #[test]
    fn test_response_method_patterns() {
        let patterns = ResponseMethodPatterns::new();

        assert!(patterns.is_response_method("response", "json"));
        assert!(patterns.is_response_method("resp", "text"));
        assert!(patterns.is_response_method("CustomResponse", "bytes"));
        assert!(!patterns.is_response_method("request", "json"));
        assert!(!patterns.is_response_method("response", "send"));
    }

    #[test]
    fn test_parameter_type_map() {
        let map = ParameterTypeMap::web_framework();

        let (pattern, kind) = map.get_kind("web::Path<String>").unwrap();
        assert_eq!(pattern, "Path");
        assert_eq!(kind, SourceKind::UrlPath);

        let (pattern, kind) = map.get_kind("Query<SearchParams>").unwrap();
        assert_eq!(pattern, "Query");
        assert_eq!(kind, SourceKind::RequestParam);

        assert!(map.get_kind("String").is_none());
    }

    #[test]
    fn test_import_aliases() {
        let mut aliases = ImportAliases::new();
        aliases.add_alias("req", "request");
        aliases.add_request_alias("ctx");

        assert_eq!(aliases.resolve("req"), Some(&"request".to_string()));
        assert!(aliases.is_request_alias("req"));
        assert!(aliases.is_request_alias("ctx"));
        assert!(!aliases.is_request_alias("unknown"));
    }

    #[test]
    fn test_tainted_variables() {
        let mut vars = TaintedVariables::new();

        vars.add("user_input", SourceKind::Stdin);
        vars.add("env_var", SourceKind::Environment);

        assert!(vars.is_tainted("user_input"));
        assert_eq!(vars.get_kind("user_input"), Some(SourceKind::Stdin));
        assert!(!vars.is_tainted("safe_var"));

        vars.remove("user_input");
        assert!(!vars.is_tainted("user_input"));
    }

    #[test]
    fn test_scan_context_base() {
        let source = b"test source";
        let mut ctx = ScanContextBase::new(source, "test.rs");

        assert!(!ctx.in_handler_scope);
        assert!(ctx.current_function.is_none());

        ctx.set_function("handler");
        assert_eq!(ctx.current_function, Some("handler".to_string()));

        ctx.clear_function();
        assert!(ctx.current_function.is_none());
    }
}
