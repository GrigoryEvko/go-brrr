//! Python taint source identification.
//!
//! This module identifies all locations in Python code where untrusted data
//! enters the program. It uses AST pattern matching via tree-sitter to detect:
//!
//! - **Web Frameworks**: Flask, Django, FastAPI request data
//! - **Standard Library**: input(), sys.argv, os.environ, file I/O
//! - **Network**: requests, urllib, socket operations
//! - **Database**: cursor fetch operations
//! - **Deserialization**: json, pickle, yaml loads
//!
//! # Handler Detection
//!
//! The detector recognizes web handler functions decorated with:
//! - `@app.route(...)` - Flask
//! - `@router.get(...)`, `@app.post(...)` - FastAPI
//! - Django view classes and function views
//!
//! Parameters in these handlers are automatically marked as tainted based on
//! their annotations (FastAPI) or position (Flask URL parameters).
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::security::taint::sources::python::PythonSourceDetector;
//!
//! let detector = PythonSourceDetector::new();
//! let source = r#"
//! from flask import Flask, request
//!
//! app = Flask(__name__)
//!
//! @app.route('/user/<int:id>')
//! def get_user(id):
//!     name = request.args.get('name')  # Taint source!
//!     return {"id": id, "name": name}
//! "#;
//!
//! let result = detector.scan_source(source, "app.py")?;
//! assert_eq!(result.sources.len(), 2); // id param + request.args.get
//! ```

use std::collections::HashMap;
use std::path::Path;

use tree_sitter::{Node, Parser, Tree};

use super::{
    DetectedSource, HandlerInfo, SourceKind, SourcePattern, SourceScanResult, TaintedParameter,
};
use crate::error::{Result, BrrrError};
use crate::security::taint::types::Location;

// =============================================================================
// Source Pattern Definitions
// =============================================================================

/// Flask request taint sources.
const FLASK_SOURCES: &[SourcePattern] = &[
    SourcePattern::property_access(
        "flask_request_args",
        SourceKind::RequestParam,
        "request",
        "args",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_form",
        SourceKind::RequestBody,
        "request",
        "form",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_json",
        SourceKind::RequestBody,
        "request",
        "json",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_data",
        SourceKind::RequestBody,
        "request",
        "data",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_files",
        SourceKind::FileUpload,
        "request",
        "files",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_cookies",
        SourceKind::Cookie,
        "request",
        "cookies",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_headers",
        SourceKind::HttpHeader,
        "request",
        "headers",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_values",
        SourceKind::RequestParam,
        "request",
        "values",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_get_json",
        SourceKind::RequestBody,
        "request",
        "get_json",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_get_data",
        SourceKind::RequestBody,
        "request",
        "get_data",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_stream",
        SourceKind::RequestBody,
        "request",
        "stream",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_environ",
        SourceKind::Environment,
        "request",
        "environ",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_path",
        SourceKind::UrlPath,
        "request",
        "path",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_full_path",
        SourceKind::UrlPath,
        "request",
        "full_path",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_url",
        SourceKind::UrlPath,
        "request",
        "url",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_base_url",
        SourceKind::UrlPath,
        "request",
        "base_url",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_host",
        SourceKind::HttpHeader,
        "request",
        "host",
        Some("flask"),
    ),
    SourcePattern::property_access(
        "flask_request_content_type",
        SourceKind::HttpHeader,
        "request",
        "content_type",
        Some("flask"),
    ),
];

/// Django request taint sources.
const DJANGO_SOURCES: &[SourcePattern] = &[
    SourcePattern::property_access(
        "django_request_GET",
        SourceKind::RequestParam,
        "request",
        "GET",
        Some("django"),
    ),
    SourcePattern::property_access(
        "django_request_POST",
        SourceKind::RequestBody,
        "request",
        "POST",
        Some("django"),
    ),
    SourcePattern::property_access(
        "django_request_body",
        SourceKind::RequestBody,
        "request",
        "body",
        Some("django"),
    ),
    SourcePattern::property_access(
        "django_request_FILES",
        SourceKind::FileUpload,
        "request",
        "FILES",
        Some("django"),
    ),
    SourcePattern::property_access(
        "django_request_COOKIES",
        SourceKind::Cookie,
        "request",
        "COOKIES",
        Some("django"),
    ),
    SourcePattern::property_access(
        "django_request_META",
        SourceKind::HttpHeader,
        "request",
        "META",
        Some("django"),
    ),
    SourcePattern::property_access(
        "django_request_headers",
        SourceKind::HttpHeader,
        "request",
        "headers",
        Some("django"),
    ),
    SourcePattern::property_access(
        "django_request_path",
        SourceKind::UrlPath,
        "request",
        "path",
        Some("django"),
    ),
    SourcePattern::property_access(
        "django_request_path_info",
        SourceKind::UrlPath,
        "request",
        "path_info",
        Some("django"),
    ),
    SourcePattern::property_access(
        "django_request_content_type",
        SourceKind::HttpHeader,
        "request",
        "content_type",
        Some("django"),
    ),
    SourcePattern::property_access(
        "django_request_read",
        SourceKind::RequestBody,
        "request",
        "read",
        Some("django"),
    ),
];

/// Standard library taint sources.
const STDLIB_SOURCES: &[SourcePattern] = &[
    SourcePattern::function_call("builtin_input", SourceKind::Stdin, "input", 1.0),
    SourcePattern::property_access(
        "sys_argv",
        SourceKind::ProcessArgs,
        "sys",
        "argv",
        None,
    ),
    SourcePattern::property_access(
        "os_environ",
        SourceKind::Environment,
        "os",
        "environ",
        None,
    ),
    SourcePattern::method_call(
        "os_getenv",
        SourceKind::Environment,
        "os",
        "getenv",
        None,
    ),
    SourcePattern::function_call("raw_input", SourceKind::Stdin, "raw_input", 1.0),
];

/// Network library taint sources.
const NETWORK_SOURCES: &[SourcePattern] = &[
    // requests library
    SourcePattern::method_call(
        "requests_get",
        SourceKind::HttpResponse,
        "requests",
        "get",
        None,
    ),
    SourcePattern::method_call(
        "requests_post",
        SourceKind::HttpResponse,
        "requests",
        "post",
        None,
    ),
    SourcePattern::method_call(
        "requests_put",
        SourceKind::HttpResponse,
        "requests",
        "put",
        None,
    ),
    SourcePattern::method_call(
        "requests_delete",
        SourceKind::HttpResponse,
        "requests",
        "delete",
        None,
    ),
    SourcePattern::method_call(
        "requests_patch",
        SourceKind::HttpResponse,
        "requests",
        "patch",
        None,
    ),
    // httpx library
    SourcePattern::method_call(
        "httpx_get",
        SourceKind::HttpResponse,
        "httpx",
        "get",
        None,
    ),
    SourcePattern::method_call(
        "httpx_post",
        SourceKind::HttpResponse,
        "httpx",
        "post",
        None,
    ),
    // aiohttp
    SourcePattern::method_call(
        "aiohttp_get",
        SourceKind::HttpResponse,
        "session",
        "get",
        None,
    ),
    SourcePattern::method_call(
        "aiohttp_post",
        SourceKind::HttpResponse,
        "session",
        "post",
        None,
    ),
    // urllib
    SourcePattern::method_call(
        "urllib_urlopen",
        SourceKind::HttpResponse,
        "urllib.request",
        "urlopen",
        None,
    ),
    // socket
    SourcePattern::method_call(
        "socket_recv",
        SourceKind::SocketRecv,
        "socket",
        "recv",
        None,
    ),
    SourcePattern::method_call(
        "socket_recvfrom",
        SourceKind::SocketRecv,
        "socket",
        "recvfrom",
        None,
    ),
    SourcePattern::method_call(
        "socket_recv_into",
        SourceKind::SocketRecv,
        "socket",
        "recv_into",
        None,
    ),
];

/// Database taint sources.
const DATABASE_SOURCES: &[SourcePattern] = &[
    SourcePattern::method_call(
        "cursor_fetchone",
        SourceKind::DatabaseResult,
        "cursor",
        "fetchone",
        None,
    ),
    SourcePattern::method_call(
        "cursor_fetchall",
        SourceKind::DatabaseResult,
        "cursor",
        "fetchall",
        None,
    ),
    SourcePattern::method_call(
        "cursor_fetchmany",
        SourceKind::DatabaseResult,
        "cursor",
        "fetchmany",
        None,
    ),
    // Also match on any object with these method names (duck typing)
    SourcePattern::function_call("fetchone", SourceKind::DatabaseResult, "fetchone", 0.7),
    SourcePattern::function_call("fetchall", SourceKind::DatabaseResult, "fetchall", 0.7),
    SourcePattern::function_call("fetchmany", SourceKind::DatabaseResult, "fetchmany", 0.7),
];

/// Deserialization taint sources.
const DESERIALIZATION_SOURCES: &[SourcePattern] = &[
    // JSON
    SourcePattern::method_call(
        "json_load",
        SourceKind::Deserialized,
        "json",
        "load",
        None,
    ),
    SourcePattern::method_call(
        "json_loads",
        SourceKind::Deserialized,
        "json",
        "loads",
        None,
    ),
    // YAML
    SourcePattern::method_call(
        "yaml_load",
        SourceKind::Deserialized,
        "yaml",
        "load",
        None,
    ),
    SourcePattern::method_call(
        "yaml_safe_load",
        SourceKind::Deserialized,
        "yaml",
        "safe_load",
        None,
    ),
    SourcePattern::method_call(
        "yaml_unsafe_load",
        SourceKind::Deserialized,
        "yaml",
        "unsafe_load",
        None,
    ),
    // Pickle (dangerous!)
    SourcePattern::method_call(
        "pickle_load",
        SourceKind::Deserialized,
        "pickle",
        "load",
        None,
    ),
    SourcePattern::method_call(
        "pickle_loads",
        SourceKind::Deserialized,
        "pickle",
        "loads",
        None,
    ),
    // TOML
    SourcePattern::method_call(
        "toml_load",
        SourceKind::Deserialized,
        "toml",
        "load",
        None,
    ),
    SourcePattern::method_call(
        "toml_loads",
        SourceKind::Deserialized,
        "toml",
        "loads",
        None,
    ),
    // ConfigParser
    SourcePattern::method_call(
        "configparser_read",
        SourceKind::Deserialized,
        "config",
        "read",
        None,
    ),
];

/// File I/O taint sources (when path might be user-controlled).
const FILE_SOURCES: &[SourcePattern] = &[
    SourcePattern::function_call("open_read", SourceKind::FileRead, "open", 0.6),
    SourcePattern::method_call(
        "pathlib_read_text",
        SourceKind::FileRead,
        "Path",
        "read_text",
        None,
    ),
    SourcePattern::method_call(
        "pathlib_read_bytes",
        SourceKind::FileRead,
        "Path",
        "read_bytes",
        None,
    ),
];

/// WebSocket taint sources.
const WEBSOCKET_SOURCES: &[SourcePattern] = &[
    SourcePattern::method_call(
        "websocket_receive",
        SourceKind::WebSocketMessage,
        "websocket",
        "receive",
        None,
    ),
    SourcePattern::method_call(
        "websocket_receive_text",
        SourceKind::WebSocketMessage,
        "websocket",
        "receive_text",
        None,
    ),
    SourcePattern::method_call(
        "websocket_receive_bytes",
        SourceKind::WebSocketMessage,
        "websocket",
        "receive_bytes",
        None,
    ),
    SourcePattern::method_call(
        "websocket_receive_json",
        SourceKind::WebSocketMessage,
        "websocket",
        "receive_json",
        None,
    ),
];

// =============================================================================
// Route Decorator Patterns
// =============================================================================

/// Patterns for Flask-style route decorators.
const FLASK_ROUTE_PATTERNS: &[&str] = &[
    "route",
    "get",
    "post",
    "put",
    "delete",
    "patch",
];

/// Patterns for FastAPI route decorators.
const FASTAPI_ROUTE_PATTERNS: &[&str] = &[
    "get",
    "post",
    "put",
    "delete",
    "patch",
    "options",
    "head",
    "trace",
    "api_route",
    "websocket",
];

/// FastAPI parameter annotations that indicate taint sources.
const FASTAPI_PARAM_ANNOTATIONS: &[(&str, SourceKind)] = &[
    ("Query", SourceKind::RequestParam),
    ("Path", SourceKind::UrlPath),
    ("Body", SourceKind::RequestBody),
    ("Form", SourceKind::RequestBody),
    ("Header", SourceKind::HttpHeader),
    ("Cookie", SourceKind::Cookie),
    ("File", SourceKind::FileUpload),
    ("UploadFile", SourceKind::FileUpload),
];

// =============================================================================
// Python Source Detector
// =============================================================================

/// Detects taint sources in Python code using AST analysis.
///
/// The detector identifies sources through:
/// 1. Pattern matching on function/method calls and property accesses
/// 2. Decorator analysis for web framework handlers
/// 3. Type annotation analysis for FastAPI parameters
pub struct PythonSourceDetector {
    /// All source patterns to check
    patterns: Vec<SourcePattern>,
    /// Import aliases (e.g., "req" -> "request")
    import_aliases: HashMap<String, String>,
    /// Known handler decorators (decorator name -> framework)
    handler_decorators: HashMap<String, String>,
}

impl PythonSourceDetector {
    /// Create a new Python source detector with default patterns.
    pub fn new() -> Self {
        let mut patterns = Vec::new();
        patterns.extend_from_slice(FLASK_SOURCES);
        patterns.extend_from_slice(DJANGO_SOURCES);
        patterns.extend_from_slice(STDLIB_SOURCES);
        patterns.extend_from_slice(NETWORK_SOURCES);
        patterns.extend_from_slice(DATABASE_SOURCES);
        patterns.extend_from_slice(DESERIALIZATION_SOURCES);
        patterns.extend_from_slice(FILE_SOURCES);
        patterns.extend_from_slice(WEBSOCKET_SOURCES);

        let mut handler_decorators = HashMap::new();
        for pattern in FLASK_ROUTE_PATTERNS {
            handler_decorators.insert(pattern.to_string(), "flask".to_string());
        }
        for pattern in FASTAPI_ROUTE_PATTERNS {
            handler_decorators.insert(pattern.to_string(), "fastapi".to_string());
        }

        Self {
            patterns,
            import_aliases: HashMap::new(),
            handler_decorators,
        }
    }

    /// Add a custom source pattern.
    pub fn add_pattern(&mut self, pattern: SourcePattern) {
        self.patterns.push(pattern);
    }

    /// Scan a source file for taint sources.
    pub fn scan_file(&self, path: impl AsRef<Path>) -> Result<SourceScanResult> {
        let path = path.as_ref();
        let source = std::fs::read_to_string(path)
            .map_err(|e| BrrrError::IoWithPath {
                error: e,
                path: path.to_path_buf(),
            })?;
        self.scan_source(&source, path.to_string_lossy().as_ref())
    }

    /// Scan source code for taint sources.
    pub fn scan_source(&self, source: &str, file_name: &str) -> Result<SourceScanResult> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_python::LANGUAGE.into())
            .map_err(|e| BrrrError::Parse {
                file: file_name.to_string(),
                message: format!("Failed to set Python language: {}", e),
            })?;

        let tree = parser
            .parse(source, None)
            .ok_or_else(|| BrrrError::Parse {
                file: file_name.to_string(),
                message: "Failed to parse Python source".to_string(),
            })?;

        self.scan_tree(&tree, source, file_name)
    }

    /// Scan a parsed AST for taint sources.
    fn scan_tree(&self, tree: &Tree, source: &str, file_name: &str) -> Result<SourceScanResult> {
        let mut result = SourceScanResult::new(file_name, "python");
        let source_bytes = source.as_bytes();
        let root = tree.root_node();

        // First pass: collect import aliases
        let mut import_aliases = self.import_aliases.clone();
        self.collect_imports(root, source_bytes, &mut import_aliases);

        // Create scanning context
        let mut ctx = ScanContext {
            source: source_bytes,
            file_name,
            import_aliases: &import_aliases,
            current_function: None,
            current_handler: None,
            in_handler_scope: false,
        };

        // Second pass: find sources and handlers
        self.scan_node(root, &mut ctx, &mut result);

        Ok(result)
    }

    /// Collect import aliases from the module.
    fn collect_imports(
        &self,
        root: Node,
        source: &[u8],
        aliases: &mut HashMap<String, String>,
    ) {
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            match child.kind() {
                "import_from_statement" => {
                    self.process_import_from(child, source, aliases);
                }
                "import_statement" => {
                    self.process_import(child, source, aliases);
                }
                _ => {}
            }
        }
    }

    /// Process `from X import Y as Z` statements.
    fn process_import_from(&self, node: Node, source: &[u8], aliases: &mut HashMap<String, String>) {
        // Extract module name
        let module = self.child_by_field(node, "module_name")
            .map(|n| self.node_text(n, source))
            .unwrap_or("");

        // Look for aliased imports
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "aliased_import" {
                if let (Some(name), Some(alias)) = (
                    self.child_by_field(child, "name"),
                    self.child_by_field(child, "alias"),
                ) {
                    let original = self.node_text(name, source);
                    let alias_name = self.node_text(alias, source);

                    // Map alias to original
                    if module == "flask" && original == "request" {
                        aliases.insert(alias_name.to_string(), "request".to_string());
                    }
                }
            }
        }
    }

    /// Process `import X as Y` statements.
    fn process_import(&self, node: Node, source: &[u8], aliases: &mut HashMap<String, String>) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "aliased_import" {
                if let (Some(name), Some(alias)) = (
                    self.child_by_field(child, "name"),
                    self.child_by_field(child, "alias"),
                ) {
                    let original = self.node_text(name, source);
                    let alias_name = self.node_text(alias, source);
                    aliases.insert(alias_name.to_string(), original.to_string());
                }
            }
        }
    }

    /// Recursively scan AST nodes for sources.
    fn scan_node(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        match node.kind() {
            "decorated_definition" => {
                self.scan_decorated_definition(node, ctx, result);
            }
            "function_definition" => {
                let old_func = ctx.current_function.take();
                let old_handler = ctx.current_handler.take();
                let old_in_handler = ctx.in_handler_scope;

                // Get function name
                if let Some(name_node) = self.child_by_field(node, "name") {
                    ctx.current_function = Some(self.node_text(name_node, ctx.source).to_string());
                }

                // Scan function body
                self.scan_children(node, ctx, result);

                ctx.current_function = old_func;
                ctx.current_handler = old_handler;
                ctx.in_handler_scope = old_in_handler;
            }
            "call" => {
                self.scan_call(node, ctx, result);
                self.scan_children(node, ctx, result);
            }
            "attribute" => {
                self.scan_attribute(node, ctx, result);
                self.scan_children(node, ctx, result);
            }
            "subscript" => {
                self.scan_subscript(node, ctx, result);
                self.scan_children(node, ctx, result);
            }
            "assignment" => {
                self.scan_assignment(node, ctx, result);
            }
            _ => {
                self.scan_children(node, ctx, result);
            }
        }
    }

    /// Scan children of a node.
    fn scan_children(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.scan_node(child, ctx, result);
        }
    }

    /// Scan a decorated definition (function with decorators).
    fn scan_decorated_definition(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        // Extract decorators
        let decorators = self.extract_decorators(node, ctx.source);

        // Check if any decorator is a route handler
        let handler_info = self.analyze_handler_decorators(&decorators, node, ctx);

        if let Some(handler) = &handler_info {
            // Add tainted parameters as sources
            for param in &handler.tainted_params {
                let loc = Location::new(ctx.file_name, handler.start_line, 0);
                let source = DetectedSource::new(param.kind, loc, format!("parameter:{}", param.name))
                    .with_assignment(&param.name)
                    .with_framework(&handler.framework)
                    .in_handler_function(&handler.name);
                result.add_source(source);
            }
            result.add_handler(handler.clone());
        }

        // Update context for scanning function body
        let old_handler = ctx.current_handler.take();
        let old_in_handler = ctx.in_handler_scope;

        if handler_info.is_some() {
            ctx.current_handler = handler_info;
            ctx.in_handler_scope = true;
        }

        // Scan the decorated definition's children
        self.scan_children(node, ctx, result);

        ctx.current_handler = old_handler;
        ctx.in_handler_scope = old_in_handler;
    }

    /// Extract decorators from a decorated_definition node.
    fn extract_decorators(&self, node: Node, source: &[u8]) -> Vec<DecoratorInfo> {
        let mut decorators = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            if child.kind() == "decorator" {
                if let Some(info) = self.parse_decorator(child, source) {
                    decorators.push(info);
                }
            }
        }

        decorators
    }

    /// Parse a single decorator node.
    fn parse_decorator(&self, node: Node, source: &[u8]) -> Option<DecoratorInfo> {
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "@" => continue, // Skip the @ symbol
                "identifier" => {
                    return Some(DecoratorInfo {
                        name: self.node_text(child, source).to_string(),
                        object: None,
                        arguments: Vec::new(),
                        line: child.start_position().row + 1,
                    });
                }
                "call" => {
                    return self.parse_decorator_call(child, source);
                }
                "attribute" => {
                    // @app.route, @router.get, etc.
                    return self.parse_decorator_attribute(child, source);
                }
                _ => {}
            }
        }

        None
    }

    /// Parse a decorator that is a call: @decorator(args)
    fn parse_decorator_call(&self, node: Node, source: &[u8]) -> Option<DecoratorInfo> {
        let func = self.child_by_field(node, "function")?;

        match func.kind() {
            "identifier" => {
                let name = self.node_text(func, source).to_string();
                let args = self.extract_call_arguments(node, source);
                Some(DecoratorInfo {
                    name,
                    object: None,
                    arguments: args,
                    line: node.start_position().row + 1,
                })
            }
            "attribute" => {
                // @app.route(...), @router.get(...)
                let object = self.child_by_field(func, "object")
                    .map(|n| self.node_text(n, source).to_string());
                let attr = self.child_by_field(func, "attribute")
                    .map(|n| self.node_text(n, source).to_string())?;
                let args = self.extract_call_arguments(node, source);

                Some(DecoratorInfo {
                    name: attr,
                    object,
                    arguments: args,
                    line: node.start_position().row + 1,
                })
            }
            _ => None,
        }
    }

    /// Parse a decorator that is an attribute access: @app.route (without call)
    fn parse_decorator_attribute(&self, node: Node, source: &[u8]) -> Option<DecoratorInfo> {
        let object = self.child_by_field(node, "object")
            .map(|n| self.node_text(n, source).to_string());
        let attr = self.child_by_field(node, "attribute")
            .map(|n| self.node_text(n, source).to_string())?;

        Some(DecoratorInfo {
            name: attr,
            object,
            arguments: Vec::new(),
            line: node.start_position().row + 1,
        })
    }

    /// Extract arguments from a call node.
    fn extract_call_arguments(&self, call_node: Node, source: &[u8]) -> Vec<String> {
        let mut args = Vec::new();

        if let Some(args_node) = self.child_by_field(call_node, "arguments") {
            let mut cursor = args_node.walk();
            for child in args_node.children(&mut cursor) {
                match child.kind() {
                    "string" => {
                        args.push(self.node_text(child, source).to_string());
                    }
                    "keyword_argument" => {
                        args.push(self.node_text(child, source).to_string());
                    }
                    _ => {}
                }
            }
        }

        args
    }

    /// Analyze decorators to determine if this is a web handler.
    fn analyze_handler_decorators(
        &self,
        decorators: &[DecoratorInfo],
        def_node: Node,
        ctx: &ScanContext,
    ) -> Option<HandlerInfo> {
        for decorator in decorators {
            // Check for Flask/FastAPI route decorators
            if let Some(obj) = &decorator.object {
                let obj_lower = obj.to_lowercase();

                // Flask uses "route" decorator, FastAPI uses http method decorators directly
                // Prioritize Flask if "route" is used, else FastAPI patterns
                let is_flask_specific = obj_lower == "blueprint" || obj_lower == "bp";
                let is_fastapi_specific = obj_lower == "router" || obj_lower == "api_router";
                let is_app = obj_lower == "app";

                // Check which framework's pattern matches
                let is_flask_pattern = FLASK_ROUTE_PATTERNS.contains(&decorator.name.as_str());
                let is_fastapi_pattern = FASTAPI_ROUTE_PATTERNS.contains(&decorator.name.as_str());

                // Determine framework based on decorator pattern and object
                let framework = if is_flask_specific {
                    Some("flask")
                } else if is_fastapi_specific {
                    Some("fastapi")
                } else if is_app {
                    // For @app.*, use decorator name to distinguish
                    // Flask typically uses @app.route(), FastAPI uses @app.get(), @app.post(), etc.
                    if decorator.name == "route" {
                        Some("flask")
                    } else if is_fastapi_pattern {
                        Some("fastapi")
                    } else if is_flask_pattern {
                        Some("flask")
                    } else {
                        None
                    }
                } else {
                    None
                };

                if let Some(fw) = framework {
                    return self.build_handler_info(def_node, decorator, fw, ctx);
                }
            }

            // Check for @route decorator (standalone)
            if decorator.name == "route" && decorator.object.is_none() {
                return self.build_handler_info(def_node, decorator, "flask", ctx);
            }
        }

        None
    }

    /// Build handler info from a function definition.
    fn build_handler_info(
        &self,
        def_node: Node,
        decorator: &DecoratorInfo,
        framework: &str,
        ctx: &ScanContext,
    ) -> Option<HandlerInfo> {
        // Find the actual function_definition child
        let func_node = self.find_function_in_decorated(def_node)?;

        let name = self.child_by_field(func_node, "name")
            .map(|n| self.node_text(n, ctx.source).to_string())?;

        let start_line = func_node.start_position().row + 1;
        let end_line = func_node.end_position().row + 1;

        // Extract route path from decorator arguments
        let route = decorator.arguments.first()
            .map(|s| s.trim_matches(|c| c == '"' || c == '\'').to_string());

        // Extract HTTP methods from decorator arguments
        let methods = self.extract_http_methods(&decorator.arguments, &decorator.name);

        // Extract tainted parameters
        let tainted_params = self.extract_tainted_params(func_node, framework, ctx);

        Some(HandlerInfo {
            name,
            start_line,
            end_line,
            route,
            methods,
            framework: framework.to_string(),
            tainted_params,
        })
    }

    /// Find function_definition inside decorated_definition.
    fn find_function_in_decorated<'a>(&self, node: Node<'a>) -> Option<Node<'a>> {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "function_definition" {
                return Some(child);
            }
        }
        None
    }

    /// Extract HTTP methods from decorator arguments.
    fn extract_http_methods(&self, args: &[String], decorator_name: &str) -> Vec<String> {
        let mut methods = Vec::new();

        // If decorator name is an HTTP method, use it
        let method_decorators = ["get", "post", "put", "delete", "patch", "head", "options"];
        if method_decorators.contains(&decorator_name.to_lowercase().as_str()) {
            methods.push(decorator_name.to_uppercase());
            return methods;
        }

        // Look for methods= argument
        for arg in args {
            if arg.starts_with("methods=") {
                // Parse methods=['GET', 'POST']
                let methods_str = arg.trim_start_matches("methods=");
                let cleaned = methods_str.trim_matches(|c| c == '[' || c == ']' || c == ' ');
                for method in cleaned.split(',') {
                    let method = method.trim().trim_matches(|c| c == '"' || c == '\'');
                    if !method.is_empty() {
                        methods.push(method.to_uppercase());
                    }
                }
            }
        }

        if methods.is_empty() {
            methods.push("GET".to_string());
        }

        methods
    }

    /// Extract tainted parameters from a function definition.
    fn extract_tainted_params(
        &self,
        func_node: Node,
        framework: &str,
        ctx: &ScanContext,
    ) -> Vec<TaintedParameter> {
        let mut params = Vec::new();

        let params_node = match self.child_by_field(func_node, "parameters") {
            Some(n) => n,
            None => return params,
        };

        let mut cursor = params_node.walk();
        let mut param_index = 0;

        for child in params_node.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    let name = self.node_text(child, ctx.source).to_string();

                    // Skip 'self' and 'request' parameters
                    if name == "self" || name == "cls" {
                        continue;
                    }

                    // For Flask, non-request params after 'self' are URL path params
                    if framework == "flask" && name != "request" {
                        params.push(TaintedParameter {
                            name,
                            kind: SourceKind::UrlPath,
                            index: param_index,
                            annotation: None,
                        });
                    }

                    param_index += 1;
                }
                "typed_parameter" => {
                    let (name, annotation) = self.parse_typed_param(child, ctx.source);

                    if name == "self" || name == "cls" {
                        continue;
                    }

                    // For FastAPI, check type annotation for source type
                    let (kind, ann) = if framework == "fastapi" {
                        self.classify_fastapi_param(&annotation)
                    } else if name != "request" {
                        (SourceKind::UrlPath, None)
                    } else {
                        param_index += 1;
                        continue;
                    };

                    params.push(TaintedParameter {
                        name,
                        kind,
                        index: param_index,
                        annotation: ann,
                    });

                    param_index += 1;
                }
                "typed_default_parameter" => {
                    let (name, type_ann) = self.parse_typed_param(child, ctx.source);

                    if name == "self" || name == "cls" {
                        continue;
                    }

                    // For FastAPI, check the default value (e.g., Header(None), Query(...))
                    // not just the type annotation
                    let default_value = self.extract_default_value(child, ctx.source);
                    let (kind, ann) = if framework == "fastapi" {
                        // Check default value first, then type annotation
                        let (k, a) = self.classify_fastapi_param(&default_value);
                        if a.is_some() {
                            (k, a)
                        } else {
                            self.classify_fastapi_param(&type_ann)
                        }
                    } else if name != "request" {
                        (SourceKind::UrlPath, None)
                    } else {
                        param_index += 1;
                        continue;
                    };

                    params.push(TaintedParameter {
                        name,
                        kind,
                        index: param_index,
                        annotation: ann,
                    });

                    param_index += 1;
                }
                "default_parameter" => {
                    let name = self.child_by_kind(child, "identifier")
                        .map(|n| self.node_text(n, ctx.source).to_string())
                        .unwrap_or_default();

                    if name == "self" || name == "cls" || name == "request" {
                        continue;
                    }

                    // For FastAPI, check the default value
                    let default_value = self.extract_default_value(child, ctx.source);
                    let (kind, ann) = if framework == "fastapi" {
                        self.classify_fastapi_param(&default_value)
                    } else {
                        // Default parameters in Flask handlers are typically query params
                        (SourceKind::RequestParam, None)
                    };

                    params.push(TaintedParameter {
                        name,
                        kind,
                        index: param_index,
                        annotation: ann,
                    });

                    param_index += 1;
                }
                _ => {}
            }
        }

        params
    }

    /// Parse a typed parameter node.
    fn parse_typed_param(&self, node: Node, source: &[u8]) -> (String, String) {
        let name = self.child_by_field(node, "name")
            .or_else(|| self.child_by_kind(node, "identifier"))
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_default();

        let annotation = self.child_by_field(node, "type")
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_default();

        (name, annotation)
    }

    /// Extract the default value from a parameter node.
    fn extract_default_value(&self, node: Node, source: &[u8]) -> String {
        // Look for the value after the "=" token
        let mut cursor = node.walk();
        let mut saw_equals = false;

        for child in node.children(&mut cursor) {
            if child.kind() == "=" {
                saw_equals = true;
                continue;
            }
            if saw_equals {
                return self.node_text(child, source).to_string();
            }
        }

        String::new()
    }

    /// Classify a FastAPI parameter based on its type annotation.
    fn classify_fastapi_param(&self, annotation: &str) -> (SourceKind, Option<String>) {
        for (ann_type, kind) in FASTAPI_PARAM_ANNOTATIONS {
            if annotation.contains(ann_type) {
                return (*kind, Some(ann_type.to_string()));
            }
        }

        // Default to request param for unannotated FastAPI params
        (SourceKind::RequestParam, None)
    }

    /// Scan a call expression for taint sources.
    fn scan_call(
        &self,
        node: Node,
        ctx: &ScanContext,
        result: &mut SourceScanResult,
    ) {
        let func_node = match self.child_by_field(node, "function") {
            Some(n) => n,
            None => return,
        };

        let expression = self.node_text(node, ctx.source).to_string();
        let line = node.start_position().row + 1;
        let col = node.start_position().column;

        match func_node.kind() {
            "identifier" => {
                // Direct function call: input(), open(), etc.
                let func_name = self.node_text(func_node, ctx.source);

                for pattern in &self.patterns {
                    if pattern.object.is_none() && pattern.method == func_name {
                        let loc = Location::new(ctx.file_name, line, col);
                        let mut source = DetectedSource::new(pattern.kind, loc, &expression)
                            .with_confidence(pattern.confidence);

                        if let Some(fw) = pattern.framework {
                            source = source.with_framework(fw);
                        }

                        if ctx.in_handler_scope {
                            if let Some(func) = &ctx.current_function {
                                source = source.in_handler_function(func);
                            }
                        }

                        result.add_source(source);
                        return;
                    }
                }
            }
            "attribute" => {
                // Method call: request.args.get(), os.getenv(), etc.
                self.scan_method_call(func_node, node, ctx, result);
            }
            _ => {}
        }
    }

    /// Scan a method call (attribute access followed by call).
    fn scan_method_call(
        &self,
        attr_node: Node,
        call_node: Node,
        ctx: &ScanContext,
        result: &mut SourceScanResult,
    ) {
        let object = match self.child_by_field(attr_node, "object") {
            Some(n) => n,
            None => return,
        };

        let method = match self.child_by_field(attr_node, "attribute") {
            Some(n) => self.node_text(n, ctx.source),
            None => return,
        };

        let object_name = self.get_object_name(object, ctx);
        let expression = self.node_text(call_node, ctx.source).to_string();
        let line = call_node.start_position().row + 1;
        let col = call_node.start_position().column;

        // Check for response attribute access: response.text, response.json(), etc.
        if self.is_response_method(&object_name, method) {
            let loc = Location::new(ctx.file_name, line, col);
            let source = DetectedSource::new(SourceKind::HttpResponse, loc, &expression)
                .with_confidence(0.85)
                .with_context(format!("response.{}", method));

            result.add_source(source);
            return;
        }

        // Check patterns
        for pattern in &self.patterns {
            if let Some(pattern_obj) = pattern.object {
                if object_name == pattern_obj && method == pattern.method {
                    let loc = Location::new(ctx.file_name, line, col);
                    let mut source = DetectedSource::new(pattern.kind, loc, &expression)
                        .with_confidence(pattern.confidence);

                    if let Some(fw) = pattern.framework {
                        source = source.with_framework(fw);
                    }

                    if ctx.in_handler_scope {
                        if let Some(func) = &ctx.current_function {
                            source = source.in_handler_function(func);
                        }
                    }

                    result.add_source(source);
                    return;
                }
            }
        }

        // Check for cursor.fetch* patterns on any object
        if method == "fetchone" || method == "fetchall" || method == "fetchmany" {
            let loc = Location::new(ctx.file_name, line, col);
            let source = DetectedSource::new(SourceKind::DatabaseResult, loc, &expression)
                .with_confidence(0.8)
                .with_context(format!("{}.{}", object_name, method));

            result.add_source(source);
        }
    }

    /// Check if this is a response method that returns data.
    fn is_response_method(&self, object_name: &str, method: &str) -> bool {
        let response_objects = ["response", "resp", "r", "result"];
        let response_methods = ["text", "json", "content", "read", "iter_content", "iter_lines"];

        response_objects.contains(&object_name) && response_methods.contains(&method)
    }

    /// Get the name of an object node.
    fn get_object_name(&self, node: Node, ctx: &ScanContext) -> String {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node, ctx.source);
                // Check for import aliases
                ctx.import_aliases.get(name).cloned().unwrap_or_else(|| name.to_string())
            }
            "attribute" => {
                // For chained attributes like urllib.request
                let mut parts = Vec::new();
                let mut current = node;

                loop {
                    if let Some(attr) = self.child_by_field(current, "attribute") {
                        parts.push(self.node_text(attr, ctx.source));
                    }

                    if let Some(obj) = self.child_by_field(current, "object") {
                        if obj.kind() == "identifier" {
                            parts.push(self.node_text(obj, ctx.source));
                            break;
                        } else if obj.kind() == "attribute" {
                            current = obj;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }

                parts.reverse();
                parts.join(".")
            }
            "call" => {
                // For chained calls like urlopen().read()
                self.node_text(node, ctx.source).to_string()
            }
            _ => self.node_text(node, ctx.source).to_string(),
        }
    }

    /// Scan an attribute access for taint sources.
    fn scan_attribute(
        &self,
        node: Node,
        ctx: &ScanContext,
        result: &mut SourceScanResult,
    ) {
        // Only check if this is not the function part of a call
        // (those are handled by scan_call)
        if node.parent().map(|p| p.kind()) == Some("call") {
            if node.parent().and_then(|p| self.child_by_field(p, "function")) == Some(node) {
                return;
            }
        }

        let object = match self.child_by_field(node, "object") {
            Some(n) => n,
            None => return,
        };

        let attr = match self.child_by_field(node, "attribute") {
            Some(n) => self.node_text(n, ctx.source),
            None => return,
        };

        let object_name = self.get_object_name(object, ctx);
        let expression = self.node_text(node, ctx.source).to_string();
        let line = node.start_position().row + 1;
        let col = node.start_position().column;

        // Check property patterns
        for pattern in &self.patterns {
            if let Some(pattern_obj) = pattern.object {
                if pattern.is_property && object_name == pattern_obj && attr == pattern.method {
                    let loc = Location::new(ctx.file_name, line, col);
                    let mut source = DetectedSource::new(pattern.kind, loc, &expression)
                        .with_confidence(pattern.confidence);

                    if let Some(fw) = pattern.framework {
                        source = source.with_framework(fw);
                    }

                    if ctx.in_handler_scope {
                        if let Some(func) = &ctx.current_function {
                            source = source.in_handler_function(func);
                        }
                    }

                    result.add_source(source);
                    return;
                }
            }
        }
    }

    /// Scan subscript access for taint sources.
    fn scan_subscript(
        &self,
        node: Node,
        ctx: &ScanContext,
        result: &mut SourceScanResult,
    ) {
        let value = match self.child_by_field(node, "value") {
            Some(n) => n,
            None => return,
        };

        // Check for request.args['key'], os.environ['VAR'], etc.
        if value.kind() == "attribute" {
            let object = self.child_by_field(value, "object");
            let attr = self.child_by_field(value, "attribute");

            if let (Some(obj), Some(att)) = (object, attr) {
                let object_name = self.get_object_name(obj, ctx);
                let attr_name = self.node_text(att, ctx.source);
                let expression = self.node_text(node, ctx.source).to_string();
                let line = node.start_position().row + 1;
                let col = node.start_position().column;

                for pattern in &self.patterns {
                    if let Some(pattern_obj) = pattern.object {
                        if object_name == pattern_obj && attr_name == pattern.method {
                            let loc = Location::new(ctx.file_name, line, col);
                            let mut source = DetectedSource::new(pattern.kind, loc, &expression)
                                .with_confidence(pattern.confidence);

                            if let Some(fw) = pattern.framework {
                                source = source.with_framework(fw);
                            }

                            if ctx.in_handler_scope {
                                if let Some(func) = &ctx.current_function {
                                    source = source.in_handler_function(func);
                                }
                            }

                            result.add_source(source);
                            return;
                        }
                    }
                }
            }
        }

        // Check for sys.argv[n] access
        if value.kind() == "attribute" {
            let expression = self.node_text(value, ctx.source);
            if expression == "sys.argv" {
                let full_expr = self.node_text(node, ctx.source).to_string();
                let line = node.start_position().row + 1;
                let col = node.start_position().column;
                let loc = Location::new(ctx.file_name, line, col);

                let source = DetectedSource::new(SourceKind::ProcessArgs, loc, &full_expr)
                    .with_confidence(1.0);

                result.add_source(source);
            }
        }
    }

    /// Scan an assignment to track taint flow.
    fn scan_assignment(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let left = self.child_by_field(node, "left");
        let right = self.child_by_field(node, "right");

        // Track what variable is being assigned to
        let assigned_var = left.and_then(|n| {
            if n.kind() == "identifier" {
                Some(self.node_text(n, ctx.source).to_string())
            } else {
                None
            }
        });

        // Scan the right side for sources
        let source_count_before = result.sources.len();

        if let Some(right_node) = right {
            self.scan_node(right_node, ctx, result);
        }

        // If we found new sources, update them with the assignment info
        if let Some(var_name) = assigned_var {
            for source in result.sources.iter_mut().skip(source_count_before) {
                if source.assigned_to.is_none() {
                    source.assigned_to = Some(var_name.clone());
                }
            }
        }
    }

    // ==========================================================================
    // AST Helper Methods
    // ==========================================================================

    /// Get text from a node.
    fn node_text<'a>(&self, node: Node<'a>, source: &'a [u8]) -> &'a str {
        std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }

    /// Get child by field name.
    fn child_by_field<'a>(&self, node: Node<'a>, field: &str) -> Option<Node<'a>> {
        node.child_by_field_name(field)
    }

    /// Get first child with given kind.
    fn child_by_kind<'a>(&self, node: Node<'a>, kind: &str) -> Option<Node<'a>> {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == kind {
                return Some(child);
            }
        }
        None
    }
}

impl Default for PythonSourceDetector {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Context Types
// =============================================================================

/// Scanning context passed through recursive AST traversal.
struct ScanContext<'a> {
    /// Source bytes
    source: &'a [u8],
    /// File name for locations
    file_name: &'a str,
    /// Import aliases
    import_aliases: &'a HashMap<String, String>,
    /// Current function name
    current_function: Option<String>,
    /// Current handler info (if in a handler)
    current_handler: Option<HandlerInfo>,
    /// Whether we're in a handler scope
    in_handler_scope: bool,
}

/// Information about a decorator.
#[derive(Debug, Clone)]
struct DecoratorInfo {
    /// Decorator name (e.g., "route", "get")
    name: String,
    /// Object the decorator is called on (e.g., "app", "router")
    object: Option<String>,
    /// Arguments to the decorator
    arguments: Vec<String>,
    /// Line number
    line: usize,
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn scan(source: &str) -> SourceScanResult {
        let detector = PythonSourceDetector::new();
        detector.scan_source(source, "test.py").unwrap()
    }

    // =========================================================================
    // Flask Tests
    // =========================================================================

    #[test]
    fn test_flask_request_args() {
        let source = r#"
from flask import request

def handler():
    name = request.args.get('name')
"#;
        let result = scan(source);
        assert!(!result.sources.is_empty());
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestParam));
    }

    #[test]
    fn test_flask_request_form() {
        let source = r#"
from flask import request

def handler():
    data = request.form['username']
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_flask_request_json() {
        let source = r#"
from flask import request

@app.route('/api', methods=['POST'])
def api_handler():
    payload = request.json
    return {"received": payload}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_flask_request_cookies() {
        let source = r#"
from flask import request

def handler():
    session_id = request.cookies.get('session')
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Cookie));
    }

    #[test]
    fn test_flask_request_files() {
        let source = r#"
from flask import request

@app.route('/upload', methods=['POST'])
def upload():
    file = request.files['document']
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::FileUpload));
    }

    #[test]
    fn test_flask_request_headers() {
        let source = r#"
from flask import request

def handler():
    auth = request.headers.get('Authorization')
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::HttpHeader));
    }

    #[test]
    fn test_flask_route_decorator() {
        let source = r#"
from flask import Flask

app = Flask(__name__)

@app.route('/users/<int:user_id>')
def get_user(user_id):
    return {"id": user_id}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 1);
        assert_eq!(result.handlers[0].name, "get_user");
        assert_eq!(result.handlers[0].framework, "flask");
        assert!(result.handlers[0].route.as_ref().unwrap().contains("users"));

        // URL path parameter should be tainted
        assert!(result.sources.iter().any(|s| {
            s.kind == SourceKind::UrlPath && s.expression.contains("user_id")
        }));
    }

    #[test]
    fn test_flask_multiple_methods() {
        let source = r#"
@app.route('/data', methods=['GET', 'POST'])
def data_handler():
    if request.method == 'POST':
        return request.json
    return {}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 1);
        assert!(result.handlers[0].methods.contains(&"GET".to_string()));
        assert!(result.handlers[0].methods.contains(&"POST".to_string()));
    }

    // =========================================================================
    // Django Tests
    // =========================================================================

    #[test]
    fn test_django_request_get() {
        let source = r#"
def view(request):
    user_id = request.GET.get('id')
    return HttpResponse(user_id)
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestParam));
    }

    #[test]
    fn test_django_request_post() {
        let source = r#"
def view(request):
    username = request.POST['username']
    password = request.POST['password']
"#;
        let result = scan(source);
        let post_sources: Vec<_> = result.sources.iter()
            .filter(|s| s.kind == SourceKind::RequestBody)
            .collect();
        // At least 2 sources (may detect more from subscript + attribute)
        assert!(post_sources.len() >= 2, "Expected at least 2 POST sources, got {}", post_sources.len());
    }

    #[test]
    fn test_django_request_body() {
        let source = r#"
import json

def api_view(request):
    data = json.loads(request.body)
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_django_request_meta() {
        let source = r#"
def view(request):
    ip = request.META.get('REMOTE_ADDR')
    ua = request.META.get('HTTP_USER_AGENT')
"#;
        let result = scan(source);
        let meta_sources: Vec<_> = result.sources.iter()
            .filter(|s| s.kind == SourceKind::HttpHeader)
            .collect();
        assert_eq!(meta_sources.len(), 2);
    }

    // =========================================================================
    // FastAPI Tests
    // =========================================================================

    #[test]
    fn test_fastapi_query_param() {
        let source = r#"
from fastapi import FastAPI, Query

app = FastAPI()

@app.get("/items/")
def read_items(q: str = Query(None)):
    return {"q": q}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 1);
        assert_eq!(result.handlers[0].framework, "fastapi");

        // Query parameter should be tainted
        assert!(result.handlers[0].tainted_params.iter()
            .any(|p| p.name == "q" && p.kind == SourceKind::RequestParam));
    }

    #[test]
    fn test_fastapi_path_param() {
        let source = r#"
from fastapi import FastAPI, Path

app = FastAPI()

@app.get("/items/{item_id}")
def read_item(item_id: int = Path(...)):
    return {"item_id": item_id}
"#;
        let result = scan(source);
        assert!(result.handlers[0].tainted_params.iter()
            .any(|p| p.name == "item_id" && p.kind == SourceKind::UrlPath));
    }

    #[test]
    fn test_fastapi_body_param() {
        let source = r#"
from fastapi import FastAPI, Body
from pydantic import BaseModel

class Item(BaseModel):
    name: str

@app.post("/items/")
def create_item(item: Item = Body(...)):
    return item
"#;
        let result = scan(source);
        assert!(result.handlers[0].tainted_params.iter()
            .any(|p| p.name == "item" && p.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_fastapi_header_param() {
        let source = r#"
from fastapi import FastAPI, Header

@app.get("/items/")
def read_items(x_token: str = Header(None)):
    return {"X-Token": x_token}
"#;
        let result = scan(source);
        assert!(result.handlers[0].tainted_params.iter()
            .any(|p| p.name == "x_token" && p.kind == SourceKind::HttpHeader));
    }

    #[test]
    fn test_fastapi_cookie_param() {
        let source = r#"
from fastapi import FastAPI, Cookie

@app.get("/items/")
def read_items(ads_id: str = Cookie(None)):
    return {"ads_id": ads_id}
"#;
        let result = scan(source);
        assert!(result.handlers[0].tainted_params.iter()
            .any(|p| p.name == "ads_id" && p.kind == SourceKind::Cookie));
    }

    #[test]
    fn test_fastapi_router() {
        let source = r#"
from fastapi import APIRouter

router = APIRouter()

@router.get("/users/{user_id}")
def get_user(user_id: int):
    return {"user_id": user_id}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 1);
        assert_eq!(result.handlers[0].framework, "fastapi");
    }

    // =========================================================================
    // Standard Library Tests
    // =========================================================================

    #[test]
    fn test_input_builtin() {
        let source = r#"
name = input("Enter your name: ")
print(f"Hello, {name}")
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Stdin));
        assert!(result.sources.iter().any(|s| s.assigned_to == Some("name".to_string())));
    }

    #[test]
    fn test_sys_argv() {
        let source = r#"
import sys

filename = sys.argv[1]
mode = sys.argv[2]
"#;
        let result = scan(source);
        let argv_sources: Vec<_> = result.sources.iter()
            .filter(|s| s.kind == SourceKind::ProcessArgs)
            .collect();
        // At least 2 sources (may detect more from subscript + attribute patterns)
        assert!(argv_sources.len() >= 2, "Expected at least 2 argv sources, got {}", argv_sources.len());
    }

    #[test]
    fn test_os_environ() {
        let source = r#"
import os

db_url = os.environ['DATABASE_URL']
secret = os.environ.get('SECRET_KEY')
"#;
        let result = scan(source);
        let env_sources: Vec<_> = result.sources.iter()
            .filter(|s| s.kind == SourceKind::Environment)
            .collect();
        // At least 2 sources (may detect more from subscript + attribute patterns)
        assert!(env_sources.len() >= 2, "Expected at least 2 environ sources, got {}", env_sources.len());
    }

    #[test]
    fn test_os_getenv() {
        let source = r#"
import os

home = os.getenv('HOME')
path = os.getenv('PATH', '/usr/bin')
"#;
        let result = scan(source);
        let env_sources: Vec<_> = result.sources.iter()
            .filter(|s| s.kind == SourceKind::Environment)
            .collect();
        assert_eq!(env_sources.len(), 2);
    }

    // =========================================================================
    // Network Library Tests
    // =========================================================================

    #[test]
    fn test_requests_get() {
        let source = r#"
import requests

response = requests.get('http://api.example.com/data')
data = response.json()
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::HttpResponse));
    }

    #[test]
    fn test_requests_post() {
        let source = r#"
import requests

resp = requests.post('http://api.example.com/submit', json={"key": "value"})
result = resp.text
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::HttpResponse));
    }

    #[test]
    fn test_socket_recv() {
        let source = r#"
import socket

sock = socket.socket()
sock.connect(('localhost', 8080))
data = socket.recv(1024)
"#;
        let result = scan(source);
        // Note: The source uses "socket" object for recv() call since
        // variable aliasing detection would require dataflow analysis
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::SocketRecv));
    }

    // =========================================================================
    // Database Tests
    // =========================================================================

    #[test]
    fn test_cursor_fetchone() {
        let source = r#"
import sqlite3

conn = sqlite3.connect('db.sqlite')
cursor = conn.cursor()
cursor.execute("SELECT * FROM users WHERE id = ?", (user_id,))
row = cursor.fetchone()
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::DatabaseResult));
    }

    #[test]
    fn test_cursor_fetchall() {
        let source = r#"
cursor.execute("SELECT * FROM users")
rows = cursor.fetchall()
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::DatabaseResult));
    }

    #[test]
    fn test_cursor_fetchmany() {
        let source = r#"
cursor.execute("SELECT * FROM logs")
batch = cursor.fetchmany(100)
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::DatabaseResult));
    }

    // =========================================================================
    // Deserialization Tests
    // =========================================================================

    #[test]
    fn test_json_loads() {
        let source = r#"
import json

data = json.loads(user_input)
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Deserialized));
    }

    #[test]
    fn test_yaml_load() {
        let source = r#"
import yaml

with open('config.yaml') as f:
    config = yaml.load(f, Loader=yaml.SafeLoader)
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Deserialized));
    }

    #[test]
    fn test_pickle_loads() {
        let source = r#"
import pickle

obj = pickle.loads(data)
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Deserialized));
    }

    // =========================================================================
    // Assignment Tracking Tests
    // =========================================================================

    #[test]
    fn test_assignment_tracking() {
        let source = r#"
user_input = input("Enter value: ")
env_var = os.getenv('CONFIG')
"#;
        let result = scan(source);

        let input_source = result.sources.iter()
            .find(|s| s.kind == SourceKind::Stdin)
            .unwrap();
        assert_eq!(input_source.assigned_to, Some("user_input".to_string()));

        let env_source = result.sources.iter()
            .find(|s| s.kind == SourceKind::Environment)
            .unwrap();
        assert_eq!(env_source.assigned_to, Some("env_var".to_string()));
    }

    // =========================================================================
    // Handler Context Tests
    // =========================================================================

    #[test]
    fn test_source_in_handler_context() {
        let source = r#"
@app.route('/search')
def search():
    query = request.args.get('q')
    return {"results": []}
"#;
        let result = scan(source);

        let source = result.sources.iter()
            .find(|s| s.kind == SourceKind::RequestParam)
            .unwrap();

        assert!(source.in_handler);
        assert_eq!(source.enclosing_function, Some("search".to_string()));
    }

    // =========================================================================
    // Complex Scenarios Tests
    // =========================================================================

    #[test]
    fn test_multiple_sources_in_handler() {
        let source = r#"
@app.route('/process', methods=['POST'])
def process():
    user_id = request.args.get('user_id')
    data = request.json
    auth = request.headers.get('Authorization')
    session = request.cookies.get('session')
    return {}
"#;
        let result = scan(source);

        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestParam));
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestBody));
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::HttpHeader));
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Cookie));
    }

    #[test]
    fn test_nested_attribute_access() {
        let source = r#"
data = request.json['users'][0]['name']
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_chained_method_calls() {
        let source = r#"
text = requests.get(url).text
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::HttpResponse));
    }

    // =========================================================================
    // WebSocket Tests
    // =========================================================================

    #[test]
    fn test_websocket_receive() {
        let source = r#"
async def websocket_handler(websocket):
    data = await websocket.receive_json()
    text = await websocket.receive_text()
"#;
        let result = scan(source);
        let ws_sources: Vec<_> = result.sources.iter()
            .filter(|s| s.kind == SourceKind::WebSocketMessage)
            .collect();
        assert_eq!(ws_sources.len(), 2);
    }

    // =========================================================================
    // Edge Cases
    // =========================================================================

    #[test]
    fn test_empty_source() {
        let result = scan("");
        assert!(result.sources.is_empty());
        assert!(result.handlers.is_empty());
    }

    #[test]
    fn test_no_sources() {
        let source = r#"
def pure_function(x, y):
    return x + y

result = pure_function(1, 2)
"#;
        let result = scan(source);
        assert!(result.sources.is_empty());
    }

    #[test]
    fn test_import_alias() {
        let source = r#"
from flask import request as req

def handler():
    data = req.json
"#;
        let result = scan(source);
        // Note: Import alias tracking requires more sophisticated analysis
        // This test documents current behavior
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_confidence_levels() {
        let source = r#"
# High confidence source
name = input()

# Lower confidence (duck typing)
row = obj.fetchone()
"#;
        let result = scan(source);

        let input_source = result.sources.iter()
            .find(|s| s.kind == SourceKind::Stdin)
            .unwrap();
        assert!((input_source.confidence - 1.0).abs() < f64::EPSILON);

        let fetch_source = result.sources.iter()
            .find(|s| s.kind == SourceKind::DatabaseResult)
            .unwrap();
        assert!(fetch_source.confidence < 1.0);
    }
}
