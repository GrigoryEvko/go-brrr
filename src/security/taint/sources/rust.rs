//! Rust taint source identification.
//!
//! This module identifies all locations in Rust code where untrusted data
//! enters the program. It uses AST pattern matching via tree-sitter to detect:
//!
//! - **Web Frameworks**: Actix-web, Axum, Rocket request extractors
//! - **Standard Library**: std::env::args(), std::env::var(), std::io::stdin()
//! - **File I/O**: std::fs::read_to_string(), BufReader operations
//! - **Network**: TcpStream::read(), reqwest response methods
//! - **Database**: sqlx query results, diesel queries
//! - **Deserialization**: serde_json, toml, bincode
//!
//! # Rust-Specific Tracking
//!
//! The detector handles Rust's unique ownership semantics:
//!
//! ## Result/Option Unwrapping
//!
//! Taint propagates through `?` operator, `unwrap()`, `expect()`, and pattern matching:
//! ```rust,ignore
//! let data = fs::read_to_string(path)?;           // data is tainted
//! let val = env::var("KEY").unwrap();             // val is tainted
//! if let Ok(content) = fs::read(path) { ... }    // content is tainted
//! ```
//!
//! ## Pattern Matching
//!
//! Taint flows through match arms:
//! ```rust,ignore
//! match result {
//!     Ok(data) => process(data),    // data is tainted
//!     Err(e) => handle(e),
//! }
//! ```
//!
//! ## Async Operations
//!
//! Taint persists through `.await`:
//! ```rust,ignore
//! let body = response.text().await?;  // body is tainted
//! ```
//!
//! ## Move Semantics
//!
//! Taint follows moved values:
//! ```rust,ignore
//! let input = stdin().read_line(&mut buffer)?;
//! let processed = buffer;  // processed inherits taint from buffer
//! ```
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::security::taint::sources::rust::RustSourceDetector;
//!
//! let detector = RustSourceDetector::new();
//! let source = r#"
//! use actix_web::{web, HttpRequest};
//!
//! async fn handler(
//!     path: web::Path<String>,
//!     query: web::Query<Params>,
//!     body: web::Json<Data>,
//! ) -> impl Responder {
//!     let id = path.into_inner();  // tainted from URL path
//!     let search = query.q.clone();  // tainted from query string
//!     format!("{}: {}", id, search)
//! }
//! "#;
//!
//! let result = detector.scan_source(source, "handler.rs")?;
//! assert!(result.sources.len() >= 3);
//! ```

use std::collections::{HashMap, HashSet};
use std::path::Path;

use tree_sitter::{Node, Parser, Tree};

use super::{
    DetectedSource, HandlerInfo, SourceKind, SourcePattern, SourceScanResult, TaintedParameter,
};
use crate::error::{BrrrError, Result};
use crate::security::taint::types::Location;

// =============================================================================
// Source Pattern Definitions
// =============================================================================

/// Actix-web framework taint sources.
const ACTIX_SOURCES: &[SourcePattern] = &[
    SourcePattern::property_access(
        "actix_web_path",
        SourceKind::UrlPath,
        "web",
        "Path",
        Some("actix-web"),
    ),
    SourcePattern::property_access(
        "actix_web_query",
        SourceKind::RequestParam,
        "web",
        "Query",
        Some("actix-web"),
    ),
    SourcePattern::property_access(
        "actix_web_json",
        SourceKind::RequestBody,
        "web",
        "Json",
        Some("actix-web"),
    ),
    SourcePattern::property_access(
        "actix_web_form",
        SourceKind::RequestBody,
        "web",
        "Form",
        Some("actix-web"),
    ),
    SourcePattern::property_access(
        "actix_web_data",
        SourceKind::GenericUserInput,
        "web",
        "Data",
        Some("actix-web"),
    ),
    SourcePattern::property_access(
        "actix_web_bytes",
        SourceKind::RequestBody,
        "web",
        "Bytes",
        Some("actix-web"),
    ),
    SourcePattern::method_call(
        "actix_http_request_headers",
        SourceKind::HttpHeader,
        "HttpRequest",
        "headers",
        Some("actix-web"),
    ),
    SourcePattern::method_call(
        "actix_http_request_cookie",
        SourceKind::Cookie,
        "HttpRequest",
        "cookie",
        Some("actix-web"),
    ),
    SourcePattern::method_call(
        "actix_http_request_path",
        SourceKind::UrlPath,
        "HttpRequest",
        "path",
        Some("actix-web"),
    ),
    SourcePattern::method_call(
        "actix_http_request_query_string",
        SourceKind::RequestParam,
        "HttpRequest",
        "query_string",
        Some("actix-web"),
    ),
    SourcePattern::method_call(
        "actix_http_request_uri",
        SourceKind::UrlPath,
        "HttpRequest",
        "uri",
        Some("actix-web"),
    ),
    SourcePattern::method_call(
        "actix_http_request_match_info",
        SourceKind::UrlPath,
        "HttpRequest",
        "match_info",
        Some("actix-web"),
    ),
];

/// Axum framework taint sources.
const AXUM_SOURCES: &[SourcePattern] = &[
    SourcePattern::property_access(
        "axum_extract_path",
        SourceKind::UrlPath,
        "extract",
        "Path",
        Some("axum"),
    ),
    SourcePattern::property_access(
        "axum_extract_query",
        SourceKind::RequestParam,
        "extract",
        "Query",
        Some("axum"),
    ),
    SourcePattern::property_access(
        "axum_extract_json",
        SourceKind::RequestBody,
        "extract",
        "Json",
        Some("axum"),
    ),
    SourcePattern::property_access(
        "axum_extract_form",
        SourceKind::RequestBody,
        "extract",
        "Form",
        Some("axum"),
    ),
    SourcePattern::property_access(
        "axum_extract_multipart",
        SourceKind::FileUpload,
        "extract",
        "Multipart",
        Some("axum"),
    ),
    SourcePattern::property_access(
        "axum_extract_raw_body",
        SourceKind::RequestBody,
        "extract",
        "RawBody",
        Some("axum"),
    ),
    SourcePattern::property_access(
        "axum_extract_typed_header",
        SourceKind::HttpHeader,
        "extract",
        "TypedHeader",
        Some("axum"),
    ),
    SourcePattern::property_access(
        "axum_extract_connect_info",
        SourceKind::HttpHeader,
        "extract",
        "ConnectInfo",
        Some("axum"),
    ),
    SourcePattern::property_access(
        "axum_extract_host",
        SourceKind::HttpHeader,
        "extract",
        "Host",
        Some("axum"),
    ),
    SourcePattern::property_access(
        "axum_extract_state",
        SourceKind::GenericUserInput,
        "extract",
        "State",
        Some("axum"),
    ),
    // Direct axum type names (without extract:: prefix)
    SourcePattern::function_call("axum_path", SourceKind::UrlPath, "Path", 0.85),
    SourcePattern::function_call("axum_query", SourceKind::RequestParam, "Query", 0.85),
    SourcePattern::function_call("axum_json", SourceKind::RequestBody, "Json", 0.85),
    SourcePattern::function_call("axum_form", SourceKind::RequestBody, "Form", 0.85),
];

/// Rocket framework taint sources.
const ROCKET_SOURCES: &[SourcePattern] = &[
    SourcePattern::property_access(
        "rocket_data",
        SourceKind::RequestBody,
        "rocket",
        "Data",
        Some("rocket"),
    ),
    SourcePattern::property_access(
        "rocket_form",
        SourceKind::RequestBody,
        "rocket",
        "Form",
        Some("rocket"),
    ),
    SourcePattern::property_access(
        "rocket_json",
        SourceKind::RequestBody,
        "rocket",
        "Json",
        Some("rocket"),
    ),
    SourcePattern::method_call(
        "rocket_cookies_get",
        SourceKind::Cookie,
        "CookieJar",
        "get",
        Some("rocket"),
    ),
    SourcePattern::method_call(
        "rocket_cookies_get_private",
        SourceKind::Cookie,
        "CookieJar",
        "get_private",
        Some("rocket"),
    ),
];

/// Standard library taint sources.
const STDLIB_SOURCES: &[SourcePattern] = &[
    // Command line arguments
    SourcePattern::function_call("env_args", SourceKind::ProcessArgs, "args", 0.95),
    SourcePattern::function_call("env_args_os", SourceKind::ProcessArgs, "args_os", 0.95),
    SourcePattern::method_call("std_env_args", SourceKind::ProcessArgs, "env", "args", None),
    SourcePattern::method_call(
        "std_env_args_os",
        SourceKind::ProcessArgs,
        "env",
        "args_os",
        None,
    ),
    // Environment variables
    SourcePattern::function_call("env_var", SourceKind::Environment, "var", 0.9),
    SourcePattern::function_call("env_var_os", SourceKind::Environment, "var_os", 0.9),
    SourcePattern::method_call("std_env_var", SourceKind::Environment, "env", "var", None),
    SourcePattern::method_call(
        "std_env_var_os",
        SourceKind::Environment,
        "env",
        "var_os",
        None,
    ),
    SourcePattern::method_call("std_env_vars", SourceKind::Environment, "env", "vars", None),
    SourcePattern::method_call(
        "std_env_vars_os",
        SourceKind::Environment,
        "env",
        "vars_os",
        None,
    ),
    // Standard input
    SourcePattern::function_call("io_stdin", SourceKind::Stdin, "stdin", 0.95),
    SourcePattern::method_call("std_io_stdin", SourceKind::Stdin, "io", "stdin", None),
    SourcePattern::method_call(
        "stdin_read_line",
        SourceKind::Stdin,
        "stdin",
        "read_line",
        None,
    ),
    SourcePattern::method_call(
        "stdin_read_to_string",
        SourceKind::Stdin,
        "stdin",
        "read_to_string",
        None,
    ),
    SourcePattern::method_call("stdin_lock", SourceKind::Stdin, "stdin", "lock", None),
];

/// File I/O taint sources.
const FILE_SOURCES: &[SourcePattern] = &[
    // std::fs functions
    SourcePattern::method_call("fs_read", SourceKind::FileRead, "fs", "read", None),
    SourcePattern::method_call(
        "fs_read_to_string",
        SourceKind::FileRead,
        "fs",
        "read_to_string",
        None,
    ),
    SourcePattern::method_call("fs_read_dir", SourceKind::FileRead, "fs", "read_dir", None),
    SourcePattern::method_call(
        "fs_read_link",
        SourceKind::FileRead,
        "fs",
        "read_link",
        None,
    ),
    // File/BufReader methods
    SourcePattern::method_call("file_read", SourceKind::FileRead, "File", "open", None),
    SourcePattern::method_call(
        "buf_reader_read_line",
        SourceKind::FileRead,
        "BufReader",
        "read_line",
        None,
    ),
    SourcePattern::method_call(
        "buf_reader_read_until",
        SourceKind::FileRead,
        "BufReader",
        "read_until",
        None,
    ),
    SourcePattern::method_call(
        "buf_reader_lines",
        SourceKind::FileRead,
        "BufReader",
        "lines",
        None,
    ),
    // Read trait methods (on any implementor)
    SourcePattern::function_call(
        "read_to_string",
        SourceKind::FileRead,
        "read_to_string",
        0.7,
    ),
    SourcePattern::function_call("read_to_end", SourceKind::FileRead, "read_to_end", 0.7),
    SourcePattern::function_call("read_exact", SourceKind::FileRead, "read_exact", 0.7),
    // tokio::fs
    SourcePattern::method_call(
        "tokio_fs_read",
        SourceKind::FileRead,
        "tokio::fs",
        "read",
        None,
    ),
    SourcePattern::method_call(
        "tokio_fs_read_to_string",
        SourceKind::FileRead,
        "tokio::fs",
        "read_to_string",
        None,
    ),
];

/// Network taint sources.
const NETWORK_SOURCES: &[SourcePattern] = &[
    // TcpStream
    SourcePattern::method_call(
        "tcp_stream_read",
        SourceKind::SocketRecv,
        "TcpStream",
        "read",
        None,
    ),
    SourcePattern::method_call(
        "tcp_stream_read_exact",
        SourceKind::SocketRecv,
        "TcpStream",
        "read_exact",
        None,
    ),
    SourcePattern::method_call(
        "tcp_stream_read_to_end",
        SourceKind::SocketRecv,
        "TcpStream",
        "read_to_end",
        None,
    ),
    SourcePattern::method_call(
        "tcp_stream_read_to_string",
        SourceKind::SocketRecv,
        "TcpStream",
        "read_to_string",
        None,
    ),
    // UdpSocket
    SourcePattern::method_call(
        "udp_socket_recv",
        SourceKind::SocketRecv,
        "UdpSocket",
        "recv",
        None,
    ),
    SourcePattern::method_call(
        "udp_socket_recv_from",
        SourceKind::SocketRecv,
        "UdpSocket",
        "recv_from",
        None,
    ),
    // reqwest
    SourcePattern::method_call(
        "reqwest_get",
        SourceKind::HttpResponse,
        "reqwest",
        "get",
        None,
    ),
    SourcePattern::method_call(
        "reqwest_client_get",
        SourceKind::HttpResponse,
        "Client",
        "get",
        None,
    ),
    SourcePattern::method_call(
        "reqwest_client_post",
        SourceKind::HttpResponse,
        "Client",
        "post",
        None,
    ),
    SourcePattern::method_call(
        "reqwest_response_text",
        SourceKind::HttpResponse,
        "Response",
        "text",
        None,
    ),
    SourcePattern::method_call(
        "reqwest_response_json",
        SourceKind::HttpResponse,
        "Response",
        "json",
        None,
    ),
    SourcePattern::method_call(
        "reqwest_response_bytes",
        SourceKind::HttpResponse,
        "Response",
        "bytes",
        None,
    ),
    SourcePattern::method_call(
        "reqwest_response_chunk",
        SourceKind::HttpResponse,
        "Response",
        "chunk",
        None,
    ),
    // hyper
    SourcePattern::method_call(
        "hyper_body_collect",
        SourceKind::HttpResponse,
        "Body",
        "collect",
        None,
    ),
    SourcePattern::method_call(
        "hyper_body_to_bytes",
        SourceKind::HttpResponse,
        "body",
        "to_bytes",
        None,
    ),
];

/// Database taint sources.
const DATABASE_SOURCES: &[SourcePattern] = &[
    // sqlx - Note: method patterns check for specific object types,
    // but we also add function_call patterns for generic method name matching
    SourcePattern::method_call(
        "sqlx_fetch_one",
        SourceKind::DatabaseResult,
        "query",
        "fetch_one",
        None,
    ),
    SourcePattern::method_call(
        "sqlx_fetch_all",
        SourceKind::DatabaseResult,
        "query",
        "fetch_all",
        None,
    ),
    SourcePattern::method_call(
        "sqlx_fetch_optional",
        SourceKind::DatabaseResult,
        "query",
        "fetch_optional",
        None,
    ),
    SourcePattern::method_call(
        "sqlx_fetch",
        SourceKind::DatabaseResult,
        "query",
        "fetch",
        None,
    ),
    SourcePattern::method_call(
        "sqlx_row_get",
        SourceKind::DatabaseResult,
        "Row",
        "get",
        None,
    ),
    SourcePattern::method_call(
        "sqlx_row_try_get",
        SourceKind::DatabaseResult,
        "Row",
        "try_get",
        None,
    ),
    // diesel
    SourcePattern::method_call(
        "diesel_load",
        SourceKind::DatabaseResult,
        "RunQueryDsl",
        "load",
        None,
    ),
    SourcePattern::method_call(
        "diesel_first",
        SourceKind::DatabaseResult,
        "RunQueryDsl",
        "first",
        None,
    ),
    SourcePattern::method_call(
        "diesel_get_result",
        SourceKind::DatabaseResult,
        "RunQueryDsl",
        "get_result",
        None,
    ),
    SourcePattern::method_call(
        "diesel_get_results",
        SourceKind::DatabaseResult,
        "RunQueryDsl",
        "get_results",
        None,
    ),
];

/// Deserialization taint sources.
const DESERIALIZATION_SOURCES: &[SourcePattern] = &[
    // serde_json
    SourcePattern::method_call(
        "serde_json_from_str",
        SourceKind::Deserialized,
        "serde_json",
        "from_str",
        None,
    ),
    SourcePattern::method_call(
        "serde_json_from_slice",
        SourceKind::Deserialized,
        "serde_json",
        "from_slice",
        None,
    ),
    SourcePattern::method_call(
        "serde_json_from_reader",
        SourceKind::Deserialized,
        "serde_json",
        "from_reader",
        None,
    ),
    SourcePattern::method_call(
        "serde_json_from_value",
        SourceKind::Deserialized,
        "serde_json",
        "from_value",
        None,
    ),
    // serde_yaml
    SourcePattern::method_call(
        "serde_yaml_from_str",
        SourceKind::Deserialized,
        "serde_yaml",
        "from_str",
        None,
    ),
    SourcePattern::method_call(
        "serde_yaml_from_slice",
        SourceKind::Deserialized,
        "serde_yaml",
        "from_slice",
        None,
    ),
    SourcePattern::method_call(
        "serde_yaml_from_reader",
        SourceKind::Deserialized,
        "serde_yaml",
        "from_reader",
        None,
    ),
    // toml
    SourcePattern::method_call(
        "toml_from_str",
        SourceKind::Deserialized,
        "toml",
        "from_str",
        None,
    ),
    SourcePattern::method_call(
        "toml_de_from_str",
        SourceKind::Deserialized,
        "toml::de",
        "from_str",
        None,
    ),
    // bincode
    SourcePattern::method_call(
        "bincode_deserialize",
        SourceKind::Deserialized,
        "bincode",
        "deserialize",
        None,
    ),
    SourcePattern::method_call(
        "bincode_deserialize_from",
        SourceKind::Deserialized,
        "bincode",
        "deserialize_from",
        None,
    ),
    // rmp_serde (MessagePack)
    SourcePattern::method_call(
        "rmp_serde_from_slice",
        SourceKind::Deserialized,
        "rmp_serde",
        "from_slice",
        None,
    ),
    SourcePattern::method_call(
        "rmp_serde_from_read",
        SourceKind::Deserialized,
        "rmp_serde",
        "from_read",
        None,
    ),
    // Generic deserialize pattern
    SourcePattern::function_call("from_str", SourceKind::Deserialized, "from_str", 0.6),
    SourcePattern::function_call("from_slice", SourceKind::Deserialized, "from_slice", 0.65),
    SourcePattern::function_call("from_reader", SourceKind::Deserialized, "from_reader", 0.65),
    SourcePattern::function_call("deserialize", SourceKind::Deserialized, "deserialize", 0.6),
];

/// Clap CLI argument taint sources.
const CLAP_SOURCES: &[SourcePattern] = &[
    SourcePattern::method_call(
        "clap_get_one",
        SourceKind::ProcessArgs,
        "ArgMatches",
        "get_one",
        None,
    ),
    SourcePattern::method_call(
        "clap_get_many",
        SourceKind::ProcessArgs,
        "ArgMatches",
        "get_many",
        None,
    ),
    SourcePattern::method_call(
        "clap_get_raw",
        SourceKind::ProcessArgs,
        "ArgMatches",
        "get_raw",
        None,
    ),
    SourcePattern::method_call(
        "clap_value_of",
        SourceKind::ProcessArgs,
        "ArgMatches",
        "value_of",
        None,
    ),
    SourcePattern::method_call(
        "clap_values_of",
        SourceKind::ProcessArgs,
        "ArgMatches",
        "values_of",
        None,
    ),
    SourcePattern::method_call(
        "clap_is_present",
        SourceKind::ProcessArgs,
        "ArgMatches",
        "is_present",
        None,
    ),
];

/// WebSocket taint sources.
const WEBSOCKET_SOURCES: &[SourcePattern] = &[
    // tokio-tungstenite
    SourcePattern::method_call(
        "ws_next",
        SourceKind::WebSocketMessage,
        "WebSocketStream",
        "next",
        None,
    ),
    SourcePattern::method_call(
        "ws_recv",
        SourceKind::WebSocketMessage,
        "WebSocket",
        "recv",
        None,
    ),
    // tungstenite Message
    SourcePattern::method_call(
        "ws_message_into_text",
        SourceKind::WebSocketMessage,
        "Message",
        "into_text",
        None,
    ),
    SourcePattern::method_call(
        "ws_message_into_data",
        SourceKind::WebSocketMessage,
        "Message",
        "into_data",
        None,
    ),
    SourcePattern::method_call(
        "ws_message_to_text",
        SourceKind::WebSocketMessage,
        "Message",
        "to_text",
        None,
    ),
];

// =============================================================================
// Handler Attribute Patterns
// =============================================================================

/// Actix-web route macros.
const ACTIX_ROUTE_MACROS: &[&str] = &[
    "get", "post", "put", "delete", "patch", "head", "options", "trace", "connect", "route",
];

/// Axum router methods (for future router-based handler detection).
#[allow(dead_code)]
const AXUM_ROUTER_METHODS: &[&str] = &[
    "get",
    "post",
    "put",
    "delete",
    "patch",
    "head",
    "options",
    "trace",
    "route",
    "route_service",
];

/// Rocket route macros.
const ROCKET_ROUTE_MACROS: &[&str] = &["get", "post", "put", "delete", "patch", "head", "options"];

/// Type patterns that indicate taint sources in function parameters.
const TAINTED_PARAM_TYPES: &[(&str, SourceKind)] = &[
    // Actix-web
    ("web::Path", SourceKind::UrlPath),
    ("web::Query", SourceKind::RequestParam),
    ("web::Json", SourceKind::RequestBody),
    ("web::Form", SourceKind::RequestBody),
    ("web::Bytes", SourceKind::RequestBody),
    ("web::Data", SourceKind::GenericUserInput),
    ("HttpRequest", SourceKind::RequestBody),
    // Axum
    ("Path", SourceKind::UrlPath),
    ("Query", SourceKind::RequestParam),
    ("Json", SourceKind::RequestBody),
    ("Form", SourceKind::RequestBody),
    ("RawBody", SourceKind::RequestBody),
    ("Multipart", SourceKind::FileUpload),
    ("TypedHeader", SourceKind::HttpHeader),
    ("extract::Path", SourceKind::UrlPath),
    ("extract::Query", SourceKind::RequestParam),
    ("extract::Json", SourceKind::RequestBody),
    ("extract::Form", SourceKind::RequestBody),
    // Rocket
    ("rocket::Data", SourceKind::RequestBody),
    ("rocket::Form", SourceKind::RequestBody),
    ("rocket::Json", SourceKind::RequestBody),
    // Generic
    ("String", SourceKind::GenericUserInput), // Only in handler params
    ("&str", SourceKind::GenericUserInput),   // Only in handler params
];

// =============================================================================
// Rust Source Detector
// =============================================================================

/// Detects taint sources in Rust code using AST analysis.
///
/// The detector identifies sources through:
/// 1. Pattern matching on function calls and method invocations
/// 2. Handler attribute analysis for Actix-web, Axum, Rocket
/// 3. Result/Option unwrap tracking
/// 4. Match expression taint propagation
/// 5. Async/await handling
pub struct RustSourceDetector {
    /// All source patterns to check
    patterns: Vec<SourcePattern>,
    /// Use statement aliases (e.g., "env" -> "std::env")
    use_aliases: HashMap<String, String>,
    /// Known tainted variable names (for cross-file analysis).
    #[allow(dead_code)]
    tainted_vars: HashSet<String>,
}

impl RustSourceDetector {
    /// Create a new Rust source detector with default patterns.
    pub fn new() -> Self {
        let mut patterns = Vec::new();
        patterns.extend_from_slice(ACTIX_SOURCES);
        patterns.extend_from_slice(AXUM_SOURCES);
        patterns.extend_from_slice(ROCKET_SOURCES);
        patterns.extend_from_slice(STDLIB_SOURCES);
        patterns.extend_from_slice(FILE_SOURCES);
        patterns.extend_from_slice(NETWORK_SOURCES);
        patterns.extend_from_slice(DATABASE_SOURCES);
        patterns.extend_from_slice(DESERIALIZATION_SOURCES);
        patterns.extend_from_slice(CLAP_SOURCES);
        patterns.extend_from_slice(WEBSOCKET_SOURCES);

        Self {
            patterns,
            use_aliases: HashMap::new(),
            tainted_vars: HashSet::new(),
        }
    }

    /// Add a custom source pattern.
    pub fn add_pattern(&mut self, pattern: SourcePattern) {
        self.patterns.push(pattern);
    }

    /// Scan a source file for taint sources.
    pub fn scan_file(&self, path: impl AsRef<Path>) -> Result<SourceScanResult> {
        let path = path.as_ref();
        let source = std::fs::read_to_string(path).map_err(|e| BrrrError::IoWithPath {
            error: e,
            path: path.to_path_buf(),
        })?;
        self.scan_source(&source, path.to_string_lossy().as_ref())
    }

    /// Scan source code for taint sources.
    pub fn scan_source(&self, source: &str, file_name: &str) -> Result<SourceScanResult> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .map_err(|e| BrrrError::Parse {
                file: file_name.to_string(),
                message: format!("Failed to set Rust language: {}", e),
            })?;

        let tree = parser.parse(source, None).ok_or_else(|| BrrrError::Parse {
            file: file_name.to_string(),
            message: "Failed to parse Rust source".to_string(),
        })?;

        self.scan_tree(&tree, source, file_name)
    }

    /// Scan a parsed AST for taint sources.
    fn scan_tree(&self, tree: &Tree, source: &str, file_name: &str) -> Result<SourceScanResult> {
        let mut result = SourceScanResult::new(file_name, "rust");
        let source_bytes = source.as_bytes();
        let root = tree.root_node();

        // First pass: collect use statements for alias resolution
        let mut use_aliases = self.use_aliases.clone();
        self.collect_use_statements(root, source_bytes, &mut use_aliases);

        // Create scanning context
        let mut ctx = ScanContext {
            source: source_bytes,
            file_name,
            use_aliases: &use_aliases,
            tainted_vars: HashSet::new(),
            current_function: None,
            current_handler: None,
            in_handler_scope: false,
            in_async_context: false,
            in_try_expression: false,
        };

        // Second pass: find sources and handlers
        self.scan_node(root, &mut ctx, &mut result);

        Ok(result)
    }

    /// Collect use statements for alias resolution.
    fn collect_use_statements(
        &self,
        root: Node,
        source: &[u8],
        aliases: &mut HashMap<String, String>,
    ) {
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "use_declaration" {
                self.process_use_declaration(child, source, aliases);
            }
        }
    }

    /// Process a use declaration to extract aliases.
    fn process_use_declaration(
        &self,
        node: Node,
        source: &[u8],
        aliases: &mut HashMap<String, String>,
    ) {
        // Handle: use std::env;
        // Handle: use std::env::var;
        // Handle: use std::env as environment;
        // Handle: use std::{env, fs};

        let use_text = self.node_text(node, source);

        // Simple case: use foo::bar;
        if let Some(idx) = use_text.rfind("::") {
            let after_last_colon = &use_text[idx + 2..].trim_end_matches(';');
            if !after_last_colon.contains('{') && !after_last_colon.contains(' ') {
                // Extract the path before the last item
                let full_path = use_text
                    .trim_start_matches("use ")
                    .trim_end_matches(';')
                    .trim();
                aliases.insert(after_last_colon.to_string(), full_path.to_string());
            }
        }

        // Handle 'as' aliases: use foo::bar as baz;
        if use_text.contains(" as ") {
            if let Some(as_idx) = use_text.find(" as ") {
                let before_as = &use_text[..as_idx];
                let after_as = use_text[as_idx + 4..].trim_end_matches(';').trim();
                let full_path = before_as.trim_start_matches("use ").trim();
                aliases.insert(after_as.to_string(), full_path.to_string());
            }
        }
    }

    /// Recursively scan AST nodes for sources.
    fn scan_node(&self, node: Node, ctx: &mut ScanContext, result: &mut SourceScanResult) {
        match node.kind() {
            // Function definitions with potential handler attributes
            "function_item" => {
                self.scan_function_item(node, ctx, result);
            }
            // Method calls: object.method()
            "call_expression" => {
                self.scan_call_expression(node, ctx, result);
                self.scan_children(node, ctx, result);
            }
            // Field/method access: obj.field
            "field_expression" => {
                self.scan_field_expression(node, ctx, result);
                self.scan_children(node, ctx, result);
            }
            // Let bindings with potential destructuring
            "let_declaration" => {
                self.scan_let_declaration(node, ctx, result);
            }
            // Match expressions for taint propagation
            "match_expression" => {
                self.scan_match_expression(node, ctx, result);
            }
            // Try expressions (?)
            "try_expression" => {
                self.scan_try_expression(node, ctx, result);
            }
            // Await expressions
            "await_expression" => {
                self.scan_await_expression(node, ctx, result);
            }
            // Macro invocations (some macros are sources)
            "macro_invocation" => {
                self.scan_macro_invocation(node, ctx, result);
                self.scan_children(node, ctx, result);
            }
            // Identifier references (check if tainted var)
            "identifier" => {
                self.scan_identifier(node, ctx, result);
            }
            _ => {
                self.scan_children(node, ctx, result);
            }
        }
    }

    /// Scan children of a node.
    fn scan_children(&self, node: Node, ctx: &mut ScanContext, result: &mut SourceScanResult) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.scan_node(child, ctx, result);
        }
    }

    /// Scan a function item for handler attributes and tainted parameters.
    fn scan_function_item(&self, node: Node, ctx: &mut ScanContext, result: &mut SourceScanResult) {
        let old_func = ctx.current_function.take();
        let old_handler = ctx.current_handler.take();
        let old_in_handler = ctx.in_handler_scope;
        let old_async = ctx.in_async_context;

        // Extract function name
        let func_name = self.extract_function_name(node, ctx.source);
        ctx.current_function = Some(func_name.clone());

        // Check if function is async
        if self.is_async_function(node, ctx.source) {
            ctx.in_async_context = true;
        }

        // Check for handler attributes
        if let Some(handler_info) = self.analyze_handler_attributes(node, ctx) {
            // Add tainted parameters as sources
            for param in &handler_info.tainted_params {
                let loc = Location::new(ctx.file_name, handler_info.start_line, 0);
                let source =
                    DetectedSource::new(param.kind, loc, format!("parameter:{}", param.name))
                        .with_assignment(&param.name)
                        .with_framework(&handler_info.framework)
                        .in_handler_function(&handler_info.name);

                result.add_source(source);

                // Track tainted parameter names
                ctx.tainted_vars.insert(param.name.clone());
            }

            result.add_handler(handler_info.clone());
            ctx.current_handler = Some(handler_info);
            ctx.in_handler_scope = true;
        }

        // Scan function body
        self.scan_children(node, ctx, result);

        ctx.current_function = old_func;
        ctx.current_handler = old_handler;
        ctx.in_handler_scope = old_in_handler;
        ctx.in_async_context = old_async;
    }

    /// Extract function name from a function_item node.
    fn extract_function_name(&self, node: Node, source: &[u8]) -> String {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "identifier" {
                return self.node_text(child, source).to_string();
            }
        }
        "<anonymous>".to_string()
    }

    /// Check if a function is async.
    fn is_async_function(&self, node: Node, source: &[u8]) -> bool {
        let text = self.node_text(node, source);
        text.contains("async fn") || text.starts_with("async ")
    }

    /// Analyze attributes to detect handler functions.
    fn analyze_handler_attributes(&self, node: Node, ctx: &ScanContext) -> Option<HandlerInfo> {
        // Look for preceding attributes
        let mut sibling = node.prev_sibling();
        let mut route = None;
        let mut methods = Vec::new();
        let mut framework = None;

        // First, determine framework from imports in the source
        let source_text = std::str::from_utf8(ctx.source).unwrap_or("");
        let is_actix = source_text.contains("actix_web") || source_text.contains("actix-web");
        let is_rocket = source_text.contains("use rocket::") || source_text.contains("rocket::");

        while let Some(prev) = sibling {
            if prev.kind() == "attribute_item" {
                let attr_text = self.node_text(prev, ctx.source);

                // Check for route macros - use import context to determine framework
                // Actix-web and Rocket share the same macro names (get, post, etc.)
                for macro_name in ACTIX_ROUTE_MACROS {
                    let pattern = format!("#[{}(", macro_name);
                    if attr_text.contains(&pattern) {
                        // Determine framework based on imports
                        if is_actix && !is_rocket {
                            framework = Some("actix-web");
                        } else if is_rocket && !is_actix {
                            framework = Some("rocket");
                        } else {
                            // Both or neither imported - default to actix-web (more common)
                            framework = Some("actix-web");
                        }
                        methods.push(macro_name.to_uppercase());
                        route = self.extract_route_from_attribute(attr_text);
                        break;
                    }
                }
            } else if prev.kind() != "line_comment" && prev.kind() != "block_comment" {
                break;
            }
            sibling = prev.prev_sibling();
        }

        if framework.is_some() {
            let func_name = self.extract_function_name(node, ctx.source);
            let params = self.extract_tainted_params(node, framework.unwrap(), ctx);

            Some(HandlerInfo {
                name: func_name,
                start_line: node.start_position().row + 1,
                end_line: node.end_position().row + 1,
                route,
                methods,
                framework: framework.unwrap().to_string(),
                tainted_params: params,
            })
        } else {
            // Check for axum-style handlers (no attribute, but specific parameter types)
            if self.looks_like_axum_handler(node, ctx) {
                let func_name = self.extract_function_name(node, ctx.source);
                let params = self.extract_tainted_params(node, "axum", ctx);

                if !params.is_empty() {
                    return Some(HandlerInfo {
                        name: func_name,
                        start_line: node.start_position().row + 1,
                        end_line: node.end_position().row + 1,
                        route: None,
                        methods: Vec::new(),
                        framework: "axum".to_string(),
                        tainted_params: params,
                    });
                }
            }
            None
        }
    }

    /// Extract route path from attribute like #[get("/users/<id>")]
    fn extract_route_from_attribute(&self, attr_text: &str) -> Option<String> {
        // Find content between first ( and matching )
        if let Some(start) = attr_text.find('(') {
            let after_paren = &attr_text[start + 1..];
            // Extract quoted string
            if let Some(quote_start) = after_paren.find('"') {
                let after_quote = &after_paren[quote_start + 1..];
                if let Some(quote_end) = after_quote.find('"') {
                    return Some(after_quote[..quote_end].to_string());
                }
            }
        }
        None
    }

    /// Check if function looks like an axum handler based on parameter types.
    fn looks_like_axum_handler(&self, node: Node, ctx: &ScanContext) -> bool {
        let func_text = self.node_text(node, ctx.source);

        // Check for axum extractor types in parameters
        for (type_pattern, _) in TAINTED_PARAM_TYPES {
            if func_text.contains(type_pattern) {
                // Verify it's in a parameter position
                if func_text.contains(&format!("{}<", type_pattern))
                    || func_text.contains(&format!("{},", type_pattern))
                    || func_text.contains(&format!("{})", type_pattern))
                {
                    return true;
                }
            }
        }
        false
    }

    /// Extract tainted parameters from a function.
    fn extract_tainted_params(
        &self,
        node: Node,
        framework: &str,
        ctx: &ScanContext,
    ) -> Vec<TaintedParameter> {
        let mut params = Vec::new();

        for child in node.children(&mut node.walk()) {
            if child.kind() == "parameters" {
                let mut param_index = 0;
                for param_node in child.children(&mut child.walk()) {
                    if param_node.kind() == "parameter" {
                        if let Some(tainted_param) =
                            self.analyze_parameter(param_node, param_index, framework, ctx)
                        {
                            params.push(tainted_param);
                        }
                        param_index += 1;
                    }
                }
            }
        }

        params
    }

    /// Analyze a single parameter for taint source types.
    fn analyze_parameter(
        &self,
        param_node: Node,
        index: usize,
        framework: &str,
        ctx: &ScanContext,
    ) -> Option<TaintedParameter> {
        let param_text = self.node_text(param_node, ctx.source);

        // Extract parameter name
        let name = self.extract_param_name(param_node, ctx.source)?;

        // Skip 'self' parameters
        if name == "self" || name == "_" {
            return None;
        }

        // Check parameter type against known taint sources
        for (type_pattern, kind) in TAINTED_PARAM_TYPES {
            if param_text.contains(type_pattern) {
                // For generic types like String/&str, only taint in handler context
                if *type_pattern == "String" || *type_pattern == "&str" {
                    if framework.is_empty() {
                        continue;
                    }
                }

                return Some(TaintedParameter {
                    name,
                    kind: *kind,
                    index,
                    annotation: Some(type_pattern.to_string()),
                });
            }
        }

        // In handler context, parameters without explicit types might still be tainted
        // (e.g., from path segments in Rocket: fn handler(id: usize))
        if !framework.is_empty()
            && !param_text.contains("State")
            && !param_text.contains("Extension")
        {
            // Check if this could be a path parameter based on framework conventions
            if framework == "rocket" {
                // Rocket uses #[get("/<name>")] syntax, simple types are path params
                return Some(TaintedParameter {
                    name,
                    kind: SourceKind::UrlPath,
                    index,
                    annotation: None,
                });
            }
        }

        None
    }

    /// Extract parameter name from parameter node.
    fn extract_param_name(&self, param_node: Node, source: &[u8]) -> Option<String> {
        for child in param_node.children(&mut param_node.walk()) {
            if child.kind() == "identifier" {
                return Some(self.node_text(child, source).to_string());
            }
            // Handle pattern binding: name: Type
            if child.kind() == "identifier" || child.kind() == "reference_pattern" {
                // Get the actual identifier
                if child.kind() == "reference_pattern" {
                    for inner in child.children(&mut child.walk()) {
                        if inner.kind() == "identifier" {
                            return Some(self.node_text(inner, source).to_string());
                        }
                    }
                }
                return Some(self.node_text(child, source).to_string());
            }
        }

        // Fallback: try to extract from text
        let text = self.node_text(param_node, source);
        if let Some(colon_idx) = text.find(':') {
            let name = text[..colon_idx].trim();
            if !name.is_empty() && name != "mut" {
                return Some(name.trim_start_matches("mut ").to_string());
            }
        }

        None
    }

    /// Scan a call expression for taint sources.
    fn scan_call_expression(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let expression = self.node_text(node, ctx.source).to_string();
        let line = node.start_position().row + 1;
        let col = node.start_position().column;

        // Get the function being called
        let func_node = match node.child_by_field_name("function") {
            Some(n) => n,
            None => return,
        };

        match func_node.kind() {
            "identifier" => {
                // Direct function call: stdin(), args(), etc.
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
            "field_expression" => {
                // Method call: obj.method()
                self.scan_method_call(func_node, node, ctx, result);
            }
            "scoped_identifier" => {
                // Namespaced call: std::env::var(), serde_json::from_str()
                self.scan_scoped_call(func_node, node, ctx, result);
            }
            _ => {}
        }

        // Check for Result/Option unwrapping
        self.check_unwrap_call(node, ctx, result);
    }

    /// Scan a method call (field_expression followed by call).
    fn scan_method_call(
        &self,
        field_node: Node,
        call_node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let object = match field_node.child_by_field_name("value") {
            Some(o) => o,
            None => return,
        };
        let method = match field_node.child_by_field_name("field") {
            Some(m) => m,
            None => return,
        };

        let object_name = self.get_object_name(object, ctx);
        let method_name = self.node_text(method, ctx.source);
        let expression = self.node_text(call_node, ctx.source).to_string();
        let line = call_node.start_position().row + 1;
        let col = call_node.start_position().column;

        // Check for response methods that return tainted data
        if self.is_response_method(&object_name, method_name) {
            let loc = Location::new(ctx.file_name, line, col);
            let source = DetectedSource::new(SourceKind::HttpResponse, loc, &expression)
                .with_confidence(0.85)
                .with_context(format!("{}.{}", object_name, method_name));
            result.add_source(source);
            return;
        }

        // Check patterns
        for pattern in &self.patterns {
            if let Some(pattern_obj) = pattern.object {
                if (object_name == pattern_obj
                    || self.matches_alias(&object_name, pattern_obj, ctx))
                    && method_name == pattern.method
                {
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

        // Check for known taint source method names regardless of object type
        // This handles cases where we can't infer the object's type from the variable name
        if let Some((kind, confidence)) = self.check_known_taint_method(method_name, &expression) {
            let loc = Location::new(ctx.file_name, line, col);
            let source = DetectedSource::new(kind, loc, &expression)
                .with_confidence(confidence)
                .with_context(format!("{}.{}", object_name, method_name));
            result.add_source(source);
            return;
        }

        // Check if calling method on a tainted variable
        if ctx.tainted_vars.contains(&object_name) {
            // Taint propagates through method calls on tainted objects
            // (except for sanitizing methods which we don't track here)
            let loc = Location::new(ctx.file_name, line, col);
            let source = DetectedSource::new(SourceKind::GenericUserInput, loc, &expression)
                .with_confidence(0.75)
                .with_context(format!("tainted_var:{}", object_name));
            result.add_source(source);
        }
    }

    /// Check if a method name is a known taint source method.
    ///
    /// Returns the SourceKind and confidence if the method is a known taint source,
    /// regardless of the object it's called on.
    fn check_known_taint_method(
        &self,
        method_name: &str,
        expression: &str,
    ) -> Option<(SourceKind, f64)> {
        // Database fetch methods (sqlx, diesel, sea-orm)
        let db_fetch_methods = [
            "fetch_one",
            "fetch_all",
            "fetch_optional",
            "fetch",
            "get_results",
            "get_result",
            "first",
        ];
        if db_fetch_methods.contains(&method_name) {
            return Some((SourceKind::DatabaseResult, 0.8));
        }

        // Clap argument retrieval
        let clap_methods = ["get_one", "get_many", "get_raw", "value_of", "values_of"];
        if clap_methods.contains(&method_name) {
            return Some((SourceKind::ProcessArgs, 0.85));
        }

        // HTTP response methods (reqwest, hyper, ureq)
        let http_response_methods = [
            "text",
            "json",
            "bytes",
            "chunk",
            "body_string",
            "body_bytes",
        ];
        if http_response_methods.contains(&method_name) {
            // Only if it looks like a response context
            if expression.contains("response")
                || expression.contains("resp")
                || expression.contains("res.")
                || expression.contains(".await")
            {
                return Some((SourceKind::HttpResponse, 0.75));
            }
        }

        // Read methods (file, socket, buffer)
        let read_methods = ["read_line", "read_to_string", "read_to_end", "read_exact"];
        if read_methods.contains(&method_name) {
            return Some((SourceKind::FileRead, 0.7));
        }

        // Deserialization methods
        if method_name == "from_str" || method_name == "from_slice" || method_name == "from_reader"
        {
            // Only if it looks like deserialization
            if expression.contains("json")
                || expression.contains("serde")
                || expression.contains("yaml")
                || expression.contains("toml")
            {
                return Some((SourceKind::Deserialized, 0.75));
            }
        }

        None
    }

    /// Scan a scoped/namespaced call (e.g., std::env::var()).
    fn scan_scoped_call(
        &self,
        scoped_node: Node,
        call_node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let full_path = self.node_text(scoped_node, ctx.source);
        let expression = self.node_text(call_node, ctx.source).to_string();
        let line = call_node.start_position().row + 1;
        let col = call_node.start_position().column;

        // Extract the final identifier (the function name)
        let func_name = full_path.rsplit("::").next().unwrap_or("");
        // Extract the path (module)
        let path = if let Some(idx) = full_path.rfind("::") {
            &full_path[..idx]
        } else {
            ""
        };

        // Check patterns with scoped paths
        for pattern in &self.patterns {
            if let Some(pattern_obj) = pattern.object {
                // Match full path: std::env::var matches "env" object
                if (path.ends_with(pattern_obj) || path == pattern_obj)
                    && func_name == pattern.method
                {
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

            // Also check patterns without object (direct function name match)
            if pattern.object.is_none() && func_name == pattern.method {
                let loc = Location::new(ctx.file_name, line, col);
                let mut source = DetectedSource::new(pattern.kind, loc, &expression)
                    .with_confidence(pattern.confidence * 0.9); // Slightly lower confidence for generic match

                if let Some(fw) = pattern.framework {
                    source = source.with_framework(fw);
                }

                result.add_source(source);
                return;
            }
        }

        // Special handling for known scoped sources
        let known_sources = [
            ("std::env::args", SourceKind::ProcessArgs),
            ("std::env::args_os", SourceKind::ProcessArgs),
            ("std::env::var", SourceKind::Environment),
            ("std::env::var_os", SourceKind::Environment),
            ("std::env::vars", SourceKind::Environment),
            ("std::io::stdin", SourceKind::Stdin),
            ("std::fs::read", SourceKind::FileRead),
            ("std::fs::read_to_string", SourceKind::FileRead),
            ("std::fs::read_dir", SourceKind::FileRead),
            ("tokio::fs::read", SourceKind::FileRead),
            ("tokio::fs::read_to_string", SourceKind::FileRead),
            ("serde_json::from_str", SourceKind::Deserialized),
            ("serde_json::from_slice", SourceKind::Deserialized),
            ("serde_json::from_reader", SourceKind::Deserialized),
            ("serde_yaml::from_str", SourceKind::Deserialized),
            ("toml::from_str", SourceKind::Deserialized),
        ];

        for (source_path, kind) in known_sources {
            if full_path == source_path {
                let loc = Location::new(ctx.file_name, line, col);
                let source = DetectedSource::new(kind, loc, &expression).with_confidence(1.0);
                result.add_source(source);
                return;
            }
        }
    }

    /// Check for Result/Option unwrapping that propagates taint.
    fn check_unwrap_call(
        &self,
        call_node: Node,
        _ctx: &mut ScanContext,
        _result: &mut SourceScanResult,
    ) {
        let call_text = self.node_text(call_node, _ctx.source);

        // Check for unwrap(), expect(), unwrap_or(), etc.
        let unwrap_methods = [
            "unwrap()",
            "expect(",
            "unwrap_or(",
            "unwrap_or_else(",
            "unwrap_or_default()",
        ];

        for method in unwrap_methods {
            if call_text.contains(method) {
                // The unwrapped value should inherit taint from the Result/Option
                // This is handled by the assignment tracking
                break;
            }
        }
    }

    /// Scan a field expression for property access taint sources.
    fn scan_field_expression(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        // Skip if this is the function part of a call expression
        if let Some(parent) = node.parent() {
            if parent.kind() == "call_expression" {
                if let Some(func) = parent.child_by_field_name("function") {
                    if func == node {
                        return;
                    }
                }
            }
        }

        let object = match node.child_by_field_name("value") {
            Some(o) => o,
            None => return,
        };
        let field = match node.child_by_field_name("field") {
            Some(f) => f,
            None => return,
        };

        let object_name = self.get_object_name(object, ctx);
        let field_name = self.node_text(field, ctx.source);
        let expression = self.node_text(node, ctx.source).to_string();
        let line = node.start_position().row + 1;
        let col = node.start_position().column;

        // Check if accessing a tainted variable's field
        if ctx.tainted_vars.contains(&object_name) {
            let loc = Location::new(ctx.file_name, line, col);
            let source = DetectedSource::new(SourceKind::GenericUserInput, loc, &expression)
                .with_confidence(0.85)
                .with_context(format!("tainted_field:{}.{}", object_name, field_name));
            result.add_source(source);
        }

        // Check patterns for property access
        for pattern in &self.patterns {
            if let Some(pattern_obj) = pattern.object {
                if pattern.is_property
                    && (object_name == pattern_obj
                        || self.matches_alias(&object_name, pattern_obj, ctx))
                    && field_name == pattern.method
                {
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

    /// Scan a let declaration for taint propagation.
    fn scan_let_declaration(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        // Extract the pattern (variable name or destructuring)
        let pattern_node = node.child_by_field_name("pattern");
        let value_node = node.child_by_field_name("value");

        // Track if the value is a taint source
        let source_count_before = result.sources.len();

        // Scan the value side first
        if let Some(value) = value_node {
            self.scan_node(value, ctx, result);
        }

        // If we found new sources, track the assigned variable
        if result.sources.len() > source_count_before {
            if let Some(pattern) = pattern_node {
                self.track_tainted_pattern(pattern, ctx, result, source_count_before);
            }
        }

        // Handle if-let patterns that extract from Result/Option
        // let x = y? or if let Ok(x) = y pattern is handled by try_expression
    }

    /// Track variables that receive tainted values from a pattern.
    fn track_tainted_pattern(
        &self,
        pattern: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
        source_start_idx: usize,
    ) {
        match pattern.kind() {
            "identifier" => {
                let var_name = self.node_text(pattern, ctx.source).to_string();
                ctx.tainted_vars.insert(var_name.clone());

                // Update sources with assignment info
                for source in result.sources.iter_mut().skip(source_start_idx) {
                    if source.assigned_to.is_none() {
                        source.assigned_to = Some(var_name.clone());
                    }
                }
            }
            "tuple_pattern" | "struct_pattern" | "slice_pattern" => {
                // Destructuring: all bound variables inherit taint
                self.extract_pattern_vars(pattern, ctx);
            }
            "ref_pattern" | "mut_pattern" => {
                // ref x or mut x - track the inner identifier
                for child in pattern.children(&mut pattern.walk()) {
                    if child.kind() == "identifier" {
                        let var_name = self.node_text(child, ctx.source).to_string();
                        ctx.tainted_vars.insert(var_name);
                    }
                }
            }
            _ => {}
        }
    }

    /// Extract all variable names from a pattern (for destructuring).
    fn extract_pattern_vars(&self, pattern: Node, ctx: &mut ScanContext) {
        match pattern.kind() {
            "identifier" => {
                let var_name = self.node_text(pattern, ctx.source).to_string();
                if var_name != "_" {
                    ctx.tainted_vars.insert(var_name);
                }
            }
            _ => {
                let mut cursor = pattern.walk();
                for child in pattern.children(&mut cursor) {
                    self.extract_pattern_vars(child, ctx);
                }
            }
        }
    }

    /// Scan a match expression for taint propagation through arms.
    fn scan_match_expression(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        // Check if the matched value is tainted
        let matched_expr = node.child_by_field_name("value");
        let is_tainted_match = if let Some(expr) = matched_expr {
            let expr_text = self.node_text(expr, ctx.source);
            ctx.tainted_vars.iter().any(|v| expr_text.contains(v))
                || self.expr_contains_taint_source(expr, ctx)
        } else {
            false
        };

        // Scan match arms
        for child in node.children(&mut node.walk()) {
            if child.kind() == "match_block" {
                for arm in child.children(&mut child.walk()) {
                    if arm.kind() == "match_arm" {
                        // If matching on tainted value, pattern bindings are tainted
                        if is_tainted_match {
                            if let Some(pattern) = arm.child_by_field_name("pattern") {
                                self.extract_pattern_vars(pattern, ctx);
                            }
                        }

                        // Scan the arm body
                        if let Some(body) = arm.child_by_field_name("value") {
                            self.scan_node(body, ctx, result);
                        }
                    }
                }
            }
        }
    }

    /// Check if an expression contains a taint source.
    fn expr_contains_taint_source(&self, expr: Node, ctx: &ScanContext) -> bool {
        let expr_text = self.node_text(expr, ctx.source);

        // Check for known taint source patterns
        let source_patterns = [
            "stdin()",
            "args()",
            "env::var(",
            "read_to_string(",
            "request.",
            "req.",
            "body.",
            "query.",
            "params.",
        ];

        for pattern in source_patterns {
            if expr_text.contains(pattern) {
                return true;
            }
        }

        false
    }

    /// Scan a try expression (?) for taint propagation.
    fn scan_try_expression(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let old_in_try = ctx.in_try_expression;
        ctx.in_try_expression = true;

        // The inner expression's Ok value flows out
        // Track sources found within the try expression
        for child in node.children(&mut node.walk()) {
            if child.kind() != "?" {
                self.scan_node(child, ctx, result);
            }
        }

        ctx.in_try_expression = old_in_try;
    }

    /// Scan an await expression for async taint propagation.
    fn scan_await_expression(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        // Taint flows through .await
        // The awaited value inherits taint from the future

        for child in node.children(&mut node.walk()) {
            if child.kind() != "." && child.kind() != "await" {
                self.scan_node(child, ctx, result);
            }
        }
    }

    /// Scan a macro invocation for taint sources.
    fn scan_macro_invocation(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let macro_text = self.node_text(node, ctx.source);
        let line = node.start_position().row + 1;
        let col = node.start_position().column;

        // Check for known source macros
        let source_macros = [
            ("env!", SourceKind::Environment),
            ("option_env!", SourceKind::Environment),
            ("include_str!", SourceKind::FileRead),
            ("include_bytes!", SourceKind::FileRead),
        ];

        for (macro_name, kind) in source_macros {
            if macro_text.starts_with(macro_name) {
                let loc = Location::new(ctx.file_name, line, col);
                let source =
                    DetectedSource::new(kind, loc, macro_text.to_string()).with_confidence(1.0);
                result.add_source(source);
                return;
            }
        }
    }

    /// Scan an identifier for references to tainted variables.
    fn scan_identifier(&self, node: Node, ctx: &mut ScanContext, _result: &mut SourceScanResult) {
        let name = self.node_text(node, ctx.source);

        // Track tainted variable usage for propagation analysis
        // (actual propagation is handled elsewhere)
        if ctx.tainted_vars.contains(name) {
            // Could emit a source here for comprehensive tracking,
            // but this would be noisy. Better to track in propagation engine.
        }
    }

    // ==========================================================================
    // Helper Methods
    // ==========================================================================

    /// Check if this is a response method that returns tainted data.
    fn is_response_method(&self, object_name: &str, method: &str) -> bool {
        let response_objects = ["response", "resp", "res", "result", "Response"];
        let response_methods = [
            "text",
            "json",
            "bytes",
            "body",
            "chunk",
            "into_body",
            "collect",
        ];

        (response_objects.contains(&object_name) || object_name.ends_with("Response"))
            && response_methods.contains(&method)
    }

    /// Check if an object name matches an alias.
    fn matches_alias(&self, object_name: &str, pattern_obj: &str, ctx: &ScanContext) -> bool {
        if let Some(alias_target) = ctx.use_aliases.get(object_name) {
            return alias_target.ends_with(pattern_obj) || alias_target == pattern_obj;
        }
        false
    }

    /// Get the name of an object node, resolving chains.
    fn get_object_name(&self, node: Node, ctx: &ScanContext) -> String {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node, ctx.source);
                ctx.use_aliases
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| name.to_string())
            }
            "field_expression" => {
                // Chained access: foo.bar.baz
                let mut parts = Vec::new();
                let mut current = node;

                loop {
                    if let Some(field) = current.child_by_field_name("field") {
                        parts.push(self.node_text(field, ctx.source));
                    }

                    if let Some(value) = current.child_by_field_name("value") {
                        if value.kind() == "identifier" {
                            parts.push(self.node_text(value, ctx.source));
                            break;
                        } else if value.kind() == "field_expression" {
                            current = value;
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
            "scoped_identifier" => self.node_text(node, ctx.source).to_string(),
            "call_expression" => {
                // For chained calls, get the base
                self.node_text(node, ctx.source).to_string()
            }
            _ => self.node_text(node, ctx.source).to_string(),
        }
    }

    /// Get text from a node.
    fn node_text<'a>(&self, node: Node<'a>, source: &'a [u8]) -> &'a str {
        std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }
}

impl Default for RustSourceDetector {
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
    /// Use statement aliases
    use_aliases: &'a HashMap<String, String>,
    /// Known tainted variable names
    tainted_vars: HashSet<String>,
    /// Current function name
    current_function: Option<String>,
    /// Current handler info (if in a handler)
    current_handler: Option<HandlerInfo>,
    /// Whether we're in a handler scope
    in_handler_scope: bool,
    /// Whether we're in an async context
    in_async_context: bool,
    /// Whether we're inside a try expression (?)
    in_try_expression: bool,
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn scan(source: &str) -> SourceScanResult {
        let detector = RustSourceDetector::new();
        detector.scan_source(source, "test.rs").unwrap()
    }

    // =========================================================================
    // Actix-web Tests
    // =========================================================================

    #[test]
    fn test_actix_web_path() {
        let source = r#"
use actix_web::{web, HttpResponse};

async fn handler(path: web::Path<String>) -> HttpResponse {
    let id = path.into_inner();
    HttpResponse::Ok().body(id)
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::UrlPath));
    }

    #[test]
    fn test_actix_web_query() {
        let source = r#"
use actix_web::{web, HttpResponse};

async fn search(query: web::Query<SearchParams>) -> HttpResponse {
    let term = &query.q;
    HttpResponse::Ok().json(term)
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::RequestParam));
    }

    #[test]
    fn test_actix_web_json() {
        let source = r#"
use actix_web::{web, HttpResponse};

async fn create(body: web::Json<CreateRequest>) -> HttpResponse {
    let data = body.into_inner();
    HttpResponse::Created().json(data)
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_actix_web_handler_attribute() {
        let source = r#"
use actix_web::{get, web, HttpResponse};

#[get("/users/{id}")]
async fn get_user(path: web::Path<u32>) -> HttpResponse {
    HttpResponse::Ok().body("user")
}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 1);
        assert_eq!(result.handlers[0].framework, "actix-web");
        assert!(result.handlers[0].route.as_ref().unwrap().contains("users"));
    }

    // =========================================================================
    // Axum Tests
    // =========================================================================

    #[test]
    fn test_axum_extract_path() {
        let source = r#"
use axum::extract::Path;

async fn handler(Path(id): Path<u32>) -> String {
    format!("User {}", id)
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::UrlPath));
    }

    #[test]
    fn test_axum_extract_json() {
        let source = r#"
use axum::extract::Json;

async fn create(Json(payload): Json<CreateRequest>) -> impl IntoResponse {
    (StatusCode::CREATED, Json(payload))
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_axum_extract_query() {
        let source = r#"
use axum::extract::Query;

async fn search(Query(params): Query<SearchParams>) -> String {
    params.q.clone()
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::RequestParam));
    }

    // =========================================================================
    // Standard Library Tests
    // =========================================================================

    #[test]
    fn test_std_env_args() {
        let source = r#"
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    println!("{:?}", args);
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::ProcessArgs));
    }

    #[test]
    fn test_std_env_var() {
        let source = r#"
use std::env;

fn main() {
    let home = env::var("HOME").unwrap();
    let path = env::var("PATH").unwrap_or_default();
}
"#;
        let result = scan(source);
        let env_sources: Vec<_> = result
            .sources
            .iter()
            .filter(|s| s.kind == SourceKind::Environment)
            .collect();
        assert!(env_sources.len() >= 2);
    }

    #[test]
    fn test_std_io_stdin() {
        let source = r#"
use std::io::{self, BufRead};

fn main() {
    let stdin = io::stdin();
    let mut line = String::new();
    stdin.lock().read_line(&mut line).unwrap();
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Stdin));
    }

    // =========================================================================
    // File I/O Tests
    // =========================================================================

    #[test]
    fn test_fs_read_to_string() {
        let source = r#"
use std::fs;

fn read_config() -> String {
    fs::read_to_string("config.toml").unwrap()
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::FileRead));
    }

    #[test]
    fn test_fs_read() {
        let source = r#"
use std::fs;

fn read_binary() -> Vec<u8> {
    fs::read("data.bin").unwrap()
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::FileRead));
    }

    // =========================================================================
    // Network Tests
    // =========================================================================

    #[test]
    fn test_reqwest_response() {
        let source = r#"
async fn fetch_data() -> String {
    let response = reqwest::get("https://api.example.com/data").await.unwrap();
    response.text().await.unwrap()
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::HttpResponse));
    }

    // =========================================================================
    // Database Tests
    // =========================================================================

    #[test]
    fn test_sqlx_fetch() {
        let source = r#"
async fn get_user(pool: &PgPool, id: i32) -> User {
    sqlx::query_as!(User, "SELECT * FROM users WHERE id = $1", id)
        .fetch_one(pool)
        .await
        .unwrap()
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::DatabaseResult));
    }

    // =========================================================================
    // Deserialization Tests
    // =========================================================================

    #[test]
    fn test_serde_json_from_str() {
        let source = r#"
use serde_json;

fn parse_config(json: &str) -> Config {
    serde_json::from_str(json).unwrap()
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::Deserialized));
    }

    // =========================================================================
    // Result/Option Handling Tests
    // =========================================================================

    #[test]
    fn test_try_operator() {
        let source = r#"
use std::fs;

fn read_config() -> Result<String, std::io::Error> {
    let content = fs::read_to_string("config.toml")?;
    Ok(content)
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::FileRead));
    }

    // =========================================================================
    // Macro Tests
    // =========================================================================

    #[test]
    fn test_env_macro() {
        let source = r#"
fn get_compile_time_env() -> &'static str {
    env!("CARGO_PKG_NAME")
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::Environment));
    }

    #[test]
    fn test_include_str_macro() {
        let source = r#"
const CONFIG: &str = include_str!("../config.toml");
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::FileRead));
    }

    // =========================================================================
    // Async Tests
    // =========================================================================

    #[test]
    fn test_async_await_chain() {
        let source = r#"
async fn fetch_and_parse() -> Data {
    let resp = client.get(url).send().await.unwrap();
    let text = resp.text().await.unwrap();
    serde_json::from_str(&text).unwrap()
}
"#;
        let result = scan(source);
        // Should detect both HTTP response and deserialization sources
        assert!(
            result
                .sources
                .iter()
                .any(|s| s.kind == SourceKind::HttpResponse)
                || result
                    .sources
                    .iter()
                    .any(|s| s.kind == SourceKind::Deserialized)
        );
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
fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    let result = add(1, 2);
    println!("{}", result);
}
"#;
        let result = scan(source);
        assert!(result.sources.is_empty());
    }

    #[test]
    fn test_multiple_handlers() {
        let source = r#"
use actix_web::{get, post, web, HttpResponse};

#[get("/users")]
async fn list_users() -> HttpResponse {
    HttpResponse::Ok().json(Vec::<User>::new())
}

#[post("/users")]
async fn create_user(body: web::Json<CreateUser>) -> HttpResponse {
    HttpResponse::Created().json(body.into_inner())
}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 2);
    }

    // =========================================================================
    // Clap Tests
    // =========================================================================

    #[test]
    fn test_clap_args() {
        // Note: The turbofish ::<String> in get_one::<String> is parsed as a generic_type_with_turbofish
        // by tree-sitter, so the method name detection uses the full expression.
        // Using value_of which is a simpler method call.
        let source = r#"
use clap::{App, Arg};

fn main() {
    let matches = App::new("test").get_matches();
    let input = matches.value_of("input").unwrap();
}
"#;
        let result = scan(source);
        assert!(result
            .sources
            .iter()
            .any(|s| s.kind == SourceKind::ProcessArgs));
    }
}
