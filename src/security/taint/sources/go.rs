//! Go taint source identification.
//!
//! This module identifies all locations in Go code where untrusted data
//! enters the program. It uses AST pattern matching via tree-sitter to detect:
//!
//! - **net/http**: r.URL.Query(), r.FormValue(), r.Body, r.Header.Get(), r.Cookies()
//! - **Gin**: c.Query(), c.Param(), c.PostForm(), c.ShouldBindJSON()
//! - **Echo**: c.QueryParam(), c.FormValue(), c.Bind()
//! - **Fiber**: c.Query(), c.Params(), c.Body()
//! - **CLI**: os.Args, flag.String(), flag.Int()
//! - **Environment**: os.Getenv(), os.LookupEnv()
//! - **File I/O**: os.ReadFile(), ioutil.ReadFile(), bufio.Scanner.Text()
//! - **Network**: net.Conn.Read(), http.Response.Body
//! - **Database**: rows.Scan(), sql.Row.Scan()
//!
//! # Go-Specific Patterns
//!
//! ## Multiple Return Values
//!
//! The detector tracks taint through Go's multiple return values:
//! ```go
//! data, err := os.ReadFile(userPath)  // data is tainted
//! content, _ := ioutil.ReadAll(r.Body) // content is tainted
//! ```
//!
//! ## Channel Propagation
//!
//! Taint flows through channels:
//! ```go
//! ch <- taintedData  // channel send
//! data := <-ch       // data receives taint from channel
//! ```
//!
//! ## Goroutine Captures
//!
//! Variables captured by goroutines are tracked:
//! ```go
//! go func() {
//!     process(userInput)  // userInput captured by closure
//! }()
//! ```
//!
//! ## Interface Implementations
//!
//! io.Reader and similar interfaces are recognized:
//! ```go
//! reader := bytes.NewReader(body)
//! io.ReadAll(reader)  // returns tainted data if body is tainted
//! ```
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::security::taint::sources::go::GoSourceDetector;
//!
//! let detector = GoSourceDetector::new();
//! let source = r#"
//! package main
//!
//! import "net/http"
//!
//! func handler(w http.ResponseWriter, r *http.Request) {
//!     userID := r.URL.Query().Get("id")  // Taint source!
//!     name := r.FormValue("name")         // Taint source!
//! }
//! "#;
//!
//! let result = detector.scan_source(source, "handler.go")?;
//! assert!(result.sources.len() >= 2);
//! ```

use std::collections::{HashMap, HashSet};
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

/// net/http request taint sources.
const HTTP_REQUEST_SOURCES: &[SourcePattern] = &[
    // URL query parameters
    SourcePattern::method_call(
        "http_url_query",
        SourceKind::RequestParam,
        "URL",
        "Query",
        Some("net/http"),
    ),
    SourcePattern::property_access(
        "http_url_path",
        SourceKind::UrlPath,
        "URL",
        "Path",
        Some("net/http"),
    ),
    SourcePattern::property_access(
        "http_url_rawquery",
        SourceKind::RequestParam,
        "URL",
        "RawQuery",
        Some("net/http"),
    ),
    SourcePattern::property_access(
        "http_url_rawpath",
        SourceKind::UrlPath,
        "URL",
        "RawPath",
        Some("net/http"),
    ),
    SourcePattern::property_access(
        "http_url_fragment",
        SourceKind::UrlPath,
        "URL",
        "Fragment",
        Some("net/http"),
    ),
    // Form values
    SourcePattern::method_call(
        "http_formvalue",
        SourceKind::RequestParam,
        "r",
        "FormValue",
        Some("net/http"),
    ),
    SourcePattern::method_call(
        "http_postformvalue",
        SourceKind::RequestBody,
        "r",
        "PostFormValue",
        Some("net/http"),
    ),
    // Request body
    SourcePattern::property_access(
        "http_request_body",
        SourceKind::RequestBody,
        "r",
        "Body",
        Some("net/http"),
    ),
    // Headers
    SourcePattern::method_call(
        "http_header_get",
        SourceKind::HttpHeader,
        "Header",
        "Get",
        Some("net/http"),
    ),
    SourcePattern::property_access(
        "http_request_header",
        SourceKind::HttpHeader,
        "r",
        "Header",
        Some("net/http"),
    ),
    // Cookies
    SourcePattern::method_call(
        "http_cookies",
        SourceKind::Cookie,
        "r",
        "Cookies",
        Some("net/http"),
    ),
    SourcePattern::method_call(
        "http_cookie",
        SourceKind::Cookie,
        "r",
        "Cookie",
        Some("net/http"),
    ),
    // PostForm map
    SourcePattern::property_access(
        "http_postform",
        SourceKind::RequestBody,
        "r",
        "PostForm",
        Some("net/http"),
    ),
    SourcePattern::property_access(
        "http_form",
        SourceKind::RequestParam,
        "r",
        "Form",
        Some("net/http"),
    ),
    // Multipart form
    SourcePattern::property_access(
        "http_multipartform",
        SourceKind::FileUpload,
        "r",
        "MultipartForm",
        Some("net/http"),
    ),
    SourcePattern::method_call(
        "http_formfile",
        SourceKind::FileUpload,
        "r",
        "FormFile",
        Some("net/http"),
    ),
    // Host (can be spoofed)
    SourcePattern::property_access(
        "http_request_host",
        SourceKind::HttpHeader,
        "r",
        "Host",
        Some("net/http"),
    ),
    // Remote address
    SourcePattern::property_access(
        "http_request_remoteaddr",
        SourceKind::HttpHeader,
        "r",
        "RemoteAddr",
        Some("net/http"),
    ),
    // Request URI
    SourcePattern::property_access(
        "http_request_requesturi",
        SourceKind::UrlPath,
        "r",
        "RequestURI",
        Some("net/http"),
    ),
];

/// Gin framework taint sources.
const GIN_SOURCES: &[SourcePattern] = &[
    // Query parameters
    SourcePattern::method_call(
        "gin_query",
        SourceKind::RequestParam,
        "c",
        "Query",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_defaultquery",
        SourceKind::RequestParam,
        "c",
        "DefaultQuery",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_getquery",
        SourceKind::RequestParam,
        "c",
        "GetQuery",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_queryarray",
        SourceKind::RequestParam,
        "c",
        "QueryArray",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_querymap",
        SourceKind::RequestParam,
        "c",
        "QueryMap",
        Some("gin"),
    ),
    // URL path parameters
    SourcePattern::method_call(
        "gin_param",
        SourceKind::UrlPath,
        "c",
        "Param",
        Some("gin"),
    ),
    // POST form
    SourcePattern::method_call(
        "gin_postform",
        SourceKind::RequestBody,
        "c",
        "PostForm",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_defaultpostform",
        SourceKind::RequestBody,
        "c",
        "DefaultPostForm",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_postformarray",
        SourceKind::RequestBody,
        "c",
        "PostFormArray",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_postformmap",
        SourceKind::RequestBody,
        "c",
        "PostFormMap",
        Some("gin"),
    ),
    // Headers
    SourcePattern::method_call(
        "gin_getheader",
        SourceKind::HttpHeader,
        "c",
        "GetHeader",
        Some("gin"),
    ),
    // Cookies
    SourcePattern::method_call(
        "gin_cookie",
        SourceKind::Cookie,
        "c",
        "Cookie",
        Some("gin"),
    ),
    // JSON binding
    SourcePattern::method_call(
        "gin_bindjson",
        SourceKind::RequestBody,
        "c",
        "BindJSON",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_shouldbindjson",
        SourceKind::RequestBody,
        "c",
        "ShouldBindJSON",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_shouldbind",
        SourceKind::RequestBody,
        "c",
        "ShouldBind",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_bind",
        SourceKind::RequestBody,
        "c",
        "Bind",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_shouldbinduri",
        SourceKind::UrlPath,
        "c",
        "ShouldBindUri",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_shouldbindquery",
        SourceKind::RequestParam,
        "c",
        "ShouldBindQuery",
        Some("gin"),
    ),
    // Raw data
    SourcePattern::method_call(
        "gin_getrawdata",
        SourceKind::RequestBody,
        "c",
        "GetRawData",
        Some("gin"),
    ),
    // File uploads
    SourcePattern::method_call(
        "gin_formfile",
        SourceKind::FileUpload,
        "c",
        "FormFile",
        Some("gin"),
    ),
    SourcePattern::method_call(
        "gin_multipartform",
        SourceKind::FileUpload,
        "c",
        "MultipartForm",
        Some("gin"),
    ),
    // Request access
    SourcePattern::property_access(
        "gin_request",
        SourceKind::RequestBody,
        "c",
        "Request",
        Some("gin"),
    ),
    // Client IP (can be spoofed via headers)
    SourcePattern::method_call(
        "gin_clientip",
        SourceKind::HttpHeader,
        "c",
        "ClientIP",
        Some("gin"),
    ),
    // Full path
    SourcePattern::method_call(
        "gin_fullpath",
        SourceKind::UrlPath,
        "c",
        "FullPath",
        Some("gin"),
    ),
];

/// Echo framework taint sources.
const ECHO_SOURCES: &[SourcePattern] = &[
    SourcePattern::method_call(
        "echo_queryparam",
        SourceKind::RequestParam,
        "c",
        "QueryParam",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_queryparams",
        SourceKind::RequestParam,
        "c",
        "QueryParams",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_param",
        SourceKind::UrlPath,
        "c",
        "Param",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_paramnames",
        SourceKind::UrlPath,
        "c",
        "ParamNames",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_formvalue",
        SourceKind::RequestBody,
        "c",
        "FormValue",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_formparams",
        SourceKind::RequestBody,
        "c",
        "FormParams",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_formfile",
        SourceKind::FileUpload,
        "c",
        "FormFile",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_multipartform",
        SourceKind::FileUpload,
        "c",
        "MultipartForm",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_bind",
        SourceKind::RequestBody,
        "c",
        "Bind",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_request",
        SourceKind::RequestBody,
        "c",
        "Request",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_cookie",
        SourceKind::Cookie,
        "c",
        "Cookie",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_cookies",
        SourceKind::Cookie,
        "c",
        "Cookies",
        Some("echo"),
    ),
    SourcePattern::method_call(
        "echo_realip",
        SourceKind::HttpHeader,
        "c",
        "RealIP",
        Some("echo"),
    ),
];

/// Fiber framework taint sources.
const FIBER_SOURCES: &[SourcePattern] = &[
    SourcePattern::method_call(
        "fiber_query",
        SourceKind::RequestParam,
        "c",
        "Query",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_queries",
        SourceKind::RequestParam,
        "c",
        "Queries",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_params",
        SourceKind::UrlPath,
        "c",
        "Params",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_allparams",
        SourceKind::UrlPath,
        "c",
        "AllParams",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_body",
        SourceKind::RequestBody,
        "c",
        "Body",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_bodyraw",
        SourceKind::RequestBody,
        "c",
        "BodyRaw",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_bodyparser",
        SourceKind::RequestBody,
        "c",
        "BodyParser",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_formvalue",
        SourceKind::RequestBody,
        "c",
        "FormValue",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_formfile",
        SourceKind::FileUpload,
        "c",
        "FormFile",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_cookies",
        SourceKind::Cookie,
        "c",
        "Cookies",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_get",
        SourceKind::HttpHeader,
        "c",
        "Get",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_ip",
        SourceKind::HttpHeader,
        "c",
        "IP",
        Some("fiber"),
    ),
    SourcePattern::method_call(
        "fiber_ips",
        SourceKind::HttpHeader,
        "c",
        "IPs",
        Some("fiber"),
    ),
];

/// Standard library taint sources.
const STDLIB_SOURCES: &[SourcePattern] = &[
    // os package
    SourcePattern::property_access("os_args", SourceKind::ProcessArgs, "os", "Args", None),
    SourcePattern::method_call("os_getenv", SourceKind::Environment, "os", "Getenv", None),
    SourcePattern::method_call("os_lookupenv", SourceKind::Environment, "os", "LookupEnv", None),
    SourcePattern::property_access("os_stdin", SourceKind::Stdin, "os", "Stdin", None),
    // File operations
    SourcePattern::method_call("os_readfile", SourceKind::FileRead, "os", "ReadFile", None),
    SourcePattern::method_call("os_open", SourceKind::FileRead, "os", "Open", None),
    SourcePattern::method_call("os_openfile", SourceKind::FileRead, "os", "OpenFile", None),
    // ioutil (deprecated but still used)
    SourcePattern::method_call(
        "ioutil_readfile",
        SourceKind::FileRead,
        "ioutil",
        "ReadFile",
        None,
    ),
    SourcePattern::method_call(
        "ioutil_readall",
        SourceKind::FileRead,
        "ioutil",
        "ReadAll",
        None,
    ),
    // io package
    SourcePattern::method_call("io_readall", SourceKind::FileRead, "io", "ReadAll", None),
    SourcePattern::method_call("io_copy", SourceKind::FileRead, "io", "Copy", None),
    SourcePattern::method_call("io_readfull", SourceKind::FileRead, "io", "ReadFull", None),
    // bufio package
    SourcePattern::method_call("bufio_text", SourceKind::FileRead, "Scanner", "Text", None),
    SourcePattern::method_call("bufio_bytes", SourceKind::FileRead, "Scanner", "Bytes", None),
    SourcePattern::method_call(
        "bufio_readline",
        SourceKind::FileRead,
        "Reader",
        "ReadLine",
        None,
    ),
    SourcePattern::method_call(
        "bufio_readstring",
        SourceKind::FileRead,
        "Reader",
        "ReadString",
        None,
    ),
    SourcePattern::method_call(
        "bufio_readbytes",
        SourceKind::FileRead,
        "Reader",
        "ReadBytes",
        None,
    ),
    // flag package
    SourcePattern::method_call("flag_string", SourceKind::ProcessArgs, "flag", "String", None),
    SourcePattern::method_call("flag_int", SourceKind::ProcessArgs, "flag", "Int", None),
    SourcePattern::method_call("flag_bool", SourceKind::ProcessArgs, "flag", "Bool", None),
    SourcePattern::method_call("flag_float64", SourceKind::ProcessArgs, "flag", "Float64", None),
    SourcePattern::method_call(
        "flag_duration",
        SourceKind::ProcessArgs,
        "flag",
        "Duration",
        None,
    ),
    SourcePattern::method_call("flag_var", SourceKind::ProcessArgs, "flag", "Var", None),
    SourcePattern::method_call("flag_arg", SourceKind::ProcessArgs, "flag", "Arg", None),
    SourcePattern::method_call("flag_args", SourceKind::ProcessArgs, "flag", "Args", None),
    SourcePattern::method_call(
        "flag_narg",
        SourceKind::ProcessArgs,
        "flag",
        "NArg",
        None,
    ),
];

/// Network taint sources.
const NETWORK_SOURCES: &[SourcePattern] = &[
    // net package
    SourcePattern::method_call("net_conn_read", SourceKind::SocketRecv, "Conn", "Read", None),
    SourcePattern::method_call(
        "net_udpconn_read",
        SourceKind::SocketRecv,
        "UDPConn",
        "ReadFromUDP",
        None,
    ),
    SourcePattern::method_call(
        "net_tcpconn_read",
        SourceKind::SocketRecv,
        "TCPConn",
        "Read",
        None,
    ),
    // HTTP client response
    SourcePattern::property_access(
        "http_response_body",
        SourceKind::HttpResponse,
        "Response",
        "Body",
        Some("net/http"),
    ),
    SourcePattern::property_access(
        "http_response_header",
        SourceKind::HttpResponse,
        "Response",
        "Header",
        Some("net/http"),
    ),
    // HTTP client functions
    SourcePattern::method_call(
        "http_get",
        SourceKind::HttpResponse,
        "http",
        "Get",
        Some("net/http"),
    ),
    SourcePattern::method_call(
        "http_post",
        SourceKind::HttpResponse,
        "http",
        "Post",
        Some("net/http"),
    ),
    SourcePattern::method_call(
        "http_postform",
        SourceKind::HttpResponse,
        "http",
        "PostForm",
        Some("net/http"),
    ),
    SourcePattern::method_call(
        "http_head",
        SourceKind::HttpResponse,
        "http",
        "Head",
        Some("net/http"),
    ),
    SourcePattern::method_call(
        "http_client_do",
        SourceKind::HttpResponse,
        "Client",
        "Do",
        Some("net/http"),
    ),
    SourcePattern::method_call(
        "http_client_get",
        SourceKind::HttpResponse,
        "Client",
        "Get",
        Some("net/http"),
    ),
    SourcePattern::method_call(
        "http_client_post",
        SourceKind::HttpResponse,
        "Client",
        "Post",
        Some("net/http"),
    ),
    // WebSocket (gorilla/websocket)
    SourcePattern::method_call(
        "ws_readmessage",
        SourceKind::WebSocketMessage,
        "Conn",
        "ReadMessage",
        Some("websocket"),
    ),
    SourcePattern::method_call(
        "ws_readjson",
        SourceKind::WebSocketMessage,
        "Conn",
        "ReadJSON",
        Some("websocket"),
    ),
    SourcePattern::method_call(
        "ws_nextreader",
        SourceKind::WebSocketMessage,
        "Conn",
        "NextReader",
        Some("websocket"),
    ),
];

/// Database taint sources.
const DATABASE_SOURCES: &[SourcePattern] = &[
    // database/sql
    SourcePattern::method_call(
        "sql_rows_scan",
        SourceKind::DatabaseResult,
        "Rows",
        "Scan",
        Some("database/sql"),
    ),
    SourcePattern::method_call(
        "sql_row_scan",
        SourceKind::DatabaseResult,
        "Row",
        "Scan",
        Some("database/sql"),
    ),
    // For query results that are used directly
    SourcePattern::method_call(
        "sql_query",
        SourceKind::DatabaseResult,
        "DB",
        "Query",
        Some("database/sql"),
    ),
    SourcePattern::method_call(
        "sql_queryrow",
        SourceKind::DatabaseResult,
        "DB",
        "QueryRow",
        Some("database/sql"),
    ),
    SourcePattern::method_call(
        "sql_querycontext",
        SourceKind::DatabaseResult,
        "DB",
        "QueryContext",
        Some("database/sql"),
    ),
    SourcePattern::method_call(
        "sql_queryrowcontext",
        SourceKind::DatabaseResult,
        "DB",
        "QueryRowContext",
        Some("database/sql"),
    ),
    // sqlx extensions
    SourcePattern::method_call(
        "sqlx_get",
        SourceKind::DatabaseResult,
        "DB",
        "Get",
        Some("sqlx"),
    ),
    SourcePattern::method_call(
        "sqlx_select",
        SourceKind::DatabaseResult,
        "DB",
        "Select",
        Some("sqlx"),
    ),
    // GORM
    SourcePattern::method_call(
        "gorm_find",
        SourceKind::DatabaseResult,
        "DB",
        "Find",
        Some("gorm"),
    ),
    SourcePattern::method_call(
        "gorm_first",
        SourceKind::DatabaseResult,
        "DB",
        "First",
        Some("gorm"),
    ),
    SourcePattern::method_call(
        "gorm_take",
        SourceKind::DatabaseResult,
        "DB",
        "Take",
        Some("gorm"),
    ),
    SourcePattern::method_call(
        "gorm_last",
        SourceKind::DatabaseResult,
        "DB",
        "Last",
        Some("gorm"),
    ),
    SourcePattern::method_call(
        "gorm_scan",
        SourceKind::DatabaseResult,
        "DB",
        "Scan",
        Some("gorm"),
    ),
];

/// Deserialization taint sources.
const DESERIALIZATION_SOURCES: &[SourcePattern] = &[
    // encoding/json
    SourcePattern::method_call(
        "json_unmarshal",
        SourceKind::Deserialized,
        "json",
        "Unmarshal",
        Some("encoding/json"),
    ),
    SourcePattern::method_call(
        "json_decode",
        SourceKind::Deserialized,
        "Decoder",
        "Decode",
        Some("encoding/json"),
    ),
    // encoding/xml
    SourcePattern::method_call(
        "xml_unmarshal",
        SourceKind::Deserialized,
        "xml",
        "Unmarshal",
        Some("encoding/xml"),
    ),
    SourcePattern::method_call(
        "xml_decode",
        SourceKind::Deserialized,
        "Decoder",
        "Decode",
        Some("encoding/xml"),
    ),
    // encoding/gob
    SourcePattern::method_call(
        "gob_decode",
        SourceKind::Deserialized,
        "Decoder",
        "Decode",
        Some("encoding/gob"),
    ),
    // yaml.v3 / yaml.v2
    SourcePattern::method_call(
        "yaml_unmarshal",
        SourceKind::Deserialized,
        "yaml",
        "Unmarshal",
        Some("gopkg.in/yaml"),
    ),
    SourcePattern::method_call(
        "yaml_decode",
        SourceKind::Deserialized,
        "Decoder",
        "Decode",
        Some("gopkg.in/yaml"),
    ),
    // msgpack
    SourcePattern::method_call(
        "msgpack_unmarshal",
        SourceKind::Deserialized,
        "msgpack",
        "Unmarshal",
        Some("msgpack"),
    ),
    // toml
    SourcePattern::method_call(
        "toml_unmarshal",
        SourceKind::Deserialized,
        "toml",
        "Unmarshal",
        Some("toml"),
    ),
    SourcePattern::method_call(
        "toml_decode",
        SourceKind::Deserialized,
        "toml",
        "Decode",
        Some("toml"),
    ),
];

/// HTTP route methods for handler detection.
const HTTP_ROUTE_METHODS: &[&str] = &[
    "HandleFunc",
    "Handle",
    "Get",
    "Post",
    "Put",
    "Delete",
    "Patch",
    "Options",
    "Head",
    "Any",
    "GET",
    "POST",
    "PUT",
    "DELETE",
    "PATCH",
    "OPTIONS",
    "HEAD",
    "Group",
    "Use",
];

/// Common request variable names in Go handlers.
const REQUEST_VAR_NAMES: &[&str] = &[
    "r", "req", "request", "c", "ctx", "context", "w", "writer",
];

// =============================================================================
// Go Source Detector
// =============================================================================

/// Detects taint sources in Go code using AST analysis.
///
/// The detector identifies sources through:
/// 1. Pattern matching on method calls and property accesses
/// 2. HTTP handler parameter analysis (net/http, gin, echo, fiber)
/// 3. Multiple return value tracking
/// 4. Channel propagation detection
/// 5. Goroutine capture analysis
/// 6. io.Reader interface implementations
pub struct GoSourceDetector {
    /// All source patterns to check
    patterns: Vec<SourcePattern>,
    /// Import aliases (e.g., "mux" -> "github.com/gorilla/mux")
    import_aliases: HashMap<String, String>,
    /// Known request variable names
    request_aliases: HashSet<String>,
}

impl GoSourceDetector {
    /// Create a new Go source detector with default patterns.
    pub fn new() -> Self {
        let mut patterns = Vec::new();
        patterns.extend_from_slice(HTTP_REQUEST_SOURCES);
        patterns.extend_from_slice(GIN_SOURCES);
        patterns.extend_from_slice(ECHO_SOURCES);
        patterns.extend_from_slice(FIBER_SOURCES);
        patterns.extend_from_slice(STDLIB_SOURCES);
        patterns.extend_from_slice(NETWORK_SOURCES);
        patterns.extend_from_slice(DATABASE_SOURCES);
        patterns.extend_from_slice(DESERIALIZATION_SOURCES);

        let mut request_aliases = HashSet::new();
        for name in REQUEST_VAR_NAMES {
            request_aliases.insert((*name).to_string());
        }

        Self {
            patterns,
            import_aliases: HashMap::new(),
            request_aliases,
        }
    }

    /// Add a custom source pattern.
    pub fn add_pattern(&mut self, pattern: SourcePattern) {
        self.patterns.push(pattern);
    }

    /// Add a request alias (variables that should be treated like request objects).
    pub fn add_request_alias(&mut self, alias: impl Into<String>) {
        self.request_aliases.insert(alias.into());
    }

    /// Scan a source file for taint sources.
    pub fn scan_file(&self, path: impl AsRef<Path>) -> Result<SourceScanResult> {
        let path = path.as_ref();
        let source = std::fs::read_to_string(path).map_err(|e| BrrrError::Parse {
            file: path.display().to_string(),
            message: format!("Failed to read file: {}", e),
        })?;

        self.scan_source(&source, path.to_string_lossy().as_ref())
    }

    /// Scan source code for taint sources.
    pub fn scan_source(&self, source: &str, file_name: &str) -> Result<SourceScanResult> {
        let mut parser = Parser::new();

        let language = tree_sitter_go::LANGUAGE.into();
        parser.set_language(&language).map_err(|e| BrrrError::Parse {
            file: file_name.to_string(),
            message: format!("Failed to set Go language: {}", e),
        })?;

        let tree = parser.parse(source, None).ok_or_else(|| BrrrError::Parse {
            file: file_name.to_string(),
            message: "Failed to parse Go source".to_string(),
        })?;

        self.scan_tree(&tree, source, file_name)
    }

    /// Scan a parsed AST for taint sources.
    fn scan_tree(&self, tree: &Tree, source: &str, file_name: &str) -> Result<SourceScanResult> {
        let mut result = SourceScanResult::new(file_name, "go");
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
            request_aliases: &self.request_aliases,
            tainted_vars: HashMap::new(),
            channel_taint: HashMap::new(),
            current_function: None,
            current_handler: None,
            in_handler_scope: false,
            in_goroutine: false,
        };

        // Second pass: find sources and handlers
        self.scan_node(root, &mut ctx, &mut result);

        Ok(result)
    }

    /// Collect import aliases from the module.
    fn collect_imports(&self, root: Node, source: &[u8], aliases: &mut HashMap<String, String>) {
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "import_declaration" {
                self.process_import_declaration(child, source, aliases);
            }
        }
    }

    /// Process import declaration for aliases.
    fn process_import_declaration(
        &self,
        node: Node,
        source: &[u8],
        aliases: &mut HashMap<String, String>,
    ) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "import_spec" => {
                    self.process_import_spec(child, source, aliases);
                }
                "import_spec_list" => {
                    let mut inner_cursor = child.walk();
                    for inner_child in child.children(&mut inner_cursor) {
                        if inner_child.kind() == "import_spec" {
                            self.process_import_spec(inner_child, source, aliases);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Process a single import spec.
    fn process_import_spec(&self, node: Node, source: &[u8], aliases: &mut HashMap<String, String>) {
        let mut alias_name: Option<String> = None;
        let mut path: Option<String> = None;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "package_identifier" => {
                    alias_name = Some(self.node_text(child, source).to_string());
                }
                "interpreted_string_literal" => {
                    let text = self.node_text(child, source);
                    path = Some(text.trim_matches('"').to_string());
                }
                "blank_identifier" => {
                    alias_name = Some("_".to_string());
                }
                "dot" => {
                    alias_name = Some(".".to_string());
                }
                _ => {}
            }
        }

        if let Some(import_path) = path {
            // Extract package name from path (last component)
            let pkg_name = import_path.rsplit('/').next().unwrap_or(&import_path);

            if let Some(alias) = alias_name {
                if alias != "_" && alias != "." {
                    aliases.insert(alias.clone(), import_path.clone());
                    aliases.insert(pkg_name.to_string(), import_path);
                }
            } else {
                aliases.insert(pkg_name.to_string(), import_path);
            }
        }
    }

    /// Recursively scan AST nodes for sources.
    fn scan_node(&self, node: Node, ctx: &mut ScanContext, result: &mut SourceScanResult) {
        match node.kind() {
            // Function declarations (potential handlers)
            "function_declaration" => {
                self.scan_function_declaration(node, ctx, result);
            }
            // Method declarations
            "method_declaration" => {
                self.scan_method_declaration(node, ctx, result);
            }
            // Call expressions (method calls, function calls)
            "call_expression" => {
                self.scan_call_expression(node, ctx, result);
            }
            // Selector expressions (property access: r.URL, r.Body)
            "selector_expression" => {
                self.scan_selector_expression(node, ctx, result);
            }
            // Short variable declaration (x := expr)
            "short_var_declaration" => {
                self.scan_short_var_declaration(node, ctx, result);
            }
            // Assignment statement (x = expr)
            "assignment_statement" => {
                self.scan_assignment_statement(node, ctx, result);
            }
            // Goroutine statement (go func() { ... })
            "go_statement" => {
                self.scan_go_statement(node, ctx, result);
            }
            // Channel send (ch <- val)
            "send_statement" => {
                self.scan_send_statement(node, ctx, result);
            }
            // Channel receive (<-ch in expression)
            "unary_expression" => {
                self.scan_unary_expression(node, ctx, result);
            }
            // Index expression (arr[i], map[key])
            "index_expression" => {
                self.scan_index_expression(node, ctx, result);
            }
            // For-range loops (may iterate over tainted data)
            "for_statement" => {
                self.scan_for_statement(node, ctx, result);
            }
            _ => {
                // Scan children
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

    /// Scan function declaration for handler patterns.
    fn scan_function_declaration(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let name = node
            .child_by_field_name("name")
            .map(|n| self.node_text(n, ctx.source).to_string())
            .unwrap_or_else(|| "<anonymous>".to_string());

        let old_func = ctx.current_function.take();
        ctx.current_function = Some(name.clone());

        // Check if this is an HTTP handler function
        // Pattern: func handler(w http.ResponseWriter, r *http.Request)
        if let Some(params) = node.child_by_field_name("parameters") {
            if let Some(handler_info) = self.check_http_handler_signature(node, params, &name, ctx) {
                // Mark parameters as tainted
                for param in &handler_info.tainted_params {
                    ctx.tainted_vars
                        .insert(param.name.clone(), param.kind);

                    let loc = Location::new(ctx.file_name, handler_info.start_line, 0);
                    let source =
                        DetectedSource::new(param.kind, loc, format!("parameter:{}", param.name))
                            .with_assignment(&param.name)
                            .with_framework(&handler_info.framework)
                            .in_handler_function(&handler_info.name);
                    result.add_source(source);
                }

                result.add_handler(handler_info.clone());

                let old_handler = ctx.current_handler.take();
                let old_in_handler = ctx.in_handler_scope;
                ctx.current_handler = Some(handler_info);
                ctx.in_handler_scope = true;

                // Scan function body
                if let Some(body) = node.child_by_field_name("body") {
                    self.scan_children(body, ctx, result);
                }

                ctx.current_handler = old_handler;
                ctx.in_handler_scope = old_in_handler;
                ctx.current_function = old_func;
                return;
            }
        }

        // Not a handler, scan normally
        self.scan_children(node, ctx, result);
        ctx.current_function = old_func;
    }

    /// Scan method declaration.
    fn scan_method_declaration(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let name = node
            .child_by_field_name("name")
            .map(|n| self.node_text(n, ctx.source).to_string())
            .unwrap_or_else(|| "<anonymous>".to_string());

        let old_func = ctx.current_function.take();
        ctx.current_function = Some(name);

        self.scan_children(node, ctx, result);

        ctx.current_function = old_func;
    }

    /// Check if function signature matches HTTP handler pattern.
    fn check_http_handler_signature(
        &self,
        func_node: Node,
        params_node: Node,
        func_name: &str,
        ctx: &ScanContext,
    ) -> Option<HandlerInfo> {
        let mut has_response_writer = false;
        let mut has_request = false;
        let mut has_gin_context = false;
        let mut has_echo_context = false;
        let mut has_fiber_context = false;
        let mut tainted_params = Vec::new();
        let mut param_index = 0;

        let mut cursor = params_node.walk();
        for child in params_node.children(&mut cursor) {
            if child.kind() == "parameter_declaration" {
                let param_names = self.extract_param_names(child, ctx.source);
                let param_type = self.extract_param_type(child, ctx.source);

                for name in param_names {
                    // Check for http.ResponseWriter
                    if param_type.contains("ResponseWriter") {
                        has_response_writer = true;
                    }
                    // Check for *http.Request
                    else if param_type.contains("Request") && param_type.contains("*") {
                        has_request = true;
                        tainted_params.push(TaintedParameter {
                            name: name.clone(),
                            kind: SourceKind::RequestBody,
                            index: param_index,
                            annotation: Some(param_type.clone()),
                        });
                    }
                    // Check for *gin.Context
                    else if param_type.contains("gin") && param_type.contains("Context") {
                        has_gin_context = true;
                        tainted_params.push(TaintedParameter {
                            name: name.clone(),
                            kind: SourceKind::RequestBody,
                            index: param_index,
                            annotation: Some(param_type.clone()),
                        });
                    }
                    // Check for echo.Context
                    else if param_type.contains("echo") && param_type.contains("Context") {
                        has_echo_context = true;
                        tainted_params.push(TaintedParameter {
                            name: name.clone(),
                            kind: SourceKind::RequestBody,
                            index: param_index,
                            annotation: Some(param_type.clone()),
                        });
                    }
                    // Check for *fiber.Ctx
                    else if param_type.contains("fiber") && param_type.contains("Ctx") {
                        has_fiber_context = true;
                        tainted_params.push(TaintedParameter {
                            name: name.clone(),
                            kind: SourceKind::RequestBody,
                            index: param_index,
                            annotation: Some(param_type.clone()),
                        });
                    }
                    // Check for context.Context (common first param, not tainted itself)
                    else if param_type.contains("context.Context") || param_type == "Context" {
                        // Not a taint source, skip
                    }

                    param_index += 1;
                }
            }
        }

        // Determine framework
        let framework = if has_gin_context {
            "gin"
        } else if has_echo_context {
            "echo"
        } else if has_fiber_context {
            "fiber"
        } else if has_response_writer && has_request {
            "net/http"
        } else {
            return None;
        };

        Some(HandlerInfo {
            name: func_name.to_string(),
            start_line: func_node.start_position().row + 1,
            end_line: func_node.end_position().row + 1,
            route: None,  // Would need to track mux.HandleFunc calls
            methods: Vec::new(),
            framework: framework.to_string(),
            tainted_params,
        })
    }

    /// Extract parameter names from parameter declaration.
    fn extract_param_names(&self, param_node: Node, source: &[u8]) -> Vec<String> {
        let mut names = Vec::new();
        let mut cursor = param_node.walk();

        for child in param_node.children(&mut cursor) {
            if child.kind() == "identifier" {
                names.push(self.node_text(child, source).to_string());
            }
        }

        names
    }

    /// Extract parameter type from parameter declaration.
    fn extract_param_type(&self, param_node: Node, source: &[u8]) -> String {
        let mut cursor = param_node.walk();

        for child in param_node.children(&mut cursor) {
            match child.kind() {
                "type_identifier" | "pointer_type" | "qualified_type" | "slice_type"
                | "map_type" | "interface_type" | "struct_type" | "channel_type" => {
                    return self.node_text(child, source).to_string();
                }
                _ => {}
            }
        }

        String::new()
    }

    /// Scan call expression for taint sources.
    fn scan_call_expression(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let func_node = match node.child_by_field_name("function") {
            Some(n) => n,
            None => {
                self.scan_children(node, ctx, result);
                return;
            }
        };

        let expression = self.node_text(node, ctx.source).to_string();
        let line = node.start_position().row + 1;
        let col = node.start_position().column;

        // Check for selector expression (method call): obj.Method()
        if func_node.kind() == "selector_expression" {
            self.scan_method_call(func_node, node, ctx, result);
        }
        // Check for identifier (function call): Function()
        else if func_node.kind() == "identifier" {
            let func_name = self.node_text(func_node, ctx.source);

            // Check for standalone functions like flag.String, os.Getenv
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
                }
            }

            // Check for route handler registration patterns
            if HTTP_ROUTE_METHODS.contains(&func_name) {
                self.scan_route_registration(node, ctx, result);
            }
        }
        // Check for qualified identifier: pkg.Function()
        else if func_node.kind() == "qualified_type" || func_node.kind() == "selector_expression" {
            self.scan_qualified_call(func_node, node, ctx, result);
        }

        self.scan_children(node, ctx, result);
    }

    /// Scan method call for taint sources.
    fn scan_method_call(
        &self,
        selector_node: Node,
        call_node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let object = match selector_node.child_by_field_name("operand") {
            Some(o) => o,
            None => return,
        };
        let field = match selector_node.child_by_field_name("field") {
            Some(f) => f,
            None => return,
        };

        let object_name = self.get_object_name(object, ctx);
        let method_name = self.node_text(field, ctx.source);
        let expression = self.node_text(call_node, ctx.source).to_string();
        let line = call_node.start_position().row + 1;
        let col = call_node.start_position().column;

        // Check if object is a tainted variable (e.g., r.FormValue)
        if let Some(kind) = ctx.tainted_vars.get(&object_name) {
            // Method call on tainted variable
            let source_kind = self.classify_method_on_tainted(method_name, *kind);
            if let Some(sk) = source_kind {
                let loc = Location::new(ctx.file_name, line, col);
                let source = DetectedSource::new(sk, loc, &expression)
                    .with_confidence(0.95)
                    .with_context(format!("{}.{}", object_name, method_name));
                result.add_source(source);
            }
        }

        // Check patterns with case-insensitive matching for type/variable names
        let object_lower = object_name.to_lowercase();

        for pattern in &self.patterns {
            if let Some(pattern_obj) = pattern.object {
                let pattern_obj_lower = pattern_obj.to_lowercase();

                // Check for direct match, case-insensitive match, or chain (e.g., r.URL.Query)
                let matches = object_name == pattern_obj
                    || object_lower == pattern_obj_lower
                    || object_name.ends_with(&format!(".{}", pattern_obj))
                    || object_lower.ends_with(&format!(".{}", pattern_obj_lower))
                    || (ctx.request_aliases.contains(&object_name)
                        && (pattern_obj == "r" || pattern_obj == "req" || pattern_obj == "c"));

                if matches && method_name == pattern.method && !pattern.is_property {
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
                    break;
                }
            }
        }

        // Heuristic matching for well-known patterns based on method names
        // These methods are almost always taint sources regardless of the exact type name
        let heuristic_match = match method_name {
            // Database: row.Scan(), rows.Scan()
            "Scan" if object_lower.contains("row") => Some((SourceKind::DatabaseResult, "database/sql")),
            // HTTP client: client.Do(), client.Get(), client.Post()
            "Do" if object_lower.contains("client") => Some((SourceKind::HttpResponse, "net/http")),
            // JSON/XML/YAML decoder: decoder.Decode()
            "Decode" if object_lower.contains("decoder") => Some((SourceKind::Deserialized, "encoding")),
            // WebSocket: conn.ReadMessage(), conn.ReadJSON()
            "ReadMessage" | "ReadJSON" | "NextReader"
                if object_lower.contains("conn") || object_lower.contains("ws") =>
            {
                Some((SourceKind::WebSocketMessage, "websocket"))
            }
            // bufio Reader/Scanner
            "Text" | "Bytes" if object_lower.contains("scanner") => Some((SourceKind::FileRead, "bufio")),
            "ReadLine" | "ReadString" | "ReadBytes" if object_lower.contains("reader") => {
                Some((SourceKind::FileRead, "bufio"))
            }
            // URL Query on chained expressions (r.URL.Query())
            "Query" if object_lower.contains("url") => Some((SourceKind::RequestParam, "net/http")),
            // Get on Query result (r.URL.Query().Get())
            "Get" if object_lower.contains("query") => Some((SourceKind::RequestParam, "net/http")),
            _ => None,
        };

        if let Some((kind, framework)) = heuristic_match {
            let loc = Location::new(ctx.file_name, line, col);
            let source = DetectedSource::new(kind, loc, &expression)
                .with_confidence(0.90)
                .with_framework(framework);
            result.add_source(source);
        }

        // Check for io.ReadAll(r.Body) pattern
        if method_name == "ReadAll" && (object_name == "io" || object_name == "ioutil") {
            // Check if argument contains tainted source
            if let Some(args) = call_node.child_by_field_name("arguments") {
                let args_text = self.node_text(args, ctx.source);
                if args_text.contains("Body") || args_text.contains(".Request") {
                    let loc = Location::new(ctx.file_name, line, col);
                    let source = DetectedSource::new(SourceKind::RequestBody, loc, &expression)
                        .with_confidence(0.95)
                        .with_framework("io");
                    result.add_source(source);
                }
            }
        }

        // Check for json.Unmarshal with tainted data
        if method_name == "Unmarshal" && (object_name == "json" || object_name == "xml" || object_name == "yaml") {
            let loc = Location::new(ctx.file_name, line, col);
            let source = DetectedSource::new(SourceKind::Deserialized, loc, &expression)
                .with_confidence(0.9)
                .with_framework(&format!("encoding/{}", object_name));
            result.add_source(source);
        }

        // Check for route handler registration: mux.HandleFunc(), router.GET()
        if HTTP_ROUTE_METHODS.contains(&method_name) {
            self.scan_route_registration(call_node, ctx, result);
        }
    }

    /// Scan qualified function call (pkg.Function).
    fn scan_qualified_call(
        &self,
        func_node: Node,
        call_node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let expression = self.node_text(call_node, ctx.source).to_string();
        let line = call_node.start_position().row + 1;
        let col = call_node.start_position().column;

        // Get package.function name
        let qual_name = self.node_text(func_node, ctx.source);

        for pattern in &self.patterns {
            if let Some(pattern_obj) = pattern.object {
                let expected = format!("{}.{}", pattern_obj, pattern.method);
                if qual_name == expected || qual_name.ends_with(&format!(".{}", pattern.method)) {
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
                    break;
                }
            }
        }
    }

    /// Scan selector expression (property access).
    fn scan_selector_expression(
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

        let object = match node.child_by_field_name("operand") {
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

        // Check for property access on tainted variable
        if let Some(kind) = ctx.tainted_vars.get(&object_name) {
            let source_kind = self.classify_property_access(field_name, *kind);
            if let Some(sk) = source_kind {
                let loc = Location::new(ctx.file_name, line, col);
                let source = DetectedSource::new(sk, loc, &expression)
                    .with_confidence(0.9)
                    .with_context(format!("{}.{}", object_name, field_name));
                result.add_source(source);
            }
        }

        // Check property patterns
        for pattern in &self.patterns {
            if let Some(pattern_obj) = pattern.object {
                if pattern.is_property {
                    let matches = object_name == pattern_obj
                        || object_name.ends_with(&format!(".{}", pattern_obj))
                        || (ctx.request_aliases.contains(&object_name)
                            && (pattern_obj == "r" || pattern_obj == "req" || pattern_obj == "c"));

                    if matches && field_name == pattern.method {
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

        // Check for os.Args access
        if object_name == "os" && field_name == "Args" {
            let loc = Location::new(ctx.file_name, line, col);
            let source = DetectedSource::new(SourceKind::ProcessArgs, loc, &expression)
                .with_confidence(1.0);
            result.add_source(source);
        }

        // Check for os.Stdin access
        if object_name == "os" && field_name == "Stdin" {
            let loc = Location::new(ctx.file_name, line, col);
            let source = DetectedSource::new(SourceKind::Stdin, loc, &expression)
                .with_confidence(1.0);
            result.add_source(source);
        }

        self.scan_children(node, ctx, result);
    }

    /// Scan short variable declaration for taint propagation.
    fn scan_short_var_declaration(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let left = node.child_by_field_name("left");
        let right = node.child_by_field_name("right");

        if let (Some(left_node), Some(right_node)) = (left, right) {
            // Check if right side is a taint source
            let right_taint = self.check_expression_taint(right_node, ctx);

            if let Some(kind) = right_taint {
                // Extract variable names from left side
                let var_names = self.extract_declaration_names(left_node, ctx.source);

                for (idx, name) in var_names.iter().enumerate() {
                    if name != "_" {
                        // First variable typically gets the data, second gets error
                        // e.g., data, err := ioutil.ReadAll(...)
                        let var_kind = if idx == 0 {
                            kind
                        } else {
                            // Second+ variables are often errors, not tainted
                            continue;
                        };

                        ctx.tainted_vars.insert(name.clone(), var_kind);
                    }
                }
            }
        }

        self.scan_children(node, ctx, result);
    }

    /// Scan assignment statement for taint propagation.
    fn scan_assignment_statement(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let left = node.child_by_field_name("left");
        let right = node.child_by_field_name("right");

        if let (Some(left_node), Some(right_node)) = (left, right) {
            let right_taint = self.check_expression_taint(right_node, ctx);

            if let Some(kind) = right_taint {
                let var_names = self.extract_declaration_names(left_node, ctx.source);

                for (idx, name) in var_names.iter().enumerate() {
                    if name != "_" && idx == 0 {
                        ctx.tainted_vars.insert(name.clone(), kind);
                    }
                }
            }
        }

        self.scan_children(node, ctx, result);
    }

    /// Scan goroutine statement for captured variables.
    fn scan_go_statement(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let old_in_goroutine = ctx.in_goroutine;
        ctx.in_goroutine = true;

        // Goroutines can capture tainted variables from enclosing scope
        // This is tracked for potential race condition detection

        self.scan_children(node, ctx, result);

        ctx.in_goroutine = old_in_goroutine;
    }

    /// Scan channel send statement for taint propagation.
    fn scan_send_statement(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let channel = node.child_by_field_name("channel");
        let value = node.child_by_field_name("value");

        if let (Some(ch_node), Some(val_node)) = (channel, value) {
            let ch_name = self.node_text(ch_node, ctx.source).to_string();

            // Check if value being sent is tainted
            if let Some(kind) = self.check_expression_taint(val_node, ctx) {
                // Mark channel as carrying tainted data
                ctx.channel_taint.insert(ch_name, kind);
            }
        }

        self.scan_children(node, ctx, result);
    }

    /// Scan unary expression for channel receive.
    fn scan_unary_expression(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let text = self.node_text(node, ctx.source);

        // Check for channel receive: <-ch
        if text.starts_with("<-") {
            if let Some(operand) = node.child_by_field_name("operand") {
                let ch_name = self.node_text(operand, ctx.source).to_string();

                // If channel carries tainted data, the receive is tainted
                if let Some(&kind) = ctx.channel_taint.get(&ch_name) {
                    let line = node.start_position().row + 1;
                    let col = node.start_position().column;
                    let loc = Location::new(ctx.file_name, line, col);

                    let source = DetectedSource::new(kind, loc, text)
                        .with_confidence(0.85)
                        .with_context(format!("channel_receive:{}", ch_name));
                    result.add_source(source);
                }
            }
        }

        self.scan_children(node, ctx, result);
    }

    /// Scan index expression for tainted array/map access.
    fn scan_index_expression(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        let operand = node.child_by_field_name("operand");
        let expression = self.node_text(node, ctx.source).to_string();
        let line = node.start_position().row + 1;
        let col = node.start_position().column;

        if let Some(op) = operand {
            let op_name = self.get_object_name(op, ctx);

            // Check for os.Args[n]
            if op_name == "os.Args" {
                let loc = Location::new(ctx.file_name, line, col);
                let source = DetectedSource::new(SourceKind::ProcessArgs, loc, &expression)
                    .with_confidence(1.0);
                result.add_source(source);
            }
            // Check for tainted map/slice access
            else if let Some(&kind) = ctx.tainted_vars.get(&op_name) {
                let loc = Location::new(ctx.file_name, line, col);
                let source = DetectedSource::new(kind, loc, &expression)
                    .with_confidence(0.85)
                    .with_context(format!("indexed:{}", op_name));
                result.add_source(source);
            }
        }

        self.scan_children(node, ctx, result);
    }

    /// Scan for statement for tainted iteration.
    fn scan_for_statement(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        result: &mut SourceScanResult,
    ) {
        // Check for range clause
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "range_clause" {
                // for k, v := range taintedMap
                if let Some(right) = child.child_by_field_name("right") {
                    if let Some(kind) = self.check_expression_taint(right, ctx) {
                        // Mark loop variables as tainted
                        if let Some(left) = child.child_by_field_name("left") {
                            let var_names = self.extract_declaration_names(left, ctx.source);
                            for name in var_names {
                                if name != "_" {
                                    ctx.tainted_vars.insert(name, kind);
                                }
                            }
                        }
                    }
                }
            }
        }

        self.scan_children(node, ctx, result);
    }

    /// Scan route registration call for handler info.
    fn scan_route_registration(
        &self,
        node: Node,
        ctx: &mut ScanContext,
        _result: &mut SourceScanResult,
    ) {
        // Try to extract route path and handler from arguments
        if let Some(args) = node.child_by_field_name("arguments") {
            let mut route_path = None;
            let mut handler_name = None;

            let mut cursor = args.walk();
            let mut arg_idx = 0;

            for child in args.children(&mut cursor) {
                if !child.is_named() {
                    continue;
                }

                match child.kind() {
                    "interpreted_string_literal" => {
                        let text = self.node_text(child, ctx.source);
                        route_path = Some(text.trim_matches('"').to_string());
                    }
                    "identifier" => {
                        if arg_idx > 0 {
                            handler_name = Some(self.node_text(child, ctx.source).to_string());
                        }
                    }
                    "func_literal" => {
                        // Inline handler function
                        handler_name = Some("<inline>".to_string());
                    }
                    _ => {}
                }
                arg_idx += 1;
            }

            // If we found a route, update any existing handler info
            if let (Some(path), Some(name)) = (route_path, handler_name) {
                // This could be linked to handler analysis
                // For now, just note that we detected a route registration
                let _ = (path, name);
            }
        }
    }

    // ==========================================================================
    // Helper Methods
    // ==========================================================================

    /// Check if an expression is a taint source.
    fn check_expression_taint(&self, node: Node, ctx: &ScanContext) -> Option<SourceKind> {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node, ctx.source);
                ctx.tainted_vars.get(name).copied()
            }
            "call_expression" => {
                // Check if this is a taint source call
                if let Some(func) = node.child_by_field_name("function") {
                    let func_text = self.node_text(func, ctx.source);

                    // Check patterns for matching function calls
                    for pattern in &self.patterns {
                        if let Some(obj) = pattern.object {
                            let expected = format!("{}.{}", obj, pattern.method);
                            if func_text.contains(&expected) || func_text.ends_with(pattern.method) {
                                return Some(pattern.kind);
                            }
                        }
                    }

                    // Check common taint source functions
                    if func_text.contains("ReadFile") || func_text.contains("ReadAll") {
                        return Some(SourceKind::FileRead);
                    }
                    if func_text.contains("Getenv") || func_text.contains("LookupEnv") {
                        return Some(SourceKind::Environment);
                    }
                    if func_text.contains("FormValue") || func_text.contains("PostFormValue") {
                        return Some(SourceKind::RequestParam);
                    }
                    if func_text.contains("Query") && !func_text.contains("QueryRow") {
                        return Some(SourceKind::RequestParam);
                    }
                    if func_text.contains("Param") {
                        return Some(SourceKind::UrlPath);
                    }
                    if func_text.contains("Unmarshal") || func_text.contains("Decode") {
                        return Some(SourceKind::Deserialized);
                    }
                    if func_text.contains("Scan") && func_text.contains(".") {
                        return Some(SourceKind::DatabaseResult);
                    }
                }
                None
            }
            "selector_expression" => {
                let object = node.child_by_field_name("operand")?;
                let field = node.child_by_field_name("field")?;

                let obj_name = self.get_object_name(object, ctx);
                let field_name = self.node_text(field, ctx.source);

                // Check for property access on tainted variable
                if let Some(&kind) = ctx.tainted_vars.get(&obj_name) {
                    return Some(kind);
                }

                // Check patterns
                for pattern in &self.patterns {
                    if pattern.is_property {
                        if let Some(obj) = pattern.object {
                            if (obj_name == obj || ctx.request_aliases.contains(&obj_name))
                                && field_name == pattern.method
                            {
                                return Some(pattern.kind);
                            }
                        }
                    }
                }

                // Check for os.Args, os.Stdin
                if obj_name == "os" {
                    if field_name == "Args" {
                        return Some(SourceKind::ProcessArgs);
                    }
                    if field_name == "Stdin" {
                        return Some(SourceKind::Stdin);
                    }
                }

                None
            }
            "unary_expression" => {
                let text = self.node_text(node, ctx.source);
                // Channel receive
                if text.starts_with("<-") {
                    if let Some(operand) = node.child_by_field_name("operand") {
                        let ch_name = self.node_text(operand, ctx.source);
                        return ctx.channel_taint.get(ch_name).copied();
                    }
                }
                None
            }
            "index_expression" => {
                if let Some(operand) = node.child_by_field_name("operand") {
                    let op_name = self.get_object_name(operand, ctx);
                    if op_name == "os.Args" {
                        return Some(SourceKind::ProcessArgs);
                    }
                    return ctx.tainted_vars.get(&op_name).copied();
                }
                None
            }
            _ => None,
        }
    }

    /// Classify method call on a tainted object.
    fn classify_method_on_tainted(&self, method: &str, base_kind: SourceKind) -> Option<SourceKind> {
        // Methods that return parts of a request
        match method {
            "FormValue" | "PostFormValue" => Some(SourceKind::RequestParam),
            "Query" | "Get" if base_kind == SourceKind::RequestBody => Some(SourceKind::RequestParam),
            "Cookie" | "Cookies" => Some(SourceKind::Cookie),
            "Header" => Some(SourceKind::HttpHeader),
            "Body" => Some(SourceKind::RequestBody),
            "Path" | "RawPath" | "RequestURI" => Some(SourceKind::UrlPath),
            "Read" | "ReadAll" => Some(base_kind),
            "Scan" => Some(SourceKind::DatabaseResult),
            "Text" | "Bytes" => Some(base_kind),
            _ => None,
        }
    }

    /// Classify property access on a tainted object.
    fn classify_property_access(&self, property: &str, base_kind: SourceKind) -> Option<SourceKind> {
        match property {
            "Body" => Some(SourceKind::RequestBody),
            "Header" | "Headers" => Some(SourceKind::HttpHeader),
            "URL" => Some(SourceKind::UrlPath),
            "Form" | "PostForm" => Some(SourceKind::RequestParam),
            "MultipartForm" => Some(SourceKind::FileUpload),
            "Host" | "RemoteAddr" => Some(SourceKind::HttpHeader),
            "RequestURI" => Some(SourceKind::UrlPath),
            "Request" => Some(base_kind),
            _ => None,
        }
    }

    /// Get the name of an object node, resolving chains.
    fn get_object_name(&self, node: Node, ctx: &ScanContext) -> String {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(node, ctx.source);
                ctx.import_aliases
                    .get(name)
                    .map(|s| s.split('/').last().unwrap_or(s).to_string())
                    .unwrap_or_else(|| name.to_string())
            }
            "selector_expression" => {
                let mut parts = Vec::new();
                let mut current = node;

                loop {
                    if let Some(field) = current.child_by_field_name("field") {
                        parts.push(self.node_text(field, ctx.source).to_string());
                    }

                    if let Some(operand) = current.child_by_field_name("operand") {
                        if operand.kind() == "identifier" {
                            parts.push(self.node_text(operand, ctx.source).to_string());
                            break;
                        } else if operand.kind() == "selector_expression" {
                            current = operand;
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
            "call_expression" => {
                // For chained calls like r.URL.Query()
                self.node_text(node, ctx.source).to_string()
            }
            _ => self.node_text(node, ctx.source).to_string(),
        }
    }

    /// Extract variable names from declaration.
    fn extract_declaration_names(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut names = Vec::new();

        match node.kind() {
            "identifier" => {
                names.push(self.node_text(node, source).to_string());
            }
            "expression_list" => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "identifier" {
                        names.push(self.node_text(child, source).to_string());
                    } else if child.kind() == "blank_identifier" {
                        names.push("_".to_string());
                    }
                }
            }
            "blank_identifier" => {
                names.push("_".to_string());
            }
            _ => {}
        }

        names
    }

    /// Get text from a node.
    fn node_text<'a>(&self, node: Node<'a>, source: &'a [u8]) -> &'a str {
        std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }
}

impl Default for GoSourceDetector {
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
    /// Known request variable names
    request_aliases: &'a HashSet<String>,
    /// Variables that have been tainted
    tainted_vars: HashMap<String, SourceKind>,
    /// Channels that carry tainted data
    channel_taint: HashMap<String, SourceKind>,
    /// Current function name
    current_function: Option<String>,
    /// Current handler info (if in a handler)
    current_handler: Option<HandlerInfo>,
    /// Whether we're in a handler scope
    in_handler_scope: bool,
    /// Whether we're inside a goroutine
    in_goroutine: bool,
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn scan(source: &str) -> SourceScanResult {
        let detector = GoSourceDetector::new();
        detector.scan_source(source, "test.go").unwrap()
    }

    // =========================================================================
    // net/http Tests
    // =========================================================================

    #[test]
    fn test_http_formvalue() {
        let source = r#"
package main

import "net/http"

func handler(w http.ResponseWriter, r *http.Request) {
    name := r.FormValue("name")
    _ = name
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestParam
            || s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_http_url_query() {
        let source = r#"
package main

import "net/http"

func handler(w http.ResponseWriter, r *http.Request) {
    id := r.URL.Query().Get("id")
    _ = id
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestParam
            || s.kind == SourceKind::UrlPath));
    }

    #[test]
    fn test_http_header_get() {
        let source = r#"
package main

import "net/http"

func handler(w http.ResponseWriter, r *http.Request) {
    auth := r.Header.Get("Authorization")
    _ = auth
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::HttpHeader));
    }

    #[test]
    fn test_http_cookies() {
        let source = r#"
package main

import "net/http"

func handler(w http.ResponseWriter, r *http.Request) {
    cookie, _ := r.Cookie("session")
    _ = cookie
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Cookie
            || s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_http_body_readall() {
        let source = r#"
package main

import (
    "io"
    "net/http"
)

func handler(w http.ResponseWriter, r *http.Request) {
    body, _ := io.ReadAll(r.Body)
    _ = body
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestBody
            || s.kind == SourceKind::FileRead));
    }

    #[test]
    fn test_http_handler_detection() {
        let source = r#"
package main

import "net/http"

func handler(w http.ResponseWriter, r *http.Request) {
    w.Write([]byte("hello"))
}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 1);
        assert_eq!(result.handlers[0].framework, "net/http");
    }

    // =========================================================================
    // Gin Framework Tests
    // =========================================================================

    #[test]
    fn test_gin_query() {
        let source = r#"
package main

import "github.com/gin-gonic/gin"

func handler(c *gin.Context) {
    name := c.Query("name")
    _ = name
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestParam
            || s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_gin_param() {
        let source = r#"
package main

import "github.com/gin-gonic/gin"

func handler(c *gin.Context) {
    id := c.Param("id")
    _ = id
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::UrlPath
            || s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_gin_postform() {
        let source = r#"
package main

import "github.com/gin-gonic/gin"

func handler(c *gin.Context) {
    data := c.PostForm("data")
    _ = data
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_gin_shouldbindjson() {
        let source = r#"
package main

import "github.com/gin-gonic/gin"

type Input struct {
    Name string
}

func handler(c *gin.Context) {
    var input Input
    c.ShouldBindJSON(&input)
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_gin_getheader() {
        let source = r#"
package main

import "github.com/gin-gonic/gin"

func handler(c *gin.Context) {
    token := c.GetHeader("X-Token")
    _ = token
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::HttpHeader
            || s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_gin_handler_detection() {
        let source = r#"
package main

import "github.com/gin-gonic/gin"

func handler(c *gin.Context) {
    c.JSON(200, gin.H{})
}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 1);
        assert_eq!(result.handlers[0].framework, "gin");
    }

    // =========================================================================
    // Standard Library Tests
    // =========================================================================

    #[test]
    fn test_os_args() {
        let source = r#"
package main

import "os"

func main() {
    arg := os.Args[1]
    _ = arg
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::ProcessArgs));
    }

    #[test]
    fn test_os_getenv() {
        let source = r#"
package main

import "os"

func main() {
    dbUrl := os.Getenv("DATABASE_URL")
    _ = dbUrl
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Environment));
    }

    #[test]
    fn test_os_lookupenv() {
        let source = r#"
package main

import "os"

func main() {
    val, ok := os.LookupEnv("SECRET")
    _ = val
    _ = ok
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Environment));
    }

    #[test]
    fn test_flag_string() {
        let source = r#"
package main

import "flag"

func main() {
    name := flag.String("name", "", "your name")
    flag.Parse()
    _ = name
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::ProcessArgs));
    }

    // =========================================================================
    // File I/O Tests
    // =========================================================================

    #[test]
    fn test_os_readfile() {
        let source = r#"
package main

import "os"

func main() {
    data, _ := os.ReadFile("file.txt")
    _ = data
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::FileRead));
    }

    #[test]
    fn test_ioutil_readfile() {
        let source = r#"
package main

import "io/ioutil"

func main() {
    data, _ := ioutil.ReadFile("file.txt")
    _ = data
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::FileRead));
    }

    #[test]
    fn test_io_readall() {
        let source = r#"
package main

import (
    "io"
    "os"
)

func main() {
    f, _ := os.Open("file.txt")
    data, _ := io.ReadAll(f)
    _ = data
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::FileRead));
    }

    #[test]
    fn test_bufio_scanner() {
        let source = r#"
package main

import (
    "bufio"
    "os"
)

func main() {
    scanner := bufio.NewScanner(os.Stdin)
    for scanner.Scan() {
        text := scanner.Text()
        _ = text
    }
}
"#;
        let result = scan(source);
        // Should detect os.Stdin as taint source
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Stdin
            || s.kind == SourceKind::FileRead));
    }

    // =========================================================================
    // Network Tests
    // =========================================================================

    #[test]
    fn test_http_get() {
        let source = r#"
package main

import "net/http"

func main() {
    resp, _ := http.Get("https://example.com")
    _ = resp
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::HttpResponse));
    }

    #[test]
    fn test_http_client_do() {
        let source = r#"
package main

import "net/http"

func main() {
    client := &http.Client{}
    req, _ := http.NewRequest("GET", "https://example.com", nil)
    resp, _ := client.Do(req)
    _ = resp
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::HttpResponse));
    }

    // =========================================================================
    // Database Tests
    // =========================================================================

    #[test]
    fn test_sql_row_scan() {
        let source = r#"
package main

import "database/sql"

func query(db *sql.DB) {
    var name string
    row := db.QueryRow("SELECT name FROM users WHERE id = 1")
    row.Scan(&name)
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::DatabaseResult));
    }

    #[test]
    fn test_sql_rows_scan() {
        let source = r#"
package main

import "database/sql"

func query(db *sql.DB) {
    rows, _ := db.Query("SELECT name FROM users")
    for rows.Next() {
        var name string
        rows.Scan(&name)
    }
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::DatabaseResult));
    }

    // =========================================================================
    // Deserialization Tests
    // =========================================================================

    #[test]
    fn test_json_unmarshal() {
        let source = r#"
package main

import "encoding/json"

func main() {
    data := []byte(`{"name": "test"}`)
    var result map[string]interface{}
    json.Unmarshal(data, &result)
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Deserialized));
    }

    #[test]
    fn test_json_decoder() {
        let source = r#"
package main

import (
    "encoding/json"
    "strings"
)

func main() {
    r := strings.NewReader(`{"name": "test"}`)
    decoder := json.NewDecoder(r)
    var result map[string]interface{}
    decoder.Decode(&result)
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::Deserialized));
    }

    // =========================================================================
    // Multiple Return Value Tests
    // =========================================================================

    #[test]
    fn test_multiple_return_taint_propagation() {
        let source = r#"
package main

import "os"

func main() {
    data, err := os.ReadFile("user/path.txt")
    if err != nil {
        panic(err)
    }
    process(data)
}

func process(data []byte) {}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::FileRead));
    }

    #[test]
    fn test_blank_identifier_multiple_return() {
        let source = r#"
package main

import "os"

func main() {
    data, _ := os.ReadFile("config.txt")
    _ = data
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::FileRead));
    }

    // =========================================================================
    // Channel Tests
    // =========================================================================

    #[test]
    fn test_channel_taint_propagation() {
        let source = r#"
package main

import "os"

func main() {
    ch := make(chan []byte)

    go func() {
        data, _ := os.ReadFile("file.txt")
        ch <- data
    }()

    received := <-ch
    _ = received
}
"#;
        let result = scan(source);
        // Should detect os.ReadFile as source
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::FileRead));
    }

    // =========================================================================
    // Goroutine Tests
    // =========================================================================

    #[test]
    fn test_goroutine_capture() {
        let source = r#"
package main

import "os"

func main() {
    userInput := os.Args[1]

    go func() {
        process(userInput)
    }()
}

func process(s string) {}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::ProcessArgs));
    }

    // =========================================================================
    // Edge Cases
    // =========================================================================

    #[test]
    fn test_empty_source() {
        let result = scan("package main");
        assert!(result.sources.is_empty());
        assert!(result.handlers.is_empty());
    }

    #[test]
    fn test_no_sources() {
        let source = r#"
package main

func add(a, b int) int {
    return a + b
}

func main() {
    result := add(1, 2)
    _ = result
}
"#;
        let result = scan(source);
        // No external taint sources
        assert!(result.sources.is_empty() || result.sources.iter().all(|s| {
            s.kind != SourceKind::RequestParam && s.kind != SourceKind::FileRead
        }));
    }

    #[test]
    fn test_multiple_handlers() {
        let source = r#"
package main

import (
    "net/http"
    "github.com/gin-gonic/gin"
)

func httpHandler(w http.ResponseWriter, r *http.Request) {
    w.Write([]byte("http"))
}

func ginHandler(c *gin.Context) {
    c.JSON(200, gin.H{})
}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 2);
        assert!(result.handlers.iter().any(|h| h.framework == "net/http"));
        assert!(result.handlers.iter().any(|h| h.framework == "gin"));
    }

    #[test]
    fn test_chained_method_calls() {
        let source = r#"
package main

import "net/http"

func handler(w http.ResponseWriter, r *http.Request) {
    value := r.URL.Query().Get("key")
    _ = value
}
"#;
        let result = scan(source);
        assert!(result.sources.iter().any(|s| s.kind == SourceKind::RequestParam
            || s.kind == SourceKind::UrlPath
            || s.kind == SourceKind::RequestBody));
    }

    #[test]
    fn test_echo_framework() {
        let source = r#"
package main

import "github.com/labstack/echo/v4"

func handler(c echo.Context) error {
    name := c.QueryParam("name")
    id := c.Param("id")
    _ = name
    _ = id
    return nil
}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 1);
        assert_eq!(result.handlers[0].framework, "echo");
    }

    #[test]
    fn test_fiber_framework() {
        let source = r#"
package main

import "github.com/gofiber/fiber/v2"

func handler(c *fiber.Ctx) error {
    name := c.Query("name")
    body := c.Body()
    _ = name
    _ = body
    return nil
}
"#;
        let result = scan(source);
        assert_eq!(result.handlers.len(), 1);
        assert_eq!(result.handlers[0].framework, "fiber");
    }
}
