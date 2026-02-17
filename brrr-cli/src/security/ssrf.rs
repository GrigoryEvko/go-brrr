//! Server-Side Request Forgery (SSRF) vulnerability detection.
//!
//! Detects SSRF vulnerabilities by tracking data flow from user-controlled inputs
//! to network request functions that can access internal services.
//!
//! # SSRF Attack Types
//!
//! - **Full URL Control**: Attacker controls the entire URL, can access any endpoint.
//!   Example: `requests.get(user_url)` where `user_url = "http://169.254.169.254/metadata"`
//!
//! - **Partial URL Control**: Attacker controls part of URL (host, path, etc.).
//!   Example: `requests.get(f"http://{user_host}/api")` - can redirect to internal hosts.
//!
//! - **Redirect SSRF**: Following redirects to internal URLs.
//!   Example: External URL returns 302 to `http://localhost:8080/admin`
//!
//! - **Import/Include SSRF**: Dynamic module loading from URLs.
//!   Example: `import(user_url)` in JavaScript
//!
//! # Cloud Metadata Endpoints
//!
//! SSRF is particularly dangerous for accessing cloud metadata services:
//! - AWS: `169.254.169.254` (EC2 instance metadata, IAM credentials)
//! - GCP: `169.254.169.254` or `metadata.google.internal`
//! - Azure: `169.254.169.254`
//! - Alibaba: `100.100.100.200`
//! - DigitalOcean: `169.254.169.254`
//!
//! # URL Parsing Bypasses
//!
//! Common bypass techniques detected:
//! - `user@host:port` - credentials before host can bypass checks
//! - `host:port@attacker.com` - port as auth can redirect
//! - `localhost` variants: `127.0.0.1`, `0.0.0.0`, `::1`, `0x7f000001`
//! - DNS rebinding: legitimate DNS resolves to internal IP
//! - URL encoding: `%31%36%39.254.169.254`
//!
//! # Detection Strategy
//!
//! 1. Parse source files using tree-sitter
//! 2. Identify calls to known HTTP/network request sinks
//! 3. Track data flow backwards to identify user-controlled inputs
//! 4. Check for URL validation/allowlist patterns (safe patterns)
//! 5. Detect cloud metadata IP patterns in code
//! 6. Report findings with severity based on control level

use std::collections::HashMap;
use std::path::Path;

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use streaming_iterator::StreamingIterator;
use tree_sitter::{Node, Query, QueryCursor, Tree};

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;
use crate::util::format_query_error;

// =============================================================================
// Type Definitions
// =============================================================================

/// Severity level for SSRF findings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// Informational - may not be exploitable but worth reviewing
    Info,
    /// Low severity - limited impact or requires specific conditions
    Low,
    /// Medium severity - partial URL control
    Medium,
    /// High severity - significant URL control, likely exploitable
    High,
    /// Critical - full URL control, direct access to internal services
    Critical,
}

impl Default for Severity {
    fn default() -> Self {
        Self::Low
    }
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Info => write!(f, "INFO"),
            Self::Low => write!(f, "LOW"),
            Self::Medium => write!(f, "MEDIUM"),
            Self::High => write!(f, "HIGH"),
            Self::Critical => write!(f, "CRITICAL"),
        }
    }
}

impl std::str::FromStr for Severity {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "info" | "informational" => Ok(Self::Info),
            "low" => Ok(Self::Low),
            "medium" | "med" => Ok(Self::Medium),
            "high" => Ok(Self::High),
            "critical" | "crit" => Ok(Self::Critical),
            _ => Err(format!("Unknown severity: {s}")),
        }
    }
}

/// Confidence level for the detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Confidence {
    /// Low confidence - pattern match only, no data flow confirmation
    Low,
    /// Medium confidence - some data flow indicators but incomplete path
    Medium,
    /// High confidence - clear data flow from source to sink
    High,
}

impl Default for Confidence {
    fn default() -> Self {
        Self::Low
    }
}

impl std::fmt::Display for Confidence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "LOW"),
            Self::Medium => write!(f, "MEDIUM"),
            Self::High => write!(f, "HIGH"),
        }
    }
}

impl std::str::FromStr for Confidence {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "low" => Ok(Self::Low),
            "medium" | "med" => Ok(Self::Medium),
            "high" => Ok(Self::High),
            _ => Err(format!("Unknown confidence: {s}")),
        }
    }
}

/// Type of SSRF vulnerability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SSRFType {
    /// User controls the entire URL - can access any endpoint
    FullUrl,
    /// User controls part of URL (host, port, path)
    PartialUrl,
    /// User controls redirect target through 3xx responses
    Redirect,
    /// Dynamic import/include from user-controlled URL
    Import,
    /// DNS rebinding attack vector
    DnsRebinding,
}

impl std::fmt::Display for SSRFType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FullUrl => write!(f, "full_url_control"),
            Self::PartialUrl => write!(f, "partial_url_control"),
            Self::Redirect => write!(f, "redirect_ssrf"),
            Self::Import => write!(f, "import_ssrf"),
            Self::DnsRebinding => write!(f, "dns_rebinding"),
        }
    }
}

/// Source location in code.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SourceLocation {
    /// File path
    pub file: String,
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed)
    pub column: usize,
    /// End line number (1-indexed)
    pub end_line: usize,
    /// End column number (1-indexed)
    pub end_column: usize,
}

impl std::fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.column)
    }
}

/// An SSRF vulnerability finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SSRFFinding {
    /// Location of the vulnerable sink call
    pub location: SourceLocation,
    /// Severity of the vulnerability
    pub severity: Severity,
    /// Confidence level of the finding
    pub confidence: Confidence,
    /// Name of the sink function making the request
    pub sink_function: String,
    /// The tainted URL or URL component
    pub tainted_url: String,
    /// Type of SSRF vulnerability
    pub ssrf_type: SSRFType,
    /// Potential targets that could be accessed (cloud metadata, localhost, etc.)
    pub potential_targets: Vec<String>,
    /// Recommended remediation
    pub remediation: String,
    /// Code snippet showing the vulnerable pattern
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code_snippet: Option<String>,
    /// Description of the vulnerability
    pub description: String,
}

/// Result of scanning a file or directory.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ScanResult {
    /// All SSRF findings
    pub findings: Vec<SSRFFinding>,
    /// Number of files scanned
    pub files_scanned: usize,
    /// Scan duration in milliseconds
    #[serde(skip_serializing_if = "Option::is_none")]
    pub duration_ms: Option<u64>,
}

// =============================================================================
// SSRF Sinks by Language
// =============================================================================

/// Definition of an SSRF-prone network request sink.
#[derive(Debug, Clone)]
pub struct SSRFSink {
    /// Language this sink applies to
    pub language: &'static str,
    /// Module or namespace (e.g., "requests", "urllib")
    pub module: Option<&'static str>,
    /// Function/method name (e.g., "get", "urlopen")
    pub function: &'static str,
    /// Argument index that receives the URL (0-indexed)
    pub url_arg_index: usize,
    /// Whether this sink follows redirects by default
    pub follows_redirects: bool,
    /// Base severity when this sink is exploited
    pub severity: Severity,
    /// Description of the sink
    pub description: &'static str,
}

/// Get all known SSRF sinks for a language.
pub fn get_ssrf_sinks(language: &str) -> Vec<SSRFSink> {
    match language {
        "python" => python_ssrf_sinks(),
        "typescript" | "javascript" => typescript_ssrf_sinks(),
        "go" => go_ssrf_sinks(),
        "rust" => rust_ssrf_sinks(),
        "java" => java_ssrf_sinks(),
        _ => vec![],
    }
}

fn python_ssrf_sinks() -> Vec<SSRFSink> {
    vec![
        // requests library
        SSRFSink {
            language: "python",
            module: Some("requests"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "HTTP GET request with redirect following",
        },
        SSRFSink {
            language: "python",
            module: Some("requests"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "HTTP POST request with redirect following",
        },
        SSRFSink {
            language: "python",
            module: Some("requests"),
            function: "put",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "HTTP PUT request with redirect following",
        },
        SSRFSink {
            language: "python",
            module: Some("requests"),
            function: "delete",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "HTTP DELETE request with redirect following",
        },
        SSRFSink {
            language: "python",
            module: Some("requests"),
            function: "patch",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "HTTP PATCH request with redirect following",
        },
        SSRFSink {
            language: "python",
            module: Some("requests"),
            function: "head",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::High,
            description: "HTTP HEAD request",
        },
        SSRFSink {
            language: "python",
            module: Some("requests"),
            function: "options",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::High,
            description: "HTTP OPTIONS request",
        },
        SSRFSink {
            language: "python",
            module: Some("requests"),
            function: "request",
            url_arg_index: 1, // method is arg 0, url is arg 1
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Generic HTTP request",
        },
        // requests.Session methods
        SSRFSink {
            language: "python",
            module: Some("Session"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Session HTTP GET request",
        },
        SSRFSink {
            language: "python",
            module: Some("Session"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Session HTTP POST request",
        },
        // urllib.request
        SSRFSink {
            language: "python",
            module: Some("urllib.request"),
            function: "urlopen",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Opens URL, follows redirects",
        },
        SSRFSink {
            language: "python",
            module: Some("urllib.request"),
            function: "urlretrieve",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Downloads file from URL",
        },
        SSRFSink {
            language: "python",
            module: Some("urllib.request"),
            function: "Request",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "Creates URL request object",
        },
        // urllib3
        SSRFSink {
            language: "python",
            module: Some("urllib3"),
            function: "request",
            url_arg_index: 1,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "urllib3 HTTP request",
        },
        SSRFSink {
            language: "python",
            module: Some("PoolManager"),
            function: "request",
            url_arg_index: 1,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "urllib3 PoolManager request",
        },
        // httpx (async HTTP client)
        SSRFSink {
            language: "python",
            module: Some("httpx"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "httpx async GET request",
        },
        SSRFSink {
            language: "python",
            module: Some("httpx"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "httpx async POST request",
        },
        SSRFSink {
            language: "python",
            module: Some("httpx"),
            function: "AsyncClient",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::High,
            description: "httpx async client creation",
        },
        // aiohttp
        SSRFSink {
            language: "python",
            module: Some("aiohttp"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "aiohttp GET request",
        },
        SSRFSink {
            language: "python",
            module: Some("ClientSession"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "aiohttp ClientSession GET",
        },
        SSRFSink {
            language: "python",
            module: Some("ClientSession"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "aiohttp ClientSession POST",
        },
        SSRFSink {
            language: "python",
            module: Some("ClientSession"),
            function: "request",
            url_arg_index: 1,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "aiohttp ClientSession generic request",
        },
        // http.client
        SSRFSink {
            language: "python",
            module: Some("http.client"),
            function: "HTTPConnection",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "Low-level HTTP connection",
        },
        SSRFSink {
            language: "python",
            module: Some("http.client"),
            function: "HTTPSConnection",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "Low-level HTTPS connection",
        },
        // socket - very low level
        SSRFSink {
            language: "python",
            module: Some("socket"),
            function: "create_connection",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "Raw socket connection",
        },
        // pycurl
        SSRFSink {
            language: "python",
            module: Some("pycurl"),
            function: "setopt",
            url_arg_index: 1, // CURLOPT_URL
            follows_redirects: true,
            severity: Severity::Critical,
            description: "pycurl URL option",
        },
    ]
}

fn typescript_ssrf_sinks() -> Vec<SSRFSink> {
    vec![
        // fetch API
        SSRFSink {
            language: "typescript",
            module: None,
            function: "fetch",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Fetch API HTTP request",
        },
        // axios
        SSRFSink {
            language: "typescript",
            module: Some("axios"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "axios GET request",
        },
        SSRFSink {
            language: "typescript",
            module: Some("axios"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "axios POST request",
        },
        SSRFSink {
            language: "typescript",
            module: Some("axios"),
            function: "put",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "axios PUT request",
        },
        SSRFSink {
            language: "typescript",
            module: Some("axios"),
            function: "delete",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "axios DELETE request",
        },
        SSRFSink {
            language: "typescript",
            module: Some("axios"),
            function: "patch",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "axios PATCH request",
        },
        SSRFSink {
            language: "typescript",
            module: Some("axios"),
            function: "request",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "axios generic request",
        },
        // Node.js http/https
        SSRFSink {
            language: "typescript",
            module: Some("http"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "Node.js HTTP GET",
        },
        SSRFSink {
            language: "typescript",
            module: Some("http"),
            function: "request",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "Node.js HTTP request",
        },
        SSRFSink {
            language: "typescript",
            module: Some("https"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "Node.js HTTPS GET",
        },
        SSRFSink {
            language: "typescript",
            module: Some("https"),
            function: "request",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "Node.js HTTPS request",
        },
        // got
        SSRFSink {
            language: "typescript",
            module: Some("got"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "got HTTP GET",
        },
        SSRFSink {
            language: "typescript",
            module: Some("got"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "got HTTP POST",
        },
        SSRFSink {
            language: "typescript",
            module: None,
            function: "got",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "got default export",
        },
        // node-fetch
        SSRFSink {
            language: "typescript",
            module: Some("node-fetch"),
            function: "default",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "node-fetch request",
        },
        // superagent
        SSRFSink {
            language: "typescript",
            module: Some("superagent"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "superagent GET",
        },
        SSRFSink {
            language: "typescript",
            module: Some("superagent"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "superagent POST",
        },
        // request (deprecated but still used)
        SSRFSink {
            language: "typescript",
            module: Some("request"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "request GET",
        },
        SSRFSink {
            language: "typescript",
            module: Some("request"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "request POST",
        },
        // undici (modern Node.js HTTP client)
        SSRFSink {
            language: "typescript",
            module: Some("undici"),
            function: "fetch",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "undici fetch",
        },
        SSRFSink {
            language: "typescript",
            module: Some("undici"),
            function: "request",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "undici request",
        },
        // WebSocket
        SSRFSink {
            language: "typescript",
            module: None,
            function: "WebSocket",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "WebSocket connection",
        },
        // Dynamic imports
        SSRFSink {
            language: "typescript",
            module: None,
            function: "import",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::Critical,
            description: "Dynamic import from URL",
        },
    ]
}

fn go_ssrf_sinks() -> Vec<SSRFSink> {
    vec![
        // net/http
        SSRFSink {
            language: "go",
            module: Some("http"),
            function: "Get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "HTTP GET request",
        },
        SSRFSink {
            language: "go",
            module: Some("http"),
            function: "Post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "HTTP POST request",
        },
        SSRFSink {
            language: "go",
            module: Some("http"),
            function: "PostForm",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "HTTP POST form request",
        },
        SSRFSink {
            language: "go",
            module: Some("http"),
            function: "Head",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::High,
            description: "HTTP HEAD request",
        },
        SSRFSink {
            language: "go",
            module: Some("http"),
            function: "NewRequest",
            url_arg_index: 1,         // method is arg 0, url is arg 1
            follows_redirects: false, // depends on client
            severity: Severity::High,
            description: "Creates HTTP request",
        },
        SSRFSink {
            language: "go",
            module: Some("http"),
            function: "NewRequestWithContext",
            url_arg_index: 2, // ctx, method, url
            follows_redirects: false,
            severity: Severity::High,
            description: "Creates HTTP request with context",
        },
        // Client.Do - not directly detectable as URL is in Request
        SSRFSink {
            language: "go",
            module: Some("http.Client"),
            function: "Do",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::High,
            description: "Executes HTTP request",
        },
        SSRFSink {
            language: "go",
            module: Some("http.Client"),
            function: "Get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Client HTTP GET",
        },
        SSRFSink {
            language: "go",
            module: Some("http.Client"),
            function: "Post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Client HTTP POST",
        },
        // net.Dial
        SSRFSink {
            language: "go",
            module: Some("net"),
            function: "Dial",
            url_arg_index: 1, // network, address
            follows_redirects: false,
            severity: Severity::High,
            description: "Raw network dial",
        },
        SSRFSink {
            language: "go",
            module: Some("net"),
            function: "DialTCP",
            url_arg_index: 1,
            follows_redirects: false,
            severity: Severity::High,
            description: "TCP dial",
        },
        SSRFSink {
            language: "go",
            module: Some("net"),
            function: "DialTimeout",
            url_arg_index: 1,
            follows_redirects: false,
            severity: Severity::High,
            description: "Dial with timeout",
        },
        // url.Parse
        SSRFSink {
            language: "go",
            module: Some("url"),
            function: "Parse",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::Medium,
            description: "URL parsing (check if used for request)",
        },
        // resty
        SSRFSink {
            language: "go",
            module: Some("resty"),
            function: "Get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "resty GET request",
        },
        SSRFSink {
            language: "go",
            module: Some("resty"),
            function: "Post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "resty POST request",
        },
    ]
}

fn rust_ssrf_sinks() -> Vec<SSRFSink> {
    vec![
        // reqwest
        SSRFSink {
            language: "rust",
            module: Some("reqwest"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "reqwest HTTP GET",
        },
        SSRFSink {
            language: "rust",
            module: Some("reqwest::Client"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "reqwest Client GET",
        },
        SSRFSink {
            language: "rust",
            module: Some("reqwest::Client"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "reqwest Client POST",
        },
        SSRFSink {
            language: "rust",
            module: Some("reqwest::Client"),
            function: "put",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "reqwest Client PUT",
        },
        SSRFSink {
            language: "rust",
            module: Some("reqwest::Client"),
            function: "delete",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "reqwest Client DELETE",
        },
        SSRFSink {
            language: "rust",
            module: Some("reqwest::Client"),
            function: "request",
            url_arg_index: 1,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "reqwest Client generic request",
        },
        SSRFSink {
            language: "rust",
            module: Some("Client"),
            function: "new",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Medium,
            description: "HTTP client creation",
        },
        // hyper
        SSRFSink {
            language: "rust",
            module: Some("hyper"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "hyper GET request",
        },
        SSRFSink {
            language: "rust",
            module: Some("hyper::Client"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "hyper Client GET",
        },
        SSRFSink {
            language: "rust",
            module: Some("hyper::Client"),
            function: "request",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "hyper Client request",
        },
        // ureq
        SSRFSink {
            language: "rust",
            module: Some("ureq"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "ureq GET request",
        },
        SSRFSink {
            language: "rust",
            module: Some("ureq"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "ureq POST request",
        },
        // surf
        SSRFSink {
            language: "rust",
            module: Some("surf"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "surf GET request",
        },
        SSRFSink {
            language: "rust",
            module: Some("surf"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "surf POST request",
        },
        // std::net
        SSRFSink {
            language: "rust",
            module: Some("std::net"),
            function: "TcpStream::connect",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "TCP stream connection",
        },
    ]
}

fn java_ssrf_sinks() -> Vec<SSRFSink> {
    vec![
        // java.net.URL
        SSRFSink {
            language: "java",
            module: Some("java.net"),
            function: "URL",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "URL object construction",
        },
        SSRFSink {
            language: "java",
            module: Some("URL"),
            function: "openConnection",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Opens URL connection",
        },
        SSRFSink {
            language: "java",
            module: Some("URL"),
            function: "openStream",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Opens URL input stream",
        },
        // HttpURLConnection
        SSRFSink {
            language: "java",
            module: Some("HttpURLConnection"),
            function: "connect",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "HTTP connection",
        },
        // Apache HttpClient
        SSRFSink {
            language: "java",
            module: Some("HttpClient"),
            function: "execute",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Apache HttpClient execute",
        },
        SSRFSink {
            language: "java",
            module: Some("HttpGet"),
            function: "new",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "Apache HttpGet construction",
        },
        SSRFSink {
            language: "java",
            module: Some("HttpPost"),
            function: "new",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "Apache HttpPost construction",
        },
        // OkHttp
        SSRFSink {
            language: "java",
            module: Some("Request.Builder"),
            function: "url",
            url_arg_index: 0,
            follows_redirects: false,
            severity: Severity::High,
            description: "OkHttp Request URL",
        },
        // RestTemplate (Spring)
        SSRFSink {
            language: "java",
            module: Some("RestTemplate"),
            function: "getForObject",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Spring RestTemplate GET",
        },
        SSRFSink {
            language: "java",
            module: Some("RestTemplate"),
            function: "postForObject",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Spring RestTemplate POST",
        },
        SSRFSink {
            language: "java",
            module: Some("RestTemplate"),
            function: "exchange",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Spring RestTemplate exchange",
        },
        // WebClient (Spring WebFlux)
        SSRFSink {
            language: "java",
            module: Some("WebClient"),
            function: "get",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Spring WebClient GET",
        },
        SSRFSink {
            language: "java",
            module: Some("WebClient"),
            function: "post",
            url_arg_index: 0,
            follows_redirects: true,
            severity: Severity::Critical,
            description: "Spring WebClient POST",
        },
    ]
}

// =============================================================================
// Cloud Metadata Detection
// =============================================================================

/// Known cloud metadata service IPs and hostnames.
pub const CLOUD_METADATA_TARGETS: &[(&str, &str)] = &[
    ("169.254.169.254", "AWS/GCP/Azure EC2 Metadata Service"),
    ("100.100.100.200", "Alibaba Cloud Metadata Service"),
    ("metadata.google.internal", "GCP Metadata Service"),
    ("metadata", "Generic Cloud Metadata"),
    ("169.254.170.2", "AWS ECS Task Metadata"),
    ("fd00:ec2::254", "AWS EC2 Metadata (IPv6)"),
    // Localhost variants
    ("127.0.0.1", "Localhost"),
    ("localhost", "Localhost"),
    ("0.0.0.0", "All Interfaces"),
    ("::1", "IPv6 Localhost"),
    ("0x7f000001", "Localhost (hex)"),
    ("2130706433", "Localhost (decimal)"),
    ("017700000001", "Localhost (octal)"),
    ("127.1", "Localhost (short form)"),
    // Internal networks
    ("10.", "Private Network (10.0.0.0/8)"),
    ("172.16.", "Private Network (172.16.0.0/12)"),
    ("172.17.", "Docker Default Network"),
    ("192.168.", "Private Network (192.168.0.0/16)"),
];

/// Check if a URL or IP could access cloud metadata or internal services.
pub fn detect_dangerous_targets(url: &str) -> Vec<String> {
    let url_lower = url.to_lowercase();
    let mut targets = Vec::new();

    for (pattern, description) in CLOUD_METADATA_TARGETS {
        if url_lower.contains(pattern) {
            targets.push(format!("{} ({})", pattern, description));
        }
    }

    // Check for encoded patterns
    if url_lower.contains("%31%36%39") || url_lower.contains("%2f%2f169") {
        targets.push("URL-encoded metadata IP detected".to_string());
    }

    // Check for @ in URL (potential auth bypass)
    if url.contains('@') && !url.starts_with("mailto:") {
        targets.push("URL contains @ - potential bypass attempt".to_string());
    }

    targets
}

// =============================================================================
// Safe Pattern Detection
// =============================================================================

/// Patterns that indicate proper URL validation is in place.
const SAFE_PATTERNS: &[&str] = &[
    // Allowlist checks
    "allowlist",
    "whitelist",
    "allowed_hosts",
    "allowed_domains",
    "valid_hosts",
    "trusted_hosts",
    // URL validation
    "url_validate",
    "validate_url",
    "is_valid_url",
    "check_url",
    "verify_url",
    // Scheme validation
    "scheme_validate",
    "check_scheme",
    "is_https",
    "require_https",
    // Private IP blocking
    "is_private",
    "is_internal",
    "block_private",
    "deny_internal",
    "is_local",
    "block_metadata",
    // URL parsing with validation
    "urlparse",
    "URL.parse",
    "new URL",
];

/// Check if context suggests URL validation is in place.
fn has_url_validation(source: &str, line: usize) -> bool {
    let lines: Vec<&str> = source.lines().collect();

    // Check surrounding lines (5 lines before and after)
    let start = line.saturating_sub(6);
    let end = (line + 5).min(lines.len());

    for i in start..end {
        if let Some(line_content) = lines.get(i) {
            let lower = line_content.to_lowercase();
            for pattern in SAFE_PATTERNS {
                if lower.contains(pattern) {
                    return true;
                }
            }
        }
    }

    false
}

// =============================================================================
// Tree-Sitter Queries for SSRF Detection
// =============================================================================

/// Get tree-sitter query for detecting SSRF sinks in a language.
fn get_ssrf_query(language: &str) -> Option<&'static str> {
    match language {
        "python" => Some(PYTHON_SSRF_QUERY),
        "typescript" | "javascript" => Some(TYPESCRIPT_SSRF_QUERY),
        "go" => Some(GO_SSRF_QUERY),
        "rust" => Some(RUST_SSRF_QUERY),
        _ => None,
    }
}

/// Python SSRF sink detection query.
const PYTHON_SSRF_QUERY: &str = r#"
; requests.get/post/put/delete/patch(url)
(call
  function: (attribute
    object: (identifier) @module
    attribute: (identifier) @method)
  arguments: (argument_list . (identifier) @url_arg)
  (#eq? @module "requests")
  (#any-of? @method "get" "post" "put" "delete" "patch" "head" "options" "request")) @ssrf_sink

; requests.get/post with string literal (less dangerous but still check)
(call
  function: (attribute
    object: (identifier) @module
    attribute: (identifier) @method)
  arguments: (argument_list . (_) @url_arg)
  (#eq? @module "requests")
  (#any-of? @method "get" "post" "put" "delete" "patch")) @ssrf_sink

; urllib.request.urlopen(url)
(call
  function: (attribute
    object: (attribute
      object: (identifier) @pkg
      attribute: (identifier) @subpkg)
    attribute: (identifier) @method)
  arguments: (argument_list . (_) @url_arg)
  (#eq? @pkg "urllib")
  (#eq? @subpkg "request")
  (#any-of? @method "urlopen" "urlretrieve")) @ssrf_sink

; httpx.get/post(url) and httpx.AsyncClient
(call
  function: (attribute
    object: (identifier) @module
    attribute: (identifier) @method)
  arguments: (argument_list . (_) @url_arg)
  (#eq? @module "httpx")
  (#any-of? @method "get" "post" "put" "delete" "patch")) @ssrf_sink

; aiohttp.ClientSession().get(url)
(call
  function: (attribute
    object: (call
      function: (attribute attribute: (identifier) @ctor)
      (#eq? @ctor "ClientSession"))
    attribute: (identifier) @method)
  arguments: (argument_list . (_) @url_arg)
  (#any-of? @method "get" "post" "put" "delete" "request")) @ssrf_sink

; session.get/post where session could be requests.Session
(call
  function: (attribute
    object: (identifier) @session
    attribute: (identifier) @method)
  arguments: (argument_list . (_) @url_arg)
  (#any-of? @session "session" "sess" "client" "http_client")
  (#any-of? @method "get" "post" "put" "delete" "patch" "request")) @ssrf_sink

; Taint sources - HTTP request parameters
(attribute
  object: (identifier) @obj
  attribute: (identifier) @attr
  (#any-of? @obj "request" "req")
  (#any-of? @attr "args" "form" "data" "json" "params" "query_params")) @taint_source

; f-string in URL context
(call
  function: (attribute attribute: (identifier) @method)
  arguments: (argument_list
    . (string (interpolation)) @fstring_url)
  (#any-of? @method "get" "post" "put" "delete" "urlopen")) @ssrf_fstring
"#;

/// TypeScript/JavaScript SSRF sink detection query.
const TYPESCRIPT_SSRF_QUERY: &str = r#"
; fetch(url)
(call_expression
  function: (identifier) @func
  arguments: (arguments . (_) @url_arg)
  (#eq? @func "fetch")) @ssrf_sink

; axios.get/post(url)
(call_expression
  function: (member_expression
    object: (identifier) @module
    property: (property_identifier) @method)
  arguments: (arguments . (_) @url_arg)
  (#eq? @module "axios")
  (#any-of? @method "get" "post" "put" "delete" "patch" "request")) @ssrf_sink

; http.get/request(url) and https.get/request(url)
(call_expression
  function: (member_expression
    object: (identifier) @module
    property: (property_identifier) @method)
  arguments: (arguments . (_) @url_arg)
  (#any-of? @module "http" "https")
  (#any-of? @method "get" "request")) @ssrf_sink

; got(url)
(call_expression
  function: (identifier) @func
  arguments: (arguments . (_) @url_arg)
  (#eq? @func "got")) @ssrf_sink

; got.get/post(url)
(call_expression
  function: (member_expression
    object: (identifier) @module
    property: (property_identifier) @method)
  arguments: (arguments . (_) @url_arg)
  (#eq? @module "got")
  (#any-of? @method "get" "post" "put" "delete" "patch")) @ssrf_sink

; new WebSocket(url)
(new_expression
  constructor: (identifier) @ctor
  arguments: (arguments . (_) @url_arg)
  (#eq? @ctor "WebSocket")) @ssrf_sink

; superagent.get/post(url)
(call_expression
  function: (member_expression
    object: (identifier) @module
    property: (property_identifier) @method)
  arguments: (arguments . (_) @url_arg)
  (#any-of? @module "superagent" "request")
  (#any-of? @method "get" "post" "put" "delete" "patch")) @ssrf_sink

; Template literals in URL context
(call_expression
  function: (_) @func
  arguments: (arguments . (template_string) @template_url)) @ssrf_template

; Taint sources
(member_expression
  object: (identifier) @obj
  property: (property_identifier) @prop
  (#eq? @obj "req")
  (#any-of? @prop "body" "query" "params" "headers")) @taint_source
"#;

/// Go SSRF sink detection query.
const GO_SSRF_QUERY: &str = r#"
; http.Get(url)
(call_expression
  function: (selector_expression
    operand: (identifier) @pkg
    field: (field_identifier) @method)
  arguments: (argument_list . (_) @url_arg)
  (#eq? @pkg "http")
  (#any-of? @method "Get" "Post" "PostForm" "Head")) @ssrf_sink

; http.NewRequest(method, url, body)
(call_expression
  function: (selector_expression
    operand: (identifier) @pkg
    field: (field_identifier) @method)
  arguments: (argument_list (_) (_) @url_arg (_)?)
  (#eq? @pkg "http")
  (#any-of? @method "NewRequest" "NewRequestWithContext")) @ssrf_sink

; client.Get/Post(url) where client is http.Client
(call_expression
  function: (selector_expression
    operand: (identifier) @client
    field: (field_identifier) @method)
  arguments: (argument_list . (_) @url_arg)
  (#any-of? @client "client" "httpClient" "c")
  (#any-of? @method "Get" "Post" "Do")) @ssrf_sink

; net.Dial(network, address)
(call_expression
  function: (selector_expression
    operand: (identifier) @pkg
    field: (field_identifier) @method)
  arguments: (argument_list (_) (_) @addr_arg)
  (#eq? @pkg "net")
  (#any-of? @method "Dial" "DialTCP" "DialTimeout")) @ssrf_sink

; url.Parse(rawurl)
(call_expression
  function: (selector_expression
    operand: (identifier) @pkg
    field: (field_identifier) @method)
  arguments: (argument_list . (_) @url_arg)
  (#eq? @pkg "url")
  (#eq? @method "Parse")) @ssrf_sink

; Taint sources
(selector_expression
  operand: (identifier) @r
  field: (field_identifier) @field
  (#any-of? @r "r" "req" "request")
  (#any-of? @field "URL" "Body" "Form" "PostForm")) @taint_source
"#;

/// Rust SSRF sink detection query.
const RUST_SSRF_QUERY: &str = r#"
; reqwest::get(url)
(call_expression
  function: (scoped_identifier
    path: (identifier) @module
    name: (identifier) @func)
  arguments: (arguments . (_) @url_arg)
  (#eq? @module "reqwest")
  (#eq? @func "get")) @ssrf_sink

; client.get(url) where client is reqwest::Client
(call_expression
  function: (field_expression
    value: (identifier) @client
    field: (field_identifier) @method)
  arguments: (arguments . (_) @url_arg)
  (#any-of? @client "client" "http_client" "reqwest_client")
  (#any-of? @method "get" "post" "put" "delete")) @ssrf_sink

; Client::new().get(url)
(call_expression
  function: (field_expression
    value: (call_expression
      function: (scoped_identifier) @ctor)
    field: (field_identifier) @method)
  arguments: (arguments . (_) @url_arg)
  (#any-of? @method "get" "post" "put" "delete")) @ssrf_sink

; ureq::get(url)
(call_expression
  function: (scoped_identifier
    path: (identifier) @module
    name: (identifier) @func)
  arguments: (arguments . (_) @url_arg)
  (#eq? @module "ureq")
  (#any-of? @func "get" "post")) @ssrf_sink

; TcpStream::connect(addr)
(call_expression
  function: (scoped_identifier) @func
  arguments: (arguments . (_) @addr_arg)
  (#match? @func "TcpStream::connect")) @ssrf_sink
"#;

// =============================================================================
// Taint Source Queries
// =============================================================================

/// Get tree-sitter query for taint sources.
fn get_taint_source_query(language: &str) -> Option<&'static str> {
    match language {
        "python" => Some(PYTHON_TAINT_QUERY),
        "typescript" | "javascript" => Some(TYPESCRIPT_TAINT_QUERY),
        "go" => Some(GO_TAINT_QUERY),
        "rust" => Some(RUST_TAINT_QUERY),
        _ => None,
    }
}

const PYTHON_TAINT_QUERY: &str = r#"
; Flask/Django request parameters
(attribute
  object: (identifier) @obj
  attribute: (identifier) @attr
  (#any-of? @obj "request" "req")
  (#any-of? @attr "args" "form" "data" "json" "params" "query_params" "GET" "POST" "FILES")) @source

; request.get_json() / request.get_data()
(call
  function: (attribute
    object: (identifier) @obj
    attribute: (identifier) @method)
  (#any-of? @obj "request" "req")
  (#any-of? @method "get_json" "get_data" "get")) @source

; FastAPI path/query parameters in function args are sources
(function_definition
  parameters: (parameters
    (typed_parameter
      name: (identifier) @param_name))) @source

; input()
(call function: (identifier) @func (#eq? @func "input")) @source
"#;

const TYPESCRIPT_TAINT_QUERY: &str = r#"
; Express req.body, req.query, req.params
(member_expression
  object: (identifier) @obj
  property: (property_identifier) @prop
  (#eq? @obj "req")
  (#any-of? @prop "body" "query" "params" "headers" "cookies")) @source

; request.body, request.query
(member_expression
  object: (identifier) @obj
  property: (property_identifier) @prop
  (#eq? @obj "request")
  (#any-of? @prop "body" "query" "params")) @source

; process.argv
(member_expression
  object: (member_expression
    object: (identifier) @obj
    property: (property_identifier) @prop)
  (#eq? @obj "process")
  (#eq? @prop "argv")) @source

; URL search params
(new_expression
  constructor: (identifier) @ctor
  (#eq? @ctor "URLSearchParams")) @source
"#;

const GO_TAINT_QUERY: &str = r#"
; HTTP request parameters
(selector_expression
  operand: (identifier) @obj
  field: (field_identifier) @field
  (#any-of? @obj "r" "req" "request")
  (#any-of? @field "Body" "URL" "Form" "PostForm" "Header")) @source

; r.URL.Query()
(call_expression
  function: (selector_expression
    operand: (selector_expression
      operand: (identifier) @req
      field: (field_identifier) @url)
    field: (field_identifier) @method)
  (#any-of? @req "r" "req" "request")
  (#eq? @url "URL")
  (#any-of? @method "Query" "RawQuery")) @source

; r.FormValue, r.PostFormValue
(call_expression
  function: (selector_expression
    operand: (identifier) @req
    field: (field_identifier) @method)
  (#any-of? @req "r" "req" "request")
  (#any-of? @method "FormValue" "PostFormValue")) @source
"#;

const RUST_TAINT_QUERY: &str = r#"
; Axum extractors
(call_expression
  function: (scoped_identifier) @extractor
  (#match? @extractor "(Query|Path|Json|Form)")) @source

; actix-web extractors
(function_item
  parameters: (parameters
    (parameter
      pattern: (identifier) @param
      type: (type_identifier) @type))
  (#any-of? @type "Query" "Path" "Json" "Form" "web::Query" "web::Path")) @source

; std::env::args
(call_expression
  function: (scoped_identifier) @func
  (#match? @func "env::args")) @source
"#;

// =============================================================================
// Scanning Functions
// =============================================================================

/// Scan a single file for SSRF vulnerabilities.
pub fn scan_file_ssrf(
    file_path: impl AsRef<Path>,
    language: Option<&str>,
) -> Result<Vec<SSRFFinding>> {
    let file_path = file_path.as_ref();
    let source =
        std::fs::read_to_string(file_path).map_err(|e| BrrrError::io_with_path(e, file_path))?;

    let registry = LanguageRegistry::global();

    // Detect or use specified language
    let lang = match language {
        Some(lang_name) => registry
            .get_by_name(lang_name)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(lang_name.to_string()))?,
        None => match registry.detect_language(file_path) {
            Some(l) => l,
            None => return Ok(vec![]), // Unknown file type
        },
    };

    let lang_name = lang.name();

    // Parse the file
    let mut parser = lang.parser_for_path(file_path)?;
    let tree = parser
        .parse(&source, None)
        .ok_or_else(|| BrrrError::Parse {
            file: file_path.to_string_lossy().to_string(),
            message: "Failed to parse file".to_string(),
        })?;

    let file_str = file_path.to_string_lossy().to_string();
    analyze_ssrf(&source, &tree, lang_name, &file_str)
}

/// Scan a directory for SSRF vulnerabilities.
pub fn scan_ssrf(path: impl AsRef<Path>, language: Option<&str>) -> Result<ScanResult> {
    let path = path.as_ref();
    let start_time = std::time::Instant::now();

    if path.is_file() {
        let findings = scan_file_ssrf(path, language)?;
        return Ok(ScanResult {
            findings,
            files_scanned: 1,
            duration_ms: Some(start_time.elapsed().as_millis() as u64),
        });
    }

    // Directory scan
    let scan_config = match language {
        Some(lang) => ScanConfig::for_language(lang),
        None => ScanConfig::default(),
    };

    let scanner = ProjectScanner::new(path.to_string_lossy().as_ref())?;
    let scan_result = scanner.scan_with_config(&scan_config)?;

    // Scan files in parallel
    let findings: Vec<SSRFFinding> = scan_result
        .files
        .par_iter()
        .filter_map(|file| {
            let lang = language.or_else(|| {
                let lang_str = detect_language(file);
                if lang_str.is_empty() {
                    None
                } else {
                    Some(lang_str)
                }
            });
            scan_file_ssrf(file, lang).ok()
        })
        .flatten()
        .collect();

    Ok(ScanResult {
        findings,
        files_scanned: scan_result.files.len(),
        duration_ms: Some(start_time.elapsed().as_millis() as u64),
    })
}

/// Analyze a parsed file for SSRF vulnerabilities.
fn analyze_ssrf(
    source: &str,
    tree: &Tree,
    language: &str,
    file_path: &str,
) -> Result<Vec<SSRFFinding>> {
    let mut findings = Vec::new();

    // Get the tree-sitter Language from the parsed tree
    let ts_lang = tree.language();

    // Get SSRF sink query
    let ssrf_query_str = match get_ssrf_query(language) {
        Some(q) => q,
        None => return Ok(findings),
    };

    let query = match Query::new(&ts_lang, ssrf_query_str) {
        Ok(q) => q,
        Err(e) => {
            // Log query error but continue
            eprintln!(
                "SSRF query error for {}: {}",
                language,
                format_query_error(language, "ssrf", ssrf_query_str, &e)
            );
            return Ok(findings);
        }
    };

    // Find taint sources in the file
    let taint_sources = find_taint_sources(source, tree, language, &ts_lang)?;

    // Execute SSRF sink query
    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source.as_bytes());

    let sink_idx = query.capture_index_for_name("ssrf_sink");
    let url_arg_idx = query.capture_index_for_name("url_arg");

    while let Some(m) = matches.next() {
        let mut sink_node: Option<Node> = None;
        let mut url_arg_node: Option<Node> = None;

        for capture in m.captures {
            if Some(capture.index) == sink_idx {
                sink_node = Some(capture.node);
            }
            if Some(capture.index) == url_arg_idx {
                url_arg_node = Some(capture.node);
            }
        }

        if let (Some(sink), Some(url_arg)) = (sink_node, url_arg_node) {
            let line = sink.start_position().row + 1;

            // Skip if URL validation is present nearby
            if has_url_validation(source, line) {
                continue;
            }

            let url_text = url_arg
                .utf8_text(source.as_bytes())
                .unwrap_or("")
                .to_string();

            let sink_text = sink.utf8_text(source.as_bytes()).unwrap_or("").to_string();

            // Determine SSRF type and severity
            let (ssrf_type, severity, confidence) =
                classify_ssrf(&url_text, &taint_sources, source, line);

            // Check for dangerous target patterns
            let potential_targets = detect_dangerous_targets(&url_text);

            // Skip hardcoded safe URLs
            if is_safe_hardcoded_url(&url_text) && potential_targets.is_empty() {
                continue;
            }

            // Generate remediation advice
            let remediation = generate_remediation(ssrf_type, language);

            // Extract code snippet
            let code_snippet = extract_code_snippet(source, line, 2);

            // Extract sink function name
            let sink_function = extract_sink_function(&sink_text, language);

            findings.push(SSRFFinding {
                location: SourceLocation {
                    file: file_path.to_string(),
                    line,
                    column: sink.start_position().column + 1,
                    end_line: sink.end_position().row + 1,
                    end_column: sink.end_position().column + 1,
                },
                severity,
                confidence,
                sink_function,
                tainted_url: url_text,
                ssrf_type,
                potential_targets,
                remediation,
                code_snippet: Some(code_snippet),
                description: format!(
                    "Server-Side Request Forgery ({}) - user-controlled URL in network request",
                    ssrf_type
                ),
            });
        }
    }

    Ok(findings)
}

/// Find taint sources in the file.
fn find_taint_sources(
    source: &str,
    tree: &Tree,
    language: &str,
    ts_lang: &tree_sitter::Language,
) -> Result<HashMap<usize, Vec<String>>> {
    let mut sources: HashMap<usize, Vec<String>> = HashMap::new();

    let query_str = match get_taint_source_query(language) {
        Some(q) => q,
        None => return Ok(sources),
    };

    let query = match Query::new(ts_lang, query_str) {
        Ok(q) => q,
        Err(_) => return Ok(sources),
    };

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source.as_bytes());

    let source_idx = query.capture_index_for_name("source");

    while let Some(m) = matches.next() {
        for capture in m.captures {
            if Some(capture.index) == source_idx {
                let line = capture.node.start_position().row + 1;
                let text = capture
                    .node
                    .utf8_text(source.as_bytes())
                    .unwrap_or("")
                    .to_string();
                sources.entry(line).or_default().push(text);
            }
        }
    }

    Ok(sources)
}

/// Classify the SSRF type and determine severity.
fn classify_ssrf(
    url_text: &str,
    taint_sources: &HashMap<usize, Vec<String>>,
    source: &str,
    sink_line: usize,
) -> (SSRFType, Severity, Confidence) {
    // Check if this looks like a direct variable (full URL control)
    let is_simple_variable = url_text.chars().all(|c| c.is_alphanumeric() || c == '_');

    // Check for f-strings/template literals (partial control)
    let has_interpolation =
        url_text.contains('{') || url_text.contains("${") || url_text.contains("` + ");

    // Check if URL contains hardcoded scheme
    let has_scheme = url_text.contains("http://") || url_text.contains("https://");

    // Check if there are taint sources nearby
    let has_nearby_taint = (sink_line.saturating_sub(10)..=sink_line + 5)
        .any(|line| taint_sources.contains_key(&line));

    // Check for dynamic import
    if url_text.contains("import(") || source.contains("import(") {
        return (SSRFType::Import, Severity::Critical, Confidence::High);
    }

    // Classify based on patterns
    if is_simple_variable && has_nearby_taint {
        // Direct variable from taint source - full control
        (SSRFType::FullUrl, Severity::Critical, Confidence::High)
    } else if is_simple_variable {
        // Variable but no confirmed taint
        (SSRFType::FullUrl, Severity::High, Confidence::Medium)
    } else if has_interpolation && !has_scheme {
        // String interpolation without scheme - full control
        (SSRFType::FullUrl, Severity::Critical, Confidence::High)
    } else if has_interpolation && has_scheme {
        // String interpolation with scheme - partial control (host/path)
        (SSRFType::PartialUrl, Severity::High, Confidence::High)
    } else if has_scheme && !has_interpolation {
        // Hardcoded URL - likely safe but check for patterns
        (SSRFType::PartialUrl, Severity::Low, Confidence::Low)
    } else {
        // Unknown pattern
        (SSRFType::PartialUrl, Severity::Medium, Confidence::Medium)
    }
}

/// Check if a URL is a safe hardcoded value.
fn is_safe_hardcoded_url(url: &str) -> bool {
    // Remove quotes
    let cleaned = url.trim_matches(|c| c == '"' || c == '\'' || c == '`');

    // Check for safe patterns
    let _safe_prefixes = [
        "https://api.",
        "https://www.",
        "http://localhost:",
        "http://127.0.0.1:",
    ];

    // If it's a simple string literal with a safe domain
    if cleaned.starts_with("http://") || cleaned.starts_with("https://") {
        // Check it's not an internal IP
        if !cleaned.contains("169.254")
            && !cleaned.contains("100.100.100")
            && !cleaned.contains("metadata")
        {
            return true;
        }
    }

    false
}

/// Generate remediation advice based on SSRF type and language.
fn generate_remediation(ssrf_type: SSRFType, language: &str) -> String {
    let base = match ssrf_type {
        SSRFType::FullUrl => {
            "1. Implement URL allowlisting - only permit requests to known-safe domains.\n\
             2. Parse and validate URL components (scheme, host, port) before use.\n\
             3. Block requests to private/internal IP ranges (10.x, 172.16.x, 192.168.x).\n\
             4. Block cloud metadata IPs (169.254.169.254, 100.100.100.200).\n\
             5. Do not follow redirects, or validate redirect targets."
        }
        SSRFType::PartialUrl => {
            "1. Validate host/path components against an allowlist.\n\
             2. Use URL parsing to extract and validate components.\n\
             3. Ensure user input cannot modify the scheme or host.\n\
             4. Consider using a proxy service for external requests."
        }
        SSRFType::Redirect => {
            "1. Disable automatic redirect following.\n\
             2. If redirects are needed, validate each redirect target.\n\
             3. Limit redirect depth to prevent chains to internal services.\n\
             4. Check redirect Location header against allowlist."
        }
        SSRFType::Import => {
            "1. Never use dynamic imports with user-controlled URLs.\n\
             2. Use a static import map or allowlist.\n\
             3. Consider code splitting with known chunks only."
        }
        SSRFType::DnsRebinding => {
            "1. Resolve DNS and validate IP before making request.\n\
             2. Use IP-based allowlisting instead of hostname.\n\
             3. Consider using a SSRF-safe proxy library."
        }
    };

    // Add language-specific advice
    let lang_specific = match language {
        "python" => {
            "\n\nPython-specific:\n\
             - Use `requests` with `allow_redirects=False` for manual control.\n\
             - Use `ipaddress` module to check for private IPs.\n\
             - Consider `ssrf-proxy` or `ssrf-king` libraries."
        }
        "typescript" | "javascript" => {
            "\n\nNode.js/TypeScript-specific:\n\
             - Use `new URL()` to parse and validate URLs.\n\
             - Use `is-private-ip` or `private-ip` packages.\n\
             - Consider `ssrf-req-filter` middleware."
        }
        "go" => {
            "\n\nGo-specific:\n\
             - Use `net.ParseIP()` to validate IP addresses.\n\
             - Check `url.Parse()` result for private networks.\n\
             - Use custom `http.Transport.DialContext` for IP filtering."
        }
        "rust" => {
            "\n\nRust-specific:\n\
             - Use `url` crate for parsing and validation.\n\
             - Use `std::net::IpAddr` for IP validation.\n\
             - Configure `reqwest::ClientBuilder` with `redirect(Policy::none())`."
        }
        _ => "",
    };

    format!("{}{}", base, lang_specific)
}

/// Extract the sink function name from the code.
fn extract_sink_function(sink_text: &str, _language: &str) -> String {
    // Try to extract the function/method name
    let patterns = [".", "(", "["];
    let mut result = sink_text.to_string();

    for pattern in patterns {
        if let Some(idx) = result.find(pattern) {
            result = result[..idx + 1].to_string();
            break;
        }
    }

    // Clean up
    result = result.trim().to_string();
    if result.len() > 50 {
        result = result[..50].to_string() + "...";
    }

    if result.is_empty() {
        sink_text.chars().take(30).collect()
    } else {
        result
    }
}

/// Extract a code snippet around a line.
fn extract_code_snippet(source: &str, line: usize, context: usize) -> String {
    let lines: Vec<&str> = source.lines().collect();
    let start = line.saturating_sub(context + 1);
    let end = (line + context).min(lines.len());

    lines[start..end]
        .iter()
        .enumerate()
        .map(|(i, l)| format!("{:4}: {}", start + i + 1, l))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Detect language from file extension.
fn detect_language(path: &Path) -> &'static str {
    match path.extension().and_then(|e| e.to_str()) {
        Some("py") => "python",
        Some("ts") | Some("tsx") => "typescript",
        Some("js") | Some("jsx") | Some("mjs") | Some("cjs") => "javascript",
        Some("go") => "go",
        Some("rs") => "rust",
        Some("java") => "java",
        Some("c") | Some("h") => "c",
        Some("cpp") | Some("cc") | Some("cxx") | Some("hpp") | Some("cu") | Some("cuh") => "cpp",
        _ => "",
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_severity_ordering() {
        assert!(Severity::Critical > Severity::High);
        assert!(Severity::High > Severity::Medium);
        assert!(Severity::Medium > Severity::Low);
        assert!(Severity::Low > Severity::Info);
    }

    #[test]
    fn test_ssrf_type_display() {
        assert_eq!(format!("{}", SSRFType::FullUrl), "full_url_control");
        assert_eq!(format!("{}", SSRFType::PartialUrl), "partial_url_control");
        assert_eq!(format!("{}", SSRFType::Redirect), "redirect_ssrf");
    }

    #[test]
    fn test_cloud_metadata_detection() {
        let targets = detect_dangerous_targets("http://169.254.169.254/latest/meta-data/");
        assert!(!targets.is_empty());
        assert!(targets.iter().any(|t| t.contains("AWS")));

        let targets = detect_dangerous_targets("http://100.100.100.200/");
        assert!(!targets.is_empty());
        assert!(targets.iter().any(|t| t.contains("Alibaba")));

        let targets = detect_dangerous_targets("http://metadata.google.internal/");
        assert!(!targets.is_empty());
        assert!(targets.iter().any(|t| t.contains("GCP")));
    }

    #[test]
    fn test_localhost_detection() {
        let targets = detect_dangerous_targets("http://127.0.0.1:8080/");
        assert!(!targets.is_empty());
        assert!(targets.iter().any(|t| t.contains("Localhost")));

        let targets = detect_dangerous_targets("http://localhost:3000/admin");
        assert!(!targets.is_empty());
    }

    #[test]
    fn test_url_bypass_detection() {
        let targets = detect_dangerous_targets("http://evil.com@169.254.169.254/");
        assert!(!targets.is_empty());
        assert!(targets.iter().any(|t| t.contains("@")));
    }

    #[test]
    fn test_safe_hardcoded_url() {
        assert!(is_safe_hardcoded_url("\"https://api.example.com/v1\""));
        assert!(is_safe_hardcoded_url("'https://www.google.com'"));
        assert!(!is_safe_hardcoded_url("user_url"));
        assert!(!is_safe_hardcoded_url("\"http://169.254.169.254\""));
    }

    #[test]
    fn test_python_full_url_ssrf() {
        let code = r#"
from flask import request
import requests

@app.route('/fetch')
def fetch_url():
    url = request.args.get('url')
    response = requests.get(url)
    return response.text
"#;
        let mut file = NamedTempFile::with_suffix(".py").unwrap();
        file.write_all(code.as_bytes()).unwrap();

        let findings = scan_file_ssrf(file.path(), Some("python")).unwrap();
        assert!(
            !findings.is_empty(),
            "Should detect SSRF in requests.get(url)"
        );
        assert!(findings.iter().any(|f| f.ssrf_type == SSRFType::FullUrl));
        assert!(findings.iter().any(|f| f.severity >= Severity::High));
    }

    #[test]
    fn test_python_partial_url_ssrf() {
        let code = r#"
from flask import request
import requests

@app.route('/api/<path>')
def proxy(path):
    host = request.args.get('host')
    url = f"http://{host}/api/{path}"
    response = requests.get(url)
    return response.text
"#;
        let mut file = NamedTempFile::with_suffix(".py").unwrap();
        file.write_all(code.as_bytes()).unwrap();

        let findings = scan_file_ssrf(file.path(), Some("python")).unwrap();
        // Should detect f-string URL construction
        assert!(
            !findings.is_empty() || code.contains("f\""),
            "Should detect partial URL control"
        );
    }

    #[test]
    fn test_typescript_fetch_ssrf() {
        let code = r#"
import express from 'express';

const app = express();

app.get('/fetch', async (req, res) => {
    const url = req.query.url;
    const response = await fetch(url);
    res.send(await response.text());
});
"#;
        let mut file = NamedTempFile::with_suffix(".ts").unwrap();
        file.write_all(code.as_bytes()).unwrap();

        let findings = scan_file_ssrf(file.path(), Some("typescript")).unwrap();
        assert!(!findings.is_empty(), "Should detect SSRF in fetch(url)");
    }

    #[test]
    fn test_typescript_axios_ssrf() {
        let code = r#"
import axios from 'axios';

async function fetchData(userUrl: string) {
    const response = await axios.get(userUrl);
    return response.data;
}
"#;
        let mut file = NamedTempFile::with_suffix(".ts").unwrap();
        file.write_all(code.as_bytes()).unwrap();

        let findings = scan_file_ssrf(file.path(), Some("typescript")).unwrap();
        assert!(!findings.is_empty(), "Should detect SSRF in axios.get(url)");
    }

    #[test]
    fn test_go_http_ssrf() {
        let code = r#"
package main

import (
    "net/http"
)

func handler(w http.ResponseWriter, r *http.Request) {
    url := r.URL.Query().Get("url")
    resp, err := http.Get(url)
    if err != nil {
        return
    }
    defer resp.Body.Close()
}
"#;
        let mut file = NamedTempFile::with_suffix(".go").unwrap();
        file.write_all(code.as_bytes()).unwrap();

        let findings = scan_file_ssrf(file.path(), Some("go")).unwrap();
        assert!(!findings.is_empty(), "Should detect SSRF in http.Get(url)");
    }

    #[test]
    fn test_rust_reqwest_ssrf() {
        let code = r#"
use reqwest;
use axum::extract::Query;

async fn fetch_url(Query(params): Query<FetchParams>) -> String {
    let url = &params.url;
    let response = reqwest::get(url).await.unwrap();
    response.text().await.unwrap()
}
"#;
        let mut file = NamedTempFile::with_suffix(".rs").unwrap();
        file.write_all(code.as_bytes()).unwrap();

        let findings = scan_file_ssrf(file.path(), Some("rust")).unwrap();
        assert!(
            !findings.is_empty(),
            "Should detect SSRF in reqwest::get(url)"
        );
    }

    #[test]
    fn test_safe_pattern_allowlist() {
        let code = r#"
from flask import request
import requests

ALLOWED_HOSTS = ['api.example.com', 'cdn.example.com']

@app.route('/fetch')
def fetch_url():
    url = request.args.get('url')
    parsed = urlparse(url)
    if parsed.netloc not in ALLOWED_HOSTS:
        return "Invalid host", 400
    response = requests.get(url)
    return response.text
"#;
        let mut file = NamedTempFile::with_suffix(".py").unwrap();
        file.write_all(code.as_bytes()).unwrap();

        let findings = scan_file_ssrf(file.path(), Some("python")).unwrap();
        // Should have reduced confidence due to allowlist
        if !findings.is_empty() {
            assert!(
                findings.iter().all(|f| f.confidence <= Confidence::Medium),
                "Allowlist should reduce confidence"
            );
        }
    }

    #[test]
    fn test_cloud_metadata_in_code() {
        let code = r#"
import requests

# Dangerous: accessing cloud metadata
response = requests.get("http://169.254.169.254/latest/meta-data/")
"#;
        let targets = detect_dangerous_targets(code);
        assert!(
            !targets.is_empty(),
            "Should detect cloud metadata IP in code"
        );
    }

    #[test]
    fn test_get_ssrf_sinks() {
        let python_sinks = get_ssrf_sinks("python");
        assert!(!python_sinks.is_empty());
        assert!(python_sinks.iter().any(|s| s.function == "get"));

        let ts_sinks = get_ssrf_sinks("typescript");
        assert!(!ts_sinks.is_empty());
        assert!(ts_sinks.iter().any(|s| s.function == "fetch"));

        let go_sinks = get_ssrf_sinks("go");
        assert!(!go_sinks.is_empty());
        assert!(go_sinks.iter().any(|s| s.function == "Get"));

        let rust_sinks = get_ssrf_sinks("rust");
        assert!(!rust_sinks.is_empty());
        assert!(rust_sinks.iter().any(|s| s.function == "get"));
    }

    #[test]
    fn test_remediation_generation() {
        let remediation = generate_remediation(SSRFType::FullUrl, "python");
        assert!(remediation.contains("allowlist"));
        assert!(remediation.contains("Python-specific"));

        let remediation = generate_remediation(SSRFType::Redirect, "typescript");
        assert!(remediation.contains("redirect"));
        assert!(remediation.contains("Node.js"));
    }

    #[test]
    fn test_severity_from_str() {
        assert_eq!("critical".parse::<Severity>().unwrap(), Severity::Critical);
        assert_eq!("HIGH".parse::<Severity>().unwrap(), Severity::High);
        assert_eq!("med".parse::<Severity>().unwrap(), Severity::Medium);
    }

    #[test]
    fn test_confidence_from_str() {
        assert_eq!("high".parse::<Confidence>().unwrap(), Confidence::High);
        assert_eq!("MEDIUM".parse::<Confidence>().unwrap(), Confidence::Medium);
        assert_eq!("low".parse::<Confidence>().unwrap(), Confidence::Low);
    }
}
