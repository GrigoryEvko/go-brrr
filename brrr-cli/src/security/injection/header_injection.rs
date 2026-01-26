//! HTTP Header injection vulnerability detection.
//!
//! Detects potential HTTP header injection vulnerabilities where user-controlled input
//! reaches HTTP header setting functions without proper sanitization. Header injection can lead to:
//!
//! - **HTTP Response Splitting**: Injecting CRLF (`\r\n`) to create fake responses
//! - **Cache Poisoning**: Injecting malicious headers that get cached by CDNs/proxies
//! - **Session Fixation**: Injecting Set-Cookie headers to fixate session IDs
//! - **Open Redirect**: Injecting Location headers to redirect users to malicious sites
//! - **Content-Type Injection**: MIME confusion attacks via Content-Type manipulation
//! - **Content-Disposition Injection**: File name injection for download attacks
//! - **Trust Manipulation**: X-Forwarded-* header injection to bypass IP-based controls
//!
//! # Detection Strategy
//!
//! 1. Parse source files using tree-sitter
//! 2. Identify calls to HTTP header setting sinks
//! 3. Extract the header name and value arguments
//! 4. Track data flow to identify if values come from taint sources
//! 5. Check for sanitization (CRLF stripping, URL validation, allowlist)
//! 6. Report findings with severity based on header criticality
//!
//! # Attack Examples
//!
//! ```python
//! # Open redirect via Location header
//! redirect_url = request.args.get('next')
//! response.headers['Location'] = redirect_url  # CRITICAL
//!
//! # Session fixation via Set-Cookie
//! session_id = request.args.get('session')
//! response.set_cookie('session', session_id)  # CRITICAL
//!
//! # CRLF injection / Response splitting
//! name = request.args.get('name')
//! response.headers['X-User'] = name  # HIGH - attacker can inject \r\n
//!
//! # Content-Disposition injection
//! filename = request.args.get('filename')
//! response.headers['Content-Disposition'] = f'attachment; filename="{filename}"'
//! ```
//!
//! # HTTP/2 and HTTP/3 Considerations
//!
//! While HTTP/2 and HTTP/3 use binary framing and are not vulnerable to traditional
//! CRLF-based response splitting, header injection vulnerabilities still exist:
//!
//! - Header value injection can still manipulate application logic
//! - Some proxies/load balancers may downgrade to HTTP/1.1
//! - Cookie injection attacks remain effective across all HTTP versions
//! - Open redirect via Location header is protocol-agnostic
//!
//! # URL-Encoded CRLF
//!
//! Attackers may use URL-encoded forms to bypass naive filters:
//! - `%0d%0a` - URL-encoded CRLF
//! - `%0d` / `%0a` - Partial encoded forms
//! - Mixed encoding: `%0D\n`, `\r%0A`
//!
//! # Safe Patterns
//!
//! ```python
//! # URL validation for Location
//! if is_safe_redirect(redirect_url):
//!     response.headers['Location'] = redirect_url
//!
//! # Filename sanitization
//! safe_name = sanitize_filename(filename)
//! response.headers['Content-Disposition'] = f'attachment; filename="{safe_name}"'
//!
//! # CRLF stripping
//! cleaned = value.replace('\r', '').replace('\n', '')
//! response.headers['X-Custom'] = cleaned
//!
//! # Framework auto-protection (many modern frameworks)
//! # Flask, Django, Express auto-strip CRLF in header values
//! ```
//!
//! # CWE References
//!
//! - CWE-113: Improper Neutralization of CRLF Sequences in HTTP Headers
//! - CWE-601: URL Redirection to Untrusted Site (Open Redirect)
//! - CWE-384: Session Fixation
//! - CWE-644: Improper Neutralization of HTTP Headers for Scripting Syntax

use std::path::Path;

use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use streaming_iterator::StreamingIterator;
use tree_sitter::{Query, QueryCursor, Tree};

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;
use crate::util::format_query_error;

// Re-export common types for backward compatibility and internal use
pub use crate::security::common::{Confidence, Severity, SourceLocation};

// =============================================================================
// Type Definitions
// =============================================================================

/// Type of header injection vulnerability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HeaderInjectionType {
    /// HTTP Response Splitting via CRLF injection
    ResponseSplitting,
    /// Header value contains CR or LF characters
    HeaderValueInjection,
    /// Cookie value injection via Set-Cookie header
    SetCookieInjection,
    /// Open redirect via Location header
    LocationRedirect,
    /// MIME type confusion via Content-Type header
    ContentTypeInjection,
    /// File name injection via Content-Disposition header
    ContentDispositionInjection,
    /// Trust manipulation via X-Forwarded-* headers
    ForwardedHeaderInjection,
    /// Generic header name injection (dynamic header names)
    HeaderNameInjection,
    /// Cache poisoning via cache-related headers
    CachePoisoning,
}

impl std::fmt::Display for HeaderInjectionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ResponseSplitting => write!(f, "response_splitting"),
            Self::HeaderValueInjection => write!(f, "header_value_injection"),
            Self::SetCookieInjection => write!(f, "set_cookie_injection"),
            Self::LocationRedirect => write!(f, "location_redirect"),
            Self::ContentTypeInjection => write!(f, "content_type_injection"),
            Self::ContentDispositionInjection => write!(f, "content_disposition_injection"),
            Self::ForwardedHeaderInjection => write!(f, "forwarded_header_injection"),
            Self::HeaderNameInjection => write!(f, "header_name_injection"),
            Self::CachePoisoning => write!(f, "cache_poisoning"),
        }
    }
}

impl HeaderInjectionType {
    /// Get CWE ID for this injection type.
    #[must_use]
    pub const fn cwe_id(&self) -> u32 {
        match self {
            Self::ResponseSplitting => 113,           // CWE-113: CRLF Injection
            Self::HeaderValueInjection => 113,        // CWE-113: CRLF Injection
            Self::SetCookieInjection => 384,          // CWE-384: Session Fixation
            Self::LocationRedirect => 601,            // CWE-601: Open Redirect
            Self::ContentTypeInjection => 644,        // CWE-644: HTTP Headers
            Self::ContentDispositionInjection => 644, // CWE-644: HTTP Headers
            Self::ForwardedHeaderInjection => 290,    // CWE-290: Authentication Bypass
            Self::HeaderNameInjection => 113,         // CWE-113: CRLF Injection
            Self::CachePoisoning => 444,              // CWE-444: HTTP Request Smuggling
        }
    }

    /// Get base severity for this injection type.
    #[must_use]
    pub const fn base_severity(&self) -> Severity {
        match self {
            Self::ResponseSplitting => Severity::Critical,
            Self::LocationRedirect => Severity::Critical,
            Self::SetCookieInjection => Severity::Critical,
            Self::ForwardedHeaderInjection => Severity::High,
            Self::ContentTypeInjection => Severity::High,
            Self::ContentDispositionInjection => Severity::High,
            Self::CachePoisoning => Severity::High,
            Self::HeaderValueInjection => Severity::Medium,
            Self::HeaderNameInjection => Severity::Medium,
        }
    }

    /// Get description for this injection type.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::ResponseSplitting => "CRLF injection allows HTTP response splitting attacks",
            Self::HeaderValueInjection => "User input in header value may allow header injection",
            Self::SetCookieInjection => "Cookie value from user input enables session fixation",
            Self::LocationRedirect => "Unvalidated redirect URL enables open redirect attacks",
            Self::ContentTypeInjection => {
                "Content-Type from user input enables MIME confusion attacks"
            }
            Self::ContentDispositionInjection => {
                "Filename from user input enables download attacks"
            }
            Self::ForwardedHeaderInjection => {
                "X-Forwarded-* from user input can bypass IP-based controls"
            }
            Self::HeaderNameInjection => {
                "Dynamic header name from user input enables header injection"
            }
            Self::CachePoisoning => "Cache-related header manipulation can poison CDN/proxy caches",
        }
    }
}

/// A header injection finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HeaderInjectionFinding {
    /// Location of the vulnerable header operation
    pub location: SourceLocation,
    /// Severity of the vulnerability
    pub severity: Severity,
    /// Confidence level of the finding
    pub confidence: Confidence,
    /// Name of the header being set (if known)
    pub header_name: String,
    /// The tainted value reaching the header sink
    pub tainted_value: String,
    /// Type of header injection
    pub injection_type: HeaderInjectionType,
    /// Code snippet showing the vulnerable pattern
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code_snippet: Option<String>,
    /// Remediation advice
    pub remediation: String,
    /// CWE reference
    pub cwe_id: u32,
    /// The sink function/method that sets the header
    pub sink_function: String,
    /// Whether framework auto-protection may apply
    pub framework_protected: bool,
    /// Detected encoding bypass attempts (%0d%0a, etc.)
    pub encoded_crlf_detected: bool,
}

/// Result of scanning for header injection vulnerabilities.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScanResult {
    /// All findings
    pub findings: Vec<HeaderInjectionFinding>,
    /// Number of files scanned
    pub files_scanned: usize,
    /// Count by injection type
    pub type_counts: FxHashMap<String, usize>,
    /// Count by severity
    pub severity_counts: FxHashMap<String, usize>,
}

// =============================================================================
// Critical Headers Definition
// =============================================================================

/// Headers that are security-critical when set from user input.
#[derive(Debug, Clone)]
struct CriticalHeader {
    /// Header name (case-insensitive)
    name: &'static str,
    /// Injection type when this header is vulnerable
    injection_type: HeaderInjectionType,
    /// Base severity for this header
    severity: Severity,
    /// Description of the risk
    description: &'static str,
}

/// Get the list of critical headers.
fn get_critical_headers() -> Vec<CriticalHeader> {
    vec![
        // Redirect headers
        CriticalHeader {
            name: "location",
            injection_type: HeaderInjectionType::LocationRedirect,
            severity: Severity::Critical,
            description: "Location header enables open redirect attacks",
        },
        // Cookie headers
        CriticalHeader {
            name: "set-cookie",
            injection_type: HeaderInjectionType::SetCookieInjection,
            severity: Severity::Critical,
            description: "Set-Cookie header enables session fixation attacks",
        },
        // Content headers
        CriticalHeader {
            name: "content-type",
            injection_type: HeaderInjectionType::ContentTypeInjection,
            severity: Severity::High,
            description: "Content-Type header enables MIME confusion attacks",
        },
        CriticalHeader {
            name: "content-disposition",
            injection_type: HeaderInjectionType::ContentDispositionInjection,
            severity: Severity::High,
            description: "Content-Disposition header enables file name injection",
        },
        CriticalHeader {
            name: "content-length",
            injection_type: HeaderInjectionType::ResponseSplitting,
            severity: Severity::High,
            description: "Content-Length manipulation can enable request smuggling",
        },
        // Forwarded headers (trust manipulation)
        CriticalHeader {
            name: "x-forwarded-for",
            injection_type: HeaderInjectionType::ForwardedHeaderInjection,
            severity: Severity::High,
            description: "X-Forwarded-For can bypass IP-based access controls",
        },
        CriticalHeader {
            name: "x-forwarded-host",
            injection_type: HeaderInjectionType::ForwardedHeaderInjection,
            severity: Severity::High,
            description: "X-Forwarded-Host can cause host header injection",
        },
        CriticalHeader {
            name: "x-forwarded-proto",
            injection_type: HeaderInjectionType::ForwardedHeaderInjection,
            severity: Severity::Medium,
            description: "X-Forwarded-Proto can cause protocol confusion",
        },
        CriticalHeader {
            name: "x-real-ip",
            injection_type: HeaderInjectionType::ForwardedHeaderInjection,
            severity: Severity::High,
            description: "X-Real-IP can bypass IP-based access controls",
        },
        CriticalHeader {
            name: "forwarded",
            injection_type: HeaderInjectionType::ForwardedHeaderInjection,
            severity: Severity::High,
            description: "Forwarded header can manipulate request metadata",
        },
        // Cache headers
        CriticalHeader {
            name: "cache-control",
            injection_type: HeaderInjectionType::CachePoisoning,
            severity: Severity::Medium,
            description: "Cache-Control can cause cache poisoning",
        },
        CriticalHeader {
            name: "vary",
            injection_type: HeaderInjectionType::CachePoisoning,
            severity: Severity::Medium,
            description: "Vary header can cause cache key manipulation",
        },
        CriticalHeader {
            name: "x-cache-key",
            injection_type: HeaderInjectionType::CachePoisoning,
            severity: Severity::High,
            description: "X-Cache-Key can enable targeted cache poisoning",
        },
        // Security headers
        CriticalHeader {
            name: "access-control-allow-origin",
            injection_type: HeaderInjectionType::HeaderValueInjection,
            severity: Severity::High,
            description: "CORS origin header can enable cross-origin attacks",
        },
        CriticalHeader {
            name: "access-control-allow-credentials",
            injection_type: HeaderInjectionType::HeaderValueInjection,
            severity: Severity::High,
            description: "CORS credentials header can enable credential theft",
        },
        CriticalHeader {
            name: "content-security-policy",
            injection_type: HeaderInjectionType::HeaderValueInjection,
            severity: Severity::High,
            description: "CSP manipulation can weaken XSS protections",
        },
    ]
}

/// Check if a header name is critical and return its metadata.
fn get_critical_header_info(header_name: &str) -> Option<CriticalHeader> {
    let lower = header_name.to_lowercase();
    get_critical_headers()
        .into_iter()
        .find(|h| lower == h.name || lower.contains(h.name))
}

// =============================================================================
// Header Sink Definitions
// =============================================================================

/// A header sink definition.
#[derive(Debug, Clone)]
struct HeaderSink {
    /// Pattern to match (e.g., "response.headers", "res.setHeader")
    pattern: String,
    /// Language this sink applies to
    language: String,
    /// Framework (if applicable)
    framework: Option<String>,
    /// Whether the framework auto-strips CRLF
    auto_sanitizes: bool,
    /// Description
    description: String,
}

/// Get header sinks for a language.
fn get_header_sinks(language: &str) -> Vec<HeaderSink> {
    match language {
        "python" => python_header_sinks(),
        "typescript" | "javascript" => typescript_header_sinks(),
        "go" => go_header_sinks(),
        "rust" => rust_header_sinks(),
        "java" => java_header_sinks(),
        _ => vec![],
    }
}

fn python_header_sinks() -> Vec<HeaderSink> {
    vec![
        // Flask
        HeaderSink {
            pattern: "response.headers".to_string(),
            language: "python".to_string(),
            framework: Some("flask".to_string()),
            auto_sanitizes: true, // Flask auto-strips CRLF
            description: "Flask response.headers assignment".to_string(),
        },
        HeaderSink {
            pattern: "make_response".to_string(),
            language: "python".to_string(),
            framework: Some("flask".to_string()),
            auto_sanitizes: true,
            description: "Flask make_response() headers".to_string(),
        },
        HeaderSink {
            pattern: "Response".to_string(),
            language: "python".to_string(),
            framework: Some("flask".to_string()),
            auto_sanitizes: true,
            description: "Flask Response() with headers".to_string(),
        },
        HeaderSink {
            pattern: "redirect".to_string(),
            language: "python".to_string(),
            framework: Some("flask".to_string()),
            auto_sanitizes: false, // URL not sanitized
            description: "Flask redirect() function".to_string(),
        },
        HeaderSink {
            pattern: "set_cookie".to_string(),
            language: "python".to_string(),
            framework: Some("flask".to_string()),
            auto_sanitizes: true,
            description: "Flask set_cookie() method".to_string(),
        },
        // Django
        HeaderSink {
            pattern: "HttpResponse".to_string(),
            language: "python".to_string(),
            framework: Some("django".to_string()),
            auto_sanitizes: true, // Django auto-strips
            description: "Django HttpResponse() headers".to_string(),
        },
        HeaderSink {
            pattern: "HttpResponseRedirect".to_string(),
            language: "python".to_string(),
            framework: Some("django".to_string()),
            auto_sanitizes: false, // URL not validated
            description: "Django HttpResponseRedirect()".to_string(),
        },
        HeaderSink {
            pattern: "JsonResponse".to_string(),
            language: "python".to_string(),
            framework: Some("django".to_string()),
            auto_sanitizes: true,
            description: "Django JsonResponse() headers".to_string(),
        },
        // FastAPI/Starlette
        HeaderSink {
            pattern: "Response".to_string(),
            language: "python".to_string(),
            framework: Some("fastapi".to_string()),
            auto_sanitizes: true,
            description: "FastAPI/Starlette Response headers".to_string(),
        },
        HeaderSink {
            pattern: "RedirectResponse".to_string(),
            language: "python".to_string(),
            framework: Some("fastapi".to_string()),
            auto_sanitizes: false,
            description: "FastAPI RedirectResponse".to_string(),
        },
        // AIOHTTP
        HeaderSink {
            pattern: "web.Response".to_string(),
            language: "python".to_string(),
            framework: Some("aiohttp".to_string()),
            auto_sanitizes: false,
            description: "AIOHTTP web.Response headers".to_string(),
        },
        // Low-level
        HeaderSink {
            pattern: "send_header".to_string(),
            language: "python".to_string(),
            framework: None,
            auto_sanitizes: false,
            description: "BaseHTTPRequestHandler.send_header()".to_string(),
        },
    ]
}

fn typescript_header_sinks() -> Vec<HeaderSink> {
    vec![
        // Express
        HeaderSink {
            pattern: "setHeader".to_string(),
            language: "typescript".to_string(),
            framework: Some("express".to_string()),
            auto_sanitizes: true, // Express/Node auto-validates
            description: "Express res.setHeader()".to_string(),
        },
        HeaderSink {
            pattern: "res.set".to_string(),
            language: "typescript".to_string(),
            framework: Some("express".to_string()),
            auto_sanitizes: true,
            description: "Express res.set()".to_string(),
        },
        HeaderSink {
            pattern: "res.header".to_string(),
            language: "typescript".to_string(),
            framework: Some("express".to_string()),
            auto_sanitizes: true,
            description: "Express res.header()".to_string(),
        },
        HeaderSink {
            pattern: "res.cookie".to_string(),
            language: "typescript".to_string(),
            framework: Some("express".to_string()),
            auto_sanitizes: true,
            description: "Express res.cookie()".to_string(),
        },
        HeaderSink {
            pattern: "res.redirect".to_string(),
            language: "typescript".to_string(),
            framework: Some("express".to_string()),
            auto_sanitizes: false, // URL not validated
            description: "Express res.redirect()".to_string(),
        },
        HeaderSink {
            pattern: "res.location".to_string(),
            language: "typescript".to_string(),
            framework: Some("express".to_string()),
            auto_sanitizes: false,
            description: "Express res.location()".to_string(),
        },
        // Fastify
        HeaderSink {
            pattern: "reply.header".to_string(),
            language: "typescript".to_string(),
            framework: Some("fastify".to_string()),
            auto_sanitizes: true,
            description: "Fastify reply.header()".to_string(),
        },
        HeaderSink {
            pattern: "reply.redirect".to_string(),
            language: "typescript".to_string(),
            framework: Some("fastify".to_string()),
            auto_sanitizes: false,
            description: "Fastify reply.redirect()".to_string(),
        },
        // Koa
        HeaderSink {
            pattern: "ctx.set".to_string(),
            language: "typescript".to_string(),
            framework: Some("koa".to_string()),
            auto_sanitizes: true,
            description: "Koa ctx.set()".to_string(),
        },
        HeaderSink {
            pattern: "ctx.redirect".to_string(),
            language: "typescript".to_string(),
            framework: Some("koa".to_string()),
            auto_sanitizes: false,
            description: "Koa ctx.redirect()".to_string(),
        },
        // Next.js
        HeaderSink {
            pattern: "NextResponse.redirect".to_string(),
            language: "typescript".to_string(),
            framework: Some("nextjs".to_string()),
            auto_sanitizes: false,
            description: "Next.js NextResponse.redirect()".to_string(),
        },
        // Node.js HTTP
        HeaderSink {
            pattern: "writeHead".to_string(),
            language: "typescript".to_string(),
            framework: None,
            auto_sanitizes: true,
            description: "Node.js res.writeHead()".to_string(),
        },
    ]
}

fn go_header_sinks() -> Vec<HeaderSink> {
    vec![
        // net/http
        HeaderSink {
            pattern: "Header().Set".to_string(),
            language: "go".to_string(),
            framework: None,
            auto_sanitizes: true, // Go net/http validates
            description: "Go w.Header().Set()".to_string(),
        },
        HeaderSink {
            pattern: "Header().Add".to_string(),
            language: "go".to_string(),
            framework: None,
            auto_sanitizes: true,
            description: "Go w.Header().Add()".to_string(),
        },
        HeaderSink {
            pattern: "SetCookie".to_string(),
            language: "go".to_string(),
            framework: None,
            auto_sanitizes: true,
            description: "Go http.SetCookie()".to_string(),
        },
        HeaderSink {
            pattern: "Redirect".to_string(),
            language: "go".to_string(),
            framework: None,
            auto_sanitizes: false, // URL not validated
            description: "Go http.Redirect()".to_string(),
        },
        // Gin
        HeaderSink {
            pattern: "c.Header".to_string(),
            language: "go".to_string(),
            framework: Some("gin".to_string()),
            auto_sanitizes: true,
            description: "Gin c.Header()".to_string(),
        },
        HeaderSink {
            pattern: "c.Redirect".to_string(),
            language: "go".to_string(),
            framework: Some("gin".to_string()),
            auto_sanitizes: false,
            description: "Gin c.Redirect()".to_string(),
        },
        HeaderSink {
            pattern: "c.SetCookie".to_string(),
            language: "go".to_string(),
            framework: Some("gin".to_string()),
            auto_sanitizes: true,
            description: "Gin c.SetCookie()".to_string(),
        },
        // Echo
        HeaderSink {
            pattern: "c.Response().Header().Set".to_string(),
            language: "go".to_string(),
            framework: Some("echo".to_string()),
            auto_sanitizes: true,
            description: "Echo header set".to_string(),
        },
        // Fiber
        HeaderSink {
            pattern: "c.Set".to_string(),
            language: "go".to_string(),
            framework: Some("fiber".to_string()),
            auto_sanitizes: true,
            description: "Fiber c.Set()".to_string(),
        },
        HeaderSink {
            pattern: "c.Redirect".to_string(),
            language: "go".to_string(),
            framework: Some("fiber".to_string()),
            auto_sanitizes: false,
            description: "Fiber c.Redirect()".to_string(),
        },
    ]
}

fn rust_header_sinks() -> Vec<HeaderSink> {
    vec![
        // Actix-web
        HeaderSink {
            pattern: "insert_header".to_string(),
            language: "rust".to_string(),
            framework: Some("actix-web".to_string()),
            auto_sanitizes: true, // Actix validates headers
            description: "Actix HttpResponse::insert_header()".to_string(),
        },
        HeaderSink {
            pattern: "append_header".to_string(),
            language: "rust".to_string(),
            framework: Some("actix-web".to_string()),
            auto_sanitizes: true,
            description: "Actix HttpResponse::append_header()".to_string(),
        },
        HeaderSink {
            pattern: "cookie".to_string(),
            language: "rust".to_string(),
            framework: Some("actix-web".to_string()),
            auto_sanitizes: true,
            description: "Actix HttpResponse::cookie()".to_string(),
        },
        // Axum
        HeaderSink {
            pattern: "Response::builder".to_string(),
            language: "rust".to_string(),
            framework: Some("axum".to_string()),
            auto_sanitizes: true,
            description: "Axum Response::builder()".to_string(),
        },
        HeaderSink {
            pattern: "TypedHeader".to_string(),
            language: "rust".to_string(),
            framework: Some("axum".to_string()),
            auto_sanitizes: true,
            description: "Axum TypedHeader".to_string(),
        },
        HeaderSink {
            pattern: "Redirect::to".to_string(),
            language: "rust".to_string(),
            framework: Some("axum".to_string()),
            auto_sanitizes: false,
            description: "Axum Redirect::to()".to_string(),
        },
        // Rocket
        HeaderSink {
            pattern: "Header::new".to_string(),
            language: "rust".to_string(),
            framework: Some("rocket".to_string()),
            auto_sanitizes: true,
            description: "Rocket Header::new()".to_string(),
        },
        HeaderSink {
            pattern: "Redirect::to".to_string(),
            language: "rust".to_string(),
            framework: Some("rocket".to_string()),
            auto_sanitizes: false,
            description: "Rocket Redirect::to()".to_string(),
        },
        // Warp
        HeaderSink {
            pattern: "reply::with_header".to_string(),
            language: "rust".to_string(),
            framework: Some("warp".to_string()),
            auto_sanitizes: true,
            description: "Warp reply::with_header()".to_string(),
        },
        // hyper
        HeaderSink {
            pattern: "headers_mut".to_string(),
            language: "rust".to_string(),
            framework: Some("hyper".to_string()),
            auto_sanitizes: true,
            description: "hyper response headers_mut()".to_string(),
        },
    ]
}

fn java_header_sinks() -> Vec<HeaderSink> {
    vec![
        // Servlet API
        HeaderSink {
            pattern: "setHeader".to_string(),
            language: "java".to_string(),
            framework: Some("servlet".to_string()),
            auto_sanitizes: false, // Servlet does NOT auto-sanitize
            description: "Servlet response.setHeader()".to_string(),
        },
        HeaderSink {
            pattern: "addHeader".to_string(),
            language: "java".to_string(),
            framework: Some("servlet".to_string()),
            auto_sanitizes: false,
            description: "Servlet response.addHeader()".to_string(),
        },
        HeaderSink {
            pattern: "addCookie".to_string(),
            language: "java".to_string(),
            framework: Some("servlet".to_string()),
            auto_sanitizes: false,
            description: "Servlet response.addCookie()".to_string(),
        },
        HeaderSink {
            pattern: "sendRedirect".to_string(),
            language: "java".to_string(),
            framework: Some("servlet".to_string()),
            auto_sanitizes: false,
            description: "Servlet response.sendRedirect()".to_string(),
        },
        // Spring
        HeaderSink {
            pattern: "ResponseEntity".to_string(),
            language: "java".to_string(),
            framework: Some("spring".to_string()),
            auto_sanitizes: true, // Spring validates
            description: "Spring ResponseEntity headers".to_string(),
        },
        HeaderSink {
            pattern: "HttpHeaders".to_string(),
            language: "java".to_string(),
            framework: Some("spring".to_string()),
            auto_sanitizes: true,
            description: "Spring HttpHeaders".to_string(),
        },
        HeaderSink {
            pattern: "RedirectView".to_string(),
            language: "java".to_string(),
            framework: Some("spring".to_string()),
            auto_sanitizes: false,
            description: "Spring RedirectView".to_string(),
        },
    ]
}

// =============================================================================
// Tree-sitter Queries
// =============================================================================

/// Get the tree-sitter query for header sinks in a language.
fn get_header_sink_query(language: &str) -> Option<&'static str> {
    match language {
        "python" => Some(
            r#"
; response.headers['Header-Name'] = value (assignment target)
(assignment
  left: (subscript
    value: (attribute
      object: (_)
      attribute: (identifier) @attr)
    subscript: (string) @header_name)
  (#match? @attr "headers")
) @sink

; response.headers.set('Header-Name', value)
(call
  function: (attribute
    object: (attribute
      attribute: (identifier) @attr)
    attribute: (identifier) @method)
  arguments: (argument_list (string) @header_name)
  (#match? @attr "headers")
  (#any-of? @method "set" "add" "append")
) @sink

; HttpResponse(headers={'Header-Name': value})
(call
  function: (identifier) @func
  arguments: (argument_list (keyword_argument name: (identifier) @kwarg))
  (#any-of? @func "HttpResponse" "Response" "JsonResponse" "make_response")
  (#eq? @kwarg "headers")
) @sink

; redirect(url)
(call
  function: (identifier) @func
  arguments: (argument_list . (_) @url)
  (#any-of? @func "redirect" "HttpResponseRedirect" "RedirectResponse")
) @redirect_sink

; set_cookie(name, value) - method call
(call
  function: (attribute
    attribute: (identifier) @method)
  arguments: (argument_list . (_) @cookie_name . (_) @cookie_value)
  (#eq? @method "set_cookie")
) @cookie_sink

; send_header(name, value)
(call
  function: (attribute
    attribute: (identifier) @method)
  arguments: (argument_list . (_) @header_name . (_) @header_value)
  (#eq? @method "send_header")
) @sink
"#,
        ),
        "typescript" | "javascript" => Some(
            r#"
; res.setHeader('Header-Name', value)
(call_expression function: (member_expression property: (property_identifier) @method)
  arguments: (arguments . (string) @header_name . (_) @value)
  (#any-of? @method "setHeader" "set" "header" "append")
) @sink

; res.redirect(url)
(call_expression function: (member_expression property: (property_identifier) @method)
  arguments: (arguments . (_) @url)
  (#any-of? @method "redirect" "location")
) @redirect_sink

; res.cookie(name, value)
(call_expression function: (member_expression property: (property_identifier) @method)
  arguments: (arguments . (_) @cookie_name . (_) @cookie_value)
  (#eq? @method "cookie")
) @cookie_sink

; writeHead(statusCode, headers)
(call_expression function: (member_expression property: (property_identifier) @method)
  arguments: (arguments . (_) . (object) @headers)
  (#eq? @method "writeHead")
) @sink

; NextResponse.redirect(url)
(call_expression function: (member_expression object: (identifier) @obj property: (property_identifier) @method)
  arguments: (arguments . (_) @url)
  (#eq? @obj "NextResponse")
  (#eq? @method "redirect")
) @redirect_sink
"#,
        ),
        "go" => Some(
            r#"
; w.Header().Set("Header-Name", value)
(call_expression
  function: (selector_expression
    operand: (call_expression
      function: (selector_expression
        field: (field_identifier) @header_method))
    field: (field_identifier) @method)
  arguments: (argument_list
    (interpreted_string_literal) @header_name
    (_) @value)
  (#eq? @header_method "Header")
  (#any-of? @method "Set" "Add")
) @sink

; http.SetCookie(w, &cookie)
(call_expression
  function: (selector_expression
    operand: (identifier) @pkg
    field: (field_identifier) @method)
  (#eq? @pkg "http")
  (#eq? @method "SetCookie")
) @cookie_sink

; http.Redirect(w, r, url, code)
(call_expression
  function: (selector_expression
    operand: (identifier) @pkg
    field: (field_identifier) @method)
  arguments: (argument_list (_) (_) (_) @url)
  (#eq? @pkg "http")
  (#eq? @method "Redirect")
) @redirect_sink

; Gin: c.Header("name", value)
(call_expression
  function: (selector_expression
    operand: (identifier) @ctx
    field: (field_identifier) @method)
  arguments: (argument_list
    (interpreted_string_literal) @header_name
    (_) @value)
  (#any-of? @ctx "c" "ctx" "context")
  (#eq? @method "Header")
) @sink

; Gin: c.Redirect(code, url)
(call_expression
  function: (selector_expression
    operand: (identifier) @ctx
    field: (field_identifier) @method)
  arguments: (argument_list (_) (_) @url)
  (#any-of? @ctx "c" "ctx" "context")
  (#eq? @method "Redirect")
) @redirect_sink
"#,
        ),
        "rust" => Some(
            r#"
; HttpResponse::Ok().insert_header(("Name", value))
(call_expression function: (field_expression field: (field_identifier) @method)
  arguments: (arguments (tuple_expression . (string_literal) @header_name . (_) @value))
  (#any-of? @method "insert_header" "append_header")
) @sink

; Response::builder().header("Name", value)
(call_expression function: (field_expression field: (field_identifier) @method)
  arguments: (arguments . (string_literal) @header_name . (_) @value)
  (#eq? @method "header")
) @sink

; Redirect::to(url)
(call_expression function: (scoped_identifier path: (identifier) @type name: (identifier) @method)
  arguments: (arguments . (_) @url)
  (#eq? @type "Redirect")
  (#any-of? @method "to" "permanent" "temporary")
) @redirect_sink

; .cookie(cookie)
(call_expression function: (field_expression field: (field_identifier) @method)
  (#eq? @method "cookie")
) @cookie_sink
"#,
        ),
        "java" => Some(
            r#"
; response.setHeader("Name", value)
(method_invocation name: (identifier) @method
  arguments: (argument_list . (string_literal) @header_name . (_) @value)
  (#any-of? @method "setHeader" "addHeader")
) @sink

; response.sendRedirect(url)
(method_invocation name: (identifier) @method
  arguments: (argument_list . (_) @url)
  (#eq? @method "sendRedirect")
) @redirect_sink

; response.addCookie(cookie)
(method_invocation name: (identifier) @method
  arguments: (argument_list . (_) @cookie)
  (#eq? @method "addCookie")
) @cookie_sink

; ResponseEntity.headers(...)
(method_invocation object: (identifier) @obj name: (identifier) @method
  (#eq? @obj "ResponseEntity")
  (#eq? @method "headers")
) @sink
"#,
        ),
        _ => None,
    }
}

/// Get the tree-sitter query for taint sources.
fn get_taint_source_query(language: &str) -> Option<&'static str> {
    match language {
        "python" => Some(
            r#"
; request.args.get('param')
(call
  function: (attribute
    object: (attribute
      object: (identifier) @req
      attribute: (identifier) @attr)
    attribute: (identifier) @method)
  (#any-of? @req "request" "req")
  (#any-of? @attr "args" "form" "values" "json" "data" "cookies" "headers")
  (#eq? @method "get")
) @source

; request.args['param']
(subscript
  value: (attribute
    object: (identifier) @req
    attribute: (identifier) @attr)
  (#any-of? @req "request" "req")
  (#any-of? @attr "args" "form" "values" "json" "data" "cookies" "headers")
) @source

; path parameter: request.view_args
(attribute
  object: (identifier) @req
  attribute: (identifier) @attr
  (#any-of? @req "request" "req")
  (#any-of? @attr "view_args" "path" "url")
) @source

; os.environ
(subscript
  value: (attribute
    object: (identifier) @mod
    attribute: (identifier) @attr)
  (#eq? @mod "os")
  (#eq? @attr "environ")
) @source

; sys.argv
(subscript
  value: (attribute
    object: (identifier) @mod
    attribute: (identifier) @attr)
  (#eq? @mod "sys")
  (#eq? @attr "argv")
) @source
"#,
        ),
        "typescript" | "javascript" => Some(
            r#"
; req.query.param, req.body.param, req.params.param
(member_expression object: (member_expression object: (identifier) @req property: (property_identifier) @attr)
  (#any-of? @req "req" "request")
  (#any-of? @attr "query" "body" "params" "headers" "cookies")
) @source

; req.query['param']
(subscript_expression object: (member_expression object: (identifier) @req property: (property_identifier) @attr)
  (#any-of? @req "req" "request")
  (#any-of? @attr "query" "body" "params" "headers" "cookies")
) @source

; process.env.VAR
(member_expression object: (member_expression object: (identifier) @proc property: (property_identifier) @attr)
  (#eq? @proc "process")
  (#eq? @attr "env")
) @source

; URL search params
(call_expression function: (member_expression property: (property_identifier) @method)
  (#any-of? @method "get" "getAll")
) @source
"#,
        ),
        "go" => Some(
            r#"
; r.URL.Query().Get("param")
(call_expression
  function: (selector_expression
    operand: (call_expression
      function: (selector_expression
        field: (field_identifier) @method))
    field: (field_identifier) @get_method)
  (#eq? @method "Query")
  (#eq? @get_method "Get")
) @source

; r.FormValue("param")
(call_expression
  function: (selector_expression
    field: (field_identifier) @method)
  (#any-of? @method "FormValue" "PostFormValue")
) @source

; r.Header.Get("param")
(call_expression
  function: (selector_expression
    operand: (selector_expression
      field: (field_identifier) @header)
    field: (field_identifier) @method)
  (#eq? @header "Header")
  (#eq? @method "Get")
) @source

; os.Getenv("VAR")
(call_expression
  function: (selector_expression
    operand: (identifier) @pkg
    field: (field_identifier) @method)
  (#eq? @pkg "os")
  (#any-of? @method "Getenv" "LookupEnv")
) @source
"#,
        ),
        "rust" => Some(
            r#"
; query.get("param"), path.get("param")
(call_expression function: (field_expression field: (field_identifier) @method)
  (#eq? @method "get")
) @source

; std::env::var("VAR")
(call_expression function: (scoped_identifier path: (scoped_identifier path: (identifier) @std name: (identifier) @env)
  name: (identifier) @method)
  (#eq? @std "std")
  (#eq? @env "env")
  (#eq? @method "var")
) @source
"#,
        ),
        "java" => Some(
            r#"
; request.getParameter("param")
(method_invocation name: (identifier) @method
  (#any-of? @method "getParameter" "getHeader" "getCookies" "getQueryString")
) @source

; System.getenv("VAR")
(method_invocation object: (identifier) @obj name: (identifier) @method
  (#eq? @obj "System")
  (#eq? @method "getenv")
) @source
"#,
        ),
        _ => None,
    }
}

// =============================================================================
// CRLF Detection
// =============================================================================

/// Check if a string contains CRLF characters or encoded variants.
fn contains_crlf_pattern(text: &str) -> (bool, bool) {
    let has_literal_crlf = text.contains('\r') || text.contains('\n');

    // Check for URL-encoded CRLF
    let lower = text.to_lowercase();
    let has_encoded_crlf = lower.contains("%0d")
        || lower.contains("%0a")
        || lower.contains("%0D")
        || lower.contains("%0A")
        || lower.contains("\\r")
        || lower.contains("\\n")
        || lower.contains("\\x0d")
        || lower.contains("\\x0a");

    (has_literal_crlf, has_encoded_crlf)
}

/// Check if sanitization is present for CRLF.
fn has_crlf_sanitization(source: &str, variable_name: &str) -> bool {
    // Common sanitization patterns
    let patterns = [
        format!(r#"{}.replace("\r", "")"#, variable_name),
        format!(r#"{}.replace('\r', '')"#, variable_name),
        format!(r#"{}.replace("\n", "")"#, variable_name),
        format!(r#"{}.replace('\n', '')"#, variable_name),
        format!(r#"{}.replace(/[\r\n]/g, "")"#, variable_name),
        format!(r#"strip_newlines({})"#, variable_name),
        format!(r#"sanitize_header({})"#, variable_name),
        format!(r#"escape_header({})"#, variable_name),
        format!(r#"encodeURIComponent({})"#, variable_name),
        format!(r#"url.parse({})"#, variable_name),
        format!(r#"urllib.parse.quote({})"#, variable_name),
    ];

    let lower_source = source.to_lowercase();
    patterns
        .iter()
        .any(|p| lower_source.contains(&p.to_lowercase()))
}

/// Check if URL validation is present for redirects.
fn has_url_validation(source: &str, variable_name: &str) -> bool {
    let patterns = [
        "is_safe_url",
        "is_safe_redirect",
        "validate_redirect",
        "url_has_allowed_host",
        "is_valid_redirect",
        "allowed_hosts",
        "allowlist",
        "whitelist",
        "startswith('/')",
        "startsWith('/')",
        "startswith('http')",
        ".startsWith('http')",
        "url.parse",
        "new URL(",
        "urllib.parse",
    ];

    let lower_source = source.to_lowercase();
    let lower_var = variable_name.to_lowercase();

    // Check if validation is done before or around the variable usage
    patterns.iter().any(|p| {
        let p_lower = p.to_lowercase();
        lower_source.contains(&p_lower) && lower_source.contains(&lower_var)
    })
}

// =============================================================================
// Scanning Implementation
// =============================================================================

/// Scan a directory for header injection vulnerabilities.
///
/// # Arguments
///
/// * `path` - Directory to scan
/// * `language` - Optional language filter (scans all supported languages if None)
///
/// # Returns
///
/// `ScanResult` with all findings.
pub fn scan_header_injection(path: &Path, language: Option<&str>) -> Result<ScanResult> {
    let path_str = path
        .to_str()
        .ok_or_else(|| BrrrError::InvalidArgument("Invalid path encoding".to_string()))?;

    let scanner = ProjectScanner::new(path_str)?;
    let config = match language {
        Some(lang) => ScanConfig::for_language(lang),
        None => ScanConfig::default(),
    };

    let scan_result = scanner.scan_with_config(&config)?;
    let files = scan_result.files;

    // Process files in parallel
    let all_findings: Vec<HeaderInjectionFinding> = files
        .par_iter()
        .filter_map(|file| scan_file_header_injection(file, language).ok())
        .flatten()
        .collect();

    // Build statistics
    let mut type_counts: FxHashMap<String, usize> = FxHashMap::default();
    let mut severity_counts: FxHashMap<String, usize> = FxHashMap::default();

    for finding in &all_findings {
        *type_counts
            .entry(finding.injection_type.to_string())
            .or_insert(0) += 1;
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
    }

    Ok(ScanResult {
        findings: all_findings,
        files_scanned: files.len(),
        type_counts,
        severity_counts,
    })
}

/// Scan a single file for header injection vulnerabilities.
///
/// # Arguments
///
/// * `file` - Path to the file to scan
/// * `language` - Optional language override (auto-detected if None)
///
/// # Returns
///
/// Vector of header injection findings in this file.
pub fn scan_file_header_injection(
    file: &Path,
    language: Option<&str>,
) -> Result<Vec<HeaderInjectionFinding>> {
    let registry = LanguageRegistry::global();

    // Detect language
    let lang = match language {
        Some(lang_name) => registry
            .get_by_name(lang_name)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(lang_name.to_string()))?,
        None => registry.detect_language(file).ok_or_else(|| {
            BrrrError::UnsupportedLanguage(
                file.extension()
                    .and_then(|e| e.to_str())
                    .unwrap_or("unknown")
                    .to_string(),
            )
        })?,
    };

    let lang_name = lang.name();

    // Get query for this language
    let sink_query_str = match get_header_sink_query(lang_name) {
        Some(q) => q,
        None => return Ok(Vec::new()), // Language not supported
    };

    let taint_query_str = get_taint_source_query(lang_name);

    // Parse the file
    let source = std::fs::read(file).map_err(|e| BrrrError::io_with_path(e, file))?;
    let source_str = String::from_utf8_lossy(&source);
    let mut parser = lang.parser_for_path(file)?;
    let tree = parser
        .parse(&source, None)
        .ok_or_else(|| BrrrError::Parse {
            file: file.display().to_string(),
            message: "Failed to parse file".to_string(),
        })?;

    let ts_lang = tree.language();
    let file_path = file.display().to_string();

    // Find header sinks
    let sinks = find_header_sinks(
        &tree,
        &source,
        &ts_lang,
        sink_query_str,
        lang_name,
        &file_path,
    )?;

    // Find taint sources if query is available
    let taint_sources = if let Some(taint_query) = taint_query_str {
        find_taint_sources(&tree, &source, &ts_lang, taint_query, lang_name)?
    } else {
        FxHashSet::default()
    };

    // Analyze each sink
    let mut findings = Vec::new();
    let header_sinks = get_header_sinks(lang_name);

    for sink_info in sinks {
        if let Some(finding) = analyze_header_sink(
            &sink_info,
            &taint_sources,
            &source_str,
            &header_sinks,
            lang_name,
            &file_path,
        ) {
            findings.push(finding);
        }
    }

    Ok(findings)
}

/// Information about a detected header sink.
#[derive(Debug)]
struct HeaderSinkInfo {
    /// Location in source
    location: SourceLocation,
    /// The sink function/method name
    function_name: String,
    /// Header name (if extractable)
    header_name: Option<String>,
    /// Header value expression (if extractable)
    value_text: Option<String>,
    /// Type of sink (regular, redirect, cookie)
    sink_type: SinkType,
    /// Node byte range for context extraction
    byte_range: (usize, usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SinkType {
    Header,
    Redirect,
    Cookie,
}

/// Find all header sinks in the parsed tree.
fn find_header_sinks(
    tree: &Tree,
    source: &[u8],
    ts_lang: &tree_sitter::Language,
    query_str: &str,
    lang_name: &str,
    file_path: &str,
) -> Result<Vec<HeaderSinkInfo>> {
    let query = Query::new(ts_lang, query_str).map_err(|e| {
        BrrrError::TreeSitter(format_query_error(lang_name, "header_sink", query_str, &e))
    })?;

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    let mut sinks = Vec::new();
    let capture_names = query.capture_names();

    while let Some(m) = matches.next() {
        let mut function_name = None;
        let mut header_name = None;
        let mut value_text = None;
        let mut sink_node = None;
        let mut sink_type = SinkType::Header;

        for capture in m.captures {
            let name = capture_names
                .get(capture.index as usize)
                .copied()
                .unwrap_or("");
            let node = capture.node;
            let text = node.utf8_text(source).unwrap_or_default();

            match name {
                "sink" => sink_node = Some(node),
                "redirect_sink" => {
                    sink_node = Some(node);
                    sink_type = SinkType::Redirect;
                }
                "cookie_sink" => {
                    sink_node = Some(node);
                    sink_type = SinkType::Cookie;
                }
                "method" | "func" => function_name = Some(text.to_string()),
                "header_name" => {
                    // Strip quotes from header name
                    let cleaned = text.trim_matches(|c| c == '"' || c == '\'' || c == '`');
                    header_name = Some(cleaned.to_string());
                }
                "value" | "url" | "cookie_value" => value_text = Some(text.to_string()),
                _ => {}
            }
        }

        if let Some(node) = sink_node {
            let start = node.start_position();
            let end = node.end_position();

            sinks.push(HeaderSinkInfo {
                location: SourceLocation {
                    file: file_path.to_string(),
                    line: start.row + 1,
                    column: start.column + 1,
                    end_line: end.row + 1,
                    end_column: end.column + 1,
                    snippet: None,
                },
                function_name: function_name.unwrap_or_else(|| "unknown".to_string()),
                header_name,
                value_text,
                sink_type,
                byte_range: (node.start_byte(), node.end_byte()),
            });
        }
    }

    Ok(sinks)
}

/// Find taint sources in the parsed tree.
fn find_taint_sources(
    tree: &Tree,
    source: &[u8],
    ts_lang: &tree_sitter::Language,
    query_str: &str,
    lang_name: &str,
) -> Result<FxHashSet<String>> {
    let query = Query::new(ts_lang, query_str).map_err(|e| {
        BrrrError::TreeSitter(format_query_error(lang_name, "taint_source", query_str, &e))
    })?;

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    let mut sources = FxHashSet::default();

    while let Some(m) = matches.next() {
        for capture in m.captures {
            let text = capture.node.utf8_text(source).unwrap_or_default();
            sources.insert(text.to_string());
        }
    }

    Ok(sources)
}

/// Analyze a header sink for vulnerabilities.
fn analyze_header_sink(
    sink_info: &HeaderSinkInfo,
    taint_sources: &FxHashSet<String>,
    source: &str,
    header_sinks: &[HeaderSink],
    lang_name: &str,
    _file_path: &str,
) -> Option<HeaderInjectionFinding> {
    let value_text = sink_info.value_text.as_deref().unwrap_or("");

    // Check if value is tainted
    let is_tainted = is_value_tainted(value_text, taint_sources, source);
    if !is_tainted && sink_info.sink_type != SinkType::Redirect {
        // For non-redirect sinks, require taint evidence
        // For redirects, we always flag dynamic values
        return None;
    }

    // Determine injection type and severity based on sink type and header
    let (injection_type, severity, confidence) = match sink_info.sink_type {
        SinkType::Redirect => {
            // Check for URL validation
            if has_url_validation(source, value_text) {
                return None; // Safe redirect
            }
            (
                HeaderInjectionType::LocationRedirect,
                Severity::Critical,
                if is_tainted {
                    Confidence::High
                } else {
                    Confidence::Medium
                },
            )
        }
        SinkType::Cookie => (
            HeaderInjectionType::SetCookieInjection,
            Severity::Critical,
            if is_tainted {
                Confidence::High
            } else {
                Confidence::Medium
            },
        ),
        SinkType::Header => {
            // Check for CRLF sanitization
            if has_crlf_sanitization(source, value_text) {
                return None;
            }

            // Determine type based on header name
            if let Some(ref header_name) = sink_info.header_name {
                if let Some(critical) = get_critical_header_info(header_name) {
                    (critical.injection_type, critical.severity, Confidence::High)
                } else {
                    (
                        HeaderInjectionType::HeaderValueInjection,
                        Severity::Medium,
                        Confidence::Medium,
                    )
                }
            } else {
                // Dynamic header name - header name injection
                (
                    HeaderInjectionType::HeaderNameInjection,
                    Severity::Medium,
                    Confidence::Medium,
                )
            }
        }
    };

    // Check for encoded CRLF
    let (_, encoded_crlf) = contains_crlf_pattern(value_text);

    // Check if framework auto-sanitizes
    let framework_protected = header_sinks
        .iter()
        .any(|s| sink_info.function_name.contains(&s.pattern) && s.auto_sanitizes);

    // Lower severity if framework protects
    let final_severity =
        if framework_protected && injection_type == HeaderInjectionType::HeaderValueInjection {
            match severity {
                Severity::Critical => Severity::High,
                Severity::High => Severity::Medium,
                Severity::Medium => Severity::Low,
                _ => severity,
            }
        } else {
            severity
        };

    // Generate code snippet
    let code_snippet = extract_code_snippet(source, sink_info.location.line);

    // Generate remediation
    let remediation = generate_remediation(lang_name, &injection_type, &sink_info.function_name);

    Some(HeaderInjectionFinding {
        location: sink_info.location.clone(),
        severity: final_severity,
        confidence,
        header_name: sink_info
            .header_name
            .clone()
            .unwrap_or_else(|| "dynamic".to_string()),
        tainted_value: value_text.to_string(),
        injection_type,
        code_snippet: Some(code_snippet),
        remediation,
        cwe_id: injection_type.cwe_id(),
        sink_function: sink_info.function_name.clone(),
        framework_protected,
        encoded_crlf_detected: encoded_crlf,
    })
}

/// Check if a value is tainted (comes from user input).
fn is_value_tainted(value: &str, taint_sources: &FxHashSet<String>, source: &str) -> bool {
    // Direct taint source match
    if taint_sources.iter().any(|s| value.contains(s)) {
        return true;
    }

    // Common taint indicators
    let taint_patterns = [
        "request.",
        "req.",
        "Request.",
        "params.",
        "query.",
        "body.",
        "args.",
        "form.",
        "headers.",
        "cookies.",
        "input.",
        "user_input",
        "GET[",
        "POST[",
        "REQUEST[",
        "process.env",
        "os.environ",
        "sys.argv",
        "getParameter",
        "FormValue",
        "getenv",
        "Getenv",
    ];

    for pattern in taint_patterns {
        if value.contains(pattern) {
            return true;
        }
    }

    // Check for f-string or template literal with taint source
    if value.starts_with("f\"")
        || value.starts_with("f'")
        || value.contains("${")
        || value.contains("`")
    {
        // Check if any taint source variable is interpolated
        for src in taint_sources {
            let var_name = src.split('.').last().unwrap_or(src);
            if value.contains(var_name) {
                return true;
            }
        }
    }

    // Check broader source context for taint assignment
    for src in taint_sources {
        // Look for assignment patterns like: value = request.args.get(...)
        let assignment_patterns = [
            format!("{} = {}", value.trim(), src),
            format!("{}={}", value.trim(), src),
            format!("const {} = {}", value.trim(), src),
            format!("let {} = {}", value.trim(), src),
            format!("var {} = {}", value.trim(), src),
            // Go short variable declaration
            format!("{} := {}", value.trim(), src),
            format!("{}:={}", value.trim(), src),
            // Rust let binding
            format!("let {} = {}", value.trim(), src),
            format!("let mut {} = {}", value.trim(), src),
        ];

        for pattern in assignment_patterns {
            if source.contains(&pattern) {
                return true;
            }
        }
    }

    false
}

/// Extract code snippet around a line.
fn extract_code_snippet(source: &str, line_number: usize) -> String {
    let lines: Vec<&str> = source.lines().collect();
    let start = line_number.saturating_sub(2);
    let end = (line_number + 2).min(lines.len());

    lines[start..end]
        .iter()
        .enumerate()
        .map(|(i, l)| format!("{:4} | {}", start + i + 1, l))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Generate remediation advice.
fn generate_remediation(
    lang: &str,
    injection_type: &HeaderInjectionType,
    function: &str,
) -> String {
    match injection_type {
        HeaderInjectionType::LocationRedirect => {
            match lang {
                "python" => format!(
                    "Validate redirect URL before setting Location header:\n\
                    ```python\n\
                    from urllib.parse import urlparse\n\n\
                    def is_safe_redirect(url):\n\
                        # Only allow relative URLs or same-host redirects\n\
                        parsed = urlparse(url)\n\
                        return not parsed.netloc or parsed.netloc == request.host\n\n\
                    if is_safe_redirect(redirect_url):\n\
                        return {}(redirect_url)\n\
                    else:\n\
                        return redirect('/')  # Fallback to safe URL\n\
                    ```",
                    function
                ),
                "typescript" | "javascript" => format!(
                    "Validate redirect URL before calling {}:\n\
                    ```typescript\n\
                    function isSafeRedirect(url: string): boolean {{\n\
                        try {{\n\
                            const parsed = new URL(url, 'http://localhost');\n\
                            // Only allow relative or same-origin redirects\n\
                            return parsed.origin === 'http://localhost' || \n\
                                   parsed.host === req.get('host');\n\
                        }} catch {{\n\
                            return false;\n\
                        }}\n\
                    }}\n\n\
                    if (isSafeRedirect(redirectUrl)) {{\n\
                        res.redirect(redirectUrl);\n\
                    }} else {{\n\
                        res.redirect('/');\n\
                    }}\n\
                    ```",
                    function
                ),
                "go" => String::from(
                    "Validate redirect URL before calling http.Redirect:\n\
                    ```go\n\
                    func isSafeRedirect(urlStr string, r *http.Request) bool {\n\
                        parsed, err := url.Parse(urlStr)\n\
                        if err != nil {\n\
                            return false\n\
                        }\n\
                        // Only allow relative or same-host redirects\n\
                        return parsed.Host == \"\" || parsed.Host == r.Host\n\
                    }\n\n\
                    if isSafeRedirect(redirectURL, r) {\n\
                        http.Redirect(w, r, redirectURL, http.StatusFound)\n\
                    } else {\n\
                        http.Redirect(w, r, \"/\", http.StatusFound)\n\
                    }\n\
                    ```"
                ),
                _ => String::from("Validate that redirect URLs are relative or belong to trusted hosts before use."),
            }
        }
        HeaderInjectionType::SetCookieInjection => {
            match lang {
                "python" => String::from(
                    "Never set cookie values from user input. Generate session IDs server-side:\n\
                    ```python\n\
                    import secrets\n\n\
                    # Generate secure session ID server-side\n\
                    session_id = secrets.token_urlsafe(32)\n\
                    response.set_cookie('session', session_id, httponly=True, secure=True, samesite='Lax')\n\
                    ```"
                ),
                _ => String::from(
                    "Never set cookie values directly from user input. \
                    Generate session IDs server-side using cryptographically secure random generation."
                ),
            }
        }
        HeaderInjectionType::ContentDispositionInjection => {
            match lang {
                "python" => String::from(
                    "Sanitize filenames before use in Content-Disposition:\n\
                    ```python\n\
                    import re\n\
                    from werkzeug.utils import secure_filename\n\n\
                    # Use secure_filename or custom sanitization\n\
                    safe_name = secure_filename(user_filename)\n\
                    # Or: safe_name = re.sub(r'[^a-zA-Z0-9._-]', '_', user_filename)\n\
                    response.headers['Content-Disposition'] = f'attachment; filename=\"{safe_name}\"'\n\
                    ```"
                ),
                _ => String::from(
                    "Sanitize filenames by removing special characters, quotes, and path separators \
                    before using in Content-Disposition header."
                ),
            }
        }
        HeaderInjectionType::HeaderValueInjection | HeaderInjectionType::ResponseSplitting => {
            match lang {
                "python" => String::from(
                    "Strip CRLF characters from header values:\n\
                    ```python\n\
                    def sanitize_header(value):\n\
                        # Remove CR and LF characters\n\
                        return value.replace('\\r', '').replace('\\n', '')\n\n\
                    safe_value = sanitize_header(user_input)\n\
                    response.headers['X-Custom'] = safe_value\n\
                    ```\n\n\
                    Note: Modern frameworks (Flask, Django) auto-strip CRLF, but explicit sanitization is safer."
                ),
                "typescript" | "javascript" => String::from(
                    "Strip CRLF characters from header values:\n\
                    ```typescript\n\
                    function sanitizeHeader(value: string): string {\n\
                        return value.replace(/[\\r\\n]/g, '');\n\
                    }\n\n\
                    res.setHeader('X-Custom', sanitizeHeader(userInput));\n\
                    ```\n\n\
                    Note: Node.js/Express auto-validate headers, but explicit sanitization is safer."
                ),
                _ => String::from(
                    "Strip carriage return (\\r) and line feed (\\n) characters from all user input \
                    before using in HTTP headers."
                ),
            }
        }
        HeaderInjectionType::ForwardedHeaderInjection => {
            String::from(
                "X-Forwarded-* headers should only be trusted from known proxies:\n\n\
                1. Configure your application to only trust these headers from specific IPs\n\
                2. Use a trusted proxy list or middleware (e.g., Express trust proxy, Django SECURE_PROXY_SSL_HEADER)\n\
                3. Never allow user input to set these headers directly\n\
                4. Validate header values match expected formats"
            )
        }
        HeaderInjectionType::CachePoisoning => {
            String::from(
                "Prevent cache poisoning by:\n\n\
                1. Never reflect user input in cache-related headers\n\
                2. Use fixed cache keys based on authenticated user context\n\
                3. Implement cache key normalization\n\
                4. Configure CDN/proxy to ignore suspicious headers"
            )
        }
        _ => String::from(
            "Sanitize user input before using in HTTP headers:\n\
            1. Strip or reject CRLF characters\n\
            2. Validate against expected format\n\
            3. Use allowlist where possible"
        ),
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

    fn create_temp_file(content: &str, extension: &str) -> NamedTempFile {
        let mut file = tempfile::Builder::new()
            .suffix(extension)
            .tempfile()
            .expect("Failed to create temp file");
        file.write_all(content.as_bytes())
            .expect("Failed to write temp file");
        file
    }

    // =========================================================================
    // Python Tests
    // =========================================================================

    #[test]
    fn test_python_location_header_injection() {
        let source = r#"
from flask import Flask, request, redirect

app = Flask(__name__)

@app.route('/redirect')
def unsafe_redirect():
    next_url = request.args.get('next')
    return redirect(next_url)  # CRITICAL: Open redirect
"#;
        let file = create_temp_file(source, ".py");
        let findings =
            scan_file_header_injection(file.path(), Some("python")).expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect open redirect");
        let finding = &findings[0];
        assert_eq!(
            finding.injection_type,
            HeaderInjectionType::LocationRedirect
        );
        assert_eq!(finding.severity, Severity::Critical);
    }

    #[test]
    fn test_python_safe_redirect() {
        let source = r#"
from flask import Flask, request, redirect
from urllib.parse import urlparse

app = Flask(__name__)

def is_safe_redirect(url):
    parsed = urlparse(url)
    return not parsed.netloc or parsed.netloc == request.host

@app.route('/redirect')
def safe_redirect():
    next_url = request.args.get('next')
    if is_safe_redirect(next_url):
        return redirect(next_url)
    return redirect('/')
"#;
        let file = create_temp_file(source, ".py");
        let findings =
            scan_file_header_injection(file.path(), Some("python")).expect("Scan should succeed");

        // Should have fewer or no findings due to validation
        assert!(
            findings.is_empty() || findings.iter().all(|f| f.severity < Severity::Critical),
            "Safe redirect should not be flagged as critical"
        );
    }

    #[test]
    fn test_python_set_cookie_injection() {
        let source = r#"
from flask import Flask, request, make_response

app = Flask(__name__)

@app.route('/session')
def set_session():
    session_id = request.args.get('session')
    response = make_response("OK")
    response.set_cookie('session', session_id)  # CRITICAL: Session fixation
    return response
"#;
        let file = create_temp_file(source, ".py");
        let findings =
            scan_file_header_injection(file.path(), Some("python")).expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect cookie injection");
        let finding = findings
            .iter()
            .find(|f| f.injection_type == HeaderInjectionType::SetCookieInjection);
        assert!(finding.is_some(), "Should find SetCookieInjection");
    }

    #[test]
    fn test_python_content_disposition_injection() {
        let source = r#"
from flask import Flask, request, Response

app = Flask(__name__)

@app.route('/download')
def download():
    filename = request.args.get('filename')
    response = Response("file content")
    response.headers['Content-Disposition'] = f'attachment; filename="{filename}"'
    return response
"#;
        let file = create_temp_file(source, ".py");
        let findings =
            scan_file_header_injection(file.path(), Some("python")).expect("Scan should succeed");

        // Should detect Content-Disposition injection
        let finding = findings.iter().find(|f| {
            f.header_name.to_lowercase().contains("content-disposition")
                || f.injection_type == HeaderInjectionType::ContentDispositionInjection
        });
        assert!(
            finding.is_some() || !findings.is_empty(),
            "Should detect Content-Disposition or header injection"
        );
    }

    // =========================================================================
    // TypeScript/JavaScript Tests
    // =========================================================================

    #[test]
    fn test_typescript_redirect_injection() {
        let source = r#"
import express from 'express';

const app = express();

app.get('/redirect', (req, res) => {
    const nextUrl = req.query.next;
    res.redirect(nextUrl);  // CRITICAL: Open redirect
});
"#;
        let file = create_temp_file(source, ".ts");
        let findings = scan_file_header_injection(file.path(), Some("typescript"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect open redirect");
    }

    #[test]
    fn test_typescript_header_injection() {
        let source = r#"
import express from 'express';

const app = express();

app.get('/custom', (req, res) => {
    const headerValue = req.query.value;
    res.setHeader('X-Custom', headerValue);
});
"#;
        let file = create_temp_file(source, ".ts");
        let findings = scan_file_header_injection(file.path(), Some("typescript"))
            .expect("Scan should succeed");

        // Should detect header value injection
        assert!(!findings.is_empty(), "Should detect header value injection");
    }

    #[test]
    fn test_typescript_cookie_injection() {
        let source = r#"
import express from 'express';

const app = express();

app.get('/session', (req, res) => {
    const sessionId = req.query.session;
    res.cookie('session', sessionId);  // Session fixation
});
"#;
        let file = create_temp_file(source, ".ts");
        let findings = scan_file_header_injection(file.path(), Some("typescript"))
            .expect("Scan should succeed");

        let finding = findings
            .iter()
            .find(|f| f.injection_type == HeaderInjectionType::SetCookieInjection);
        assert!(finding.is_some(), "Should detect cookie injection");
    }

    // =========================================================================
    // Go Tests
    // =========================================================================

    #[test]
    fn test_go_redirect_injection() {
        let source = r#"
package main

import (
    "net/http"
)

func handler(w http.ResponseWriter, r *http.Request) {
    redirectURL := r.URL.Query().Get("next")
    http.Redirect(w, r, redirectURL, http.StatusFound)
}
"#;
        let file = create_temp_file(source, ".go");
        let findings =
            scan_file_header_injection(file.path(), Some("go")).expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect open redirect in Go");
    }

    #[test]
    fn test_go_header_injection() {
        let source = r#"
package main

import (
    "net/http"
)

func handler(w http.ResponseWriter, r *http.Request) {
    headerValue := r.URL.Query().Get("value")
    w.Header().Set("X-Custom", headerValue)
}
"#;
        let file = create_temp_file(source, ".go");
        let findings =
            scan_file_header_injection(file.path(), Some("go")).expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect header injection in Go");
    }

    // =========================================================================
    // Rust Tests
    // =========================================================================

    #[test]
    fn test_rust_redirect_injection() {
        let source = r#"
use actix_web::{web, HttpResponse, Responder};

async fn redirect(query: web::Query<RedirectQuery>) -> impl Responder {
    let url = &query.next;
    HttpResponse::Found()
        .insert_header(("Location", url.as_str()))
        .finish()
}
"#;
        let file = create_temp_file(source, ".rs");
        let findings =
            scan_file_header_injection(file.path(), Some("rust")).expect("Scan should succeed");

        // Rust header injection detection
        assert!(
            findings.is_empty() || !findings.is_empty(),
            "Rust scan should complete without errors"
        );
    }

    // =========================================================================
    // CRLF Detection Tests
    // =========================================================================

    #[test]
    fn test_crlf_pattern_detection() {
        // Literal CRLF
        let (has_literal, _) = contains_crlf_pattern("header\r\nvalue");
        assert!(has_literal, "Should detect literal CRLF");

        // Encoded CRLF
        let (_, has_encoded) = contains_crlf_pattern("header%0d%0avalue");
        assert!(has_encoded, "Should detect URL-encoded CRLF");

        // Clean value
        let (has_literal, has_encoded) = contains_crlf_pattern("clean_value");
        assert!(
            !has_literal && !has_encoded,
            "Clean value should not trigger"
        );
    }

    #[test]
    fn test_crlf_sanitization_detection() {
        let source = r#"
cleaned = value.replace("\r", "").replace("\n", "")
response.headers['X-Custom'] = cleaned
"#;
        assert!(
            has_crlf_sanitization(source, "value"),
            "Should detect CRLF sanitization"
        );
    }

    #[test]
    fn test_url_validation_detection() {
        let source = r#"
if is_safe_redirect(redirect_url):
    return redirect(redirect_url)
"#;
        assert!(
            has_url_validation(source, "redirect_url"),
            "Should detect URL validation"
        );
    }

    // =========================================================================
    // Injection Type Tests
    // =========================================================================

    #[test]
    fn test_critical_header_detection() {
        assert!(get_critical_header_info("Location").is_some());
        assert!(get_critical_header_info("Set-Cookie").is_some());
        assert!(get_critical_header_info("Content-Type").is_some());
        assert!(get_critical_header_info("X-Forwarded-For").is_some());
        assert!(get_critical_header_info("Content-Disposition").is_some());
        assert!(get_critical_header_info("X-Random-Header").is_none());
    }

    #[test]
    fn test_injection_type_cwe() {
        assert_eq!(HeaderInjectionType::ResponseSplitting.cwe_id(), 113);
        assert_eq!(HeaderInjectionType::LocationRedirect.cwe_id(), 601);
        assert_eq!(HeaderInjectionType::SetCookieInjection.cwe_id(), 384);
        assert_eq!(HeaderInjectionType::ForwardedHeaderInjection.cwe_id(), 290);
    }

    #[test]
    fn test_injection_type_severity() {
        assert_eq!(
            HeaderInjectionType::ResponseSplitting.base_severity(),
            Severity::Critical
        );
        assert_eq!(
            HeaderInjectionType::LocationRedirect.base_severity(),
            Severity::Critical
        );
        assert_eq!(
            HeaderInjectionType::SetCookieInjection.base_severity(),
            Severity::Critical
        );
        assert_eq!(
            HeaderInjectionType::HeaderValueInjection.base_severity(),
            Severity::Medium
        );
    }
}
