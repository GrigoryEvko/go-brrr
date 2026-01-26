//! Comprehensive taint sink catalog for security analysis.
//!
//! This module provides a complete database of security-sensitive sinks (dangerous
//! functions) across multiple programming languages. Each sink is categorized by
//! vulnerability type and includes appropriate sanitization requirements.
//!
//! # Architecture
//!
//! The sink catalog is organized into:
//!
//! 1. **Core Types** - `SinkCategory`, `Sink`, `SanitizerContext`
//! 2. **Language Modules** - Python, TypeScript/JavaScript, Go, Rust
//! 3. **Matching API** - `find_sinks()`, `is_sanitized()`
//! 4. **Sanitizer Database** - Maps sanitizers to their effective contexts
//!
//! # Partial Sanitization Problem
//!
//! A critical security concern is **partial sanitization** - applying a sanitizer
//! that is appropriate for one context but not another. For example:
//!
//! - `html_escape()` prevents XSS but NOT SQL injection
//! - `shlex.quote()` prevents command injection but NOT path traversal
//! - SQL parameterization prevents SQL injection but NOT XSS
//! - `encodeURIComponent()` prevents some XSS but NOT all contexts
//!
//! This module tracks sanitization context to detect such issues:
//!
//! ```ignore
//! use brrr::security::taint::sinks::{SanitizerContext, is_sanitized_for_context};
//!
//! let applied = vec![SanitizerContext::HtmlEscape];
//! let required = SanitizerContext::SqlParameterized;
//!
//! // This will return false - HTML escape doesn't prevent SQL injection!
//! assert!(!is_sanitized_for_context(&applied, required));
//! ```
//!
//! # Usage Example
//!
//! ```ignore
//! use brrr::security::taint::sinks::{find_sinks, SinkCategory, CallInfo};
//!
//! let call = CallInfo {
//!     function_name: "cursor.execute".to_string(),
//!     receiver: Some("cursor".to_string()),
//!     arguments: vec!["query".to_string()],
//! };
//!
//! let sinks = find_sinks(&call, "python");
//! for sink in sinks {
//!     println!("Found sink: {} ({:?})", sink.function_pattern, sink.category);
//!     println!("Dangerous params: {:?}", sink.dangerous_params);
//!     println!("Required sanitizers: {:?}", sink.sanitizers);
//! }
//! ```

pub mod common;
pub mod go;
pub mod python;
pub mod rust_lang;
pub mod typescript;

// Re-export language-specific sink builders
pub use go::get_go_sinks;
pub use python::get_python_sinks;
pub use rust_lang::get_rust_sinks;
pub use typescript::get_typescript_sinks;

// Re-export common types and utilities
pub use common::{Severity, TaintSinkDef, default_sanitizers_for, is_effective_sanitizer};

/// Type alias for backward compatibility.
pub type TaintSink = Sink;

use crate::security::taint::types::{Location, TaintLabel};
use fxhash::FxHashMap;
use serde::{Deserialize, Serialize};

// =============================================================================
// Sink Categories
// =============================================================================

/// Category of security-sensitive sink.
///
/// Each category represents a distinct class of vulnerability that can occur
/// when untrusted data reaches the sink without proper sanitization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SinkCategory {
    /// SQL query execution - CWE-89: SQL Injection
    SqlInjection,
    /// Shell/OS command execution - CWE-78: OS Command Injection
    CommandInjection,
    /// HTML/JavaScript output - CWE-79: Cross-Site Scripting (XSS)
    XSS,
    /// File system operations - CWE-22: Path Traversal
    PathTraversal,
    /// Dynamic code execution - CWE-94: Code Injection
    CodeExecution,
    /// Network requests with user-controlled URLs - CWE-918: SSRF
    SSRF,
    /// Logging operations - CWE-117: Log Injection
    LogInjection,
    /// HTTP header operations - CWE-113: HTTP Response Splitting
    HeaderInjection,
    /// XPath query execution - CWE-643: XPath Injection
    XPathInjection,
    /// LDAP query execution - CWE-90: LDAP Injection
    LdapInjection,
    /// Template rendering - CWE-1336: Server-Side Template Injection
    TemplateInjection,
    /// Deserialization of untrusted data - CWE-502
    Deserialization,
    /// XML parsing with external entities - CWE-611: XXE
    XmlInjection,
    /// Open redirect vulnerability - CWE-601
    OpenRedirect,
    /// Regular expression injection - CWE-1333: ReDoS
    RegexInjection,
    /// Memory operations (C/C++/unsafe Rust) - CWE-120
    MemoryCorruption,
    /// SMTP header injection - CWE-93
    EmailHeaderInjection,
    /// NoSQL injection - CWE-943
    NoSqlInjection,
}

impl SinkCategory {
    /// Get the CWE (Common Weakness Enumeration) ID for this sink category.
    #[inline]
    pub const fn cwe_id(&self) -> &'static str {
        match self {
            Self::SqlInjection => "CWE-89",
            Self::CommandInjection => "CWE-78",
            Self::XSS => "CWE-79",
            Self::PathTraversal => "CWE-22",
            Self::CodeExecution => "CWE-94",
            Self::SSRF => "CWE-918",
            Self::LogInjection => "CWE-117",
            Self::HeaderInjection => "CWE-113",
            Self::XPathInjection => "CWE-643",
            Self::LdapInjection => "CWE-90",
            Self::TemplateInjection => "CWE-1336",
            Self::Deserialization => "CWE-502",
            Self::XmlInjection => "CWE-611",
            Self::OpenRedirect => "CWE-601",
            Self::RegexInjection => "CWE-1333",
            Self::MemoryCorruption => "CWE-120",
            Self::EmailHeaderInjection => "CWE-93",
            Self::NoSqlInjection => "CWE-943",
        }
    }

    /// Get a human-readable description of this sink category.
    #[inline]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::SqlInjection => "SQL Injection",
            Self::CommandInjection => "OS Command Injection",
            Self::XSS => "Cross-Site Scripting (XSS)",
            Self::PathTraversal => "Path Traversal",
            Self::CodeExecution => "Code Injection",
            Self::SSRF => "Server-Side Request Forgery (SSRF)",
            Self::LogInjection => "Log Injection",
            Self::HeaderInjection => "HTTP Header Injection",
            Self::XPathInjection => "XPath Injection",
            Self::LdapInjection => "LDAP Injection",
            Self::TemplateInjection => "Server-Side Template Injection (SSTI)",
            Self::Deserialization => "Insecure Deserialization",
            Self::XmlInjection => "XML External Entity (XXE) Injection",
            Self::OpenRedirect => "Open Redirect",
            Self::RegexInjection => "Regular Expression Injection (ReDoS)",
            Self::MemoryCorruption => "Buffer Overflow / Memory Corruption",
            Self::EmailHeaderInjection => "Email Header Injection",
            Self::NoSqlInjection => "NoSQL Injection",
        }
    }

    /// Get the base severity level (1-10) for this sink category.
    ///
    /// Higher values indicate more critical vulnerabilities.
    #[inline]
    pub const fn base_severity(&self) -> u8 {
        match self {
            Self::CodeExecution => 10,
            Self::CommandInjection => 10,
            Self::MemoryCorruption => 10,
            Self::Deserialization => 9,
            Self::SqlInjection => 9,
            Self::TemplateInjection => 9,
            Self::SSRF => 8,
            Self::PathTraversal => 8,
            Self::XmlInjection => 8,
            Self::XSS => 7,
            Self::LdapInjection => 7,
            Self::NoSqlInjection => 7,
            Self::XPathInjection => 6,
            Self::HeaderInjection => 6,
            Self::OpenRedirect => 5,
            Self::EmailHeaderInjection => 5,
            Self::RegexInjection => 4,
            Self::LogInjection => 3,
        }
    }

    /// Get the OWASP Top 10 category (2021) for this sink.
    #[inline]
    pub const fn owasp_category(&self) -> &'static str {
        match self {
            Self::SqlInjection
            | Self::CommandInjection
            | Self::XPathInjection
            | Self::LdapInjection
            | Self::NoSqlInjection
            | Self::CodeExecution => "A03:2021 - Injection",
            Self::XSS => "A03:2021 - Injection",
            Self::Deserialization | Self::XmlInjection => {
                "A08:2021 - Software and Data Integrity Failures"
            }
            Self::PathTraversal => "A01:2021 - Broken Access Control",
            Self::SSRF => "A10:2021 - Server-Side Request Forgery",
            Self::TemplateInjection => "A03:2021 - Injection",
            Self::HeaderInjection | Self::LogInjection | Self::EmailHeaderInjection => {
                "A03:2021 - Injection"
            }
            Self::OpenRedirect => "A01:2021 - Broken Access Control",
            Self::RegexInjection => "A03:2021 - Injection",
            Self::MemoryCorruption => "A03:2021 - Injection",
        }
    }

    /// Get all categories as a slice (useful for iteration).
    pub const fn all() -> &'static [Self] {
        &[
            Self::SqlInjection,
            Self::CommandInjection,
            Self::XSS,
            Self::PathTraversal,
            Self::CodeExecution,
            Self::SSRF,
            Self::LogInjection,
            Self::HeaderInjection,
            Self::XPathInjection,
            Self::LdapInjection,
            Self::TemplateInjection,
            Self::Deserialization,
            Self::XmlInjection,
            Self::OpenRedirect,
            Self::RegexInjection,
            Self::MemoryCorruption,
            Self::EmailHeaderInjection,
            Self::NoSqlInjection,
        ]
    }

    /// Get recommended sanitizer names for this sink category.
    ///
    /// Returns a list of sanitizer function names that can mitigate vulnerabilities
    /// for this specific sink category.
    pub const fn recommended_sanitizers(&self) -> &'static [&'static str] {
        match self {
            Self::SqlInjection | Self::NoSqlInjection => &[
                "parameterized_query",
                "prepared_statement",
                "sqlalchemy_text",
                "django_orm",
                "escape_string",
                "quote_literal",
            ],
            Self::CommandInjection => &[
                "shlex_quote",
                "shlex_split",
                "subprocess_list",
                "shell_escape",
                "escapeshellarg",
                "escapeshellcmd",
            ],
            Self::XSS => &[
                "html_escape",
                "escape",
                "sanitize_html",
                "DOMPurify",
                "bleach_clean",
                "markupsafe_escape",
                "cgi_escape",
            ],
            Self::PathTraversal => &[
                "path_join",
                "realpath",
                "abspath",
                "normpath",
                "secure_filename",
                "basename",
                "safe_join",
            ],
            Self::CodeExecution => &["ast_literal_eval", "json_parse", "safe_eval"],
            Self::SSRF => &[
                "url_validate",
                "domain_allowlist",
                "scheme_validate",
                "is_private_ip",
                "url_parse",
            ],
            Self::LogInjection => &["log_escape", "replace_newlines", "sanitize_log"],
            Self::HeaderInjection => &["header_escape", "remove_crlf", "validate_header"],
            Self::XPathInjection | Self::LdapInjection => {
                &["escape_filter", "parameterized_xpath", "ldap_escape"]
            }
            Self::TemplateInjection => &["autoescape", "sandbox_template", "safe_render"],
            Self::Deserialization => &["json_loads", "safe_load", "restricted_deserialize"],
            Self::XmlInjection => &["defusedxml", "disable_external_entities", "lxml_safe_parse"],
            Self::OpenRedirect => &["url_for", "is_safe_url", "validate_redirect"],
            Self::RegexInjection => &["re_escape", "regex_escape", "literal_pattern"],
            Self::MemoryCorruption => &["bounds_check", "safe_alloc", "size_validate"],
            Self::EmailHeaderInjection => &["email_escape", "validate_email", "header_encode"],
        }
    }
}

impl std::fmt::Display for SinkCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description())
    }
}

// =============================================================================
// Sanitizer Context
// =============================================================================

/// Context-specific sanitization types.
///
/// This enum represents the specific context for which a sanitizer is effective.
/// A sanitizer that works for one context may NOT work for another - this is the
/// "partial sanitization" problem.
///
/// # Important Security Note
///
/// Applying the wrong sanitizer can give a false sense of security:
/// - `HtmlEscape` prevents XSS but allows SQL injection
/// - `SqlParameterized` prevents SQL injection but allows XSS
/// - `ShellEscape` prevents command injection but allows path traversal
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SanitizerContext {
    // SQL Sanitization
    /// Parameterized queries / prepared statements (strongly preferred)
    SqlParameterized,
    /// SQL string escaping (database-specific, less safe than parameterized)
    SqlEscape,
    /// ORM with automatic escaping
    SqlOrm,

    // Command Sanitization
    /// Shell argument escaping (shlex.quote, escapeshellarg)
    ShellEscape,
    /// Using list arguments instead of shell string (subprocess with shell=False)
    CommandList,
    /// Allowlist validation for command names
    CommandAllowlist,

    // XSS Sanitization
    /// HTML entity encoding (&lt; &gt; &amp; etc.)
    HtmlEscape,
    /// DOM sanitization library (DOMPurify, sanitize-html)
    DomSanitize,
    /// Content Security Policy header
    ContentSecurityPolicy,
    /// JavaScript string encoding for inline scripts
    JavaScriptEscape,
    /// URL encoding for URL contexts
    UrlEncode,
    /// CSS encoding for style contexts
    CssEscape,

    // Path Sanitization
    /// Path canonicalization (realpath) + prefix check
    PathCanonicalize,
    /// Using basename to strip directory components
    PathBasename,
    /// Allowlist of permitted paths
    PathAllowlist,
    /// Path joining that prevents traversal
    PathSafeJoin,

    // LDAP Sanitization
    /// LDAP distinguished name escaping
    LdapDnEscape,
    /// LDAP filter escaping
    LdapFilterEscape,

    // XPath Sanitization
    /// XPath string escaping
    XPathEscape,
    /// Parameterized XPath queries
    XPathParameterized,

    // URL/SSRF Sanitization
    /// URL scheme validation (http/https only)
    UrlSchemeValidation,
    /// Domain allowlist validation
    UrlDomainAllowlist,
    /// Private IP address blocking
    UrlPrivateIpBlock,

    // Header Sanitization
    /// CRLF removal for headers
    HeaderCrlfRemove,
    /// Header value encoding
    HeaderEncode,

    // Log Sanitization
    /// Newline removal for logs
    LogNewlineRemove,
    /// Log message encoding
    LogEncode,

    // XML Sanitization
    /// XML entity encoding
    XmlEntityEncode,
    /// Disable external entity processing
    XmlDisableExternalEntities,

    // Template Sanitization
    /// Sandboxed template execution
    TemplateSandbox,
    /// Template autoescape enabled
    TemplateAutoescape,

    // Deserialization Sanitization
    /// Type allowlist for deserialization
    DeserializeTypeAllowlist,
    /// Signature verification before deserialization
    DeserializeSignatureVerify,
    /// Using safe formats only (JSON instead of pickle)
    DeserializeSafeFormat,

    // Regex Sanitization
    /// Regex pattern escaping
    RegexEscape,
    /// Regex timeout/limit configuration
    RegexTimeout,

    // Email Sanitization
    /// Email header newline removal
    EmailHeaderSanitize,

    // General
    /// Input validation via allowlist
    InputAllowlist,
    /// Input validation via denylist (less secure)
    InputDenylist,
    /// Type validation/casting
    TypeValidation,
    /// Length limitation
    LengthLimit,
}

impl SanitizerContext {
    /// Get the sink categories this sanitizer is effective against.
    pub fn effective_against(&self) -> &'static [SinkCategory] {
        match self {
            // SQL sanitizers
            Self::SqlParameterized | Self::SqlEscape | Self::SqlOrm => {
                &[SinkCategory::SqlInjection]
            }

            // Command sanitizers
            Self::ShellEscape | Self::CommandList | Self::CommandAllowlist => {
                &[SinkCategory::CommandInjection]
            }

            // XSS sanitizers
            Self::HtmlEscape | Self::DomSanitize => &[SinkCategory::XSS],
            Self::ContentSecurityPolicy => &[SinkCategory::XSS], // Defense in depth
            Self::JavaScriptEscape => &[SinkCategory::XSS],
            Self::UrlEncode => &[SinkCategory::XSS, SinkCategory::OpenRedirect],
            Self::CssEscape => &[SinkCategory::XSS],

            // Path sanitizers
            Self::PathCanonicalize
            | Self::PathBasename
            | Self::PathAllowlist
            | Self::PathSafeJoin => &[SinkCategory::PathTraversal],

            // LDAP sanitizers
            Self::LdapDnEscape | Self::LdapFilterEscape => &[SinkCategory::LdapInjection],

            // XPath sanitizers
            Self::XPathEscape | Self::XPathParameterized => &[SinkCategory::XPathInjection],

            // URL/SSRF sanitizers
            Self::UrlSchemeValidation | Self::UrlDomainAllowlist | Self::UrlPrivateIpBlock => {
                &[SinkCategory::SSRF, SinkCategory::OpenRedirect]
            }

            // Header sanitizers
            Self::HeaderCrlfRemove | Self::HeaderEncode => &[SinkCategory::HeaderInjection],

            // Log sanitizers
            Self::LogNewlineRemove | Self::LogEncode => &[SinkCategory::LogInjection],

            // XML sanitizers
            Self::XmlEntityEncode | Self::XmlDisableExternalEntities => {
                &[SinkCategory::XmlInjection]
            }

            // Template sanitizers
            Self::TemplateSandbox | Self::TemplateAutoescape => &[SinkCategory::TemplateInjection],

            // Deserialization sanitizers
            Self::DeserializeTypeAllowlist
            | Self::DeserializeSignatureVerify
            | Self::DeserializeSafeFormat => &[SinkCategory::Deserialization],

            // Regex sanitizers
            Self::RegexEscape | Self::RegexTimeout => &[SinkCategory::RegexInjection],

            // Email sanitizers
            Self::EmailHeaderSanitize => &[SinkCategory::EmailHeaderInjection],

            // General sanitizers - limited effectiveness
            Self::InputAllowlist => SinkCategory::all(), // Allowlist can help with many categories
            Self::InputDenylist => &[],                  // Denylist is not reliable
            Self::TypeValidation => &[
                SinkCategory::SqlInjection,
                SinkCategory::CommandInjection,
                SinkCategory::PathTraversal,
            ],
            Self::LengthLimit => &[SinkCategory::RegexInjection], // Helps with ReDoS
        }
    }

    /// Check if this sanitizer is effective against a specific sink category.
    #[inline]
    pub fn is_effective_against(&self, category: SinkCategory) -> bool {
        self.effective_against().contains(&category)
    }

    /// Get the strength of this sanitizer (higher is better, 1-10).
    #[inline]
    pub const fn strength(&self) -> u8 {
        match self {
            // Strong sanitizers
            Self::SqlParameterized => 10,
            Self::CommandList => 10,
            Self::DomSanitize => 9,
            Self::PathCanonicalize => 9,
            Self::XmlDisableExternalEntities => 10,
            Self::DeserializeSafeFormat => 9,
            Self::InputAllowlist => 9,

            // Medium-strong sanitizers
            Self::SqlOrm => 8,
            Self::HtmlEscape => 8,
            Self::ShellEscape => 8,
            Self::PathAllowlist => 8,
            Self::UrlDomainAllowlist => 8,
            Self::TemplateSandbox => 8,
            Self::DeserializeTypeAllowlist => 8,

            // Medium sanitizers
            Self::SqlEscape => 6, // Database-specific, error-prone
            Self::CommandAllowlist => 7,
            Self::ContentSecurityPolicy => 7,
            Self::PathBasename => 7,
            Self::PathSafeJoin => 7,
            Self::LdapDnEscape => 7,
            Self::LdapFilterEscape => 7,
            Self::XPathEscape => 7,
            Self::XPathParameterized => 8,
            Self::HeaderCrlfRemove => 7,
            Self::HeaderEncode => 7,
            Self::TemplateAutoescape => 7,
            Self::DeserializeSignatureVerify => 7,
            Self::RegexEscape => 7,
            Self::RegexTimeout => 6,
            Self::TypeValidation => 7,

            // Weaker sanitizers
            Self::JavaScriptEscape => 6,
            Self::UrlEncode => 5,
            Self::CssEscape => 6,
            Self::UrlSchemeValidation => 5,
            Self::UrlPrivateIpBlock => 6,
            Self::LogNewlineRemove => 5,
            Self::LogEncode => 5,
            Self::XmlEntityEncode => 5,
            Self::EmailHeaderSanitize => 6,
            Self::LengthLimit => 4,
            Self::InputDenylist => 2, // Denylist is weak
        }
    }
}

impl std::fmt::Display for SanitizerContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

// =============================================================================
// Sink Definition
// =============================================================================

/// A security-sensitive sink definition with full metadata.
///
/// Sinks represent dangerous operations where untrusted (tainted) data
/// can cause security vulnerabilities.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Sink {
    /// Vulnerability category
    pub category: SinkCategory,
    /// Pattern to match function/method calls (supports wildcards)
    pub function_pattern: String,
    /// Which parameter indices are dangerous (0-indexed)
    /// Empty means ALL parameters are potentially dangerous
    pub dangerous_params: Vec<usize>,
    /// Sanitizers that can make this sink safe
    pub sanitizers: Vec<SanitizerContext>,
    /// Human-readable description of the vulnerability
    pub description: String,
    /// Severity override (None = use category default)
    pub severity_override: Option<u8>,
    /// Confidence level (0.0-1.0) for heuristic matches
    pub confidence: f64,
    /// Required receiver type (if method call)
    pub receiver_type: Option<String>,
    /// Whether this is a property access (innerHTML) vs function call
    pub is_property: bool,
    /// Additional metadata tags
    pub tags: Vec<String>,
}

impl Sink {
    /// Create a new sink with default settings.
    pub fn new(pattern: impl Into<String>, category: SinkCategory) -> Self {
        Self {
            category,
            function_pattern: pattern.into(),
            dangerous_params: Vec::new(),
            sanitizers: common::default_sanitizers_for(category),
            description: category.description().to_string(),
            severity_override: None,
            confidence: 1.0,
            receiver_type: None,
            is_property: false,
            tags: Vec::new(),
        }
    }

    /// Create a SQL injection sink.
    pub fn sql(pattern: impl Into<String>, description: impl Into<String>) -> Self {
        let mut sink = Self::new(pattern, SinkCategory::SqlInjection);
        sink.description = description.into();
        sink.dangerous_params = vec![0]; // First arg is usually the query
        sink.sanitizers = vec![
            SanitizerContext::SqlParameterized,
            SanitizerContext::SqlOrm,
            SanitizerContext::SqlEscape,
        ];
        sink
    }

    /// Create a command injection sink.
    pub fn command(pattern: impl Into<String>, description: impl Into<String>) -> Self {
        let mut sink = Self::new(pattern, SinkCategory::CommandInjection);
        sink.description = description.into();
        sink.sanitizers = vec![
            SanitizerContext::CommandList,
            SanitizerContext::ShellEscape,
            SanitizerContext::CommandAllowlist,
        ];
        sink
    }

    /// Create an XSS sink.
    pub fn xss(pattern: impl Into<String>, description: impl Into<String>) -> Self {
        let mut sink = Self::new(pattern, SinkCategory::XSS);
        sink.description = description.into();
        sink.sanitizers = vec![
            SanitizerContext::HtmlEscape,
            SanitizerContext::DomSanitize,
            SanitizerContext::ContentSecurityPolicy,
        ];
        sink
    }

    /// Create a path traversal sink.
    pub fn path(pattern: impl Into<String>, description: impl Into<String>) -> Self {
        let mut sink = Self::new(pattern, SinkCategory::PathTraversal);
        sink.description = description.into();
        sink.dangerous_params = vec![0]; // First arg is usually the path
        sink.sanitizers = vec![
            SanitizerContext::PathCanonicalize,
            SanitizerContext::PathAllowlist,
            SanitizerContext::PathBasename,
            SanitizerContext::PathSafeJoin,
        ];
        sink
    }

    /// Create an SSRF sink.
    pub fn ssrf(pattern: impl Into<String>, description: impl Into<String>) -> Self {
        let mut sink = Self::new(pattern, SinkCategory::SSRF);
        sink.description = description.into();
        sink.dangerous_params = vec![0]; // First arg is usually the URL
        sink.sanitizers = vec![
            SanitizerContext::UrlDomainAllowlist,
            SanitizerContext::UrlSchemeValidation,
            SanitizerContext::UrlPrivateIpBlock,
        ];
        sink
    }

    /// Create a code execution sink.
    pub fn code_exec(pattern: impl Into<String>, description: impl Into<String>) -> Self {
        let mut sink = Self::new(pattern, SinkCategory::CodeExecution);
        sink.description = description.into();
        sink.severity_override = Some(10);
        // Code execution generally cannot be safely sanitized
        sink.sanitizers = vec![SanitizerContext::InputAllowlist];
        sink
    }

    /// Create an LDAP injection sink.
    pub fn ldap(pattern: impl Into<String>, description: impl Into<String>) -> Self {
        let mut sink = Self::new(pattern, SinkCategory::LdapInjection);
        sink.description = description.into();
        sink.sanitizers = vec![
            SanitizerContext::LdapDnEscape,
            SanitizerContext::LdapFilterEscape,
        ];
        sink
    }

    /// Create an XPath injection sink.
    pub fn xpath(pattern: impl Into<String>, description: impl Into<String>) -> Self {
        let mut sink = Self::new(pattern, SinkCategory::XPathInjection);
        sink.description = description.into();
        sink.sanitizers = vec![
            SanitizerContext::XPathParameterized,
            SanitizerContext::XPathEscape,
        ];
        sink
    }

    /// Create a log injection sink.
    pub fn log(pattern: impl Into<String>, description: impl Into<String>) -> Self {
        let mut sink = Self::new(pattern, SinkCategory::LogInjection);
        sink.description = description.into();
        sink.severity_override = Some(3); // Lower severity
        sink.sanitizers = vec![
            SanitizerContext::LogNewlineRemove,
            SanitizerContext::LogEncode,
        ];
        sink
    }

    /// Create a header injection sink.
    pub fn header(pattern: impl Into<String>, description: impl Into<String>) -> Self {
        let mut sink = Self::new(pattern, SinkCategory::HeaderInjection);
        sink.description = description.into();
        sink.sanitizers = vec![
            SanitizerContext::HeaderCrlfRemove,
            SanitizerContext::HeaderEncode,
        ];
        sink
    }

    /// Builder: set dangerous parameter indices.
    pub fn with_dangerous_params(mut self, params: Vec<usize>) -> Self {
        self.dangerous_params = params;
        self
    }

    /// Builder: override severity.
    pub fn with_severity(mut self, severity: u8) -> Self {
        self.severity_override = Some(severity.min(10));
        self
    }

    /// Builder: set confidence level.
    pub fn with_confidence(mut self, confidence: f64) -> Self {
        self.confidence = confidence.clamp(0.0, 1.0);
        self
    }

    /// Builder: set receiver type.
    pub fn with_receiver(mut self, receiver: impl Into<String>) -> Self {
        self.receiver_type = Some(receiver.into());
        self
    }

    /// Builder: mark as property access.
    pub fn as_property(mut self) -> Self {
        self.is_property = true;
        self
    }

    /// Builder: add sanitizers.
    pub fn with_sanitizers(mut self, sanitizers: Vec<SanitizerContext>) -> Self {
        self.sanitizers = sanitizers;
        self
    }

    /// Builder: add a tag.
    pub fn with_tag(mut self, tag: impl Into<String>) -> Self {
        self.tags.push(tag.into());
        self
    }

    /// Get the effective severity level.
    #[inline]
    pub fn severity(&self) -> u8 {
        self.severity_override
            .unwrap_or_else(|| self.category.base_severity())
    }

    /// Check if a parameter position is dangerous.
    #[inline]
    pub fn is_dangerous_param(&self, position: usize) -> bool {
        self.dangerous_params.is_empty() || self.dangerous_params.contains(&position)
    }

    /// Check if a sanitizer context is acceptable for this sink.
    #[inline]
    pub fn accepts_sanitizer(&self, context: SanitizerContext) -> bool {
        self.sanitizers.contains(&context)
    }

    /// Check if a taint label is dangerous for this sink.
    pub fn is_dangerous_label(&self, label: &TaintLabel) -> bool {
        match self.category {
            SinkCategory::SqlInjection | SinkCategory::NoSqlInjection => matches!(
                label,
                TaintLabel::UserInput
                    | TaintLabel::HttpHeader
                    | TaintLabel::Cookie
                    | TaintLabel::UrlData
                    | TaintLabel::NetworkData
                    | TaintLabel::DeserializedData
            ),
            SinkCategory::CommandInjection => matches!(
                label,
                TaintLabel::UserInput
                    | TaintLabel::ProcessArgs
                    | TaintLabel::Environment
                    | TaintLabel::FileContent
                    | TaintLabel::NetworkData
            ),
            SinkCategory::XSS => matches!(
                label,
                TaintLabel::UserInput
                    | TaintLabel::UrlData
                    | TaintLabel::NetworkData
                    | TaintLabel::DatabaseQuery
                    | TaintLabel::DeserializedData
            ),
            SinkCategory::PathTraversal => matches!(
                label,
                TaintLabel::UserInput | TaintLabel::UrlData | TaintLabel::NetworkData
            ),
            SinkCategory::CodeExecution | SinkCategory::Deserialization => {
                // Any external input is dangerous for code execution
                true
            }
            _ => matches!(
                label,
                TaintLabel::UserInput | TaintLabel::NetworkData | TaintLabel::UrlData
            ),
        }
    }

    /// Get the pattern (alias for function_pattern for backward compatibility).
    #[inline]
    pub fn pattern(&self) -> &str {
        &self.function_pattern
    }
}

// =============================================================================
// Call Information for Matching
// =============================================================================

/// Information about a function/method call for sink matching.
#[derive(Debug, Clone)]
pub struct CallInfo {
    /// The function or method name being called
    pub function_name: String,
    /// The receiver object (for method calls)
    pub receiver: Option<String>,
    /// Argument expressions as strings
    pub arguments: Vec<String>,
    /// Source file path
    pub file_path: Option<String>,
    /// Line number of the call
    pub line: Option<usize>,
}

impl CallInfo {
    /// Create a new call info for a function call.
    pub fn function(name: impl Into<String>) -> Self {
        Self {
            function_name: name.into(),
            receiver: None,
            arguments: Vec::new(),
            file_path: None,
            line: None,
        }
    }

    /// Create a new call info for a method call.
    pub fn method(receiver: impl Into<String>, name: impl Into<String>) -> Self {
        Self {
            function_name: name.into(),
            receiver: Some(receiver.into()),
            arguments: Vec::new(),
            file_path: None,
            line: None,
        }
    }

    /// Builder: add arguments.
    pub fn with_args(mut self, args: Vec<String>) -> Self {
        self.arguments = args;
        self
    }

    /// Builder: add location.
    pub fn with_location(mut self, file: impl Into<String>, line: usize) -> Self {
        self.file_path = Some(file.into());
        self.line = Some(line);
        self
    }

    /// Get the full qualified name (receiver.method or just function).
    pub fn qualified_name(&self) -> String {
        match &self.receiver {
            Some(recv) => format!("{}.{}", recv, self.function_name),
            None => self.function_name.clone(),
        }
    }
}

// =============================================================================
// Sink Registry
// =============================================================================

/// Registry of taint sinks for a language.
#[derive(Debug, Default)]
pub struct SinkRegistry {
    /// All registered sinks
    sinks: Vec<Sink>,
    /// Index by category for faster lookups
    /// Uses FxHashMap for faster lookups
    by_category: FxHashMap<SinkCategory, Vec<usize>>,
    /// Index by pattern prefix for faster matching
    /// Uses FxHashMap for faster string-keyed lookups
    by_pattern: FxHashMap<String, Vec<usize>>,
}

impl SinkRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a sink to the registry.
    pub fn add(&mut self, sink: Sink) {
        let idx = self.sinks.len();
        let category = sink.category;
        let pattern = sink.function_pattern.clone();

        // Index by category
        self.by_category.entry(category).or_default().push(idx);

        // Index by pattern (first word/identifier)
        let pattern_key = pattern
            .split(&['.', '(', ' '][..])
            .next()
            .unwrap_or(&pattern)
            .to_string();
        self.by_pattern.entry(pattern_key).or_default().push(idx);

        self.sinks.push(sink);
    }

    /// Find sinks matching a pattern.
    pub fn find_matches(&self, pattern: &str) -> Vec<&Sink> {
        self.sinks
            .iter()
            .filter(|s| {
                // Exact match
                s.function_pattern == pattern
                    // Pattern contains the sink pattern
                    || pattern.contains(&s.function_pattern)
                    // Sink pattern contains the query
                    || s.function_pattern.contains(pattern)
            })
            .collect()
    }

    /// Find sinks matching a call info.
    pub fn find_matches_for_call(&self, call: &CallInfo) -> Vec<&Sink> {
        let qualified = call.qualified_name();
        let func_name = &call.function_name;

        self.sinks
            .iter()
            .filter(|s| {
                // Match against qualified name (receiver.method)
                qualified.contains(&s.function_pattern)
                    || s.function_pattern.contains(&qualified)
                    // Match against just function name
                    || func_name.contains(&s.function_pattern)
                    || s.function_pattern.contains(func_name)
            })
            .collect()
    }

    /// Get sinks for a specific category.
    pub fn sinks_for_category(&self, category: SinkCategory) -> Vec<&Sink> {
        self.by_category
            .get(&category)
            .map(|indices| indices.iter().map(|&i| &self.sinks[i]).collect())
            .unwrap_or_default()
    }

    /// Get all registered sinks.
    pub fn all_sinks(&self) -> &[Sink] {
        &self.sinks
    }

    /// Get the number of registered sinks.
    pub fn len(&self) -> usize {
        self.sinks.len()
    }

    /// Check if registry is empty.
    pub fn is_empty(&self) -> bool {
        self.sinks.is_empty()
    }

    /// Get categories with registered sinks.
    pub fn categories(&self) -> Vec<SinkCategory> {
        self.by_category.keys().copied().collect()
    }
}

// =============================================================================
// Sanitization Tracking
// =============================================================================

/// A sanitization event in the taint path.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SanitizationEvent {
    /// The sanitizer context applied
    pub context: SanitizerContext,
    /// Location where sanitization occurred
    pub location: Location,
    /// The sanitization function/method name
    pub function_name: String,
}

/// Result of checking if a taint path is properly sanitized.
#[derive(Debug, Clone)]
pub struct SanitizationResult {
    /// Whether the path is sanitized for the target sink
    pub is_sanitized: bool,
    /// Sanitizations that were applied
    pub applied_sanitizers: Vec<SanitizationEvent>,
    /// Sanitizations that would be effective but weren't applied
    pub missing_sanitizers: Vec<SanitizerContext>,
    /// Warning if partial/wrong sanitization was detected
    pub partial_sanitization_warning: Option<String>,
}

// =============================================================================
// API Functions
// =============================================================================

/// Find all matching sinks for a call in a specific language.
///
/// # Arguments
///
/// * `call` - Information about the function/method call
/// * `lang` - Programming language ("python", "typescript", "go", "rust")
///
/// # Returns
///
/// Vector of matching `Sink` definitions.
///
/// # Example
///
/// ```ignore
/// let call = CallInfo::method("cursor", "execute")
///     .with_args(vec!["query".to_string()]);
/// let sinks = find_sinks(&call, "python");
/// // Returns SQL injection sink for cursor.execute
/// ```
pub fn find_sinks(call: &CallInfo, lang: &str) -> Vec<Sink> {
    let registry = get_sinks_for_language(lang);
    registry
        .find_matches_for_call(call)
        .into_iter()
        .cloned()
        .collect()
}

/// Check if a taint path has been properly sanitized for a target sink.
///
/// This function analyzes the sanitization events in a taint path and
/// determines if they are appropriate for the target sink category.
///
/// # Arguments
///
/// * `sanitization_events` - List of sanitization events that occurred
/// * `target_sink` - The sink category being checked
///
/// # Returns
///
/// `SanitizationResult` with detailed information about sanitization status.
///
/// # Example
///
/// ```ignore
/// let events = vec![
///     SanitizationEvent {
///         context: SanitizerContext::HtmlEscape,
///         location: Location::new("app.py", 10, 1),
///         function_name: "escape".to_string(),
///     },
/// ];
///
/// let result = check_sanitization(&events, SinkCategory::SqlInjection);
/// // result.is_sanitized = false (HTML escape doesn't prevent SQL injection)
/// // result.partial_sanitization_warning = Some("...")
/// ```
pub fn check_sanitization(
    sanitization_events: &[SanitizationEvent],
    target_sink: SinkCategory,
) -> SanitizationResult {
    let applied: Vec<SanitizerContext> = sanitization_events.iter().map(|e| e.context).collect();

    // Check if any applied sanitizer is effective against the target
    let effective_sanitizers: Vec<SanitizerContext> = applied
        .iter()
        .filter(|ctx| ctx.is_effective_against(target_sink))
        .copied()
        .collect();

    let is_sanitized = !effective_sanitizers.is_empty();

    // Find sanitizers that weren't applied but would help
    let default_sanitizers = common::default_sanitizers_for(target_sink);
    let missing: Vec<SanitizerContext> = default_sanitizers
        .iter()
        .copied()
        .filter(|s| !applied.contains(s))
        .collect();

    // Check for partial sanitization (applied but ineffective)
    let partial_warning = if !applied.is_empty() && effective_sanitizers.is_empty() {
        let applied_names: Vec<String> = applied.iter().map(|s| format!("{:?}", s)).collect();
        Some(format!(
            "Partial sanitization detected: {} applied but not effective against {}. \
             Consider using: {:?}",
            applied_names.join(", "),
            target_sink.description(),
            &default_sanitizers
        ))
    } else {
        None
    };

    SanitizationResult {
        is_sanitized,
        applied_sanitizers: sanitization_events.to_vec(),
        missing_sanitizers: missing,
        partial_sanitization_warning: partial_warning,
    }
}

/// Simplified check: is the taint path sanitized for a context?
///
/// # Arguments
///
/// * `applied_contexts` - Sanitizer contexts that were applied
/// * `target` - The target sink category
///
/// # Returns
///
/// `true` if at least one applied sanitizer is effective against the target.
pub fn is_sanitized_for_context(
    applied_contexts: &[SanitizerContext],
    target: SinkCategory,
) -> bool {
    applied_contexts
        .iter()
        .any(|ctx| ctx.is_effective_against(target))
}

/// Get the taint sink registry for a language.
pub fn get_sinks_for_language(language: &str) -> SinkRegistry {
    match language.to_lowercase().as_str() {
        "python" | "py" => python::get_python_sinks(),
        "typescript" | "ts" | "javascript" | "js" | "tsx" | "jsx" => {
            typescript::get_typescript_sinks()
        }
        "go" | "golang" => go::get_go_sinks(),
        "rust" | "rs" => rust_lang::get_rust_sinks(),
        _ => SinkRegistry::new(),
    }
}


/// Map function names to their sanitizer contexts.
///
/// This function recognizes common sanitization functions and returns the
/// appropriate `SanitizerContext` values.
pub fn recognize_sanitizer(function_name: &str, lang: &str) -> Vec<SanitizerContext> {
    let name_lower = function_name.to_lowercase();

    match lang.to_lowercase().as_str() {
        "python" | "py" => recognize_python_sanitizer(&name_lower),
        "typescript" | "ts" | "javascript" | "js" => recognize_typescript_sanitizer(&name_lower),
        "go" | "golang" => recognize_go_sanitizer(&name_lower),
        "rust" | "rs" => recognize_rust_sanitizer(&name_lower),
        _ => Vec::new(),
    }
}

fn recognize_python_sanitizer(name: &str) -> Vec<SanitizerContext> {
    let mut contexts = Vec::new();

    // SQL sanitizers
    if name.contains("parameterized")
        || name.contains("prepared")
        || name.contains("bind")
        || name.contains("mogrify")
    {
        contexts.push(SanitizerContext::SqlParameterized);
    }

    // HTML/XSS sanitizers
    if name.contains("escape") && (name.contains("html") || name.contains("markup")) {
        contexts.push(SanitizerContext::HtmlEscape);
    }
    if name == "escape" || name == "e" || name.contains("html.escape") {
        contexts.push(SanitizerContext::HtmlEscape);
    }
    if name.contains("bleach") || name.contains("sanitize") {
        contexts.push(SanitizerContext::DomSanitize);
    }

    // Shell sanitizers
    if name.contains("shlex.quote") || name.contains("quote") {
        contexts.push(SanitizerContext::ShellEscape);
    }

    // Path sanitizers
    if name.contains("realpath")
        || name.contains("abspath")
        || name.contains("normpath")
        || name.contains("resolve")
    {
        contexts.push(SanitizerContext::PathCanonicalize);
    }
    if name.contains("basename") {
        contexts.push(SanitizerContext::PathBasename);
    }

    // URL sanitizers
    if name.contains("urlencode") || name.contains("quote_plus") {
        contexts.push(SanitizerContext::UrlEncode);
    }

    contexts
}

fn recognize_typescript_sanitizer(name: &str) -> Vec<SanitizerContext> {
    let mut contexts = Vec::new();

    // XSS sanitizers
    if name.contains("dompurify")
        || name.contains("sanitize")
        || name.contains("createtextnode")
        || name.contains("textcontent")
    {
        contexts.push(SanitizerContext::DomSanitize);
    }
    if name.contains("encodeuricomponent") || name.contains("encodeuri") {
        contexts.push(SanitizerContext::UrlEncode);
    }
    if name.contains("escape") && name.contains("html") {
        contexts.push(SanitizerContext::HtmlEscape);
    }

    // Path sanitizers
    if name.contains("path.normalize") || name.contains("path.resolve") {
        contexts.push(SanitizerContext::PathCanonicalize);
    }
    if name.contains("path.basename") {
        contexts.push(SanitizerContext::PathBasename);
    }

    // SQL sanitizers
    if name.contains("prepare") || name.contains("parameterized") {
        contexts.push(SanitizerContext::SqlParameterized);
    }

    contexts
}

fn recognize_go_sanitizer(name: &str) -> Vec<SanitizerContext> {
    let mut contexts = Vec::new();

    // HTML sanitizers
    if name.contains("template.htmlescapestring")
        || name.contains("html.escapestring")
        || name.contains("htmlescape")
    {
        contexts.push(SanitizerContext::HtmlEscape);
    }

    // Path sanitizers
    if name.contains("filepath.clean") || name.contains("filepath.abs") {
        contexts.push(SanitizerContext::PathCanonicalize);
    }
    if name.contains("filepath.base") {
        contexts.push(SanitizerContext::PathBasename);
    }

    // URL sanitizers
    if name.contains("url.queryescape") || name.contains("url.pathescape") {
        contexts.push(SanitizerContext::UrlEncode);
    }

    contexts
}

fn recognize_rust_sanitizer(name: &str) -> Vec<SanitizerContext> {
    let mut contexts = Vec::new();

    // HTML sanitizers
    if name.contains("encode_safe")
        || name.contains("encode_minimal")
        || name.contains("html_escape")
    {
        contexts.push(SanitizerContext::HtmlEscape);
    }
    if name.contains("ammonia") || name.contains("sanitize") {
        contexts.push(SanitizerContext::DomSanitize);
    }

    // Path sanitizers
    if name.contains("canonicalize") {
        contexts.push(SanitizerContext::PathCanonicalize);
    }
    if name.contains("file_name") || name.contains("filename") {
        contexts.push(SanitizerContext::PathBasename);
    }

    // SQL - sqlx uses compile-time checked queries
    if name.contains("sqlx::query!") || name.contains("query_as!") {
        contexts.push(SanitizerContext::SqlParameterized);
    }

    contexts
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sink_category_metadata() {
        assert_eq!(SinkCategory::SqlInjection.cwe_id(), "CWE-89");
        assert_eq!(SinkCategory::CommandInjection.base_severity(), 10);
        assert!(SinkCategory::XSS.base_severity() > 0);
    }

    #[test]
    fn test_sanitizer_effectiveness() {
        // HTML escape should be effective against XSS
        assert!(SanitizerContext::HtmlEscape.is_effective_against(SinkCategory::XSS));
        // But NOT against SQL injection
        assert!(!SanitizerContext::HtmlEscape.is_effective_against(SinkCategory::SqlInjection));

        // SQL parameterized should be effective against SQL injection
        assert!(SanitizerContext::SqlParameterized.is_effective_against(SinkCategory::SqlInjection));
        // But NOT against XSS
        assert!(!SanitizerContext::SqlParameterized.is_effective_against(SinkCategory::XSS));
    }

    #[test]
    fn test_partial_sanitization_detection() {
        // Apply HTML escape to SQL sink - should warn about partial sanitization
        let events = vec![SanitizationEvent {
            context: SanitizerContext::HtmlEscape,
            location: Location::new("test.py", 10, 1),
            function_name: "html.escape".to_string(),
        }];

        let result = check_sanitization(&events, SinkCategory::SqlInjection);
        assert!(!result.is_sanitized);
        assert!(result.partial_sanitization_warning.is_some());

        // Apply SQL parameterized to SQL sink - should be sanitized
        let events2 = vec![SanitizationEvent {
            context: SanitizerContext::SqlParameterized,
            location: Location::new("test.py", 10, 1),
            function_name: "cursor.execute".to_string(),
        }];

        let result2 = check_sanitization(&events2, SinkCategory::SqlInjection);
        assert!(result2.is_sanitized);
        assert!(result2.partial_sanitization_warning.is_none());
    }

    #[test]
    fn test_find_sinks() {
        let call = CallInfo::method("cursor", "execute");
        let sinks = find_sinks(&call, "python");

        assert!(!sinks.is_empty());
        assert!(sinks
            .iter()
            .any(|s| s.category == SinkCategory::SqlInjection));
    }

    #[test]
    fn test_sink_dangerous_params() {
        let sql_sink = Sink::sql("execute", "test");
        assert!(sql_sink.is_dangerous_param(0));
        assert!(!sql_sink.is_dangerous_param(1));

        // Command sinks with empty dangerous_params means all are dangerous
        let cmd_sink = Sink::command("exec", "test");
        assert!(cmd_sink.is_dangerous_param(0));
        assert!(cmd_sink.is_dangerous_param(99));
    }

    #[test]
    fn test_sink_accepts_sanitizer() {
        let sql_sink = Sink::sql("execute", "test");
        assert!(sql_sink.accepts_sanitizer(SanitizerContext::SqlParameterized));
        assert!(!sql_sink.accepts_sanitizer(SanitizerContext::HtmlEscape));

        let xss_sink = Sink::xss("innerHTML", "test");
        assert!(xss_sink.accepts_sanitizer(SanitizerContext::HtmlEscape));
        assert!(!xss_sink.accepts_sanitizer(SanitizerContext::SqlParameterized));
    }

    #[test]
    fn test_call_info_qualified_name() {
        let func_call = CallInfo::function("eval");
        assert_eq!(func_call.qualified_name(), "eval");

        let method_call = CallInfo::method("cursor", "execute");
        assert_eq!(method_call.qualified_name(), "cursor.execute");
    }

    #[test]
    fn test_is_sanitized_for_context() {
        let applied = vec![SanitizerContext::HtmlEscape];

        assert!(is_sanitized_for_context(&applied, SinkCategory::XSS));
        assert!(!is_sanitized_for_context(
            &applied,
            SinkCategory::SqlInjection
        ));
    }

    #[test]
    fn test_recognize_python_sanitizer() {
        let contexts = recognize_sanitizer("html.escape", "python");
        assert!(contexts.contains(&SanitizerContext::HtmlEscape));

        let contexts = recognize_sanitizer("shlex.quote", "python");
        assert!(contexts.contains(&SanitizerContext::ShellEscape));
    }

    #[test]
    fn test_sink_registry() {
        let mut registry = SinkRegistry::new();
        registry.add(Sink::sql("execute", "test"));
        registry.add(Sink::command("system", "test"));

        assert_eq!(registry.len(), 2);

        let sql_sinks = registry.sinks_for_category(SinkCategory::SqlInjection);
        assert_eq!(sql_sinks.len(), 1);

        let cmd_sinks = registry.sinks_for_category(SinkCategory::CommandInjection);
        assert_eq!(cmd_sinks.len(), 1);
    }

    #[test]
    fn test_get_sinks_for_language() {
        let py = get_sinks_for_language("python");
        assert!(!py.is_empty());

        let ts = get_sinks_for_language("TypeScript");
        assert!(!ts.is_empty());

        let go = get_sinks_for_language("go");
        assert!(!go.is_empty());

        let rs = get_sinks_for_language("rust");
        assert!(!rs.is_empty());

        let unknown = get_sinks_for_language("cobol");
        assert!(unknown.is_empty());
    }

    #[test]
    fn test_all_categories() {
        let all = SinkCategory::all();
        assert!(all.len() >= 10);
        assert!(all.contains(&SinkCategory::SqlInjection));
        assert!(all.contains(&SinkCategory::XSS));
    }
}
