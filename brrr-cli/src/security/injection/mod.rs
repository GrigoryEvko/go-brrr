//! Injection vulnerability detection.
//!
//! Detects various injection vulnerabilities:
//! - Command injection (shell commands, eval/exec)
//! - SQL injection (Python, TypeScript/JavaScript)
//! - Path traversal (directory traversal via ../ and absolute paths)
//! - XSS injection (JavaScript/TypeScript, React, Vue, Angular)
//! - Log injection (newline injection, format strings, CRLF, terminal escapes)
//! - Header injection (HTTP response splitting, open redirect, session fixation)
//! - Template injection (SSTI - Server-Side Template Injection, CWE-1336)
//! - LDAP injection (future)
//! - XPath injection (future)
//!
//! # Architecture
//!
//! The injection detection system is built on shared infrastructure:
//!
//! - [`scanner_base`] - Common trait and utilities for all scanners
//! - [`utils`] - Shared utility functions (language detection, variable extraction)
//!
//! Each specific injection type has its own module with specialized detection logic.

// Base infrastructure (shared across all scanners)
pub mod scanner_base;
pub mod utils;

// Specific injection detectors
pub mod command;
pub mod header_injection;
pub mod log_injection;
pub mod path_traversal;
pub mod sql;
pub mod template_injection;
pub mod xss;

// Re-export commonly used types for convenience
pub use scanner_base::{
    node_text, location_from_node, location_from_node_with_snippet,
    find_child, filter_children, is_string_literal, is_identifier,
    CaptureExtractor, ScanResultSummary, SecurityScanner,
};
pub use utils::{
    detect_language_from_path, extract_code_snippet, extract_template_variables,
    is_constant_name, is_static_string, is_template_file,
};
