//! Injection vulnerability detection.
//!
//! Detects various injection vulnerabilities:
//! - Command injection (shell commands, eval/exec)
//! - SQL injection (Python, TypeScript/JavaScript)
//! - Path traversal (directory traversal via ../ and absolute paths)
//! - XSS injection (JavaScript/TypeScript, React, Vue, Angular)
//! - LDAP injection (future)
//! - XPath injection (future)

pub mod command;
pub mod path_traversal;
pub mod sql;
pub mod xss;
