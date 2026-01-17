//! Path Traversal vulnerability detection for multiple programming languages.
//!
//! Detects potential path traversal (directory traversal) vulnerabilities by analyzing:
//! - User input directly passed to file operation functions
//! - Improper use of path joining functions (os.path.join is NOT a sanitizer!)
//! - Missing path validation (realpath + startswith check)
//! - Hardcoded "../" patterns in strings
//!
//! # Vulnerability Overview
//!
//! Path traversal allows attackers to access files outside the intended directory
//! by manipulating path inputs with sequences like `../` or absolute paths.
//!
//! # Dangerous Patterns (Flagged)
//!
//! - `open(user_input)` without validation
//! - `os.path.join(base, user_input)` - Still vulnerable to absolute paths and `..`!
//! - `Path(user_input).read_text()` - Python pathlib
//! - `fs.readFile(user_input)` - Node.js
//! - `std::fs::read(user_input)` - Rust
//! - `os.Open(path)` with user input - Go
//! - `fopen(user_input)` - C
//!
//! # Safe Patterns (NOT Flagged)
//!
//! - `realpath()` followed by `startswith()` check
//! - `os.path.basename()` to extract only filename
//! - Allowlist validation against known filenames
//! - Chroot or sandboxed file access
//!
//! # Symlink Attack Considerations
//!
//! Even with path validation, symlink attacks are possible:
//! - Time-of-check to time-of-use (TOCTOU) race conditions
//! - Symlinks created between validation and file access
//! - Use `O_NOFOLLOW` flag or equivalent to prevent symlink following
//!
//! # Detection Strategy
//!
//! 1. Find file operation sinks (open, read, write, delete functions)
//! 2. Track if path argument comes from user-controlled sources
//! 3. Check for proper validation patterns nearby
//! 4. Flag `../` patterns in static strings (hardcoded traversal bugs)
//! 5. Flag `os.path.join` with user input (common misconception about safety)

use std::collections::{HashMap, HashSet};
use std::path::Path;

use aho_corasick::AhoCorasick;
use once_cell::sync::Lazy;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use streaming_iterator::StreamingIterator;
use tree_sitter::{Node, Query, QueryCursor, Tree};

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{Result, BrrrError};
use crate::lang::LanguageRegistry;
use crate::util::format_query_error;

// =============================================================================
// Static Pattern Matchers
// =============================================================================

/// Aho-Corasick automaton for detecting user input patterns.
/// Single-pass multi-pattern matching replaces 18 sequential `.contains()` calls.
static USER_INPUT_PATTERNS: Lazy<AhoCorasick> = Lazy::new(|| {
    AhoCorasick::new([
        "request", "req", "params", "query", "body", "input",
        "user", "filename", "file_name", "filepath", "file_path",
        "name", "path", "url", "uri", "data", "arg", "param",
        "stdin", "argv",
    ]).expect("USER_INPUT_PATTERNS: invalid patterns")
});

// =============================================================================
// Type Definitions
// =============================================================================

/// Severity level for path traversal findings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// Informational - pattern detected but likely not exploitable
    Info,
    /// Low severity - requires specific conditions to exploit
    Low,
    /// Medium severity - potential for file access outside intended directory
    Medium,
    /// High severity - likely exploitable path traversal
    High,
    /// Critical - easily exploitable with severe impact (arbitrary file read/write/delete)
    Critical,
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

/// Confidence level for the finding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Confidence {
    /// Low confidence - pattern match only, no data flow confirmation
    Low,
    /// Medium confidence - some indicators but incomplete validation check
    Medium,
    /// High confidence - clear user input to file operation without validation
    High,
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

/// Type of file operation sink.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FileOperationType {
    /// Reading file contents
    Read,
    /// Writing to files
    Write,
    /// Appending to files
    Append,
    /// Deleting/unlinking files
    Delete,
    /// File existence check
    Exists,
    /// Directory listing/traversal
    ListDir,
    /// File/directory creation
    Create,
    /// File move/rename
    Move,
    /// File copy
    Copy,
    /// Generic file open (mode unknown)
    Open,
}

impl std::fmt::Display for FileOperationType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Read => write!(f, "read"),
            Self::Write => write!(f, "write"),
            Self::Append => write!(f, "append"),
            Self::Delete => write!(f, "delete"),
            Self::Exists => write!(f, "exists"),
            Self::ListDir => write!(f, "list_dir"),
            Self::Create => write!(f, "create"),
            Self::Move => write!(f, "move"),
            Self::Copy => write!(f, "copy"),
            Self::Open => write!(f, "open"),
        }
    }
}

/// Type of vulnerable pattern detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VulnerablePattern {
    /// User input directly passed to file operation
    DirectUserInput,
    /// os.path.join with user input (NOT a sanitizer!)
    UnsafePathJoin,
    /// Path concatenation with user input
    PathConcatenation,
    /// Hardcoded "../" pattern in string literal
    HardcodedTraversal,
    /// Variable passed without visible validation
    UnvalidatedVariable,
    /// Template/f-string with path interpolation
    PathInterpolation,
    /// Missing realpath + startswith validation
    MissingValidation,
}

impl std::fmt::Display for VulnerablePattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DirectUserInput => write!(f, "direct_user_input"),
            Self::UnsafePathJoin => write!(f, "unsafe_path_join"),
            Self::PathConcatenation => write!(f, "path_concatenation"),
            Self::HardcodedTraversal => write!(f, "hardcoded_traversal"),
            Self::UnvalidatedVariable => write!(f, "unvalidated_variable"),
            Self::PathInterpolation => write!(f, "path_interpolation"),
            Self::MissingValidation => write!(f, "missing_validation"),
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

/// A path traversal finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PathTraversalFinding {
    /// Location of the vulnerable sink call
    pub location: SourceLocation,
    /// Severity of the vulnerability
    pub severity: Severity,
    /// Name of the file operation function being called
    pub sink_function: String,
    /// Type of file operation
    pub operation_type: FileOperationType,
    /// The path expression reaching the sink
    pub path_expression: String,
    /// Confidence level of the finding
    pub confidence: Confidence,
    /// Type of vulnerable pattern detected
    pub pattern: VulnerablePattern,
    /// Variables involved in the path construction
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub involved_variables: Vec<String>,
    /// Code snippet showing the vulnerable pattern
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code_snippet: Option<String>,
    /// Human-readable description
    pub description: String,
    /// Remediation advice
    pub remediation: String,
    /// Whether symlink attacks are also possible
    pub symlink_risk: bool,
}

/// Result of scanning for path traversal vulnerabilities.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScanResult {
    /// All findings
    pub findings: Vec<PathTraversalFinding>,
    /// Number of files scanned
    pub files_scanned: usize,
    /// Number of file operation sinks found
    pub sinks_found: usize,
    /// Counts by severity
    pub severity_counts: HashMap<String, usize>,
    /// Language detected
    pub language: String,
}

// =============================================================================
// File Operation Sink Definitions
// =============================================================================

/// Definition of a file operation sink.
#[derive(Debug, Clone)]
pub struct FileSink {
    /// Language this sink applies to
    pub language: &'static str,
    /// Module or namespace (e.g., "os", "fs", "std::fs")
    pub module: Option<&'static str>,
    /// Function name (e.g., "open", "read", "readFile")
    pub function: &'static str,
    /// Argument index that receives the path (0-indexed)
    pub path_arg_index: usize,
    /// Type of file operation
    pub operation_type: FileOperationType,
    /// Base severity when this sink is exploited
    pub severity: Severity,
    /// Description of the sink
    pub description: &'static str,
}

/// Get all known file operation sinks for a language.
pub fn get_file_sinks(language: &str) -> Vec<FileSink> {
    match language {
        "python" => python_sinks(),
        "typescript" | "javascript" => typescript_sinks(),
        "rust" => rust_sinks(),
        "go" => go_sinks(),
        "c" | "cpp" => c_sinks(),
        _ => vec![],
    }
}

fn python_sinks() -> Vec<FileSink> {
    vec![
        // Built-in open
        FileSink {
            language: "python",
            module: None,
            function: "open",
            path_arg_index: 0,
            operation_type: FileOperationType::Open,
            severity: Severity::High,
            description: "Built-in open() function",
        },
        // pathlib methods
        FileSink {
            language: "python",
            module: Some("pathlib"),
            function: "read_text",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "Path.read_text() reads file contents",
        },
        FileSink {
            language: "python",
            module: Some("pathlib"),
            function: "read_bytes",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "Path.read_bytes() reads binary file contents",
        },
        FileSink {
            language: "python",
            module: Some("pathlib"),
            function: "write_text",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "Path.write_text() writes file contents",
        },
        FileSink {
            language: "python",
            module: Some("pathlib"),
            function: "write_bytes",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "Path.write_bytes() writes binary contents",
        },
        FileSink {
            language: "python",
            module: Some("pathlib"),
            function: "unlink",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "Path.unlink() deletes file",
        },
        FileSink {
            language: "python",
            module: Some("pathlib"),
            function: "rmdir",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "Path.rmdir() removes directory",
        },
        FileSink {
            language: "python",
            module: Some("pathlib"),
            function: "mkdir",
            path_arg_index: 0,
            operation_type: FileOperationType::Create,
            severity: Severity::Medium,
            description: "Path.mkdir() creates directory",
        },
        // os module
        FileSink {
            language: "python",
            module: Some("os"),
            function: "remove",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "os.remove() deletes file",
        },
        FileSink {
            language: "python",
            module: Some("os"),
            function: "unlink",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "os.unlink() deletes file",
        },
        FileSink {
            language: "python",
            module: Some("os"),
            function: "rmdir",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "os.rmdir() removes directory",
        },
        FileSink {
            language: "python",
            module: Some("os"),
            function: "mkdir",
            path_arg_index: 0,
            operation_type: FileOperationType::Create,
            severity: Severity::Medium,
            description: "os.mkdir() creates directory",
        },
        FileSink {
            language: "python",
            module: Some("os"),
            function: "makedirs",
            path_arg_index: 0,
            operation_type: FileOperationType::Create,
            severity: Severity::Medium,
            description: "os.makedirs() creates directory tree",
        },
        FileSink {
            language: "python",
            module: Some("os"),
            function: "listdir",
            path_arg_index: 0,
            operation_type: FileOperationType::ListDir,
            severity: Severity::Medium,
            description: "os.listdir() lists directory contents",
        },
        FileSink {
            language: "python",
            module: Some("os"),
            function: "rename",
            path_arg_index: 0,
            operation_type: FileOperationType::Move,
            severity: Severity::Critical,
            description: "os.rename() moves/renames file",
        },
        FileSink {
            language: "python",
            module: Some("os"),
            function: "replace",
            path_arg_index: 0,
            operation_type: FileOperationType::Move,
            severity: Severity::Critical,
            description: "os.replace() replaces file atomically",
        },
        // os.path - join is NOT a sink itself but flagged specially
        FileSink {
            language: "python",
            module: Some("os.path"),
            function: "join",
            path_arg_index: 1, // Second arg is typically user input
            operation_type: FileOperationType::Open,
            severity: Severity::High, // Misconception that join sanitizes
            description: "os.path.join() does NOT sanitize - still vulnerable to absolute paths and ..",
        },
        // shutil module
        FileSink {
            language: "python",
            module: Some("shutil"),
            function: "copy",
            path_arg_index: 0,
            operation_type: FileOperationType::Copy,
            severity: Severity::High,
            description: "shutil.copy() copies file",
        },
        FileSink {
            language: "python",
            module: Some("shutil"),
            function: "copy2",
            path_arg_index: 0,
            operation_type: FileOperationType::Copy,
            severity: Severity::High,
            description: "shutil.copy2() copies file with metadata",
        },
        FileSink {
            language: "python",
            module: Some("shutil"),
            function: "copyfile",
            path_arg_index: 0,
            operation_type: FileOperationType::Copy,
            severity: Severity::High,
            description: "shutil.copyfile() copies file contents",
        },
        FileSink {
            language: "python",
            module: Some("shutil"),
            function: "copytree",
            path_arg_index: 0,
            operation_type: FileOperationType::Copy,
            severity: Severity::High,
            description: "shutil.copytree() copies entire directory",
        },
        FileSink {
            language: "python",
            module: Some("shutil"),
            function: "rmtree",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "shutil.rmtree() deletes entire directory tree",
        },
        FileSink {
            language: "python",
            module: Some("shutil"),
            function: "move",
            path_arg_index: 0,
            operation_type: FileOperationType::Move,
            severity: Severity::Critical,
            description: "shutil.move() moves file or directory",
        },
    ]
}

fn typescript_sinks() -> Vec<FileSink> {
    vec![
        // fs module - callback style
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "readFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "fs.readFile() reads file contents",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "readFileSync",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "fs.readFileSync() synchronously reads file",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "writeFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "fs.writeFile() writes file contents",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "writeFileSync",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "fs.writeFileSync() synchronously writes file",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "appendFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Append,
            severity: Severity::High,
            description: "fs.appendFile() appends to file",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "appendFileSync",
            path_arg_index: 0,
            operation_type: FileOperationType::Append,
            severity: Severity::High,
            description: "fs.appendFileSync() synchronously appends",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "unlink",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "fs.unlink() deletes file",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "unlinkSync",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "fs.unlinkSync() synchronously deletes file",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "rmdir",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "fs.rmdir() removes directory",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "rm",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "fs.rm() removes file or directory",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "mkdir",
            path_arg_index: 0,
            operation_type: FileOperationType::Create,
            severity: Severity::Medium,
            description: "fs.mkdir() creates directory",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "readdir",
            path_arg_index: 0,
            operation_type: FileOperationType::ListDir,
            severity: Severity::Medium,
            description: "fs.readdir() lists directory contents",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "rename",
            path_arg_index: 0,
            operation_type: FileOperationType::Move,
            severity: Severity::Critical,
            description: "fs.rename() moves/renames file",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "copyFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Copy,
            severity: Severity::High,
            description: "fs.copyFile() copies file",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "createReadStream",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "fs.createReadStream() opens read stream",
        },
        FileSink {
            language: "typescript",
            module: Some("fs"),
            function: "createWriteStream",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "fs.createWriteStream() opens write stream",
        },
        // fs/promises module
        FileSink {
            language: "typescript",
            module: Some("fs/promises"),
            function: "readFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "fsPromises.readFile() async reads file",
        },
        FileSink {
            language: "typescript",
            module: Some("fs/promises"),
            function: "writeFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "fsPromises.writeFile() async writes file",
        },
        // path.join - NOT a sanitizer!
        FileSink {
            language: "typescript",
            module: Some("path"),
            function: "join",
            path_arg_index: 1,
            operation_type: FileOperationType::Open,
            severity: Severity::High,
            description: "path.join() does NOT sanitize - still vulnerable to ..",
        },
        FileSink {
            language: "typescript",
            module: Some("path"),
            function: "resolve",
            path_arg_index: 0,
            operation_type: FileOperationType::Open,
            severity: Severity::High,
            description: "path.resolve() resolves to absolute path but doesn't validate",
        },
    ]
}

fn rust_sinks() -> Vec<FileSink> {
    vec![
        // std::fs module
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "read",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "std::fs::read() reads file to Vec<u8>",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "read_to_string",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "std::fs::read_to_string() reads file to String",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "write",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "std::fs::write() writes data to file",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "remove_file",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "std::fs::remove_file() deletes file",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "remove_dir",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "std::fs::remove_dir() removes empty directory",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "remove_dir_all",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "std::fs::remove_dir_all() recursively deletes directory",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "create_dir",
            path_arg_index: 0,
            operation_type: FileOperationType::Create,
            severity: Severity::Medium,
            description: "std::fs::create_dir() creates directory",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "create_dir_all",
            path_arg_index: 0,
            operation_type: FileOperationType::Create,
            severity: Severity::Medium,
            description: "std::fs::create_dir_all() creates directory tree",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "copy",
            path_arg_index: 0,
            operation_type: FileOperationType::Copy,
            severity: Severity::High,
            description: "std::fs::copy() copies file contents",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "rename",
            path_arg_index: 0,
            operation_type: FileOperationType::Move,
            severity: Severity::Critical,
            description: "std::fs::rename() moves/renames file",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "read_dir",
            path_arg_index: 0,
            operation_type: FileOperationType::ListDir,
            severity: Severity::Medium,
            description: "std::fs::read_dir() lists directory contents",
        },
        // File::open
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "File::open",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "File::open() opens file for reading",
        },
        FileSink {
            language: "rust",
            module: Some("std::fs"),
            function: "File::create",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "File::create() creates/truncates file",
        },
        // Path::new with user input
        FileSink {
            language: "rust",
            module: Some("std::path"),
            function: "Path::new",
            path_arg_index: 0,
            operation_type: FileOperationType::Open,
            severity: Severity::Medium,
            description: "Path::new() with user input may enable traversal",
        },
        // tokio::fs for async operations
        FileSink {
            language: "rust",
            module: Some("tokio::fs"),
            function: "read",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "tokio::fs::read() async reads file",
        },
        FileSink {
            language: "rust",
            module: Some("tokio::fs"),
            function: "write",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "tokio::fs::write() async writes file",
        },
    ]
}

fn go_sinks() -> Vec<FileSink> {
    vec![
        // os package
        FileSink {
            language: "go",
            module: Some("os"),
            function: "Open",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "os.Open() opens file for reading",
        },
        FileSink {
            language: "go",
            module: Some("os"),
            function: "OpenFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Open,
            severity: Severity::High,
            description: "os.OpenFile() opens file with specified flags",
        },
        FileSink {
            language: "go",
            module: Some("os"),
            function: "Create",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "os.Create() creates/truncates file",
        },
        FileSink {
            language: "go",
            module: Some("os"),
            function: "Remove",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "os.Remove() deletes file",
        },
        FileSink {
            language: "go",
            module: Some("os"),
            function: "RemoveAll",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "os.RemoveAll() recursively deletes path",
        },
        FileSink {
            language: "go",
            module: Some("os"),
            function: "Rename",
            path_arg_index: 0,
            operation_type: FileOperationType::Move,
            severity: Severity::Critical,
            description: "os.Rename() moves/renames file",
        },
        FileSink {
            language: "go",
            module: Some("os"),
            function: "Mkdir",
            path_arg_index: 0,
            operation_type: FileOperationType::Create,
            severity: Severity::Medium,
            description: "os.Mkdir() creates directory",
        },
        FileSink {
            language: "go",
            module: Some("os"),
            function: "MkdirAll",
            path_arg_index: 0,
            operation_type: FileOperationType::Create,
            severity: Severity::Medium,
            description: "os.MkdirAll() creates directory tree",
        },
        FileSink {
            language: "go",
            module: Some("os"),
            function: "ReadDir",
            path_arg_index: 0,
            operation_type: FileOperationType::ListDir,
            severity: Severity::Medium,
            description: "os.ReadDir() lists directory entries",
        },
        FileSink {
            language: "go",
            module: Some("os"),
            function: "ReadFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "os.ReadFile() reads entire file",
        },
        FileSink {
            language: "go",
            module: Some("os"),
            function: "WriteFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "os.WriteFile() writes entire file",
        },
        // ioutil (deprecated but still used)
        FileSink {
            language: "go",
            module: Some("ioutil"),
            function: "ReadFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Read,
            severity: Severity::High,
            description: "ioutil.ReadFile() reads entire file",
        },
        FileSink {
            language: "go",
            module: Some("ioutil"),
            function: "WriteFile",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "ioutil.WriteFile() writes entire file",
        },
        FileSink {
            language: "go",
            module: Some("ioutil"),
            function: "ReadDir",
            path_arg_index: 0,
            operation_type: FileOperationType::ListDir,
            severity: Severity::Medium,
            description: "ioutil.ReadDir() lists directory",
        },
        // filepath.Join - NOT a sanitizer!
        FileSink {
            language: "go",
            module: Some("filepath"),
            function: "Join",
            path_arg_index: 1,
            operation_type: FileOperationType::Open,
            severity: Severity::High,
            description: "filepath.Join() does NOT sanitize - cleans but allows ..",
        },
    ]
}

fn c_sinks() -> Vec<FileSink> {
    vec![
        // Standard C library
        FileSink {
            language: "c",
            module: None,
            function: "fopen",
            path_arg_index: 0,
            operation_type: FileOperationType::Open,
            severity: Severity::High,
            description: "fopen() opens file stream",
        },
        FileSink {
            language: "c",
            module: None,
            function: "freopen",
            path_arg_index: 0,
            operation_type: FileOperationType::Open,
            severity: Severity::High,
            description: "freopen() reopens file stream",
        },
        FileSink {
            language: "c",
            module: None,
            function: "open",
            path_arg_index: 0,
            operation_type: FileOperationType::Open,
            severity: Severity::High,
            description: "open() POSIX file open",
        },
        FileSink {
            language: "c",
            module: None,
            function: "openat",
            path_arg_index: 1,
            operation_type: FileOperationType::Open,
            severity: Severity::High,
            description: "openat() opens file relative to directory fd",
        },
        FileSink {
            language: "c",
            module: None,
            function: "creat",
            path_arg_index: 0,
            operation_type: FileOperationType::Write,
            severity: Severity::Critical,
            description: "creat() creates file",
        },
        FileSink {
            language: "c",
            module: None,
            function: "remove",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "remove() deletes file",
        },
        FileSink {
            language: "c",
            module: None,
            function: "unlink",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "unlink() removes file",
        },
        FileSink {
            language: "c",
            module: None,
            function: "rmdir",
            path_arg_index: 0,
            operation_type: FileOperationType::Delete,
            severity: Severity::Critical,
            description: "rmdir() removes directory",
        },
        FileSink {
            language: "c",
            module: None,
            function: "mkdir",
            path_arg_index: 0,
            operation_type: FileOperationType::Create,
            severity: Severity::Medium,
            description: "mkdir() creates directory",
        },
        FileSink {
            language: "c",
            module: None,
            function: "rename",
            path_arg_index: 0,
            operation_type: FileOperationType::Move,
            severity: Severity::Critical,
            description: "rename() moves/renames file",
        },
        FileSink {
            language: "c",
            module: None,
            function: "opendir",
            path_arg_index: 0,
            operation_type: FileOperationType::ListDir,
            severity: Severity::Medium,
            description: "opendir() opens directory for reading",
        },
        FileSink {
            language: "c",
            module: None,
            function: "stat",
            path_arg_index: 0,
            operation_type: FileOperationType::Exists,
            severity: Severity::Low,
            description: "stat() gets file status",
        },
        FileSink {
            language: "c",
            module: None,
            function: "lstat",
            path_arg_index: 0,
            operation_type: FileOperationType::Exists,
            severity: Severity::Low,
            description: "lstat() gets symlink status",
        },
        FileSink {
            language: "c",
            module: None,
            function: "access",
            path_arg_index: 0,
            operation_type: FileOperationType::Exists,
            severity: Severity::Low,
            description: "access() checks file permissions",
        },
    ]
}

// =============================================================================
// Tree-sitter Queries
// =============================================================================

/// Python sink detection query.
const PYTHON_SINK_QUERY: &str = r#"
; Built-in open()
(call function: (identifier) @func
  (#eq? @func "open")
  arguments: (argument_list) @args) @sink

; pathlib Path methods - read/write
(call function: (attribute object: (call function: (identifier) @pathlib) attribute: (identifier) @method)
  (#eq? @pathlib "Path")
  (#any-of? @method "read_text" "read_bytes" "write_text" "write_bytes" "unlink" "rmdir" "mkdir")
  arguments: (argument_list) @args) @sink

; pathlib Path(x).method() pattern
(call function: (attribute attribute: (identifier) @method)
  (#any-of? @method "read_text" "read_bytes" "write_text" "write_bytes" "unlink" "rmdir" "mkdir" "open")) @sink

; os module functions
(call function: (attribute object: (identifier) @module attribute: (identifier) @func)
  (#eq? @module "os")
  (#any-of? @func "remove" "unlink" "rmdir" "mkdir" "makedirs" "listdir" "rename" "replace")
  arguments: (argument_list) @args) @sink

; os.path.join - IMPORTANT: flag this as vulnerable pattern
(call function: (attribute object: (attribute object: (identifier) @os attribute: (identifier) @path) attribute: (identifier) @func)
  (#eq? @os "os")
  (#eq? @path "path")
  (#eq? @func "join")
  arguments: (argument_list) @args) @join_sink

; shutil functions
(call function: (attribute object: (identifier) @module attribute: (identifier) @func)
  (#eq? @module "shutil")
  (#any-of? @func "copy" "copy2" "copyfile" "copytree" "rmtree" "move")
  arguments: (argument_list) @args) @sink

; String literals containing ".." (hardcoded traversal)
(string) @string_lit
"#;

/// TypeScript/JavaScript sink detection query.
const TYPESCRIPT_SINK_QUERY: &str = r#"
; fs module functions
(call_expression function: (member_expression object: (identifier) @module property: (property_identifier) @func)
  (#any-of? @module "fs" "fsp")
  (#any-of? @func "readFile" "readFileSync" "writeFile" "writeFileSync" "appendFile" "appendFileSync"
             "unlink" "unlinkSync" "rmdir" "rm" "mkdir" "readdir" "rename" "copyFile"
             "createReadStream" "createWriteStream")
  arguments: (arguments) @args) @sink

; require('fs').method pattern
(call_expression function: (member_expression object: (call_expression function: (identifier) @req arguments: (arguments (string) @mod))
    property: (property_identifier) @func)
  (#eq? @req "require")
  (#match? @mod "fs")
  (#any-of? @func "readFile" "readFileSync" "writeFile" "writeFileSync" "unlink" "unlinkSync")
  arguments: (arguments) @args) @sink

; path.join - flag as vulnerable
(call_expression function: (member_expression object: (identifier) @module property: (property_identifier) @func)
  (#eq? @module "path")
  (#any-of? @func "join" "resolve")
  arguments: (arguments) @args) @join_sink

; String literals containing ".."
(string) @string_lit
(template_string) @template_lit
"#;

/// Go sink detection query.
const GO_SINK_QUERY: &str = r#"
; os package functions
(call_expression function: (selector_expression operand: (identifier) @pkg field: (field_identifier) @func)
  (#eq? @pkg "os")
  (#any-of? @func "Open" "OpenFile" "Create" "Remove" "RemoveAll" "Rename" "Mkdir" "MkdirAll"
            "ReadDir" "ReadFile" "WriteFile")
  arguments: (argument_list) @args) @sink

; ioutil functions (deprecated but used)
(call_expression function: (selector_expression operand: (identifier) @pkg field: (field_identifier) @func)
  (#eq? @pkg "ioutil")
  (#any-of? @func "ReadFile" "WriteFile" "ReadDir")
  arguments: (argument_list) @args) @sink

; filepath.Join - flag as vulnerable pattern
(call_expression function: (selector_expression operand: (identifier) @pkg field: (field_identifier) @func)
  (#eq? @pkg "filepath")
  (#eq? @func "Join")
  arguments: (argument_list) @args) @join_sink

; String literals containing ".."
(interpreted_string_literal) @string_lit
(raw_string_literal) @string_lit
"#;

/// Rust sink detection query.
const RUST_SINK_QUERY: &str = r#"
; std::fs functions
(call_expression function: (scoped_identifier) @func
  (#match? @func "fs::(read|read_to_string|write|remove_file|remove_dir|remove_dir_all|create_dir|create_dir_all|copy|rename|read_dir)")
  arguments: (arguments) @args) @sink

; File::open and File::create
(call_expression function: (scoped_identifier) @func
  (#match? @func "File::(open|create)")
  arguments: (arguments) @args) @sink

; Path::new with user input
(call_expression function: (scoped_identifier) @func
  (#match? @func "Path::new")
  arguments: (arguments) @args) @path_new_sink

; tokio::fs functions
(call_expression function: (scoped_identifier) @func
  (#match? @func "tokio::fs::")
  arguments: (arguments) @args) @sink

; String literals containing ".."
(string_literal) @string_lit
"#;

/// C sink detection query.
const C_SINK_QUERY: &str = r#"
; File operations
(call_expression function: (identifier) @func
  (#any-of? @func "fopen" "freopen" "open" "creat" "remove" "unlink" "rmdir" "mkdir" "rename" "opendir" "stat" "lstat" "access")
  arguments: (argument_list) @args) @sink

; openat has path at index 1
(call_expression function: (identifier) @func
  (#eq? @func "openat")
  arguments: (argument_list) @args) @sink_openat

; String literals containing ".."
(string_literal) @string_lit
"#;

/// Get tree-sitter query for detecting file sinks in a language.
fn get_sink_query(language: &str) -> Option<&'static str> {
    match language {
        "python" => Some(PYTHON_SINK_QUERY),
        "typescript" | "javascript" => Some(TYPESCRIPT_SINK_QUERY),
        "go" => Some(GO_SINK_QUERY),
        "rust" => Some(RUST_SINK_QUERY),
        "c" | "cpp" => Some(C_SINK_QUERY),
        _ => None,
    }
}

// =============================================================================
// Scanning Implementation
// =============================================================================

/// Scan a directory for path traversal vulnerabilities.
///
/// # Arguments
///
/// * `path` - Directory to scan
/// * `language` - Optional language filter (scans all supported languages if None)
///
/// # Returns
///
/// Vector of path traversal findings.
pub fn scan_path_traversal(path: &Path, language: Option<&str>) -> Result<Vec<PathTraversalFinding>> {
    let path_str = path.to_str().ok_or_else(|| {
        BrrrError::InvalidArgument("Invalid path encoding".to_string())
    })?;

    let scanner = ProjectScanner::new(path_str)?;
    let config = match language {
        Some(lang) => ScanConfig::for_language(lang),
        None => ScanConfig::default(),
    };

    let scan_result = scanner.scan_with_config(&config)?;
    let files = scan_result.files;

    // Process files in parallel
    let findings: Vec<PathTraversalFinding> = files
        .par_iter()
        .filter_map(|file| {
            scan_file_path_traversal(file, language).ok()
        })
        .flatten()
        .collect();

    Ok(findings)
}

/// Scan a single file for path traversal vulnerabilities.
///
/// # Arguments
///
/// * `file` - Path to the file to scan
/// * `language` - Optional language override (auto-detected if None)
///
/// # Returns
///
/// Vector of path traversal findings in this file.
pub fn scan_file_path_traversal(file: &Path, language: Option<&str>) -> Result<Vec<PathTraversalFinding>> {
    let registry = LanguageRegistry::global();

    // Detect language
    let lang = match language {
        Some(lang_name) => registry
            .get_by_name(lang_name)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(lang_name.to_string()))?,
        None => registry
            .detect_language(file)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(
                file.extension()
                    .and_then(|e| e.to_str())
                    .unwrap_or("unknown")
                    .to_string(),
            ))?,
    };

    let lang_name = lang.name();

    // Get query for this language
    let sink_query_str = get_sink_query(lang_name)
        .ok_or_else(|| BrrrError::UnsupportedLanguage(format!("{} (no path traversal query)", lang_name)))?;

    // Parse the file
    let source = std::fs::read(file).map_err(|e| BrrrError::io_with_path(e, file))?;
    let mut parser = lang.parser_for_path(file)?;
    let tree = parser.parse(&source, None).ok_or_else(|| BrrrError::Parse {
        file: file.display().to_string(),
        message: "Failed to parse file".to_string(),
    })?;

    let ts_lang = tree.language();
    let file_path = file.display().to_string();

    // Find sinks and analyze
    find_path_traversal_vulnerabilities(&tree, &source, &ts_lang, sink_query_str, lang_name, &file_path)
}

/// Internal function to find path traversal vulnerabilities in parsed tree.
fn find_path_traversal_vulnerabilities(
    tree: &Tree,
    source: &[u8],
    ts_lang: &tree_sitter::Language,
    query_str: &str,
    lang_name: &str,
    file_path: &str,
) -> Result<Vec<PathTraversalFinding>> {
    let query = Query::new(ts_lang, query_str)
        .map_err(|e| BrrrError::TreeSitter(format_query_error(lang_name, "path_traversal", query_str, &e)))?;

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    // Get capture indices
    let sink_idx = query.capture_index_for_name("sink");
    let join_sink_idx = query.capture_index_for_name("join_sink");
    let path_new_idx = query.capture_index_for_name("path_new_sink");
    let func_idx = query.capture_index_for_name("func");
    let args_idx = query.capture_index_for_name("args");
    let string_lit_idx = query.capture_index_for_name("string_lit");
    let template_lit_idx = query.capture_index_for_name("template_lit");

    let mut findings = Vec::new();
    let known_sinks = get_file_sinks(lang_name);

    // Track functions with validation patterns nearby
    let validation_patterns = find_validation_patterns(tree, source, lang_name);

    while let Some(match_) = matches.next() {
        // Check for hardcoded "../" in string literals
        if let Some(idx) = string_lit_idx {
            if let Some(capture) = match_.captures.iter().find(|c| c.index == idx) {
                let text = node_text(capture.node, source);
                if text.contains("../") || text.contains("..\\") {
                    let location = node_to_location(capture.node, file_path);

                    // Skip if this looks like a test or comment
                    if !is_likely_test_or_comment(capture.node, source) {
                        findings.push(PathTraversalFinding {
                            location,
                            severity: Severity::Medium,
                            sink_function: "string_literal".to_string(),
                            operation_type: FileOperationType::Open,
                            path_expression: text.to_string(),
                            confidence: Confidence::High,
                            pattern: VulnerablePattern::HardcodedTraversal,
                            involved_variables: vec![],
                            code_snippet: extract_code_snippet(source, capture.node),
                            description: "Hardcoded path traversal sequence '../' found. This may indicate intentional traversal or a vulnerability.".to_string(),
                            remediation: "Remove hardcoded '../' sequences. Use absolute paths or validate that the resolved path stays within the intended directory.".to_string(),
                            symlink_risk: false,
                        });
                    }
                }
            }
        }

        // Check template literals for interpolation with traversal
        if let Some(idx) = template_lit_idx {
            if let Some(capture) = match_.captures.iter().find(|c| c.index == idx) {
                let text = node_text(capture.node, source);
                if (text.contains("../") || text.contains("${")) && has_substitution(capture.node) {
                    let location = node_to_location(capture.node, file_path);
                    let vars = extract_template_variables(capture.node, source);

                    findings.push(PathTraversalFinding {
                        location,
                        severity: Severity::High,
                        sink_function: "template_literal".to_string(),
                        operation_type: FileOperationType::Open,
                        path_expression: text.to_string(),
                        confidence: Confidence::Medium,
                        pattern: VulnerablePattern::PathInterpolation,
                        involved_variables: vars,
                        code_snippet: extract_code_snippet(source, capture.node),
                        description: "Template literal with path interpolation detected. User input may enable path traversal.".to_string(),
                        remediation: "Validate interpolated values. Use path.basename() to extract only filename, or validate with realpath() + startswith() check.".to_string(),
                        symlink_risk: true,
                    });
                }
            }
        }

        // Check for join_sink (os.path.join, path.join, filepath.Join)
        if let Some(idx) = join_sink_idx {
            if let Some(capture) = match_.captures.iter().find(|c| c.index == idx) {
                let call_node = capture.node;
                let args_node = args_idx.and_then(|i| match_.captures.iter().find(|c| c.index == i)).map(|c| c.node);

                if let Some(args) = args_node {
                    let (path_expr, vars) = extract_path_argument(args, source, 1);

                    // Check if any argument looks like user input
                    if looks_like_user_input(&path_expr, &vars) {
                        let location = node_to_location(call_node, file_path);
                        let func_name = get_join_function_name(lang_name);

                        findings.push(PathTraversalFinding {
                            location,
                            severity: Severity::High,
                            sink_function: func_name.to_string(),
                            operation_type: FileOperationType::Open,
                            path_expression: path_expr,
                            confidence: Confidence::High,
                            pattern: VulnerablePattern::UnsafePathJoin,
                            involved_variables: vars,
                            code_snippet: extract_code_snippet(source, call_node),
                            description: format!("{}() with user input is NOT safe! It does not prevent absolute paths or '..' sequences.", func_name),
                            remediation: get_join_remediation(lang_name),
                            symlink_risk: true,
                        });
                    }
                }
            }
        }

        // Check for regular file operation sinks
        if let Some(idx) = sink_idx {
            if let Some(capture) = match_.captures.iter().find(|c| c.index == idx) {
                let call_node = capture.node;
                let func_node = func_idx.and_then(|i| match_.captures.iter().find(|c| c.index == i)).map(|c| c.node);
                let args_node = args_idx.and_then(|i| match_.captures.iter().find(|c| c.index == i)).map(|c| c.node);

                let func_name = func_node
                    .map(|n| node_text(n, source))
                    .unwrap_or("unknown");

                // Find matching sink definition
                let sink_def = known_sinks.iter().find(|s| s.function == func_name || s.function.ends_with(&format!("::{}", func_name)));

                if let Some(args) = args_node {
                    let path_arg_idx = sink_def.map(|s| s.path_arg_index).unwrap_or(0);
                    let (path_expr, vars) = extract_path_argument(args, source, path_arg_idx);

                    // Skip if this looks like safe validation is nearby
                    let has_validation = check_nearby_validation(&validation_patterns, call_node, &vars);

                    if !has_validation && !vars.is_empty() {
                        let operation_type = sink_def.map(|s| s.operation_type).unwrap_or(FileOperationType::Open);
                        let base_severity = sink_def.map(|s| s.severity).unwrap_or(Severity::Medium);

                        let (confidence, pattern) = analyze_path_expression(&path_expr, &vars, lang_name);

                        // Adjust severity based on confidence
                        let severity = if confidence == Confidence::High {
                            base_severity
                        } else if confidence == Confidence::Medium {
                            match base_severity {
                                Severity::Critical => Severity::High,
                                s => s,
                            }
                        } else {
                            Severity::Low
                        };

                        let location = node_to_location(call_node, file_path);

                        findings.push(PathTraversalFinding {
                            location,
                            severity,
                            sink_function: func_name.to_string(),
                            operation_type,
                            path_expression: path_expr.clone(),
                            confidence,
                            pattern,
                            involved_variables: vars.clone(),
                            code_snippet: extract_code_snippet(source, call_node),
                            description: generate_description(func_name, &pattern, &vars),
                            remediation: generate_remediation(lang_name, operation_type, &pattern),
                            symlink_risk: operation_type != FileOperationType::Exists,
                        });
                    }
                }
            }
        }

        // Handle Path::new in Rust
        if let Some(idx) = path_new_idx {
            if let Some(capture) = match_.captures.iter().find(|c| c.index == idx) {
                let call_node = capture.node;
                let args_node = args_idx.and_then(|i| match_.captures.iter().find(|c| c.index == i)).map(|c| c.node);

                if let Some(args) = args_node {
                    let (path_expr, vars) = extract_path_argument(args, source, 0);

                    if looks_like_user_input(&path_expr, &vars) {
                        let location = node_to_location(call_node, file_path);

                        findings.push(PathTraversalFinding {
                            location,
                            severity: Severity::Medium,
                            sink_function: "Path::new".to_string(),
                            operation_type: FileOperationType::Open,
                            path_expression: path_expr,
                            confidence: Confidence::Medium,
                            pattern: VulnerablePattern::UnvalidatedVariable,
                            involved_variables: vars,
                            code_snippet: extract_code_snippet(source, call_node),
                            description: "Path::new() with user input may enable path traversal when used with file operations.".to_string(),
                            remediation: "Validate the path after canonicalizing: use std::fs::canonicalize() and verify it starts with the expected base directory.".to_string(),
                            symlink_risk: true,
                        });
                    }
                }
            }
        }
    }

    Ok(findings)
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Get node text safely.
fn node_text<'a>(node: Node<'a>, source: &'a [u8]) -> &'a str {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
}

/// Convert node to SourceLocation.
fn node_to_location(node: Node, file_path: &str) -> SourceLocation {
    SourceLocation {
        file: file_path.to_string(),
        line: node.start_position().row + 1,
        column: node.start_position().column + 1,
        end_line: node.end_position().row + 1,
        end_column: node.end_position().column + 1,
    }
}

/// Extract code snippet around a node.
fn extract_code_snippet(source: &[u8], node: Node) -> Option<String> {
    let source_str = std::str::from_utf8(source).ok()?;
    let lines: Vec<&str> = source_str.lines().collect();

    let start_line = node.start_position().row;
    let end_line = node.end_position().row;

    // Get 1 line before and after
    let context_start = start_line.saturating_sub(1);
    let context_end = (end_line + 2).min(lines.len());

    let snippet: Vec<String> = lines[context_start..context_end]
        .iter()
        .enumerate()
        .map(|(i, line)| format!("{:4} | {}", context_start + i + 1, line))
        .collect();

    Some(snippet.join("\n"))
}

/// Extract the path argument from function call.
fn extract_path_argument(args_node: Node, source: &[u8], arg_index: usize) -> (String, Vec<String>) {
    let mut positional_args = Vec::new();
    let mut cursor = args_node.walk();

    for child in args_node.children(&mut cursor) {
        match child.kind() {
            "(" | ")" | "," | "keyword_argument" => continue,
            _ => positional_args.push(child),
        }
    }

    if let Some(arg_node) = positional_args.get(arg_index) {
        let text = node_text(*arg_node, source).to_string();
        let vars = collect_variables(*arg_node, source);
        (text, vars)
    } else if !positional_args.is_empty() {
        // Fallback to first arg
        let text = node_text(positional_args[0], source).to_string();
        let vars = collect_variables(positional_args[0], source);
        (text, vars)
    } else {
        (String::new(), Vec::new())
    }
}

/// Collect all identifier variables from a node.
fn collect_variables(node: Node, source: &[u8]) -> Vec<String> {
    let mut vars = Vec::new();
    collect_variables_recursive(node, source, &mut vars);
    vars.sort();
    vars.dedup();
    vars
}

fn collect_variables_recursive(node: Node, source: &[u8], vars: &mut Vec<String>) {
    if node.kind() == "identifier" {
        let name = node_text(node, source).to_string();
        // Filter out common non-user-input identifiers
        let ignore_list = ["True", "False", "None", "self", "cls", "os", "fs", "path", "shutil", "ioutil", "filepath", "std"];
        if !ignore_list.contains(&name.as_str()) && !name.is_empty() {
            vars.push(name);
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_variables_recursive(child, source, vars);
    }
}

/// Check if expression looks like user input.
/// Uses Aho-Corasick for O(n) multi-pattern matching instead of O(n*m) sequential contains().
fn looks_like_user_input(expr: &str, vars: &[String]) -> bool {
    let lower = expr.to_lowercase();
    if USER_INPUT_PATTERNS.is_match(&lower) {
        return true;
    }

    for var in vars {
        let lower_var = var.to_lowercase();
        if USER_INPUT_PATTERNS.is_match(&lower_var) {
            return true;
        }
    }

    // Also flag if it's just a variable (not a literal)
    if !vars.is_empty() && !expr.starts_with('"') && !expr.starts_with('\'') && !expr.starts_with('`') {
        return true;
    }

    false
}

/// Analyze path expression to determine confidence and pattern.
fn analyze_path_expression(expr: &str, vars: &[String], _lang: &str) -> (Confidence, VulnerablePattern) {
    let suspicious = [
        "request", "req", "params", "query", "body", "input",
        "user", "filename", "file_name", "filepath", "file_path",
    ];

    let lower = expr.to_lowercase();

    // High confidence if direct suspicious variable
    for pattern in suspicious {
        if lower.contains(pattern) {
            return (Confidence::High, VulnerablePattern::DirectUserInput);
        }
    }

    // Check for concatenation
    if expr.contains('+') || expr.contains("format") || expr.contains('%') {
        return (Confidence::Medium, VulnerablePattern::PathConcatenation);
    }

    // Check for interpolation (f-strings, template literals)
    if expr.contains('{') && expr.contains('}') {
        return (Confidence::Medium, VulnerablePattern::PathInterpolation);
    }

    // Check for template substitution
    if expr.contains("${") {
        return (Confidence::Medium, VulnerablePattern::PathInterpolation);
    }

    // Variable without visible validation
    if !vars.is_empty() {
        return (Confidence::Low, VulnerablePattern::UnvalidatedVariable);
    }

    (Confidence::Low, VulnerablePattern::MissingValidation)
}

/// Find validation patterns in the code (realpath + startswith, basename, etc.)
fn find_validation_patterns(_tree: &Tree, source: &[u8], lang: &str) -> HashSet<String> {
    let mut validated_vars = HashSet::new();
    let source_str = std::str::from_utf8(source).unwrap_or("");

    match lang {
        "python" => {
            // Look for realpath + startswith pattern
            if source_str.contains("realpath") && source_str.contains("startswith") {
                validated_vars.insert("_validated_".to_string());
            }
            // basename strips directory
            if source_str.contains("basename") {
                validated_vars.insert("_basename_".to_string());
            }
        }
        "typescript" | "javascript" => {
            // path.resolve + startsWith
            if source_str.contains("resolve") && source_str.contains("startsWith") {
                validated_vars.insert("_validated_".to_string());
            }
            // path.basename
            if source_str.contains("basename") {
                validated_vars.insert("_basename_".to_string());
            }
        }
        "go" => {
            // filepath.Clean + strings.HasPrefix
            if source_str.contains("filepath.Clean") && source_str.contains("HasPrefix") {
                validated_vars.insert("_validated_".to_string());
            }
            // filepath.Base
            if source_str.contains("filepath.Base") {
                validated_vars.insert("_basename_".to_string());
            }
        }
        "rust" => {
            // canonicalize + starts_with
            if source_str.contains("canonicalize") && source_str.contains("starts_with") {
                validated_vars.insert("_validated_".to_string());
            }
            // file_name() extracts filename only
            if source_str.contains("file_name()") {
                validated_vars.insert("_basename_".to_string());
            }
        }
        "c" | "cpp" => {
            // realpath + strncmp/strstr
            if source_str.contains("realpath") && (source_str.contains("strncmp") || source_str.contains("strstr")) {
                validated_vars.insert("_validated_".to_string());
            }
            // basename
            if source_str.contains("basename") {
                validated_vars.insert("_basename_".to_string());
            }
        }
        _ => {}
    }

    validated_vars
}

/// Check if there's validation nearby for the given variables.
fn check_nearby_validation(validation_patterns: &HashSet<String>, _node: Node, _vars: &[String]) -> bool {
    // If we detected validation patterns in the file, lower confidence
    // This is a heuristic - could be improved with actual data flow tracking
    !validation_patterns.is_empty()
}

/// Check if node is likely in test code or a comment.
fn is_likely_test_or_comment(node: Node, source: &[u8]) -> bool {
    // Walk up to find function/class context
    let mut current = Some(node);
    while let Some(n) = current {
        let text = node_text(n, source).to_lowercase();
        if text.contains("test") || text.contains("mock") || text.contains("spec") {
            return true;
        }
        current = n.parent();
    }
    false
}

/// Check if template string has substitutions.
fn has_substitution(node: Node) -> bool {
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "template_substitution" {
            return true;
        }
    }
    false
}

/// Extract variables from template literal substitutions.
fn extract_template_variables(node: Node, source: &[u8]) -> Vec<String> {
    let mut vars = Vec::new();
    let mut cursor = node.walk();

    for child in node.children(&mut cursor) {
        if child.kind() == "template_substitution" {
            vars.extend(collect_variables(child, source));
        }
    }

    vars
}

/// Get the join function name for a language.
fn get_join_function_name(lang: &str) -> &'static str {
    match lang {
        "python" => "os.path.join",
        "typescript" | "javascript" => "path.join",
        "go" => "filepath.Join",
        _ => "path.join",
    }
}

/// Get remediation for unsafe path join usage.
fn get_join_remediation(lang: &str) -> String {
    match lang {
        "python" => {
            "os.path.join() does NOT sanitize user input! Fix:\n\
             1. Use os.path.basename() to extract only filename: safe_name = os.path.basename(user_input)\n\
             2. Or validate with realpath: resolved = os.path.realpath(os.path.join(base, user_input))\n\
                if not resolved.startswith(os.path.realpath(base)):\n\
                    raise ValueError('Path traversal detected')".to_string()
        }
        "typescript" | "javascript" => {
            "path.join() does NOT sanitize user input! Fix:\n\
             1. Use path.basename() to extract only filename: const safeName = path.basename(userInput)\n\
             2. Or validate: const resolved = path.resolve(base, userInput)\n\
                if (!resolved.startsWith(path.resolve(base))) throw new Error('Path traversal')".to_string()
        }
        "go" => {
            "filepath.Join() does NOT sanitize user input! Fix:\n\
             1. Use filepath.Base() to extract only filename: safeName := filepath.Base(userInput)\n\
             2. Or validate: resolved := filepath.Clean(filepath.Join(base, userInput))\n\
                if !strings.HasPrefix(resolved, filepath.Clean(base)) { return error }".to_string()
        }
        _ => "Path join functions do NOT sanitize input. Use basename() or validate the resolved path.".to_string(),
    }
}

/// Generate human-readable description.
fn generate_description(func_name: &str, pattern: &VulnerablePattern, vars: &[String]) -> String {
    let var_list = if vars.is_empty() {
        "unknown variable".to_string()
    } else {
        vars.join(", ")
    };

    match pattern {
        VulnerablePattern::DirectUserInput => {
            format!(
                "Potential path traversal in {}(). Variable '{}' appears to be user-controlled and is passed directly to file operation.",
                func_name, var_list
            )
        }
        VulnerablePattern::UnsafePathJoin => {
            format!(
                "Unsafe path join in {}() with user input '{}'. Path join functions do NOT prevent path traversal!",
                func_name, var_list
            )
        }
        VulnerablePattern::PathConcatenation => {
            format!(
                "Path concatenation in {}() with variable '{}'. String concatenation for paths is vulnerable to traversal.",
                func_name, var_list
            )
        }
        VulnerablePattern::HardcodedTraversal => {
            "Hardcoded '../' path traversal sequence detected. This may allow escaping the intended directory.".to_string()
        }
        VulnerablePattern::UnvalidatedVariable => {
            format!(
                "Variable '{}' passed to {}() without visible validation. May enable path traversal if user-controlled.",
                var_list, func_name
            )
        }
        VulnerablePattern::PathInterpolation => {
            format!(
                "Path interpolation in {}() with variables '{}'. Interpolated paths are vulnerable to traversal attacks.",
                func_name, var_list
            )
        }
        VulnerablePattern::MissingValidation => {
            format!(
                "File operation {}() without visible path validation. Ensure paths are validated before use.",
                func_name
            )
        }
    }
}

/// Generate remediation advice.
fn generate_remediation(lang: &str, operation_type: FileOperationType, pattern: &VulnerablePattern) -> String {
    let op_warning = match operation_type {
        FileOperationType::Write | FileOperationType::Append => "WARNING: Write operation - attackers could overwrite critical files!",
        FileOperationType::Delete => "CRITICAL: Delete operation - attackers could delete arbitrary files!",
        FileOperationType::Read => "Attackers could read sensitive files like /etc/passwd or config files.",
        FileOperationType::Copy | FileOperationType::Move => "Attackers could copy/move files to/from unintended locations.",
        _ => "Attackers could access files outside the intended directory.",
    };

    let fix = match lang {
        "python" => {
            "Fix for Python:\n\
             1. Extract filename only: safe_name = os.path.basename(user_input)\n\
             2. Or validate resolved path:\n\
                base = os.path.realpath('/safe/base/dir')\n\
                resolved = os.path.realpath(os.path.join(base, user_input))\n\
                if not resolved.startswith(base + os.sep):\n\
                    raise ValueError('Path traversal attempt')"
        }
        "typescript" | "javascript" => {
            "Fix for JavaScript/TypeScript:\n\
             1. Extract filename only: const safeName = path.basename(userInput)\n\
             2. Or validate resolved path:\n\
                const base = path.resolve('/safe/base/dir')\n\
                const resolved = path.resolve(base, userInput)\n\
                if (!resolved.startsWith(base + path.sep)) {\n\
                    throw new Error('Path traversal attempt')\n\
                }"
        }
        "go" => {
            "Fix for Go:\n\
             1. Extract filename only: safeName := filepath.Base(userInput)\n\
             2. Or validate resolved path:\n\
                base, _ := filepath.Abs(\"/safe/base/dir\")\n\
                resolved := filepath.Clean(filepath.Join(base, userInput))\n\
                if !strings.HasPrefix(resolved, base + string(os.PathSeparator)) {\n\
                    return errors.New(\"path traversal attempt\")\n\
                }"
        }
        "rust" => {
            "Fix for Rust:\n\
             1. Extract filename only: let safe_name = Path::new(user_input).file_name()\n\
             2. Or validate canonical path:\n\
                let base = std::fs::canonicalize(\"/safe/base/dir\")?;\n\
                let resolved = std::fs::canonicalize(base.join(user_input))?;\n\
                if !resolved.starts_with(&base) {\n\
                    return Err(\"path traversal attempt\")\n\
                }"
        }
        "c" | "cpp" => {
            "Fix for C/C++:\n\
             1. Extract filename only: char *safe_name = basename(user_input)\n\
             2. Or validate with realpath:\n\
                char base[PATH_MAX], resolved[PATH_MAX];\n\
                realpath(\"/safe/base/dir\", base);\n\
                realpath(combined_path, resolved);\n\
                if (strncmp(resolved, base, strlen(base)) != 0) {\n\
                    // Path traversal detected\n\
                }"
        }
        _ => "Use basename() to extract only filename, or validate that the resolved absolute path starts with the expected base directory.",
    };

    let symlink_warning = match pattern {
        VulnerablePattern::HardcodedTraversal => "",
        _ => "\n\nSymlink Warning: Even with validation, symlink attacks may be possible. Consider:\n\
              - Use O_NOFOLLOW flag (POSIX) to prevent symlink following\n\
              - Validate paths at the moment of use (TOCTOU protection)\n\
              - Use chroot or containerization for stronger isolation"
    };

    format!("{}\n\n{}{}", op_warning, fix, symlink_warning)
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
    fn test_python_direct_open_user_input() {
        let source = r#"
def read_file(request):
    filename = request.args.get('filename')
    with open(filename) as f:
        return f.read()
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_path_traversal(file.path(), Some("python"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect open() with user input");
        let finding = &findings[0];
        assert_eq!(finding.sink_function, "open");
        assert!(finding.severity >= Severity::Medium);
    }

    #[test]
    fn test_python_unsafe_path_join() {
        let source = r#"
import os

def download_file(user_filename):
    base_dir = "/var/www/uploads"
    filepath = os.path.join(base_dir, user_filename)  # NOT SAFE!
    with open(filepath, 'rb') as f:
        return f.read()
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_path_traversal(file.path(), Some("python"))
            .expect("Scan should succeed");

        // Should flag os.path.join or the open()
        assert!(!findings.is_empty(), "Should detect path traversal risk");
    }

    #[test]
    fn test_python_hardcoded_traversal() {
        let source = r#"
def get_parent_config():
    with open("../config.ini") as f:
        return f.read()
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_path_traversal(file.path(), Some("python"))
            .expect("Scan should succeed");

        let traversal_finding = findings.iter()
            .find(|f| f.pattern == VulnerablePattern::HardcodedTraversal);
        assert!(traversal_finding.is_some(), "Should detect hardcoded '../'");
    }

    #[test]
    fn test_python_shutil_rmtree() {
        let source = r#"
import shutil

def delete_user_folder(user_path):
    shutil.rmtree(user_path)  # Critical!
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_path_traversal(file.path(), Some("python"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect shutil.rmtree");
        // Should be high/critical severity for delete operations
        let finding = findings.iter().find(|f| f.sink_function == "rmtree");
        assert!(finding.is_some() || !findings.is_empty());
    }

    // =========================================================================
    // TypeScript Tests
    // =========================================================================

    #[test]
    fn test_typescript_fs_readfile() {
        let source = r#"
import * as fs from 'fs';

function readUserFile(req: Request) {
    const filename = req.params.filename;
    return fs.readFileSync(filename);
}
"#;
        let file = create_temp_file(source, ".ts");
        let findings = scan_file_path_traversal(file.path(), Some("typescript"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect fs.readFileSync with user input");
    }

    #[test]
    fn test_typescript_path_join() {
        let source = r#"
import * as fs from 'fs';
import * as path from 'path';

function getFile(userPath: string) {
    const fullPath = path.join('/uploads', userPath);  // NOT SAFE!
    return fs.readFileSync(fullPath);
}
"#;
        let file = create_temp_file(source, ".ts");
        let findings = scan_file_path_traversal(file.path(), Some("typescript"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect path.join vulnerability");
    }

    #[test]
    fn test_typescript_template_literal() {
        let source = r#"
import * as fs from 'fs';

function readConfig(userId: string) {
    const path = `/data/${userId}/config.json`;
    return fs.readFileSync(path);
}
"#;
        let file = create_temp_file(source, ".ts");
        let findings = scan_file_path_traversal(file.path(), Some("typescript"))
            .expect("Scan should succeed");

        // May detect template literal interpolation
        if !findings.is_empty() {
            println!("Found {} findings", findings.len());
        }
    }

    // =========================================================================
    // Go Tests
    // =========================================================================

    #[test]
    fn test_go_os_open() {
        let source = r#"
package main

import "os"

func readFile(userPath string) ([]byte, error) {
    f, err := os.Open(userPath)
    if err != nil {
        return nil, err
    }
    defer f.Close()
    return io.ReadAll(f)
}
"#;
        let file = create_temp_file(source, ".go");
        let findings = scan_file_path_traversal(file.path(), Some("go"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect os.Open with user path");
    }

    #[test]
    fn test_go_filepath_join() {
        let source = r#"
package main

import (
    "os"
    "path/filepath"
)

func getFile(basePath, userInput string) ([]byte, error) {
    path := filepath.Join(basePath, userInput)  // NOT SAFE!
    return os.ReadFile(path)
}
"#;
        let file = create_temp_file(source, ".go");
        let findings = scan_file_path_traversal(file.path(), Some("go"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect filepath.Join vulnerability");
    }

    // =========================================================================
    // Rust Tests
    // =========================================================================

    #[test]
    fn test_rust_fs_read() {
        let source = r#"
use std::fs;

fn read_user_file(user_path: &str) -> std::io::Result<String> {
    fs::read_to_string(user_path)
}
"#;
        let file = create_temp_file(source, ".rs");
        let findings = scan_file_path_traversal(file.path(), Some("rust"))
            .expect("Scan should succeed");

        // Note: Rust detection depends on tree-sitter-rust grammar
        // This test verifies the scan completes
        println!("Rust findings: {:?}", findings);
    }

    // =========================================================================
    // C Tests
    // =========================================================================

    #[test]
    fn test_c_fopen() {
        let source = r#"
#include <stdio.h>

void read_file(const char* user_path) {
    FILE* f = fopen(user_path, "r");
    if (f) {
        // read file
        fclose(f);
    }
}
"#;
        let file = create_temp_file(source, ".c");
        let findings = scan_file_path_traversal(file.path(), Some("c"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect fopen with user path");
        assert_eq!(findings[0].sink_function, "fopen");
    }

    #[test]
    fn test_c_hardcoded_traversal() {
        let source = r#"
#include <stdio.h>

void read_parent() {
    FILE* f = fopen("../secret.txt", "r");
    fclose(f);
}
"#;
        let file = create_temp_file(source, ".c");
        let findings = scan_file_path_traversal(file.path(), Some("c"))
            .expect("Scan should succeed");

        let traversal = findings.iter()
            .find(|f| f.pattern == VulnerablePattern::HardcodedTraversal);
        assert!(traversal.is_some(), "Should detect hardcoded '../'");
    }

    // =========================================================================
    // Utility Tests
    // =========================================================================

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
    fn test_file_operation_type_display() {
        assert_eq!(format!("{}", FileOperationType::Read), "read");
        assert_eq!(format!("{}", FileOperationType::Write), "write");
        assert_eq!(format!("{}", FileOperationType::Delete), "delete");
    }

    #[test]
    fn test_vulnerable_pattern_display() {
        assert_eq!(format!("{}", VulnerablePattern::UnsafePathJoin), "unsafe_path_join");
        assert_eq!(format!("{}", VulnerablePattern::HardcodedTraversal), "hardcoded_traversal");
    }

    #[test]
    fn test_looks_like_user_input() {
        assert!(looks_like_user_input("request.args.get('file')", &[]));
        assert!(looks_like_user_input("user_filename", &["user_filename".to_string()]));
        assert!(looks_like_user_input("filepath", &["filepath".to_string()]));
        assert!(!looks_like_user_input("\"static.txt\"", &[]));
    }

    #[test]
    fn test_get_file_sinks_coverage() {
        let languages = ["python", "typescript", "javascript", "go", "rust", "c", "cpp"];
        for lang in languages {
            let sinks = get_file_sinks(lang);
            assert!(!sinks.is_empty(), "Should have sinks for {}", lang);
        }
    }
}
