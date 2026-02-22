//! Error types for the F* LSP server and linter.

use std::path::PathBuf;

use thiserror::Error;

// ---------------------------------------------------------------------------
// Exit codes
// ---------------------------------------------------------------------------

/// Process exit codes for brrr-lint CLI.
///
/// These follow a Unix-style convention where 0 is success and higher
/// values indicate increasingly severe problems.
pub mod exit_code {
    /// No issues found (clean).
    pub const CLEAN: i32 = 0;
    /// Lint issues were found.
    pub const LINT_ISSUES: i32 = 1;
    /// Configuration error (bad config file, invalid CLI args).
    pub const CONFIG_ERROR: i32 = 2;
    /// I/O error (file not found, permission denied, etc.).
    pub const IO_ERROR: i32 = 3;
    /// Internal error (bug in brrr-lint itself).
    pub const INTERNAL_ERROR: i32 = 4;
}

// ---------------------------------------------------------------------------
// LSP / server errors
// ---------------------------------------------------------------------------

/// Main error type for the F* LSP server.
#[derive(Error, Debug)]
pub enum FstarError {
    #[error("F* process error: {0}")]
    Process(String),

    #[error("F* process not found: {0}")]
    FstarNotFound(String),

    #[error("Protocol error: {0}")]
    Protocol(String),

    #[error("Configuration error: {0}")]
    Config(String),

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("Query timeout after {0}ms")]
    Timeout(u64),

    #[error("Query cancelled")]
    Cancelled,

    #[error("Connection closed")]
    ConnectionClosed,

    #[error("Invalid position: line {line}, column {column}")]
    InvalidPosition { line: u32, column: u32 },
}

pub type Result<T> = std::result::Result<T, FstarError>;

// ---------------------------------------------------------------------------
// Lint errors
// ---------------------------------------------------------------------------

/// Errors that can occur during linting.
#[derive(Error, Debug)]
pub enum LintError {
    #[error("I/O error reading {path}: {source}")]
    FileRead {
        path: PathBuf,
        source: std::io::Error,
    },

    #[error("file is not valid UTF-8: {path}")]
    Encoding { path: PathBuf },

    #[error("parse error in {path}: {detail}")]
    Parse { path: PathBuf, detail: String },

    #[error("binary or empty file skipped: {path}")]
    BinaryOrEmpty { path: PathBuf },

    #[error("internal regex compilation failed: {pattern}: {source}")]
    RegexCompile {
        pattern: String,
        source: regex::Error,
    },
}

// ---------------------------------------------------------------------------
// Parse errors
// ---------------------------------------------------------------------------

/// Errors specific to F* file parsing.
#[derive(Error, Debug)]
pub enum ParseError {
    #[error("file not found: {0}")]
    FileNotFound(PathBuf),

    #[error("permission denied: {0}")]
    PermissionDenied(PathBuf),

    #[error("not valid UTF-8: {0}")]
    InvalidEncoding(PathBuf),

    #[error("file appears to be binary: {0}")]
    BinaryFile(PathBuf),

    #[error("empty file: {0}")]
    EmptyFile(PathBuf),

    #[error("file has UTF-8 BOM: {0}")]
    HasBom(PathBuf),

    #[error("malformed F* syntax at line {line}: {detail}")]
    MalformedSyntax { line: usize, detail: String },

    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}
