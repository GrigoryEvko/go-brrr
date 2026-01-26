//! Central error types for go-brrr.
//!
//! Uses `thiserror` for ergonomic error definitions with automatic
//! `Display` and `From` implementations.

use std::path::{Path, PathBuf};

use memchr::memchr;
use thiserror::Error;

/// Main error type for the library.
#[derive(Error, Debug)]
pub enum BrrrError {
    /// IO operation failed (without path context - prefer IoWithPath when path is available)
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// IO operation failed with path context for better error messages
    #[error("IO error at {path}: {error}")]
    IoWithPath {
        error: std::io::Error,
        path: PathBuf,
    },

    /// Failed to parse source file
    #[error("Parse error in {file}: {message}")]
    Parse { file: String, message: String },

    /// Requested language is not supported
    #[error("Language not supported: {0}")]
    UnsupportedLanguage(String),

    /// Function not found in file
    #[error("Function not found: {0}")]
    FunctionNotFound(String),

    /// Class not found in file
    #[error("Class not found: {0}")]
    #[allow(dead_code)]
    ClassNotFound(String),

    /// Tree-sitter parsing/query error
    #[error("Tree-sitter error: {0}")]
    TreeSitter(String),

    /// gRPC communication error
    #[error("gRPC error: {0}")]
    Grpc(#[from] tonic::Status),

    /// JSON serialization/deserialization error
    #[error("Serialization error: {0}")]
    Serde(#[from] serde_json::Error),

    /// Cache operation error
    #[error("Cache error: {0}")]
    Cache(String),

    /// Path traversal attack detected (security)
    #[error("Path traversal detected: {target} escapes base directory {base}")]
    PathTraversal { target: String, base: String },

    /// Invalid argument provided to a function
    #[error("Invalid argument: {0}")]
    InvalidArgument(String),

    /// Configuration error (e.g., invalid ignore patterns)
    #[error("Configuration error: {0}")]
    Config(String),

    /// Analysis error (invariant detection, state machine analysis, etc.)
    #[error("Analysis error: {0}")]
    Analysis(String),

    /// Serialization/deserialization error (non-JSON formats)
    #[error("Serialization error: {0}")]
    Serialization(String),
}

/// Convenience type alias for Results using BrrrError.
pub type Result<T> = std::result::Result<T, BrrrError>;

impl BrrrError {
    /// Create an IO error with path context.
    ///
    /// Use this when reading/writing files to provide actionable error messages
    /// that include the file path that failed.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let source = std::fs::read(path)
    ///     .map_err(|e| BrrrError::io_with_path(e, path))?;
    /// ```
    #[inline]
    pub fn io_with_path(error: std::io::Error, path: impl AsRef<Path>) -> Self {
        BrrrError::IoWithPath {
            error,
            path: path.as_ref().to_path_buf(),
        }
    }
}

/// Validates that a target path is safely contained within a base directory.
///
/// This function prevents path traversal attacks where an attacker could use:
/// - Relative paths with `..` components (e.g., `../../../etc/passwd`)
/// - Symlinks pointing outside the base directory
/// - Encoded path separators or other bypass techniques
///
/// # Arguments
///
/// * `base` - The base directory that must contain the target
/// * `target` - The target path to validate
///
/// # Returns
///
/// * `Ok(canonical_target)` - The canonicalized target path if safely contained
/// * `Err(BrrrError::PathTraversal)` - If the target escapes the base directory
/// * `Err(BrrrError::Io)` - If paths cannot be canonicalized (e.g., don't exist)
///
/// # Security
///
/// Both paths are canonicalized to resolve:
/// - Symlinks (followed to their real targets)
/// - `.` and `..` components
/// - Redundant separators
///
/// The canonical target must start with the canonical base path prefix.
///
/// # Example
///
/// ```no_run
/// use std::path::Path;
/// use brrr::error::validate_path_containment;
///
/// let base = Path::new("/project");
/// let safe = Path::new("/project/src/main.rs");
/// let unsafe_path = Path::new("/project/../etc/passwd");
///
/// assert!(validate_path_containment(base, safe).is_ok());
/// assert!(validate_path_containment(base, unsafe_path).is_err());
/// ```
pub fn validate_path_containment(base: &Path, target: &Path) -> Result<std::path::PathBuf> {
    let canonical_base = base.canonicalize()?;
    let canonical_target = target.canonicalize()?;

    if !canonical_target.starts_with(&canonical_base) {
        return Err(BrrrError::PathTraversal {
            target: target.display().to_string(),
            base: base.display().to_string(),
        });
    }

    Ok(canonical_target)
}

/// Validates a path doesn't escape its base without requiring the target to exist.
///
/// This is useful for validating user-provided paths before attempting to access them.
/// Unlike `validate_path_containment`, this function works with non-existent paths
/// by checking for dangerous patterns in the path components.
///
/// # Arguments
///
/// * `base` - The base directory (must exist for canonicalization)
/// * `target` - The target path to validate (may not exist)
///
/// # Returns
///
/// * `Ok(())` - If the path appears safe
/// * `Err(BrrrError::PathTraversal)` - If dangerous path components are detected
///
/// # Security
///
/// Checks for:
/// - `..` components that could escape the base
/// - Absolute paths that don't start with the base
/// - Null bytes or other dangerous characters
#[allow(dead_code)]
pub fn validate_path_safe(base: &Path, target: &Path) -> Result<()> {
    // Check for null bytes (could bypass string checks)
    // Uses SIMD-accelerated memchr for O(n/16) performance on x86_64/aarch64
    let target_str = target.to_string_lossy();
    if memchr(0, target_str.as_bytes()).is_some() {
        return Err(BrrrError::PathTraversal {
            target: "<contains null byte>".to_string(),
            base: base.display().to_string(),
        });
    }

    // For absolute paths, verify they're under the base
    if target.is_absolute() {
        // Canonicalize base for comparison
        let canonical_base = base.canonicalize()?;

        // If target exists, use canonicalize for accurate check
        if target.exists() {
            return validate_path_containment(base, target).map(|_| ());
        }

        // Target doesn't exist - check path prefix (less secure but best we can do)
        // Normalize the absolute target path by resolving what we can
        if !target.starts_with(&canonical_base) {
            return Err(BrrrError::PathTraversal {
                target: target.display().to_string(),
                base: base.display().to_string(),
            });
        }
    }

    // Check for parent directory traversal attempts
    let mut depth: i32 = 0;
    for component in target.components() {
        match component {
            std::path::Component::ParentDir => {
                depth -= 1;
                if depth < 0 {
                    return Err(BrrrError::PathTraversal {
                        target: target.display().to_string(),
                        base: base.display().to_string(),
                    });
                }
            }
            std::path::Component::Normal(_) => {
                depth += 1;
            }
            _ => {}
        }
    }

    Ok(())
}
