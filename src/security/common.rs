//! Common types for security injection modules.
//!
//! This module provides unified type definitions used across injection
//! detection modules. It re-exports Severity and Confidence from types.rs
//! and defines SourceLocation with injection-module-compatible field names.

use serde::{Deserialize, Serialize};

// Re-export Severity and Confidence from the unified types module
pub use crate::security::types::{Confidence, Severity};

// =============================================================================
// Source Location (injection-module compatible)
// =============================================================================

/// Location in source code for security findings.
///
/// Uses 1-indexed line and column numbers to match editor conventions.
/// This type uses `line`/`column` field names for compatibility with
/// injection detection modules.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SourceLocation {
    /// File path (relative to project root or absolute)
    pub file: String,
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed)
    pub column: usize,
    /// End line number (1-indexed)
    pub end_line: usize,
    /// End column number (1-indexed)
    pub end_column: usize,
    /// Optional code snippet for context
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub snippet: Option<String>,
}

impl Default for SourceLocation {
    fn default() -> Self {
        Self {
            file: String::new(),
            line: 0,
            column: 0,
            end_line: 0,
            end_column: 0,
            snippet: None,
        }
    }
}

impl SourceLocation {
    /// Create a new source location.
    #[must_use]
    pub fn new(
        file: impl Into<String>,
        line: usize,
        column: usize,
        end_line: usize,
        end_column: usize,
    ) -> Self {
        Self {
            file: file.into(),
            line,
            column,
            end_line,
            end_column,
            snippet: None,
        }
    }

    /// Create a single-point location (start equals end).
    #[must_use]
    pub fn point(file: impl Into<String>, line: usize, column: usize) -> Self {
        Self {
            file: file.into(),
            line,
            column,
            end_line: line,
            end_column: column,
            snippet: None,
        }
    }

    /// Add a code snippet to this location.
    #[must_use]
    pub fn with_snippet(mut self, snippet: impl Into<String>) -> Self {
        self.snippet = Some(snippet.into());
        self
    }

    /// Convert to the unified types::Location (with start_line/start_column).
    #[must_use]
    pub fn to_unified(&self) -> crate::security::types::Location {
        crate::security::types::Location::new(
            &self.file,
            self.line,
            self.column,
            self.end_line,
            self.end_column,
        )
    }
}

impl std::fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.column)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_source_location_display() {
        let loc = SourceLocation::new("src/main.rs", 10, 5, 10, 20);
        assert_eq!(loc.to_string(), "src/main.rs:10:5");
    }

    #[test]
    fn test_source_location_point() {
        let loc = SourceLocation::point("test.py", 42, 8);
        assert_eq!(loc.line, 42);
        assert_eq!(loc.end_line, 42);
        assert_eq!(loc.column, 8);
        assert_eq!(loc.end_column, 8);
    }

    #[test]
    fn test_to_unified() {
        let loc = SourceLocation::new("test.rs", 10, 5, 15, 20);
        let unified = loc.to_unified();
        assert_eq!(unified.start_line, 10);
        assert_eq!(unified.start_column, 5);
        assert_eq!(unified.end_line, 15);
        assert_eq!(unified.end_column, 20);
    }
}
