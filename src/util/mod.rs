//! Utility modules for go-brrr.
//!
//! This module provides common utilities used throughout the codebase:
//!
//! - [`path`]: Path manipulation (normalization, relative paths, project root detection)
//! - [`ignore`]: .brrrignore and .gitignore pattern matching
//! - [`query_error`]: Tree-sitter query error formatting with rich context
//! - [`simd`]: SIMD-accelerated byte searching (wraps memchr)
//!
//! Note: Token counting is provided by the `semantic` module via `go_brrr::count_tokens()`.

pub mod ignore;
pub mod path;
pub mod query_error;
pub mod simd;

// Re-export commonly used items for convenience (may be used externally)
#[allow(unused_imports)]
pub use path::{
    detect_language, detect_project_language, get_project_root, normalize_path,
    // Path validation utilities
    require_directory, require_exists, require_file, PathValidationError,
};
pub use query_error::format_query_error;
pub use simd::{count_byte, find_all_bytes, find_byte, find_bytes, rfind_byte};
