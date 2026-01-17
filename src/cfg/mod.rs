//! Control flow graph extraction and rendering.
//!
//! Builds CFGs from parsed AST nodes, representing the control flow
//! structure of functions including branches, loops, and exception handling.
//!
//! # Modules
//!
//! - [`types`]: Core CFG data structures (blocks, edges, graph)
//! - [`builder`]: CFG construction from source code
//! - [`render`]: Output formats (Mermaid, DOT, ASCII, JSON)
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::cfg::{extract, render};
//!
//! let cfg = extract("src/main.rs", "process_data")?;
//! println!("{}", render::to_mermaid(&cfg));
//! println!("{}", render::to_dot(&cfg));
//! ```

pub mod builder;
pub mod render;
pub mod types;

// Re-exports for the crate's public API (used by lib.rs)
#[allow(unused_imports)]
pub use types::{BlockId, BlockType, CFGBlock, CFGEdge, CFGError, CFGInfo, EdgeType};

// Re-export builder
pub use builder::CfgBuilder;

// Re-export render functions for convenience
#[allow(unused_imports)]
pub use render::{to_ascii, to_dot, to_json, to_json_compact, to_mermaid};

use crate::error::Result;

/// Extract CFG for a function in a file.
///
/// This is a convenience function that wraps [`CfgBuilder::extract_from_file`].
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to extract CFG for
///
/// # Returns
///
/// The control flow graph for the specified function.
///
/// # Errors
///
/// Returns an error if:
/// - The file cannot be read
/// - The language is not supported
/// - The function is not found
/// - Parsing fails
#[allow(dead_code)]
pub fn extract(file: &str, function: &str) -> Result<CFGInfo> {
    CfgBuilder::extract_from_file(file, function)
}

/// Extract CFG for a function with explicit language specification.
///
/// This function allows overriding the language auto-detection, which is useful
/// for files without extensions or with non-standard extensions.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to extract CFG for
/// * `language` - Optional language override (e.g., "python", "typescript", "rust").
///   If `None`, language is auto-detected from file extension.
///
/// # Returns
///
/// The control flow graph for the specified function.
///
/// # Errors
///
/// Returns an error if:
/// - The file cannot be read
/// - The language is not supported
/// - The function is not found
/// - Parsing fails
pub fn extract_with_language(file: &str, function: &str, language: Option<&str>) -> Result<CFGInfo> {
    CfgBuilder::extract_from_file_with_language(file, function, language)
}
