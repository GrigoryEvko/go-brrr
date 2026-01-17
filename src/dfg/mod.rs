//! Data flow graph extraction and program slicing.
//!
//! Tracks how data flows through a function - variable definitions,
//! uses, and mutations. Supports forward and backward program slicing.
//!
//! # Program Slicing
//!
//! Program slicing extracts the subset of code relevant to a computation:
//! - **Backward slice**: What affects a given line? (debugging: "why is this value wrong?")
//! - **Forward slice**: What does a line affect? (refactoring: "what will this change break?")
//! - **Chop**: What statements lie on paths between two points?
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::dfg::{slice, DFGInfo, SliceCriteria, backward_slice};
//!
//! let dfg: DFGInfo = /* ... */;
//! let criteria = SliceCriteria::at_line(42);
//! let result = backward_slice(&dfg, &criteria);
//! println!("Lines affecting line 42: {:?}", result.lines);
//! ```

pub mod builder;
pub mod slice;
pub mod types;

// Re-export types
// Note: DFGInfo is used within this module; DataflowEdge and DataflowKind are
// re-exported from lib.rs for the public API.
#[allow(unused_imports)]
pub use types::{DFGInfo, DataflowEdge, DataflowKind};

// Re-export builder
pub use builder::DfgBuilder;

// Re-export slice types and functions
// These are re-exported for the public API; not all are used within this module.
#[allow(unused_imports)]
pub use slice::{
    backward_slice, backward_slice_variable, bidirectional_slice, chop, chop_for_variable,
    forward_slice, forward_slice_variable, ChopResult, SliceCriteria, SliceMetrics, SliceResult,
};

use crate::error::{Result, BrrrError};

/// Extract DFG for a function with explicit language specification.
///
/// This function allows overriding the language auto-detection, which is useful
/// for files without extensions or with non-standard extensions.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to extract DFG for
/// * `language` - Optional language override (e.g., "python", "typescript", "rust").
///   If `None`, language is auto-detected from file extension.
///
/// # Returns
///
/// The data flow graph for the specified function.
///
/// # Errors
///
/// Returns an error if:
/// - The file cannot be read
/// - The language is not supported
/// - The function is not found
/// - Parsing fails
pub fn extract_with_language(file: &str, function: &str, language: Option<&str>) -> Result<DFGInfo> {
    DfgBuilder::extract_from_file_with_language(file, function, language)
}

/// Get backward slice: what affects the given line?
///
/// Convenience function that extracts DFG and computes slice in one call.
/// This function provides pure data-flow-only slicing (no control dependencies).
///
/// For more accurate slicing that includes control dependencies, use the PDG-based
/// slicing functions in [`crate::pdg`].
///
/// # Errors
///
/// Returns [`BrrrError::InvalidArgument`] if line is 0 (lines are 1-indexed).
// Public API - used by lib.rs's get_slice_dfg_only function
#[allow(dead_code)]
pub fn get_slice(file: &str, function: &str, line: usize) -> Result<Vec<usize>> {
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }
    let dfg = DfgBuilder::extract_from_file(file, function)?;
    Ok(dfg.backward_slice(line))
}
