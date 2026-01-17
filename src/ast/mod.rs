//! AST extraction and code structure analysis.
//!
//! This module provides tree-sitter based code analysis for extracting
//! functions, classes, imports, and generating code structure maps.
//!
//! # Main API
//!
//! - [`code_structure`] - Extract summaries of all functions and classes in a project
//! - [`extract_file`] - Extract full AST info from a single source file
//! - [`file_tree`] - Generate a file tree structure
//!
//! # Example
//!
//! ```no_run
//! use go_brrr::ast::{code_structure, extract_file};
//!
//! // Get project structure summary
//! let structure = code_structure("./src", Some("python"), 100)?;
//! println!("Found {} functions", structure.functions.len());
//!
//! // Get detailed info from a single file (None = no base path restriction)
//! let module = extract_file("./src/main.py", None)?;
//! for func in module.functions {
//!     println!("Function: {} at line {}", func.name, func.line_number);
//! }
//!
//! // With base path validation for security
//! let restricted = extract_file("./src/main.py", Some("./src"))?;
//! # Ok::<(), go_brrr::error::BrrrError>(())
//! ```

pub mod extractor;
pub mod structure;
pub mod tree;
pub mod types;

// Re-exports for the crate's public API (used by lib.rs)
#[allow(unused_imports)]
pub use extractor::{clear_parser_cache, clear_query_cache, extract_imports, AstExtractor};
#[allow(unused_imports)]
pub use structure::{code_structure, extract_file, extract_file_unchecked};
pub use tree::file_tree;
#[allow(unused_imports)]
pub use types::{
    CallGraphInfo, ClassInfo, ClassSummary, CodeStructure, FieldInfo, FileTreeEntry, FunctionInfo,
    FunctionSummary, ImportInfo, ModuleInfo,
};
