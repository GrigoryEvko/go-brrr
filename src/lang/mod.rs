//! Language abstraction layer.
//!
//! Provides a unified interface for multi-language code analysis via the
//! [`Language`] trait. Each supported language implements this trait to
//! provide tree-sitter queries and extraction logic.

pub mod registry;
pub mod traits;

// Language implementations
pub mod c;
pub mod cpp;
pub mod go;
pub mod java;
pub mod python;
pub mod rust_lang;
pub mod typescript;

// Re-exports for the crate's public API (used by lib.rs)
pub use registry::LanguageRegistry;
#[allow(unused_imports)]
pub use traits::{BoxedLanguage, Language};
