//! BindingDetector trait for cross-language binding detection.

use tree_sitter::Tree;

use crate::bindings::types::{BindingDeclaration, BindingSystem};
use crate::error::Result;

/// Trait for binding system detectors.
///
/// Each implementation detects one specific binding system (pybind11, ctypes, etc.)
/// by walking a tree-sitter parse tree. Detectors operate on a single file;
/// cross-file resolution is handled separately by the resolver.
pub trait BindingDetector: Send + Sync {
    /// Which binding system this detector handles.
    fn system(&self) -> BindingSystem;

    /// Languages this detector applies to (matching LanguageRegistry names).
    fn applicable_languages(&self) -> &[&'static str];

    /// Detect binding declarations in a single parsed file.
    fn detect(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
        language: &str,
    ) -> Result<Vec<BindingDeclaration>>;

    /// Fast pre-check: does this file likely contain bindings for this system?
    ///
    /// Uses byte-level scanning to avoid tree-sitter overhead on the 99%+ of
    /// files that have no bindings. Default returns true (always scan).
    fn quick_check(&self, _source: &[u8], _language: &str) -> bool {
        true
    }
}
