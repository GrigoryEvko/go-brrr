//! Core Language trait definition.
//!
//! The [`Language`] trait is the central abstraction for multi-language support.
//! Each language implements this trait to provide tree-sitter parsers, queries,
//! and extraction logic specific to that language.

use std::path::Path;

use tree_sitter::{Node, Parser, Tree};

use crate::ast::types::{ClassInfo, FunctionInfo, ImportInfo};
use crate::cfg::types::CFGInfo;
use crate::dfg::types::DFGInfo;
use crate::error::Result;

/// Trait for language-specific operations.
///
/// Each language implements this to provide tree-sitter queries
/// and extraction logic.
pub trait Language: Send + Sync {
    /// Language identifier (e.g., "python", "typescript").
    fn name(&self) -> &'static str;

    /// File extensions for this language (e.g., &[".py", ".pyi"]).
    fn extensions(&self) -> &[&'static str];

    /// Get a configured tree-sitter parser for this language.
    ///
    /// This method returns a default parser for the language. For languages
    /// that have multiple grammar variants (e.g., TypeScript/TSX), use
    /// `parser_for_path` instead to get the correct parser based on file extension.
    fn parser(&self) -> Result<Parser>;

    /// Get a configured tree-sitter parser for a specific file path.
    ///
    /// This method allows languages with multiple grammar variants (e.g.,
    /// TypeScript vs TSX, JavaScript vs JSX) to return the correct parser
    /// based on the file extension.
    ///
    /// The default implementation simply calls `parser()`, which is correct
    /// for languages with a single grammar. Languages with multiple grammars
    /// (like TypeScript/TSX) should override this method.
    ///
    /// # Arguments
    /// * `path` - Path to the source file being parsed
    ///
    /// # Returns
    /// * `Result<Parser>` - A configured parser for the file
    fn parser_for_path(&self, _path: &Path) -> Result<Parser> {
        self.parser()
    }

    /// Extract function information from an AST node.
    fn extract_function(&self, node: Node, source: &[u8]) -> Option<FunctionInfo>;

    /// Extract class information from an AST node.
    fn extract_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo>;

    /// Extract all imports from a parsed tree.
    fn extract_imports(&self, tree: &Tree, source: &[u8]) -> Vec<ImportInfo>;

    /// Extract module-level docstring from a parsed tree.
    ///
    /// For languages that support module docstrings (like Python), this extracts
    /// the first string literal at module level. Default returns None.
    fn extract_module_docstring(&self, _tree: &Tree, _source: &[u8]) -> Option<String> {
        None
    }

    /// Tree-sitter query pattern for function definitions.
    fn function_query(&self) -> &'static str;

    /// Tree-sitter query pattern for class definitions.
    fn class_query(&self) -> &'static str;

    /// Tree-sitter query pattern for call expressions.
    ///
    /// Used via trait dispatch in `lib.rs` for call graph construction.
    #[allow(dead_code)]
    fn call_query(&self) -> &'static str;

    /// Build control flow graph for a function.
    fn build_cfg(&self, node: Node, source: &[u8]) -> Result<CFGInfo>;

    /// Build data flow graph for a function.
    fn build_dfg(&self, node: Node, source: &[u8]) -> Result<DFGInfo>;

    /// Check if a file should be skipped for this language based on its content.
    ///
    /// This method allows languages to reject files that match their extension
    /// but contain content incompatible with the parser. For example, the C
    /// language handler uses this to skip `.h` files that contain C++ code.
    ///
    /// # Arguments
    /// * `path` - Path to the source file
    /// * `content` - File content as bytes
    ///
    /// # Returns
    /// * `true` if the file should be skipped, `false` otherwise
    ///
    /// # Default Implementation
    /// Returns `false` (process all files matching the extension).
    fn should_skip_file(&self, _path: &Path, _content: &[u8]) -> bool {
        false
    }
}

/// Boxed language trait object for dynamic dispatch.
pub type BoxedLanguage = Box<dyn Language>;
