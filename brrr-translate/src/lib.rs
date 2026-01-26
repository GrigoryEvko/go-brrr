//! Translation layer for converting source language ASTs to Brrr IR.
//!
//! This crate provides infrastructure for translating parsed source code
//! (via tree-sitter) into the brrr-repr intermediate representation.
//!
//! # Architecture
//!
//! - [`ToIr`] - Core trait for translation to Brrr IR
//! - [`TranslateError`] - Error types for translation failures
//! - [`output::TranslatedModule`] - Rich output with full definitions
//! - [`go`] - Go language translation module
//!
//! # Example
//!
//! ```ignore
//! use brrr_translate::go::GoTranslator;
//!
//! let source = b"package main\nfunc main() {}";
//! let mut translator = GoTranslator::new(source);
//! let module = translator.translate()?;
//! // module.functions contains full FunctionDef with bodies
//! ```

pub mod go;
pub mod output;

pub use output::{ConstantDef, TranslatedModule, VariableDef};

use brrr_repr::BrrrType;
use tree_sitter::Node;

/// Error type for translation failures
#[derive(Debug, Clone)]
pub struct TranslateError {
    pub kind: TranslateErrorKind,
    pub message: String,
    pub line: usize,
    pub column: usize,
}

/// Kinds of translation errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TranslateErrorKind {
    /// Unsupported syntax construct
    UnsupportedSyntax,
    /// Unknown type
    UnknownType,
    /// Invalid expression
    InvalidExpression,
    /// Missing required node
    MissingNode,
    /// Type mismatch
    TypeMismatch,
    /// Parse error
    ParseError,
    /// Internal error
    Internal,
}

impl std::fmt::Display for TranslateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} at {}:{}: {}",
            self.kind, self.line, self.column, self.message
        )
    }
}

impl std::error::Error for TranslateError {}

/// Result type for translation operations
pub type TranslateResult<T> = Result<T, TranslateError>;

/// Trait for translating AST nodes to Brrr IR.
///
/// Implement this trait for source language AST nodes to enable
/// conversion to the brrr-repr intermediate representation.
pub trait ToIr {
    /// The target IR type
    type Output;

    /// Translate this AST node to Brrr IR
    fn to_ir(&self, ctx: &mut dyn TranslationContext) -> TranslateResult<Self::Output>;
}

/// Context for translation operations.
///
/// Provides shared state during translation including:
/// - String interning
/// - Type environment
/// - Node ID generation
/// - Source location tracking
pub trait TranslationContext {
    /// Intern a string, returning a handle
    fn intern(&mut self, s: &str) -> lasso::Spur;

    /// Look up a type by name
    fn lookup_type(&self, name: lasso::Spur) -> Option<&BrrrType>;

    /// Register a type binding
    fn bind_type(&mut self, name: lasso::Spur, ty: BrrrType);

    /// Generate a fresh node ID
    fn fresh_node_id(&mut self) -> brrr_repr::NodeId;

    /// Generate a fresh type variable
    fn fresh_type_var(&mut self) -> brrr_repr::types::TypeVar;

    /// Get the source text for a node
    fn node_text<'a>(&self, node: Node<'a>) -> &'a str;

    /// Get source bytes
    fn source(&self) -> &[u8];
}

/// Helper to create translation errors
pub fn translate_error(
    kind: TranslateErrorKind,
    message: impl Into<String>,
    node: Node<'_>,
) -> TranslateError {
    TranslateError {
        kind,
        message: message.into(),
        line: node.start_position().row + 1,
        column: node.start_position().column,
    }
}

/// Helper to create "unsupported" errors
pub fn unsupported(what: &str, node: Node<'_>) -> TranslateError {
    translate_error(
        TranslateErrorKind::UnsupportedSyntax,
        format!("unsupported: {}", what),
        node,
    )
}

/// Helper to create "missing node" errors
pub fn missing_node(what: &str, node: Node<'_>) -> TranslateError {
    translate_error(
        TranslateErrorKind::MissingNode,
        format!("missing required node: {}", what),
        node,
    )
}
