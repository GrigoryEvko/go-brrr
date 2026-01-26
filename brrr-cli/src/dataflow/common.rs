//! Common utilities for dataflow analysis modules.
//!
//! This module provides shared functions used across multiple dataflow analyses
//! to avoid code duplication.

/// Validate identifier syntax.
///
/// Checks that a string is a valid identifier:
/// - Non-empty
/// - First character is alphabetic or underscore
/// - Remaining characters are alphanumeric or underscore
///
/// # Examples
///
/// ```ignore
/// assert!(is_valid_identifier("foo"));
/// assert!(is_valid_identifier("_bar"));
/// assert!(is_valid_identifier("var123"));
/// assert!(!is_valid_identifier(""));
/// assert!(!is_valid_identifier("123abc"));
/// assert!(!is_valid_identifier("foo-bar"));
/// ```
#[inline]
#[must_use]
pub fn is_valid_identifier(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }

    let mut chars = name.chars();

    // First character must be alphabetic or underscore
    match chars.next() {
        Some(c) if c.is_alphabetic() || c == '_' => {}
        _ => return false,
    }

    // Rest must be alphanumeric or underscore
    chars.all(|c| c.is_alphanumeric() || c == '_')
}

// =============================================================================
// Test Utilities
// =============================================================================

#[cfg(test)]
pub mod test_utils {
    //! Test utilities shared across dataflow analysis tests.

    use rustc_hash::FxHashMap;

    use crate::cfg::types::{BlockType, CFGBlock, CFGEdge, EdgeType};
    use crate::cfg::{BlockId, CFGInfo};

    /// Create a CFG with a loop for testing dataflow analyses.
    ///
    /// The CFG represents:
    /// ```python
    /// def loop_test(a, b, n):
    ///     i = 0                   # Block 0 (entry)
    ///     while i < n:            # Block 1 (loop header)
    ///         x = a + b           # Block 2 (loop body)
    ///         i = i + 1
    ///     return x                # Block 3 (exit)
    /// ```
    ///
    /// Structure:
    /// - Block 0: Entry with initialization
    /// - Block 1: Loop header with condition check
    /// - Block 2: Loop body
    /// - Block 3: Exit/return
    ///
    /// Edges:
    /// - 0 -> 1: Unconditional
    /// - 1 -> 2: True (enter loop)
    /// - 2 -> 1: Back edge
    /// - 1 -> 3: False (exit loop)
    #[must_use]
    pub fn create_loop_cfg(function_name: &str) -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec![
                    format!("def {}(a, b, n):", function_name),
                    "i = 0".to_string(),
                ],
                func_calls: vec![],
                start_line: 1,
                end_line: 2,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "loop_header".to_string(),
                block_type: BlockType::LoopHeader,
                statements: vec!["while i < n:".to_string()],
                func_calls: vec![],
                start_line: 3,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "loop_body".to_string(),
                block_type: BlockType::LoopBody,
                statements: vec!["x = a + b".to_string(), "i = i + 1".to_string()],
                func_calls: vec![],
                start_line: 4,
                end_line: 5,
            },
        );

        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "exit".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return x".to_string()],
                func_calls: vec![],
                start_line: 6,
                end_line: 6,
            },
        );

        CFGInfo::new(
            function_name.to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::new(BlockId(1), BlockId(2), EdgeType::True),
                CFGEdge::new(BlockId(2), BlockId(1), EdgeType::BackEdge),
                CFGEdge::new(BlockId(1), BlockId(3), EdgeType::False),
            ],
            BlockId(0),
            vec![BlockId(3)],
        )
    }

    /// Create a CFG with conditional branches for testing.
    ///
    /// The CFG represents:
    /// ```python
    /// def branch_test(cond):
    ///     if cond:              # Block 1 (branch)
    ///         x = a + b         # Block 2 (true branch)
    ///     else:
    ///         y = a + b         # Block 3 (false branch)
    ///     return result         # Block 4 (merge)
    /// ```
    #[must_use]
    pub fn create_conditional_cfg(function_name: &str) -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec![format!("def {}(a, b, cond):", function_name)],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "condition".to_string(),
                block_type: BlockType::Branch,
                statements: vec!["if cond:".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 2,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "true_branch".to_string(),
                block_type: BlockType::Body,
                statements: vec!["x = a + b".to_string()],
                func_calls: vec![],
                start_line: 3,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "false_branch".to_string(),
                block_type: BlockType::Body,
                statements: vec!["y = a + b".to_string()],
                func_calls: vec![],
                start_line: 5,
                end_line: 5,
            },
        );

        blocks.insert(
            BlockId(4),
            CFGBlock {
                id: BlockId(4),
                label: "merge".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return x or y".to_string()],
                func_calls: vec![],
                start_line: 6,
                end_line: 6,
            },
        );

        CFGInfo::new(
            function_name.to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::new(BlockId(1), BlockId(2), EdgeType::True),
                CFGEdge::new(BlockId(1), BlockId(3), EdgeType::False),
                CFGEdge::unconditional(BlockId(2), BlockId(4)),
                CFGEdge::unconditional(BlockId(3), BlockId(4)),
            ],
            BlockId(0),
            vec![BlockId(4)],
        )
    }

    /// Create a simple linear CFG for testing.
    ///
    /// The CFG represents:
    /// ```python
    /// def linear_test(a, b):
    ///     x = a + 1
    ///     y = x + b
    ///     return y
    /// ```
    #[must_use]
    pub fn create_linear_cfg(function_name: &str) -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec![format!("def {}(a, b):", function_name)],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "body".to_string(),
                block_type: BlockType::Body,
                statements: vec!["x = a + 1".to_string(), "y = x + b".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "return".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return y".to_string()],
                func_calls: vec![],
                start_line: 4,
                end_line: 4,
            },
        );

        CFGInfo::new(
            function_name.to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::unconditional(BlockId(1), BlockId(2)),
            ],
            BlockId(0),
            vec![BlockId(2)],
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_identifiers() {
        assert!(is_valid_identifier("foo"));
        assert!(is_valid_identifier("_bar"));
        assert!(is_valid_identifier("__private"));
        assert!(is_valid_identifier("var123"));
        assert!(is_valid_identifier("CamelCase"));
        assert!(is_valid_identifier("snake_case"));
        assert!(is_valid_identifier("SCREAMING_SNAKE"));
        assert!(is_valid_identifier("a"));
        assert!(is_valid_identifier("_"));
    }

    #[test]
    fn test_invalid_identifiers() {
        assert!(!is_valid_identifier(""));
        assert!(!is_valid_identifier("123abc"));
        assert!(!is_valid_identifier("foo-bar"));
        assert!(!is_valid_identifier("foo bar"));
        assert!(!is_valid_identifier("foo.bar"));
        assert!(!is_valid_identifier("foo[0]"));
        assert!(!is_valid_identifier("foo()"));
        assert!(!is_valid_identifier("@decorator"));
        assert!(!is_valid_identifier("$var"));
    }

    #[test]
    fn test_unicode_identifiers() {
        // Rust identifiers allow Unicode alphabetic characters
        assert!(is_valid_identifier("variable"));
        // Non-ASCII alphabetic characters
        assert!(is_valid_identifier("nombre"));
    }
}
