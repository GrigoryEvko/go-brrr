//! Common AST node type constants shared across analysis modules.
//!
//! This module provides compile-time perfect hash sets (PHF) for O(1) node type
//! lookups used by metrics, quality analysis, and code smell detection.
//!
//! # Architecture
//!
//! Constants are organized by semantic category rather than language to enable
//! cross-language analysis. Each set covers Python, TypeScript/JavaScript, Rust,
//! Go, Java, and C/C++.
//!
//! # Usage
//!
//! ```ignore
//! use brrr::ast::constants::{STATEMENT_NODE_TYPES, FUNCTION_NODE_TYPES};
//!
//! if STATEMENT_NODE_TYPES.contains(node.kind()) {
//!     statement_count += 1;
//! }
//! ```
//!
//! # Performance
//!
//! PHF sets provide O(1) lookups with zero runtime initialization cost.
//! The hash function is computed at compile time.

use phf::{phf_set, Set};

// =============================================================================
// STATEMENT NODE TYPES
// =============================================================================

/// Node types that represent statements in various languages.
///
/// Used for:
/// - Logical LOC counting (statement count)
/// - Function size metrics (statement count)
/// - Long method detection (statement threshold)
///
/// Includes expression statements, control flow, declarations, and imports.
pub static STATEMENT_NODE_TYPES: Set<&'static str> = phf_set! {
    // Python
    "expression_statement",
    "return_statement",
    "if_statement",
    "for_statement",
    "while_statement",
    "try_statement",
    "with_statement",
    "assert_statement",
    "raise_statement",
    "pass_statement",
    "break_statement",
    "continue_statement",
    "import_statement",
    "import_from_statement",
    "global_statement",
    "nonlocal_statement",
    "delete_statement",
    "future_import_statement",
    "match_statement",
    // TypeScript/JavaScript
    "switch_statement",
    "for_in_statement",
    "do_statement",
    "throw_statement",
    "variable_declaration",
    "lexical_declaration",
    "export_statement",
    // Rust
    "let_declaration",
    "return_expression",
    "if_expression",
    "match_expression",
    "for_expression",
    "while_expression",
    "loop_expression",
    "break_expression",
    "continue_expression",
    "macro_invocation",
    // Go
    "go_statement",
    "select_statement",
    "defer_statement",
    "var_declaration",
    "short_var_declaration",
    "assignment_statement",
    // Java
    "switch_expression",
    "enhanced_for_statement",
    "local_variable_declaration",
    // C/C++
    "goto_statement",
    "declaration",
    "compound_statement",
};

// =============================================================================
// FUNCTION NODE TYPES
// =============================================================================

/// Node types that define functions and methods.
///
/// Used for:
/// - Function extraction and enumeration
/// - Function size analysis
/// - Call graph construction
/// - LOC function-level metrics
pub static FUNCTION_NODE_TYPES: Set<&'static str> = phf_set! {
    // Python
    "function_definition",
    // TypeScript/JavaScript
    "function_declaration",
    "method_definition",
    "arrow_function",
    // Rust
    "function_item",
    // Go
    "method_declaration",
    // Java
    "constructor_declaration",
    // C/C++ (also uses function_definition)
};

// =============================================================================
// DECISION NODE TYPES (Cyclomatic Complexity)
// =============================================================================

/// Node types that represent decision points for cyclomatic complexity.
///
/// Cyclomatic complexity = number of decision points + 1
///
/// Includes conditionals, loops, switch/match cases, exception handlers,
/// and ternary operators.
pub static DECISION_NODE_TYPES: Set<&'static str> = phf_set! {
    // Conditionals
    "if_statement",
    "if_expression",
    "elif_clause",
    "else_if_clause",
    // Loops
    "for_statement",
    "for_expression",
    "for_in_statement",
    "enhanced_for_statement",
    "while_statement",
    "while_expression",
    "do_statement",
    "loop_expression",
    // Switch/Match
    "switch_statement",
    "switch_expression",
    "match_expression",
    "match_statement",
    "case_clause",
    "match_arm",
    // Exception handling
    "try_statement",
    "except_clause",
    "catch_clause",
    // Ternary
    "conditional_expression",
    "ternary_expression",
};

// =============================================================================
// NESTING NODE TYPES
// =============================================================================

/// Node types that increase nesting depth.
///
/// Used for:
/// - Max nesting depth calculation
/// - Cognitive complexity metrics
/// - Long method detection
///
/// Includes control flow, exception handling, lambdas, and comprehensions.
pub static NESTING_NODE_TYPES: Set<&'static str> = phf_set! {
    // Conditionals
    "if_statement",
    "if_expression",
    "elif_clause",
    // Loops
    "for_statement",
    "for_expression",
    "for_in_statement",
    "while_statement",
    "while_expression",
    "do_statement",
    "loop_expression",
    // Exception handling
    "try_statement",
    "except_clause",
    "catch_clause",
    "with_statement",
    // Switch/Match
    "switch_statement",
    "switch_expression",
    "match_expression",
    // Lambdas/Closures
    "lambda",
    "arrow_function",
    "closure_expression",
    // Comprehensions (Python)
    "list_comprehension",
    "dictionary_comprehension",
    "generator_expression",
};

// =============================================================================
// BRANCH NODE TYPES
// =============================================================================

/// Node types representing branching constructs.
///
/// Used for:
/// - Branch count metrics
/// - Function size analysis (branches threshold)
///
/// More specific than decision nodes - focuses on if/switch/match branches.
pub static BRANCH_NODE_TYPES: Set<&'static str> = phf_set! {
    "if_statement",
    "if_expression",
    "elif_clause",
    "else_if_clause",
    "switch_statement",
    "switch_expression",
    "match_expression",
    "match_statement",
    "conditional_expression",
    "ternary_expression",
};

// =============================================================================
// LOOP NODE TYPES
// =============================================================================

/// Node types representing loop constructs.
///
/// Used for:
/// - Loop count metrics
/// - Extraction candidate detection (loop bodies)
/// - Replace Loop with Pipeline refactoring suggestions
pub static LOOP_NODE_TYPES: Set<&'static str> = phf_set! {
    "for_statement",
    "for_expression",
    "for_in_statement",
    "enhanced_for_statement",
    "while_statement",
    "while_expression",
    "do_statement",
    "loop_expression",
};

// =============================================================================
// EXIT/RETURN NODE TYPES
// =============================================================================

/// Node types representing function exit points.
///
/// Used for:
/// - Return statement counting
/// - Multiple exit point detection
/// - Guard clause extraction suggestions
pub static EXIT_NODE_TYPES: Set<&'static str> = phf_set! {
    "return_statement",
    "return_expression",
    "throw_statement",
    "raise_statement",
    "break_statement",
    "break_expression",
};

/// Subset of exit nodes that are specifically return statements.
///
/// Used when only counting actual returns (not throws/breaks).
pub static RETURN_NODE_TYPES: Set<&'static str> = phf_set! {
    "return_statement",
    "return_expression",
    "throw_statement",
    "raise_statement",
};

// =============================================================================
// VARIABLE DECLARATION NODE TYPES
// =============================================================================

/// Node types representing variable declarations.
///
/// Used for:
/// - Local variable counting
/// - Function size metrics (variables threshold)
/// - Extract Variable refactoring
pub static VARIABLE_DECL_TYPES: Set<&'static str> = phf_set! {
    // Python
    "assignment",
    "augmented_assignment",
    // TypeScript/JavaScript
    "variable_declaration",
    "lexical_declaration",
    "variable_declarator",
    // Rust
    "let_declaration",
    // Go
    "var_declaration",
    "short_var_declaration",
    "var_spec",
    // Java
    "local_variable_declaration",
    // C/C++
    "declaration",
    "init_declarator",
};

// =============================================================================
// COMMENT NODE TYPES
// =============================================================================

/// Node types representing comments and documentation.
///
/// Used for:
/// - Comment line counting (CLOC)
/// - Code-to-comment ratio calculation
/// - Blank vs comment vs code line classification
pub static COMMENT_NODE_TYPES: Set<&'static str> = phf_set! {
    "comment",
    "line_comment",
    "block_comment",
};

// =============================================================================
// STRING LITERAL NODE TYPES
// =============================================================================

/// Node types representing string literals (potentially multi-line).
///
/// Used for:
/// - Multi-line string detection (to not count interior as SLOC)
/// - Docstring detection (Python)
/// - Template string handling
pub static STRING_NODE_TYPES: Set<&'static str> = phf_set! {
    "string",
    "string_literal",
    "raw_string_literal",
    "template_string",
    "interpreted_string_literal",
    "raw_string",
};

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_statement_node_types_contains_common() {
        assert!(STATEMENT_NODE_TYPES.contains("return_statement"));
        assert!(STATEMENT_NODE_TYPES.contains("if_statement"));
        assert!(STATEMENT_NODE_TYPES.contains("for_statement"));
        assert!(STATEMENT_NODE_TYPES.contains("expression_statement"));
    }

    #[test]
    fn test_statement_node_types_python() {
        assert!(STATEMENT_NODE_TYPES.contains("import_statement"));
        assert!(STATEMENT_NODE_TYPES.contains("pass_statement"));
        assert!(STATEMENT_NODE_TYPES.contains("raise_statement"));
        assert!(STATEMENT_NODE_TYPES.contains("with_statement"));
    }

    #[test]
    fn test_statement_node_types_rust() {
        assert!(STATEMENT_NODE_TYPES.contains("let_declaration"));
        assert!(STATEMENT_NODE_TYPES.contains("return_expression"));
        assert!(STATEMENT_NODE_TYPES.contains("match_expression"));
        assert!(STATEMENT_NODE_TYPES.contains("macro_invocation"));
    }

    #[test]
    fn test_statement_node_types_typescript() {
        assert!(STATEMENT_NODE_TYPES.contains("lexical_declaration"));
        assert!(STATEMENT_NODE_TYPES.contains("throw_statement"));
        assert!(STATEMENT_NODE_TYPES.contains("export_statement"));
    }

    #[test]
    fn test_statement_node_types_go() {
        assert!(STATEMENT_NODE_TYPES.contains("defer_statement"));
        assert!(STATEMENT_NODE_TYPES.contains("go_statement"));
        assert!(STATEMENT_NODE_TYPES.contains("short_var_declaration"));
    }

    #[test]
    fn test_function_node_types() {
        assert!(FUNCTION_NODE_TYPES.contains("function_definition"));
        assert!(FUNCTION_NODE_TYPES.contains("function_declaration"));
        assert!(FUNCTION_NODE_TYPES.contains("method_definition"));
        assert!(FUNCTION_NODE_TYPES.contains("arrow_function"));
        assert!(FUNCTION_NODE_TYPES.contains("function_item"));
    }

    #[test]
    fn test_decision_node_types() {
        assert!(DECISION_NODE_TYPES.contains("if_statement"));
        assert!(DECISION_NODE_TYPES.contains("for_statement"));
        assert!(DECISION_NODE_TYPES.contains("while_statement"));
        assert!(DECISION_NODE_TYPES.contains("match_expression"));
        assert!(DECISION_NODE_TYPES.contains("try_statement"));
    }

    #[test]
    fn test_nesting_node_types() {
        assert!(NESTING_NODE_TYPES.contains("if_statement"));
        assert!(NESTING_NODE_TYPES.contains("for_statement"));
        assert!(NESTING_NODE_TYPES.contains("try_statement"));
        assert!(NESTING_NODE_TYPES.contains("lambda"));
        assert!(NESTING_NODE_TYPES.contains("list_comprehension"));
    }

    #[test]
    fn test_loop_node_types() {
        assert!(LOOP_NODE_TYPES.contains("for_statement"));
        assert!(LOOP_NODE_TYPES.contains("while_statement"));
        assert!(LOOP_NODE_TYPES.contains("for_in_statement"));
        assert!(LOOP_NODE_TYPES.contains("loop_expression"));
    }

    #[test]
    fn test_exit_node_types() {
        assert!(EXIT_NODE_TYPES.contains("return_statement"));
        assert!(EXIT_NODE_TYPES.contains("return_expression"));
        assert!(EXIT_NODE_TYPES.contains("throw_statement"));
        assert!(EXIT_NODE_TYPES.contains("raise_statement"));
    }

    #[test]
    fn test_variable_decl_types() {
        assert!(VARIABLE_DECL_TYPES.contains("assignment"));
        assert!(VARIABLE_DECL_TYPES.contains("let_declaration"));
        assert!(VARIABLE_DECL_TYPES.contains("var_declaration"));
        assert!(VARIABLE_DECL_TYPES.contains("lexical_declaration"));
    }

    #[test]
    fn test_comment_node_types() {
        assert!(COMMENT_NODE_TYPES.contains("comment"));
        assert!(COMMENT_NODE_TYPES.contains("line_comment"));
        assert!(COMMENT_NODE_TYPES.contains("block_comment"));
    }

    #[test]
    fn test_string_node_types() {
        assert!(STRING_NODE_TYPES.contains("string"));
        assert!(STRING_NODE_TYPES.contains("string_literal"));
        assert!(STRING_NODE_TYPES.contains("template_string"));
    }

    #[test]
    fn test_no_false_positives() {
        assert!(!STATEMENT_NODE_TYPES.contains("identifier"));
        assert!(!FUNCTION_NODE_TYPES.contains("class_definition"));
        assert!(!LOOP_NODE_TYPES.contains("if_statement"));
    }
}
