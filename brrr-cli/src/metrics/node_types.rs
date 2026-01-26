//! Shared AST node type constants for metrics analysis.
//!
//! This module centralizes node type definitions used across multiple metrics modules
//! (LOC, function size, complexity, long method detection) to eliminate duplication
//! and ensure consistency.

// =============================================================================
// STATEMENT NODE TYPES
// =============================================================================

/// Node types that represent statements for logical LOC and statement counting.
///
/// Used by:
/// - `loc.rs` for logical LOC calculation
/// - `function_size.rs` for statement counting
/// - `long_method.rs` for method length analysis
pub const STATEMENT_NODE_TYPES: &[&str] = &[
    // Python statements
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
    // TypeScript/JavaScript statements
    "switch_statement",
    "for_in_statement",
    "do_statement",
    "throw_statement",
    "variable_declaration",
    "lexical_declaration",
    "export_statement",
    // Rust statements/expressions
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
    // Go statements
    "go_statement",
    "select_statement",
    "defer_statement",
    "var_declaration",
    "short_var_declaration",
    "assignment_statement",
    // Java statements
    "switch_expression",
    "enhanced_for_statement",
    "local_variable_declaration",
    // C/C++ statements
    "goto_statement",
    "declaration",
    "compound_statement",
];

// =============================================================================
// FUNCTION NODE TYPES
// =============================================================================

/// Node types that represent function/method definitions.
///
/// Used by:
/// - `loc.rs` for function-level LOC tracking
/// - `function_size.rs` for function size analysis
/// - `long_method.rs` for method detection
pub const FUNCTION_NODE_TYPES: &[&str] = &[
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
];

// =============================================================================
// VARIABLE DECLARATION NODE TYPES
// =============================================================================

/// Node types that represent variable declarations.
///
/// Used by:
/// - `function_size.rs` for local variable counting
/// - `long_method.rs` for variable analysis
pub const VARIABLE_DECL_TYPES: &[&str] = &[
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
];

// =============================================================================
// RETURN/EXIT NODE TYPES
// =============================================================================

/// Node types that represent return or exit points.
///
/// Used by:
/// - `function_size.rs` for return statement counting
/// - `long_method.rs` for exit point analysis
pub const RETURN_NODE_TYPES: &[&str] = &[
    "return_statement",  // Python, TS/JS, Go, Java, C/C++
    "return_expression", // Rust
    "throw_statement",   // TS/JS, Java - counts as exit point
    "raise_statement",   // Python - counts as exit point
];

// =============================================================================
// BRANCH NODE TYPES
// =============================================================================

/// Node types that represent branching constructs.
///
/// Used by:
/// - `function_size.rs` for branch counting
pub const BRANCH_NODE_TYPES: &[&str] = &[
    "if_statement",
    "if_expression",
    "elif_clause",
    "else_if_clause",
    "switch_statement",
    "switch_expression",
    "match_expression",
    "match_statement",
    "conditional_expression", // ternary
    "ternary_expression",
];

// =============================================================================
// COMMENT NODE TYPES
// =============================================================================

/// Node types that represent comments in various languages.
///
/// Used by:
/// - `loc.rs` for comment line detection
pub const COMMENT_NODE_TYPES: &[&str] = &[
    "comment",       // Python, Go, TypeScript/JavaScript, Java
    "line_comment",  // Rust, Java, C/C++
    "block_comment", // Rust, Java, C/C++
];

// =============================================================================
// STRING LITERAL NODE TYPES
// =============================================================================

/// Node types that represent string literals (potential multi-line).
///
/// Used by:
/// - `loc.rs` for multi-line string handling
pub const STRING_NODE_TYPES: &[&str] = &[
    "string",                     // Python
    "string_literal",             // Rust, C, C++, Java
    "raw_string_literal",         // Rust, C++
    "template_string",            // TypeScript/JavaScript
    "interpreted_string_literal", // Go
    "raw_string",                 // Python raw strings
];
