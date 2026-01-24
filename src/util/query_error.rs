//! Tree-sitter query error formatting utilities.
//!
//! Provides rich error context for debugging tree-sitter query compilation failures.
//! Includes:
//! - Error position highlighting with context lines
//! - Human-readable error type descriptions
//! - Suggestions for common fixes based on error type

use tree_sitter::{QueryError, QueryErrorKind};

/// Format a tree-sitter query error with rich context for debugging.
///
/// Includes:
/// - Language name and error type
/// - Position information (row, column, offset)
/// - Query preview with the error location highlighted
/// - Suggestions for common fixes based on error type
///
/// # Arguments
/// * `lang_name` - Name of the language (e.g., "python", "typescript")
/// * `query_type` - Type of query ("function" or "class")
/// * `query_str` - The full query string
/// * `error` - The QueryError from tree-sitter
///
/// # Returns
/// A formatted error message string
///
/// # Example Output
/// ```text
/// Invalid function query for python (invalid node type)
///   Location: line 5, column 12 (byte offset 47)
///   Error: Invalid node type invalid_node
///
///   Query context:
///      3 | (decorated_definition
///      4 |   definition: (function_definition
/// >>> 5 |     name: (invalid_node) @name)
///                ^
///      6 | ) @function)
///
///   Suggestion: The node type 'invalid_node' doesn't exist in this language's grammar.
///   Run 'tree-sitter dump-tree <file>' to see valid node types.
/// ```
pub fn format_query_error(
    lang_name: &str,
    query_type: &str,
    query_str: &str,
    error: &QueryError,
) -> String {
    let mut msg = format!(
        "Invalid {} query for {} ({})\n",
        query_type,
        lang_name,
        format_error_kind(&error.kind)
    );

    // Add position information
    msg.push_str(&format!(
        "  Location: line {}, column {} (byte offset {})\n",
        error.row + 1, // Convert to 1-based line numbers
        error.column + 1,
        error.offset
    ));

    // Add the error message from tree-sitter
    if !error.message.is_empty() {
        msg.push_str(&format!("  Error: {}\n", error.message));
    }

    // Add query preview with error location highlighted
    msg.push_str("\n  Query context:\n");
    let lines: Vec<&str> = query_str.lines().collect();
    let error_line = error.row;

    // Show 2 lines before, the error line, and 2 lines after
    let start_line = error_line.saturating_sub(2);
    let end_line = (error_line + 3).min(lines.len());

    for (idx, line) in lines
        .iter()
        .enumerate()
        .skip(start_line)
        .take(end_line - start_line)
    {
        let line_num = idx + 1;
        let marker = if idx == error_line { ">>>" } else { "   " };
        msg.push_str(&format!("  {} {:3} | {}\n", marker, line_num, line));

        // Add caret pointing to the error column
        if idx == error_line {
            let padding = " ".repeat(error.column);
            msg.push_str(&format!("           {}^\n", padding));
        }
    }

    // Add suggestions based on error type
    if let Some(suggestion) = get_error_suggestion(&error.kind, &error.message) {
        msg.push_str(&format!("\n  Suggestion: {}\n", suggestion));
    }

    msg
}

/// Format the QueryErrorKind into a human-readable string.
fn format_error_kind(kind: &QueryErrorKind) -> &'static str {
    match kind {
        QueryErrorKind::Syntax => "syntax error",
        QueryErrorKind::NodeType => "invalid node type",
        QueryErrorKind::Field => "invalid field name",
        QueryErrorKind::Capture => "invalid capture",
        QueryErrorKind::Predicate => "invalid predicate",
        QueryErrorKind::Structure => "structure error",
        QueryErrorKind::Language => "language mismatch",
    }
}

/// Get a suggestion for fixing the error based on its type.
fn get_error_suggestion(kind: &QueryErrorKind, message: &str) -> Option<String> {
    match kind {
        QueryErrorKind::NodeType => {
            // Extract the invalid node type from the message if possible
            if let Some(invalid_type) = extract_identifier(message) {
                Some(format!(
                    "The node type '{}' doesn't exist in this language's grammar. \
                     Run 'tree-sitter dump-tree <file>' to see valid node types.",
                    invalid_type
                ))
            } else {
                Some(
                    "Check that the node type exists in this language's grammar. \
                     Run 'tree-sitter dump-tree <file>' to see valid node types."
                        .to_string(),
                )
            }
        }
        QueryErrorKind::Field => Some(
            "The field name doesn't exist in this language's grammar. \
             Check the grammar definition for valid field names."
                .to_string(),
        ),
        QueryErrorKind::Capture => Some(
            "Capture names must start with '@' and use valid identifiers. \
             Example: @function, @name, @class"
                .to_string(),
        ),
        QueryErrorKind::Syntax => Some(
            "Check for missing parentheses, brackets, or quotes. \
             Ensure patterns are properly nested."
                .to_string(),
        ),
        QueryErrorKind::Predicate => Some(
            "Predicates must use valid operators like #eq?, #match?, #not-eq?. \
             Arguments must be captures (@name) or strings (\"value\")."
                .to_string(),
        ),
        QueryErrorKind::Structure => Some(
            "The query structure doesn't match the grammar. \
             Check that child patterns match the actual AST structure."
                .to_string(),
        ),
        QueryErrorKind::Language => Some(
            "The query was compiled for a different language. \
             Ensure you're using the correct grammar for this file type."
                .to_string(),
        ),
    }
}

/// Extract an identifier from an error message (e.g., "invalid_node_type").
///
/// Uses SIMD-accelerated byte search via memchr for performance.
fn extract_identifier(message: &str) -> Option<&str> {
    // Look for quoted identifiers first using SIMD-accelerated search
    let bytes = message.as_bytes();
    if let Some(start) = memchr::memchr(b'\'', bytes) {
        if let Some(end) = memchr::memchr(b'\'', &bytes[start + 1..]) {
            // SAFETY: start and end are valid byte offsets within ASCII single quotes,
            // so slicing the original UTF-8 string at these positions is safe.
            return Some(&message[start + 1..start + 1 + end]);
        }
    }
    // Look for identifiers at the end of the message
    message.split_whitespace().last()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_error_kind() {
        assert_eq!(format_error_kind(&QueryErrorKind::Syntax), "syntax error");
        assert_eq!(
            format_error_kind(&QueryErrorKind::NodeType),
            "invalid node type"
        );
        assert_eq!(
            format_error_kind(&QueryErrorKind::Field),
            "invalid field name"
        );
        assert_eq!(
            format_error_kind(&QueryErrorKind::Capture),
            "invalid capture"
        );
        assert_eq!(
            format_error_kind(&QueryErrorKind::Predicate),
            "invalid predicate"
        );
        assert_eq!(
            format_error_kind(&QueryErrorKind::Structure),
            "structure error"
        );
        assert_eq!(
            format_error_kind(&QueryErrorKind::Language),
            "language mismatch"
        );
    }

    #[test]
    fn test_extract_identifier_quoted() {
        assert_eq!(
            extract_identifier("Invalid type 'foo_bar'"),
            Some("foo_bar")
        );
        assert_eq!(
            extract_identifier("Error: 'my_type' not found"),
            Some("my_type")
        );
    }

    #[test]
    fn test_extract_identifier_last_word() {
        assert_eq!(
            extract_identifier("Invalid node type invalid_node"),
            Some("invalid_node")
        );
        assert_eq!(extract_identifier("Unknown field name"), Some("name"));
    }

    #[test]
    fn test_get_error_suggestion_node_type() {
        let suggestion = get_error_suggestion(&QueryErrorKind::NodeType, "Invalid type 'foo'");
        assert!(suggestion.is_some());
        assert!(suggestion.unwrap().contains("foo"));
    }

    #[test]
    fn test_get_error_suggestion_syntax() {
        let suggestion = get_error_suggestion(&QueryErrorKind::Syntax, "");
        assert!(suggestion.is_some());
        assert!(suggestion.unwrap().contains("parentheses"));
    }
}
