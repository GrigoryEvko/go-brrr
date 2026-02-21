//! Shared helper functions for C++ safety checkers.

use std::collections::HashMap;

use tree_sitter::Node;

use crate::security::common::SourceLocation;

use super::rules::lookup_rule;
use super::types::CppSafetyFinding;

// =============================================================================
// Tree-sitter Queries
// =============================================================================

/// Find `new` expressions.
pub(super) const NEW_EXPR_QUERY: &str = "(new_expression) @expr";

/// Find `delete` expressions.
pub(super) const DELETE_EXPR_QUERY: &str = "(delete_expression) @expr";

/// Find `throw` statements.
pub(super) const THROW_QUERY: &str = "(throw_statement) @expr";

/// Find enum specifiers.
pub(super) const ENUM_QUERY: &str = "(enum_specifier) @enum_spec";

/// Find call expressions with identifier function names.
pub(super) const CALL_QUERY: &str = r#"
(call_expression
  function: (identifier) @func
  arguments: (argument_list) @args) @call
"#;

/// Find declarations without initializers (uninitialized locals).
pub(super) const UNINIT_VAR_QUERY: &str = r#"
(declaration
  type: (_) @type
  declarator: (identifier) @var
  !value) @decl
"#;

// =============================================================================
// Node Helpers
// =============================================================================

/// Get text content of a tree-sitter node.
pub(super) fn node_text<'a>(node: Node, source: &'a [u8]) -> &'a str {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
}

/// Build a SourceLocation from a tree-sitter node.
pub(super) fn location_from_node(node: Node, file_path: &str) -> SourceLocation {
    SourceLocation::new(
        file_path,
        node.start_position().row + 1,
        node.start_position().column + 1,
        node.end_position().row + 1,
        node.end_position().column + 1,
    )
}

/// Extract a code snippet around a line (1-indexed).
pub(super) fn snippet_at_line(source_str: &str, line: usize, context: usize) -> String {
    let lines: Vec<&str> = source_str.lines().collect();
    if lines.is_empty() || line == 0 {
        return String::new();
    }
    let idx = line.saturating_sub(1);
    let start = idx.saturating_sub(context);
    let end = (idx + context + 1).min(lines.len());
    lines[start..end].join("\n")
}

// =============================================================================
// Text Pattern Matching
// =============================================================================

/// A text search match with position.
pub(super) struct TextMatch {
    pub line: usize,
    pub column: usize,
    pub snippet: String,
}

/// Search source text for all non-comment occurrences of `pattern`.
pub(super) fn find_pattern(source: &str, pattern: &str) -> Vec<TextMatch> {
    let mut results = Vec::new();
    for (line_idx, line) in source.lines().enumerate() {
        let trimmed = line.trim();
        // Skip pure comment lines
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }
        let mut search_start = 0;
        while let Some(pos) = line[search_start..].find(pattern) {
            let abs_pos = search_start + pos;
            // Skip if preceded by a line comment on this line
            let before = &line[..abs_pos];
            if before.contains("//") {
                break;
            }
            results.push(TextMatch {
                line: line_idx + 1,
                column: abs_pos + 1,
                snippet: trimmed.to_string(),
            });
            search_start = abs_pos + pattern.len();
        }
    }
    results
}

// =============================================================================
// AST Traversal
// =============================================================================

/// Collect all AST nodes matching any of the given kinds.
pub(super) fn collect_nodes<'a>(node: Node<'a>, kinds: &[&str]) -> Vec<Node<'a>> {
    let mut results = Vec::new();
    collect_nodes_inner(node, kinds, &mut results);
    results
}

fn collect_nodes_inner<'a>(node: Node<'a>, kinds: &[&str], out: &mut Vec<Node<'a>>) {
    if kinds.contains(&node.kind()) {
        out.push(node);
    }
    for i in 0..node.child_count() {
        if let Some(child) = node.child(i as u32) {
            collect_nodes_inner(child, kinds, out);
        }
    }
}

// =============================================================================
// Finding Constructors
// =============================================================================

/// Create a finding from a rule ID and location.
pub(super) fn make_finding(
    rule_id: &str,
    location: SourceLocation,
    code_snippet: String,
) -> CppSafetyFinding {
    let rule = lookup_rule(rule_id).expect("Unknown rule ID");
    CppSafetyFinding {
        location,
        rule_id: rule_id.to_string(),
        axiom: rule.axiom,
        severity: rule.severity,
        confidence: rule.confidence,
        title: rule.title.to_string(),
        description: rule.description.to_string(),
        remediation: rule.remediation.to_string(),
        code_snippet,
        cwe_id: rule.cwe,
        metadata: HashMap::new(),
    }
}

/// Create a finding from a rule ID and a TextMatch.
pub(super) fn make_finding_from_text(rule_id: &str, file_path: &str, m: &TextMatch) -> CppSafetyFinding {
    let loc = SourceLocation::new(file_path, m.line, m.column, m.line, m.column + 1);
    make_finding(rule_id, loc, m.snippet.clone())
}

/// Check if a node is inside a function body (compound_statement under function_definition).
pub(super) fn is_inside_function(mut node: Node) -> bool {
    while let Some(parent) = node.parent() {
        if parent.kind() == "function_definition" || parent.kind() == "lambda_expression" {
            return true;
        }
        node = parent;
    }
    false
}
