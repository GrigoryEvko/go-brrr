//! D3390 §2.5.1 Pattern matching safety checks.
//!
//! Detects unsafe switch/case patterns:
//! - TSAF-006: switch on enum without default case
//! - TSAF-007: implicit fallthrough between cases
//! - TSAF-008: switch on boolean value
//! - TSAF-009: switch without default case

use crate::security::common::SourceLocation;

use super::helpers::make_finding;
use super::types::CppSafetyFinding;

/// Check for pattern matching safety violations in switch statements.
pub(super) fn check_pattern_match(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let lines: Vec<&str> = source_str.lines().collect();
    let switch_blocks = find_switch_blocks(&lines);

    for block in &switch_blocks {
        // TSAF-008: switch on bool
        check_switch_on_bool(block, &lines, file_path, findings);

        // TSAF-009: switch without default (and TSAF-006 for enum switches)
        check_switch_default(block, &lines, file_path, is_cpp, findings);

        // TSAF-007: implicit fallthrough
        check_fallthrough(block, &lines, file_path, findings);
    }
}

/// A switch block with its location and case ranges.
struct SwitchBlock {
    /// Line index of the `switch` keyword (0-indexed).
    switch_line: usize,
    /// The condition expression (between parens).
    condition: String,
    /// Line index of the opening `{`.
    body_start: usize,
    /// Line index of the closing `}`.
    body_end: usize,
}

/// A case/default label with its range.
struct CaseLabel {
    line: usize,
    is_default: bool,
    /// Line of the next case/default label or end of switch body.
    end_line: usize,
}

/// Find all switch blocks in source. Tracks brace nesting to find body boundaries.
fn find_switch_blocks(lines: &[&str]) -> Vec<SwitchBlock> {
    let mut blocks = Vec::new();

    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            i += 1;
            continue;
        }

        // Look for `switch` keyword followed by `(`
        if let Some(sw_pos) = trimmed.find("switch") {
            // Verify it's actually a keyword (not part of an identifier)
            let before = if sw_pos > 0 { &trimmed[..sw_pos] } else { "" };
            let after = &trimmed[sw_pos + 6..];
            let before_ok = before.is_empty()
                || before.ends_with(|c: char| !c.is_alphanumeric() && c != '_');
            let after_ok = after.starts_with(|c: char| c == '(' || c.is_whitespace());
            if !before_ok || !after_ok {
                i += 1;
                continue;
            }

            // Extract condition (may span multiple lines)
            let condition = extract_switch_condition(lines, i);

            // Find the opening brace
            let mut brace_line = i;
            while brace_line < lines.len() && !lines[brace_line].contains('{') {
                brace_line += 1;
            }
            if brace_line >= lines.len() {
                i += 1;
                continue;
            }

            // Find matching closing brace
            let body_end = find_matching_brace(lines, brace_line);
            if let Some(end) = body_end {
                blocks.push(SwitchBlock {
                    switch_line: i,
                    condition,
                    body_start: brace_line,
                    body_end: end,
                });
                i = end + 1;
            } else {
                i += 1;
            }
        } else {
            i += 1;
        }
    }

    blocks
}

/// Extract the condition expression from a switch statement.
fn extract_switch_condition(lines: &[&str], start_line: usize) -> String {
    let mut paren_depth = 0;
    let mut condition = String::new();
    let mut collecting = false;

    for i in start_line..lines.len().min(start_line + 5) {
        for c in lines[i].chars() {
            if c == '(' {
                if paren_depth == 0 {
                    collecting = true;
                    paren_depth += 1;
                    continue;
                }
                paren_depth += 1;
            } else if c == ')' {
                paren_depth -= 1;
                if paren_depth == 0 {
                    return condition.trim().to_string();
                }
            }
            if collecting && paren_depth > 0 {
                condition.push(c);
            }
        }
    }
    condition.trim().to_string()
}

/// Find the matching `}` for an opening `{`, accounting for nesting.
fn find_matching_brace(lines: &[&str], start_line: usize) -> Option<usize> {
    let mut depth = 0;
    for i in start_line..lines.len() {
        let trimmed = lines[i].trim();
        // Skip string literals and comments (rough)
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }
        for c in trimmed.chars() {
            if c == '{' {
                depth += 1;
            } else if c == '}' {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
        }
    }
    None
}

/// Find all case/default labels within a switch body.
fn find_case_labels(lines: &[&str], body_start: usize, body_end: usize) -> Vec<CaseLabel> {
    let mut labels = Vec::new();

    for i in (body_start + 1)..body_end {
        let trimmed = lines[i].trim();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        let is_case = trimmed.starts_with("case ") && trimmed.contains(':');
        let is_default = trimmed == "default:" || trimmed.starts_with("default:");

        if is_case || is_default {
            labels.push(CaseLabel {
                line: i,
                is_default,
                end_line: 0, // filled in below
            });
        }
    }

    // Set end_line for each label (to next label or body_end)
    for i in 0..labels.len() {
        labels[i].end_line = if i + 1 < labels.len() {
            labels[i + 1].line
        } else {
            body_end
        };
    }

    labels
}

/// TSAF-008: switch on boolean value.
fn check_switch_on_bool(
    block: &SwitchBlock,
    lines: &[&str],
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let cond = block.condition.trim();
    if cond == "true" || cond == "false" {
        let loc = SourceLocation::new(
            file_path,
            block.switch_line + 1,
            1,
            block.switch_line + 1,
            lines[block.switch_line].len(),
        );
        findings.push(make_finding(
            "TSAF-008",
            loc,
            lines[block.switch_line].trim().to_string(),
        ));
        return;
    }

    // Check if the condition variable is declared as bool in preceding lines
    let lookback = block.switch_line.saturating_sub(20);
    for i in lookback..block.switch_line {
        let l = lines[i].trim();
        if l.contains("bool") && l.contains(cond)
            && (l.contains('=') || l.contains(';') || l.contains('(') || l.contains(','))
        {
            let loc = SourceLocation::new(
                file_path,
                block.switch_line + 1,
                1,
                block.switch_line + 1,
                lines[block.switch_line].len(),
            );
            findings.push(make_finding(
                "TSAF-008",
                loc,
                lines[block.switch_line].trim().to_string(),
            ));
            return;
        }
    }
}

/// TSAF-006/TSAF-009: switch without default case.
fn check_switch_default(
    block: &SwitchBlock,
    lines: &[&str],
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let labels = find_case_labels(lines, block.body_start, block.body_end);
    let has_default = labels.iter().any(|l| l.is_default);

    if has_default {
        return;
    }

    // No default case — determine if this is an enum switch (TSAF-006) or generic (TSAF-009)
    let cond = &block.condition;
    let is_enum_switch = is_cpp && is_likely_enum_condition(cond, lines, block.switch_line);

    let rule_id = if is_enum_switch { "TSAF-006" } else { "TSAF-009" };

    let loc = SourceLocation::new(
        file_path,
        block.switch_line + 1,
        1,
        block.switch_line + 1,
        lines[block.switch_line].len(),
    );
    findings.push(make_finding(
        rule_id,
        loc,
        lines[block.switch_line].trim().to_string(),
    ));
}

/// Heuristic: is the switch condition likely an enum value?
fn is_likely_enum_condition(cond: &str, lines: &[&str], switch_line: usize) -> bool {
    // Check if the condition variable has `enum` in its declaration in lookback
    let cond_var = cond.trim();
    let lookback = switch_line.saturating_sub(30);
    for i in lookback..switch_line {
        let l = lines[i];
        if l.contains(cond_var)
            && (l.contains("enum") || l.contains("Kind") || l.contains("Type")
                || l.contains("State") || l.contains("Mode") || l.contains("Status"))
        {
            return true;
        }
    }
    // Check if case values look like enum constants (qualified names like Foo::Bar)
    for i in (switch_line + 1)..lines.len().min(switch_line + 30) {
        let trimmed = lines[i].trim();
        if trimmed.starts_with("case ") {
            if trimmed.contains("::") {
                return true;
            }
        }
        if trimmed.starts_with('}') {
            break;
        }
    }
    false
}

/// TSAF-007: implicit fallthrough detection.
fn check_fallthrough(
    block: &SwitchBlock,
    lines: &[&str],
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let labels = find_case_labels(lines, block.body_start, block.body_end);

    for (idx, label) in labels.iter().enumerate() {
        // Last case before `}` doesn't need a break
        if idx + 1 >= labels.len() {
            continue;
        }

        // Empty case (just label, no statements) — intentional grouping, skip
        let has_statements = (label.line + 1..label.end_line)
            .any(|i| {
                let t = lines[i].trim();
                !t.is_empty()
                    && !t.starts_with("//")
                    && !t.starts_with("/*")
                    && !t.starts_with('*')
                    && !t.starts_with("case ")
                    && !t.starts_with("default:")
            });
        if !has_statements {
            continue;
        }

        // Check if ANY line in the case body is a terminator (handles multi-line returns)
        let body_has_terminator = (label.line + 1..label.end_line).any(|i| {
            let t = lines[i].trim();
            if t.is_empty() || t.starts_with("//") || t.starts_with("/*") || t.starts_with('*') {
                return false;
            }
            is_terminator(t) || t.contains("[[fallthrough]]") || t.contains("/* fall")
        });
        if body_has_terminator {
            continue;
        }

        let last_stmt = find_last_statement(lines, label.line + 1, label.end_line);
        if last_stmt.is_some() {
            let loc = SourceLocation::new(
                file_path,
                label.line + 1,
                1,
                label.line + 1,
                lines[label.line].len(),
            );
            findings.push(make_finding(
                "TSAF-007",
                loc,
                lines[label.line].trim().to_string(),
            ));
        }
    }
}

/// Find the last non-empty, non-comment line in range [start, end).
fn find_last_statement(lines: &[&str], start: usize, end: usize) -> Option<usize> {
    for i in (start..end).rev() {
        let t = lines[i].trim();
        if !t.is_empty() && !t.starts_with("//") && !t.starts_with("/*") && !t.starts_with('*') {
            return Some(i);
        }
    }
    None
}

/// Check if a line is a case-terminating statement.
fn is_terminator(line: &str) -> bool {
    line.starts_with("break")
        || line.starts_with("return")
        || line.starts_with("continue")
        || line.starts_with("throw")
        || line.starts_with("goto ")
        || line.starts_with("exit(")
        || line.starts_with("abort(")
        || line.starts_with("std::abort(")
        || line.starts_with("std::exit(")
        || line.starts_with("std::unreachable(")
        || line.starts_with("__builtin_unreachable(")
        || line.contains("break;")
        || line.contains("return ")
        || line.contains("return;")
        || line.ends_with("break;")
}
