//! FST003: Comment syntax verification rule.
//!
//! Port of verify_comments.py's FStarCommentVerifier class.
//!
//! Detects common comment syntax issues in F* files:
//! 1. Unclosed (* comments that swallow code
//! 2. Premature *) that close comments too early
//! 3. Nested comment issues
//! 4. Common gotchas:
//!    - (*) asterisk operator descriptions
//!    - (-*) magic wand operator (separation logic)
//!    - (char*), (void*) C-style pointer casts
//!    - Any identifier*) pattern inside comments
//!
//! F* Comment Rules:
//! - (* text *) - regular block comment
//! - (** text *) - docstring
//! - Nested comments ARE allowed: (* outer (* inner *) outer *)
//! - DANGER: *) anywhere closes a comment level!

use lazy_static::lazy_static;
use regex::Regex;
use std::path::Path;

use super::rules::{Diagnostic, DiagnosticSeverity, Range, Rule, RuleCode};

/// Convert byte offset to character column (1-indexed).
///
/// Regex matches return byte offsets, but LSP column positions must be
/// character offsets for correct behavior with multibyte UTF-8 characters
/// (e.g., "Martínez" where 'í' is 2 bytes).
fn byte_to_char_col(s: &str, byte_offset: usize) -> usize {
    s[..byte_offset.min(s.len())].chars().count() + 1
}

lazy_static! {
    // Pattern for (*) which F* parses as unit value followed by star
    static ref UNIT_STAR_PATTERN: Regex = Regex::new(r"\(\*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern for (-*) magic wand operator from separation logic
    static ref MAGIC_WAND_PATTERN: Regex = Regex::new(r"\(-\*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern for C-style pointer casts like (char*), (void*), (int*)
    // Excludes F* operator definitions like (let*), (and*)
    static ref C_POINTER_PATTERN: Regex = Regex::new(r"\(([a-zA-Z_][a-zA-Z0-9_]*)\s*\*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    // F* operator names that look like pointer casts but aren't
    static ref FSTAR_OPERATORS: &'static [&'static str] = &[
        "let", "and", "or", "fun", "match", "if", "then", "else"
    ];

    // Pattern for suspicious close: word character followed by *)
    static ref SUSPICIOUS_CLOSE: Regex = Regex::new(r"[a-zA-Z0-9_]\*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern for empty comment blocks - requires whitespace to exclude (**)
    // (**) is a standard F* proof annotation idiom (empty doc comment) used
    // extensively in real-world F* code (e.g., 800+ occurrences in hacl-star)
    // to mark proof steps. Only flag (* *), (*  *), etc. with actual whitespace.
    static ref EMPTY_COMMENT: Regex = Regex::new(r"\(\*\s+\*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern for *) inside string literals
    static ref STRING_WITH_CLOSE: Regex = Regex::new(r#""[^"]*\*\)[^"]*""#).unwrap_or_else(|e| panic!("regex: {e}"));

    // Code keywords to detect "all commented" syndrome
    static ref CODE_KEYWORDS: &'static [&'static str] = &[
        "let ", "val ", "type ", "module ", "open ", "include "
    ];

    // FIX: Move patterns that were compiled in hot loops to lazy_static
    // Pattern to detect operator definition lookahead: (identifier*)
    static ref OPERATOR_DEF_LOOKAHEAD: Regex = Regex::new(r"^\([a-zA-Z_][a-zA-Z0-9_]*\*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern to detect operator definition lookback: (identifier
    static ref OPERATOR_DEF_LOOKBACK: Regex = Regex::new(r"\([a-zA-Z_][a-zA-Z0-9_]*$").unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern for suspicious close with context
    static ref SUSPICIOUS_CLOSE_WITH_CONTEXT: Regex = Regex::new(r"\([a-zA-Z_][a-zA-Z0-9_]*\*\)$").unwrap_or_else(|e| panic!("regex: {e}"));
}

/// Issue found during comment analysis.
#[derive(Debug, Clone)]
pub struct CommentIssue {
    pub line: usize,
    pub col: usize,
    pub issue_type: CommentIssueType,
    pub message: String,
    pub severity: IssueSeverity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommentIssueType {
    ReadError,
    UnclosedComment,
    PrematureClose,
    AsteriskOperatorPattern,
    MagicWandPattern,
    CPointerCastPattern,
    SuspiciousClosePattern,
    EmptyComment,
    AllCommented,
    CloseInString,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IssueSeverity {
    Critical,
    High,
    Medium,
    Low,
}

impl IssueSeverity {
    fn to_diagnostic_severity(self) -> DiagnosticSeverity {
        match self {
            // FIX: Critical should map to Error, not Warning
            // Critical issues like unclosed comments or premature closes
            // can break the entire file parsing
            IssueSeverity::Critical => DiagnosticSeverity::Error,
            IssueSeverity::High => DiagnosticSeverity::Warning,
            IssueSeverity::Medium => DiagnosticSeverity::Info,
            IssueSeverity::Low => DiagnosticSeverity::Hint,
        }
    }
}

/// FST003: Comment syntax verification.
pub struct CommentRule;

impl CommentRule {
    pub fn new() -> Self {
        Self
    }

    /// Analyze content for comment issues.
    pub fn analyze(&self, content: &str) -> Vec<CommentIssue> {
        let mut issues = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Count comment delimiters and check balance
        self.count_and_check_comments(content, &mut issues);

        // Compute per-line comment depth so pattern checks know context
        let line_depths = self.compute_line_comment_depths(content);

        // Check for problematic patterns (only inside comments where they matter)
        self.check_problematic_patterns(content, &lines, &line_depths, &mut issues);

        issues
    }

    /// Compute comment nesting depth at the START of each line.
    ///
    /// Returns a Vec where `result[i]` is the comment depth at the beginning
    /// of line `i` (0-indexed). Depth 0 means the line starts in code context.
    /// Depth > 0 means the line starts inside a nested block comment.
    fn compute_line_comment_depths(&self, content: &str) -> Vec<i32> {
        let chars: Vec<char> = content.chars().collect();
        let n = chars.len();
        let mut depths = Vec::new();

        let mut i = 0;
        let mut depth: i32 = 0;
        let mut in_string = false;
        let mut in_line_comment = false;

        // Depth at the start of line 1
        depths.push(depth);

        while i < n {
            let c = chars[i];

            if c == '\n' {
                in_line_comment = false;
                i += 1;
                // Record depth at start of next line
                depths.push(depth);
                continue;
            }

            if in_line_comment {
                i += 1;
                continue;
            }

            // String handling (mirrors count_and_check_comments logic)
            if c == '"' && !in_string {
                in_string = true;
                i += 1;
                continue;
            } else if c == '"' && in_string {
                let backslash_count = {
                    let mut count = 0;
                    let mut j = i;
                    while j > 0 {
                        j -= 1;
                        if chars[j] == '\\' {
                            count += 1;
                        } else {
                            break;
                        }
                    }
                    count
                };
                if backslash_count % 2 == 1 {
                    i += 1;
                    continue;
                }
                in_string = false;
                i += 1;
                continue;
            } else if in_string {
                i += 1;
                continue;
            }

            // Line comment (only outside block comments)
            if depth == 0 && c == '/' && i + 1 < n && chars[i + 1] == '/' {
                in_line_comment = true;
                i += 2;
                continue;
            }

            // Comment open (*
            if c == '(' && i + 1 < n && chars[i + 1] == '*' {
                // Skip (*) pattern
                if i + 2 < n && chars[i + 2] == ')' {
                    i += 3;
                    continue;
                }
                depth += 1;
                i += 2;
                continue;
            }

            // Comment close *)
            if c == '*' && i + 1 < n && chars[i + 1] == ')' {
                if depth > 0 {
                    depth -= 1;
                }
                i += 2;
                continue;
            }

            i += 1;
        }

        depths
    }

    /// Count comment delimiters accounting for strings and line comments.
    fn count_and_check_comments(&self, content: &str, issues: &mut Vec<CommentIssue>) {
        let chars: Vec<char> = content.chars().collect();
        let n = chars.len();

        let mut i = 0;
        let mut line = 1;
        let mut col = 1;
        let mut in_string = false;
        let mut in_line_comment = false;
        let mut depth: i32 = 0;

        // Track where unclosed comments start
        let mut unclosed_starts: Vec<(usize, usize)> = Vec::new();

        while i < n {
            let c = chars[i];

            // Track line/column
            if c == '\n' {
                line += 1;
                col = 1;
                in_line_comment = false;
                i += 1;
                continue;
            }

            // Inside line comment - skip
            if in_line_comment {
                i += 1;
                col += 1;
                continue;
            }

            // String handling
            if c == '"' && !in_string {
                in_string = true;
                i += 1;
                col += 1;
                continue;
            } else if c == '"' && in_string {
                // Check for escaped quote
                // FIX: Count consecutive backslashes to handle "\\" correctly
                // "path\\" followed by (* should NOT treat the (* as inside string
                // because \\ is an escaped backslash, not an escape for the quote
                let backslash_count = {
                    let mut count = 0;
                    let mut j = i;
                    while j > 0 {
                        j -= 1;
                        if chars[j] == '\\' {
                            count += 1;
                        } else {
                            break;
                        }
                    }
                    count
                };
                // Quote is escaped only if preceded by odd number of backslashes
                if backslash_count % 2 == 1 {
                    i += 1;
                    col += 1;
                    continue;
                }
                in_string = false;
                i += 1;
                col += 1;
                continue;
            } else if in_string {
                i += 1;
                col += 1;
                continue;
            }

            // Line comment - only when outside block comments
            // In F* (like OCaml), // inside (* *) is just text
            if depth == 0 && c == '/' && i + 1 < n && chars[i + 1] == '/' {
                in_line_comment = true;
                i += 2;
                col += 2;
                continue;
            }

            // Comment open (*
            if c == '(' && i + 1 < n && chars[i + 1] == '*' {
                // Check for (*) pattern
                if i + 2 < n && chars[i + 2] == ')' {
                    // This is (*) - skip, will be caught by pattern check
                    i += 3;
                    col += 3;
                    continue;
                }

                // Check for operator definition like (let*), (and*)
                let lookback: String = chars[i.saturating_sub(10)..i].iter().collect();
                let lookback = lookback.trim();
                if lookback.ends_with("let") || lookback.ends_with('=') {
                    // Look ahead for (identifier*)
                    let lookahead: String = chars[i..std::cmp::min(i + 15, n)].iter().collect();
                    // FIX: Use precompiled pattern instead of compiling in hot loop
                    if OPERATOR_DEF_LOOKAHEAD.is_match(&lookahead) {
                        // Operator definition, find end and skip
                        if let Some(end) = lookahead.find("*)") {
                            i += end + 2;
                            col += end + 2;
                            continue;
                        }
                    }
                }

                depth += 1;
                unclosed_starts.push((line, col));
                i += 2;
                col += 2;
                continue;
            }

            // Comment close *)
            if c == '*' && i + 1 < n && chars[i + 1] == ')' {
                // Skip if part of operator def
                let lookback: String = chars[i.saturating_sub(15)..i].iter().collect();
                // FIX: Use precompiled pattern instead of compiling in hot loop
                if OPERATOR_DEF_LOOKBACK.is_match(&lookback) {
                    i += 2;
                    col += 2;
                    continue;
                }

                if depth > 0 {
                    depth -= 1;
                    unclosed_starts.pop();
                } else {
                    // Closing without opening!
                    issues.push(CommentIssue {
                        line,
                        col,
                        issue_type: CommentIssueType::PrematureClose,
                        message: format!(
                            "*) closes comment but no comment is open (depth was {})",
                            depth
                        ),
                        severity: IssueSeverity::Critical,
                    });
                }
                i += 2;
                col += 2;
                continue;
            }

            i += 1;
            col += 1;
        }

        // Check for unclosed comments at end
        for (start_line, start_col) in unclosed_starts {
            issues.push(CommentIssue {
                line: start_line,
                col: start_col,
                issue_type: CommentIssueType::UnclosedComment,
                message: format!(
                    "(* opened at line {}:{} is never closed - swallowing {} lines!",
                    start_line,
                    start_col,
                    line - start_line
                ),
                severity: IssueSeverity::Critical,
            });
        }
    }

    /// Check for common problematic patterns.
    ///
    /// `line_depths` contains the comment nesting depth at the START of each
    /// line (0-indexed). Patterns like `(*)`, `(-*)`, and C pointer casts are
    /// only dangerous inside comments (where `*)` closes a comment level).
    /// In code context (depth 0), these are valid F* syntax.
    fn check_problematic_patterns(
        &self,
        _content: &str,
        lines: &[&str],
        line_depths: &[i32],
        issues: &mut Vec<CommentIssue>,
    ) {
        // Pattern 1: (*) - only dangerous INSIDE comments where *) closes a level.
        // In code, (*) is valid F* syntax (e.g., multiplication operator in parens).
        for (line_num, line) in lines.iter().enumerate() {
            // Only flag if line starts inside a comment
            let depth = line_depths.get(line_num).copied().unwrap_or(0);
            if depth == 0 {
                // In code context: (*) is valid F* syntax, not a problem.
                // However, if (* appears before (*) on this line, it could still
                // be inside a comment that opened on this same line.
                if let Some(m) = UNIT_STAR_PATTERN.find(line) {
                    let before = &line[..m.start()];
                    let opens_before = before.matches("(*").count();
                    let closes_before = before.matches("*)").count();
                    if opens_before <= closes_before {
                        continue; // Truly in code context, skip
                    }
                } else {
                    continue;
                }
            }
            let line_num = line_num + 1;
            if let Some(m) = UNIT_STAR_PATTERN.find(line) {
                issues.push(CommentIssue {
                    line: line_num,
                    col: byte_to_char_col(line, m.start()),
                    issue_type: CommentIssueType::AsteriskOperatorPattern,
                    message: "'(*)' found inside comment - this closes and reopens the comment! May be describing * operator. Use '(star)' instead.".to_string(),
                    severity: IssueSeverity::High,
                });
            }
        }

        // Pattern 2: (-*) - magic wand operator, only dangerous inside comments
        for (line_num, line) in lines.iter().enumerate() {
            let depth = line_depths.get(line_num).copied().unwrap_or(0);
            if depth == 0 {
                if let Some(m) = MAGIC_WAND_PATTERN.find(line) {
                    let before = &line[..m.start()];
                    let opens_before = before.matches("(*").count();
                    let closes_before = before.matches("*)").count();
                    if opens_before <= closes_before {
                        continue;
                    }
                } else {
                    continue;
                }
            }
            let line_num = line_num + 1;
            if let Some(m) = MAGIC_WAND_PATTERN.find(line) {
                issues.push(CommentIssue {
                    line: line_num,
                    col: byte_to_char_col(line, m.start()),
                    issue_type: CommentIssueType::MagicWandPattern,
                    message: "'(-*)' found inside comment - the '*)' closes a comment level! Use '(wand)' or '(dash-star)' instead.".to_string(),
                    severity: IssueSeverity::High,
                });
            }
        }

        // Pattern 3: C-style pointer casts like (char*), (void*)
        // Only dangerous inside comments where *) closes a comment level.
        for (line_num, line) in lines.iter().enumerate() {
            let depth = line_depths.get(line_num).copied().unwrap_or(0);
            let line_num = line_num + 1;
            for caps in C_POINTER_PATTERN.captures_iter(line) {
                if let Some(ident) = caps.get(1) {
                    let identifier = ident.as_str();
                    // Skip F* operator definitions
                    if FSTAR_OPERATORS.contains(&identifier) {
                        continue;
                    }
                    let Some(full_match) = caps.get(0) else { continue };
                    // Skip if it looks like a let binding
                    let match_start = full_match.start();
                    let context_start = match_start.saturating_sub(10);
                    let context_before = &line[context_start..match_start];
                    let context_before = context_before.trim();
                    if context_before.ends_with("let") || context_before.ends_with('=') {
                        continue;
                    }

                    // Only flag inside comments
                    if depth == 0 {
                        let before = &line[..match_start];
                        let opens_before = before.matches("(*").count();
                        let closes_before = before.matches("*)").count();
                        if opens_before <= closes_before {
                            continue; // In code context, skip
                        }
                    }

                    issues.push(CommentIssue {
                        line: line_num,
                        col: byte_to_char_col(line, match_start),
                        issue_type: CommentIssueType::CPointerCastPattern,
                        message: format!(
                            "'{}' found inside comment - C pointer syntax with '*)' closes a comment level! Use 'type pointer' instead.",
                            full_match.as_str()
                        ),
                        severity: IssueSeverity::High,
                    });
                }
            }
        }

        // Pattern 4: Suspicious close - word char followed by *)
        for (line_num, line) in lines.iter().enumerate() {
            let line_num = line_num + 1;

            // Count (* and *) on this line - if balanced, skip
            let line_opens = line.matches("(*").count();
            let line_closes = line.matches("*)").count();
            if line_opens == line_closes && line_opens > 0 {
                continue;
            }

            for m in SUSPICIOUS_CLOSE.find_iter(line) {
                // Skip if already caught by C_POINTER_PATTERN
                let context_start = m.start().saturating_sub(15);
                let context = &line[context_start..m.end()];
                // FIX: Use precompiled pattern instead of compiling in hot loop
                if SUSPICIOUS_CLOSE_WITH_CONTEXT.is_match(context) {
                    continue;
                }

                // Skip if there's a matching (* before this *) on same line
                let before = &line[..m.start()];
                let opens_before = before.matches("(*").count();
                let closes_before = before.matches("*)").count();
                if opens_before > closes_before {
                    continue;
                }

                // Check if it looks like it's inside a comment
                if before.contains("(*")
                    || before.trim().starts_with('*')
                    || before.trim().is_empty()
                {
                    issues.push(CommentIssue {
                        line: line_num,
                        col: byte_to_char_col(line, m.start()),
                        issue_type: CommentIssueType::SuspiciousClosePattern,
                        message: format!(
                            "'...{}' may close comment prematurely. Check if inside comment block.",
                            m.as_str()
                        ),
                        severity: IssueSeverity::Medium,
                    });
                }
            }
        }

        // Pattern 5: Empty comment blocks
        for (line_num, line) in lines.iter().enumerate() {
            let line_num = line_num + 1;
            if EMPTY_COMMENT.is_match(line) {
                if let Some(m) = line.find("(*") {
                    issues.push(CommentIssue {
                        line: line_num,
                        col: byte_to_char_col(line, m),
                        issue_type: CommentIssueType::EmptyComment,
                        message: "Empty comment block (* *) - intentional?".to_string(),
                        severity: IssueSeverity::Low,
                    });
                }
            }
        }

        // Pattern 6: Very long runs without any code
        if lines.len() > 100 {
            let mut has_code = false;
            let mut comment_depth: i32 = 0;

            for line in lines {
                // Track comment state (simplified) - use matches() for UTF-8 safety
                let opens = line.matches("(*").count() as i32;
                let closes = line.matches("*)").count() as i32;
                comment_depth += opens - closes;
                comment_depth = std::cmp::max(0, comment_depth);

                // Only check for keywords outside comments
                if comment_depth == 0 {
                    for kw in CODE_KEYWORDS.iter() {
                        if line.contains(kw) && !line.trim().starts_with("//") {
                            has_code = true;
                            break;
                        }
                    }
                }
                if has_code {
                    break;
                }
            }

            if !has_code {
                issues.push(CommentIssue {
                    line: 1,
                    col: 1,
                    issue_type: CommentIssueType::AllCommented,
                    message: format!(
                        "File has {} lines but no code keywords found outside comments - possibly all commented out!",
                        lines.len()
                    ),
                    severity: IssueSeverity::Critical,
                });
            }
        }

        // Pattern 7: *) inside string literals
        for (line_num, line) in lines.iter().enumerate() {
            let line_num = line_num + 1;
            if STRING_WITH_CLOSE.is_match(line) {
                issues.push(CommentIssue {
                    line: line_num,
                    col: 1,
                    issue_type: CommentIssueType::CloseInString,
                    message: "String contains '*)', might cause issues if string parsing fails."
                        .to_string(),
                    severity: IssueSeverity::Medium,
                });
            }
        }
    }
}

impl Default for CommentRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for CommentRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST003
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let issues = self.analyze(content);

        issues
            .into_iter()
            .map(|issue| Diagnostic {
                rule: RuleCode::FST003,
                severity: issue.severity.to_diagnostic_severity(),
                file: file.to_path_buf(),
                range: Range::point(issue.line, issue.col),
                message: issue.message,
                fix: None,
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unclosed_comment() {
        let rule = CommentRule::new();
        let content = "(* this comment is not closed\nlet x = 1";
        let issues = rule.analyze(content);
        assert!(issues
            .iter()
            .any(|i| i.issue_type == CommentIssueType::UnclosedComment));
    }

    #[test]
    fn test_premature_close() {
        let rule = CommentRule::new();
        let content = "let x = 1 *)";
        let issues = rule.analyze(content);
        assert!(issues
            .iter()
            .any(|i| i.issue_type == CommentIssueType::PrematureClose));
    }

    #[test]
    fn test_unit_star_pattern() {
        let rule = CommentRule::new();
        let content = "(* describing (*) operator *)";
        let issues = rule.analyze(content);
        assert!(issues
            .iter()
            .any(|i| i.issue_type == CommentIssueType::AsteriskOperatorPattern));
    }

    #[test]
    fn test_nested_comments_ok() {
        let rule = CommentRule::new();
        let content = "(* outer (* inner *) still outer *)";
        let issues = rule.analyze(content);
        // Should not have unclosed/premature issues
        assert!(!issues
            .iter()
            .any(|i| i.issue_type == CommentIssueType::UnclosedComment));
        assert!(!issues
            .iter()
            .any(|i| i.issue_type == CommentIssueType::PrematureClose));
    }

    #[test]
    fn test_string_not_comment() {
        let rule = CommentRule::new();
        let content = r#"let s = "(*) this is a string""#;
        let issues = rule.analyze(content);
        // Should not report asterisk pattern inside string as critical
        assert!(!issues
            .iter()
            .any(|i| i.issue_type == CommentIssueType::UnclosedComment));
    }

    #[test]
    fn test_escaped_backslash_in_string() {
        let rule = CommentRule::new();
        // FIX: "path\\" followed by (* should detect the comment correctly
        // because \\ is an escaped backslash, not an escape for the quote
        let content = r#"let path = "C:\\Users\\" (* this is a real comment *)"#;
        let issues = rule.analyze(content);
        // Should NOT report unclosed comment
        assert!(!issues
            .iter()
            .any(|i| i.issue_type == CommentIssueType::UnclosedComment));
        assert!(!issues
            .iter()
            .any(|i| i.issue_type == CommentIssueType::PrematureClose));
    }

    #[test]
    fn test_escaped_quote_in_string() {
        let rule = CommentRule::new();
        // Single backslash escapes the quote - string continues
        let content = r#"let s = "escaped \" quote" (* comment *)"#;
        let issues = rule.analyze(content);
        assert!(!issues
            .iter()
            .any(|i| i.issue_type == CommentIssueType::UnclosedComment));
    }

    #[test]
    fn test_utf8_column_offset() {
        let rule = CommentRule::new();
        // Put (*) inside a comment so the pattern check fires.
        // "Martínez" has 8 characters but 9 bytes ('í' is 2 bytes in UTF-8)
        let content = "(* Martínez (*) *)";
        let issues = rule.analyze(content);
        let asterisk_issue = issues
            .iter()
            .find(|i| i.issue_type == CommentIssueType::AsteriskOperatorPattern)
            .expect("Should find (*) pattern inside comment");
        // "Martínez " inside the comment: "(* " = 3 chars, then "Martínez " = 9 chars
        // (*) starts at character position 13 (12 chars before + 1 for 1-indexing)
        // Byte offset of (*) = 3 + 9(Martínez) + 1(space) + 1(extra byte for í) = 14
        // Character offset = 3 + 9 + 1 = 13, so col = 13 (char-based, 1-indexed)
        assert_eq!(
            asterisk_issue.col, 13,
            "Column should be character offset, not byte offset"
        );
    }

    #[test]
    fn test_byte_to_char_col_helper() {
        // Test the helper function directly
        assert_eq!(byte_to_char_col("hello", 0), 1); // First char is col 1
        assert_eq!(byte_to_char_col("hello", 5), 6); // After "hello" (5 chars + 1)
        assert_eq!(byte_to_char_col("Martínez", 0), 1); // First char
                                                        // "Martí" = bytes 0-5 (6 bytes), 5 chars, so col = 6
        assert_eq!(byte_to_char_col("Martínez", 6), 6); // After "Martí" (5 chars + 1)
                                                        // Full string "Martínez" = 9 bytes, 8 chars, so col = 9
        assert_eq!(byte_to_char_col("Martínez", 9), 9); // After full string (8 chars + 1)
    }

    // =========================================================================
    // FALSE POSITIVE REGRESSION TESTS
    // =========================================================================

    #[test]
    fn test_double_star_proof_annotation_not_flagged() {
        // (**) is a standard F* proof annotation idiom (empty doc comment).
        // Used extensively in hacl-star (800+ occurrences) to mark proof steps.
        // Must NOT be flagged as EmptyComment.
        let rule = CommentRule::new();
        let content = "(**) let blocks = n * l in\n(**) assert(x > 0);\n(**) Math.Lemmas.foo bar;";
        let issues = rule.analyze(content);
        assert!(
            !issues
                .iter()
                .any(|i| i.issue_type == CommentIssueType::EmptyComment),
            "(**) proof annotation should not be flagged as empty comment"
        );
    }

    #[test]
    fn test_empty_comment_with_space_still_flagged() {
        // (* *) with actual whitespace should still be flagged (Low severity)
        let rule = CommentRule::new();
        let content = "let x = 1\n(* *)\nlet y = 2";
        let issues = rule.analyze(content);
        assert!(
            issues
                .iter()
                .any(|i| i.issue_type == CommentIssueType::EmptyComment),
            "(* *) with whitespace should still be flagged"
        );
    }

    #[test]
    fn test_asterisk_in_code_not_flagged() {
        // (*) in code is valid F* syntax: multiplication operator in parens
        let rule = CommentRule::new();
        let content = "let mul = (*) in mul 3 4";
        let issues = rule.analyze(content);
        assert!(
            !issues
                .iter()
                .any(|i| i.issue_type == CommentIssueType::AsteriskOperatorPattern),
            "(*) in code context should not be flagged - it's valid F* multiplication"
        );
    }

    #[test]
    fn test_asterisk_inside_comment_flagged() {
        // (*) inside a comment is dangerous - it closes and reopens
        let rule = CommentRule::new();
        let content = "(* the (*) operator is multiplication *)";
        let issues = rule.analyze(content);
        assert!(
            issues
                .iter()
                .any(|i| i.issue_type == CommentIssueType::AsteriskOperatorPattern),
            "(*) inside a comment should be flagged"
        );
    }

    #[test]
    fn test_asterisk_inside_multiline_comment_flagged() {
        // (*) on a line that starts inside a multi-line comment
        let rule = CommentRule::new();
        let content = "(* this is a multi-line comment\n   describing the (*) operator\n*)";
        let issues = rule.analyze(content);
        assert!(
            issues
                .iter()
                .any(|i| i.issue_type == CommentIssueType::AsteriskOperatorPattern),
            "(*) on a line inside multi-line comment should be flagged"
        );
    }

    #[test]
    fn test_magic_wand_in_code_not_flagged() {
        // (-*) in code context should not be flagged
        let rule = CommentRule::new();
        let content = "let wand = (-*) in wand p q";
        let issues = rule.analyze(content);
        assert!(
            !issues
                .iter()
                .any(|i| i.issue_type == CommentIssueType::MagicWandPattern),
            "(-*) in code context should not be flagged"
        );
    }

    #[test]
    fn test_magic_wand_inside_comment_flagged() {
        // (-*) inside a comment is dangerous
        let rule = CommentRule::new();
        let content = "(* the (-*) magic wand operator *)";
        let issues = rule.analyze(content);
        assert!(
            issues
                .iter()
                .any(|i| i.issue_type == CommentIssueType::MagicWandPattern),
            "(-*) inside a comment should be flagged"
        );
    }

    #[test]
    fn test_let_star_operator_not_flagged() {
        // let (let*) = ... is a valid F* operator definition
        let rule = CommentRule::new();
        let content = "let (let*) (#a:Type) (#b:Type) (m:st a) (f:a -> st b) : st b = f m";
        let issues = rule.analyze(content);
        assert!(
            !issues
                .iter()
                .any(|i| i.issue_type == CommentIssueType::UnclosedComment
                    || i.issue_type == CommentIssueType::PrematureClose),
            "let (let*) operator definition should not cause nesting errors"
        );
    }

    #[test]
    fn test_c_pointer_in_code_not_flagged() {
        // (char*) in code context should not be flagged
        let rule = CommentRule::new();
        let content = "let cast = (char*) ptr";
        let issues = rule.analyze(content);
        assert!(
            !issues
                .iter()
                .any(|i| i.issue_type == CommentIssueType::CPointerCastPattern),
            "(char*) in code context should not be flagged"
        );
    }

    #[test]
    fn test_c_pointer_inside_comment_flagged() {
        // (char*) inside a comment is dangerous
        let rule = CommentRule::new();
        let content = "(* cast to (char*) for C interop *)";
        let issues = rule.analyze(content);
        assert!(
            issues
                .iter()
                .any(|i| i.issue_type == CommentIssueType::CPointerCastPattern),
            "(char*) inside a comment should be flagged"
        );
    }

    #[test]
    fn test_line_depth_tracking() {
        // Verify compute_line_comment_depths works correctly
        let rule = CommentRule::new();
        let content = "code line\n(* start comment\n  inside comment\n*)\nback to code";
        let depths = rule.compute_line_comment_depths(content);
        assert_eq!(depths[0], 0, "Line 1 should be depth 0 (code)");
        assert_eq!(depths[1], 0, "Line 2 starts at depth 0 (comment opens on this line)");
        assert_eq!(depths[2], 1, "Line 3 should be depth 1 (inside comment)");
        assert_eq!(depths[3], 1, "Line 4 starts at depth 1 (close is on this line)");
        assert_eq!(depths[4], 0, "Line 5 should be depth 0 (back to code)");
    }

    #[test]
    fn test_nested_depth_tracking() {
        let rule = CommentRule::new();
        let content = "(* outer\n(* inner\n*)\nstill outer\n*)";
        let depths = rule.compute_line_comment_depths(content);
        assert_eq!(depths[0], 0, "Line 1 starts at depth 0");
        assert_eq!(depths[1], 1, "Line 2 starts at depth 1");
        assert_eq!(depths[2], 2, "Line 3 starts at depth 2 (nested)");
        assert_eq!(depths[3], 1, "Line 4 back to depth 1");
        assert_eq!(depths[4], 1, "Line 5 starts at depth 1");
    }
}
