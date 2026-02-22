//! F* language trap rules (FST020–FST051).
//!
//! These rules detect common F* pitfalls that trip up newcomers and LLMs alike.
//! Currently implements:
//!
//! - **FST020**: `(f: a -> b)` in a `val` declaration parses as `(f:a) -> b`.
//!   The fix is to double-wrap: `(f: (a -> b))`.
//!
//! - **FST027**: Arithmetic `*` used without `open FStar.Mul`. In F*, `*` defaults
//!   to the tuple type constructor (`int * int` is a pair). You must
//!   `open FStar.Mul` to use `*` as integer multiplication.
//!
//! - **FST042**: `Lemma (post)` without `ensures` is ambiguous. In F*, bare
//!   `Lemma (P)` desugars to `Lemma (requires P) (ensures fun _ -> True)` —
//!   the opposite of what most users intend. Use `Lemma (ensures P)` instead.

use lazy_static::lazy_static;
use regex::Regex;
use std::path::Path;

use super::rules::{Diagnostic, DiagnosticSeverity, Edit, Fix, FixConfidence, Range, Rule, RuleCode};

lazy_static! {
    /// Matches `open FStar.Mul` (with optional leading whitespace).
    static ref OPEN_MUL_RE: Regex =
        Regex::new(r"(?m)^\s*open\s+FStar\.Mul\s*$")
            .unwrap_or_else(|e| panic!("FST027 regex: {e}"));

    /// Matches any `open ...` statement (used to find insertion point for the fix).
    static ref OPEN_STMT_RE: Regex =
        Regex::new(r"(?m)^\s*open\s+")
            .unwrap_or_else(|e| panic!("FST027 regex: {e}"));

    /// Matches `module ...` declaration (fallback insertion point).
    static ref MODULE_DECL_RE: Regex =
        Regex::new(r"(?m)^\s*module\s+")
            .unwrap_or_else(|e| panic!("FST027 regex: {e}"));

    /// Matches `*` between two value-like tokens in expression context.
    ///
    /// Value-like tokens: identifiers, numeric literals, closing parens/brackets.
    /// This deliberately excludes type-position `*` (e.g., `int * string` in
    /// `val` or `type` declarations) by only firing in expression bodies.
    ///
    /// Pattern: `<value_token> * <value_token>` where value_token is:
    ///   - identifier (lowercase start, or _)
    ///   - numeric literal (digit start)
    ///   - closing delimiter: ) or ]
    static ref MUL_EXPR_RE: Regex =
        Regex::new(r"(?:(?:[a-z_][a-zA-Z0-9_']*|\d[\d_]*(?:\.\d+)?|[)\]]))\s*\*\s*(?:[a-z_][a-zA-Z0-9_']*|\d[\d_]*(?:\.\d+)?|[(\[])")
            .unwrap_or_else(|e| panic!("FST027 regex: {e}"));
}

/// FST027: Detect arithmetic `*` without `open FStar.Mul`.
pub struct MissingMulOpenRule;

impl MissingMulOpenRule {
    pub fn new() -> Self {
        Self
    }
}

/// Line-level context classification for `*` disambiguation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LineContext {
    /// Inside a type declaration body (`type ... =`)
    TypeDecl,
    /// Inside a `val` signature (after `:`)
    ValSignature,
    /// Inside an expression body (let binding RHS, assert, ensures, requires)
    ExprBody,
    /// Ambiguous or unknown context
    Unknown,
}

impl Rule for MissingMulOpenRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST027
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        // If `open FStar.Mul` is already present, nothing to report.
        if OPEN_MUL_RE.is_match(content) {
            return Vec::new();
        }

        // Single-pass scan: look for `*` in expression contexts.
        let mut found_mul_line: Option<(usize, usize)> = None; // (line_number, col)
        let mut in_block_comment = 0u32; // nesting depth
        let mut in_val_block = false;
        let mut in_type_block = false;
        // Track brace depth for `let ... = EXPR` bodies
        let mut after_equals = false;

        for (line_idx, line) in content.lines().enumerate() {
            let trimmed = line.trim();

            // Track block comment nesting (simplified — doesn't handle strings)
            let mut chars = line.char_indices().peekable();
            let mut line_has_mul = false;
            let mut mul_col: usize = 0;

            // Detect top-level context from line start
            let ctx = classify_line_context(trimmed, in_val_block, in_type_block, after_equals);

            match ctx {
                LineContext::ValSignature => {
                    in_val_block = true;
                    in_type_block = false;
                }
                LineContext::TypeDecl => {
                    in_type_block = true;
                    in_val_block = false;
                }
                LineContext::ExprBody => {
                    in_val_block = false;
                    in_type_block = false;
                }
                LineContext::Unknown => {}
            }

            // Reset val/type block at blank lines or new top-level declarations
            if trimmed.is_empty()
                || trimmed.starts_with("let ")
                || trimmed.starts_with("let rec ")
                || trimmed.starts_with("and ")
            {
                in_val_block = false;
                in_type_block = false;
            }

            // Track `=` for let binding RHS detection
            if trimmed.starts_with("let ") || trimmed.starts_with("let rec ") {
                after_equals = trimmed.contains('=');
                in_val_block = false;
                in_type_block = false;
            } else if trimmed.starts_with("val ") {
                after_equals = false;
                in_val_block = true;
                in_type_block = false;
            } else if trimmed.starts_with("type ") || trimmed.starts_with("noeq type ")
                || trimmed.starts_with("unopteq type ")
            {
                after_equals = false;
                in_type_block = true;
                in_val_block = false;
            }

            // Scan characters for `*` outside comments and strings
            while let Some(&(byte_idx, ch)) = chars.peek() {
                chars.next();

                match ch {
                    '(' => {
                        // Check for (* comment open
                        if let Some(&(_, '*')) = chars.peek() {
                            chars.next();
                            in_block_comment += 1;
                        }
                    }
                    '*' if in_block_comment > 0 => {
                        // Check for *) comment close
                        if let Some(&(_, ')')) = chars.peek() {
                            chars.next();
                            in_block_comment = in_block_comment.saturating_sub(1);
                        }
                    }
                    '"' if in_block_comment == 0 => {
                        // Skip string literal contents
                        while let Some(&(_, sc)) = chars.peek() {
                            chars.next();
                            if sc == '\\' {
                                // Skip escaped character
                                chars.next();
                            } else if sc == '"' {
                                break;
                            }
                        }
                    }
                    '/' if in_block_comment == 0 => {
                        // Check for // line comment
                        if let Some(&(_, '/')) = chars.peek() {
                            break; // rest of line is comment
                        }
                    }
                    '*' if in_block_comment == 0 => {
                        // Found a `*` outside comments — check if it's in expression context
                        if is_expr_context(trimmed, in_val_block, in_type_block) {
                            // Check surrounding characters for multiplication pattern
                            let before = &line[..byte_idx];
                            // Get the rest after `*`
                            let after_star = if byte_idx + 1 < line.len() {
                                &line[byte_idx + 1..]
                            } else {
                                ""
                            };

                            if looks_like_multiplication(before.trim_end(), after_star.trim_start())
                            {
                                line_has_mul = true;
                                mul_col = byte_to_char_col(line, byte_idx);
                            }
                        }
                    }
                    _ => {}
                }
            }

            if line_has_mul && found_mul_line.is_none() {
                found_mul_line = Some((line_idx + 1, mul_col)); // 1-indexed
            }
        }

        let Some((diag_line, diag_col)) = found_mul_line else {
            return Vec::new();
        };

        // Build the auto-fix: insert `open FStar.Mul` after the last `open` statement
        let fix = build_autofix(file, content);

        vec![Diagnostic {
            rule: RuleCode::FST027,
            severity: DiagnosticSeverity::Warning,
            file: file.to_path_buf(),
            range: Range::new(diag_line, diag_col, diag_line, diag_col + 1),
            message: "`*` is the tuple type constructor by default in F*. \
                      Add `open FStar.Mul` to use `*` as integer multiplication."
                .to_string(),
            fix: Some(fix),
        }]
    }
}

/// Convert byte offset to 1-indexed character column.
fn byte_to_char_col(s: &str, byte_offset: usize) -> usize {
    s[..byte_offset.min(s.len())].chars().count() + 1
}

/// Classify the line-level context to distinguish type positions from expression positions.
fn classify_line_context(
    trimmed: &str,
    in_val_block: bool,
    in_type_block: bool,
    _after_equals: bool,
) -> LineContext {
    if trimmed.starts_with("val ") || trimmed.starts_with("assume val ") {
        return LineContext::ValSignature;
    }
    if trimmed.starts_with("type ")
        || trimmed.starts_with("noeq type ")
        || trimmed.starts_with("unopteq type ")
    {
        return LineContext::TypeDecl;
    }
    if trimmed.starts_with("let ")
        || trimmed.starts_with("let rec ")
        || trimmed.starts_with("assert")
        || trimmed.starts_with("assume (")
    {
        return LineContext::ExprBody;
    }
    // Continuation lines inherit parent context
    if in_val_block {
        return LineContext::ValSignature;
    }
    if in_type_block {
        return LineContext::TypeDecl;
    }

    // Expression-like keywords in continuation
    if trimmed.starts_with("ensures")
        || trimmed.starts_with("requires")
        || trimmed.starts_with("decreases")
        || trimmed.starts_with("=")
    {
        return LineContext::ExprBody;
    }

    LineContext::Unknown
}

/// Check if the current line is in an expression context where `*` would be multiplication.
fn is_expr_context(trimmed: &str, in_val: bool, in_type: bool) -> bool {
    // Definitely NOT multiplication in val/type positions
    if in_val || in_type {
        return false;
    }

    // Expression contexts
    if trimmed.starts_with("let ")
        || trimmed.starts_with("let rec ")
        || trimmed.starts_with("assert")
        || trimmed.starts_with("assume (")
        || trimmed.starts_with("ensures")
        || trimmed.starts_with("requires")
        || trimmed.starts_with("decreases")
        || trimmed.starts_with("calc ")
    {
        return true;
    }

    // Lines starting with `=` are RHS of let bindings
    if trimmed.starts_with('=') {
        return true;
    }

    // Continuation lines with expression-like content (indented, not starting with type keywords)
    if !trimmed.starts_with("val ")
        && !trimmed.starts_with("type ")
        && !trimmed.starts_with("open ")
        && !trimmed.starts_with("module ")
        && !trimmed.starts_with("include ")
        && !trimmed.starts_with("friend ")
        && !trimmed.starts_with("noeq ")
        && !trimmed.starts_with("unopteq ")
        && !trimmed.starts_with("->")
        && !trimmed.starts_with(":")
        && !trimmed.is_empty()
    {
        // Could be expression continuation — check with regex
        return MUL_EXPR_RE.is_match(trimmed);
    }

    false
}

/// Heuristic: does the `*` look like multiplication based on surrounding tokens?
///
/// Multiplication: `x * y`, `n * 2`, `(a + b) * c`, `foo * bar`
/// Tuple: `int * string`, `nat * bool` (uppercase-starting type names)
fn looks_like_multiplication(before: &str, after: &str) -> bool {
    let before_token = last_token(before);
    let after_token = first_token(after);

    // If both sides are empty, not multiplication
    if before_token.is_empty() || after_token.is_empty() {
        return false;
    }

    // Strip leading/trailing delimiters to get the core identifier.
    // E.g., "(x" → "x", "y)" → "y"
    let before_core = before_token.trim_start_matches(|c: char| c == '(' || c == '[');
    let after_core = after_token.trim_end_matches(|c: char| c == ')' || c == ']');

    // Use the core for type-name classification, but keep originals for delimiter checks
    let before_ident = if before_core.is_empty() { before_token } else { before_core };
    let after_ident = if after_core.is_empty() { after_token } else { after_core };

    let before_first_char = before_ident.chars().next().unwrap_or(' ');
    let after_first_char = after_ident.chars().next().unwrap_or(' ');

    // Both uppercase → tuple type (e.g., `Nat * Bool`)
    if before_first_char.is_ascii_uppercase() && after_first_char.is_ascii_uppercase() {
        return false;
    }

    // Known F* type names that start lowercase
    let type_names = [
        "int", "nat", "pos", "bool", "string", "unit", "list", "option", "either",
        "uint8", "uint16", "uint32", "uint64", "int8", "int16", "int32", "int64",
        "byte", "bytes",
    ];

    // If BOTH sides are type names → likely tuple
    let before_is_type = type_names.contains(&before_ident);
    let after_is_type = type_names.contains(&after_ident);
    if before_is_type && after_is_type {
        return false;
    }

    // Numeric literals on either side → definitely multiplication
    if before_first_char.is_ascii_digit() || after_first_char.is_ascii_digit() {
        return true;
    }

    // Closing delimiters before `*` → multiplication (e.g., `(x+1) * y`)
    if before_token.ends_with(')') || before_token.ends_with(']') {
        return true;
    }

    // Opening delimiters after `*` → multiplication (e.g., `x * (y+1)`)
    if after_token.starts_with('(') || after_token.starts_with('[') {
        return true;
    }

    // Lowercase identifier on both sides in expression context → multiplication
    if before_first_char.is_ascii_lowercase() || before_first_char == '_' {
        if after_first_char.is_ascii_lowercase()
            || after_first_char == '_'
            || after_first_char == '('
        {
            return true;
        }
    }

    false
}

/// Extract the last whitespace-delimited token from a string.
fn last_token(s: &str) -> &str {
    s.split_whitespace().next_back().unwrap_or("")
}

/// Extract the first whitespace-delimited token from a string.
fn first_token(s: &str) -> &str {
    s.split_whitespace().next().unwrap_or("")
}

/// Build an auto-fix that inserts `open FStar.Mul` at the correct position.
fn build_autofix(file: &Path, content: &str) -> Fix {
    let insert_line = find_insertion_line(content);

    Fix {
        message: "Add `open FStar.Mul` to enable `*` as multiplication".to_string(),
        edits: vec![Edit {
            file: file.to_path_buf(),
            range: Range::point(insert_line, 1),
            new_text: "open FStar.Mul\n".to_string(),
        }],
        confidence: FixConfidence::High,
        unsafe_reason: None,
        safety_level: super::rules::FixSafetyLevel::Safe,
        reversible: true,
        requires_review: false,
    }
}

/// Find the 1-indexed line number where `open FStar.Mul` should be inserted.
///
/// Strategy:
/// 1. After the last `open ...` statement in the file
/// 2. If no opens exist, after the `module ...` declaration
/// 3. If neither exists, line 1 (top of file)
fn find_insertion_line(content: &str) -> usize {
    let mut last_open_line: Option<usize> = None;
    let mut module_line: Option<usize> = None;

    for (idx, line) in content.lines().enumerate() {
        let trimmed = line.trim();
        if OPEN_STMT_RE.is_match(line) {
            last_open_line = Some(idx + 1); // 1-indexed
        }
        if module_line.is_none() && MODULE_DECL_RE.is_match(line) && !trimmed.starts_with("//") {
            module_line = Some(idx + 1);
        }
    }

    // Insert AFTER the last open (so line + 1), or after module decl + blank line
    if let Some(open_line) = last_open_line {
        open_line + 1
    } else if let Some(mod_line) = module_line {
        // Insert after module declaration with a blank line
        mod_line + 2
    } else {
        1
    }
}

// ==========================================================================
// FST020: Val binder arrow trap
// ==========================================================================

/// FST020: Detect `(name: type1 -> type2)` in `val` declarations.
///
/// In F*, `(f: a -> b)` parses as `(f:a) -> b` — a parameter named `f` of
/// type `a`, followed by return type `b`. To declare a function-typed
/// parameter, double-wrap: `(f: (a -> b))`.
pub struct ValBinderArrowRule;

impl ValBinderArrowRule {
    pub fn new() -> Self {
        Self
    }
}

/// A suspicious binder found by the paren-depth scanner.
struct SuspiciousBinder {
    /// Byte offset of the opening `(` within the line.
    open_byte: usize,
    /// Byte offset of the closing `)` within the line (points AT `)`)
    close_byte: usize,
    /// Byte offset of the `:` separator within the line.
    colon_byte: usize,
}

impl Rule for ValBinderArrowRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST020
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut in_val = false;
        let mut in_block_comment: u32 = 0;

        for (line_idx, line) in content.lines().enumerate() {
            let trimmed = line.trim();

            // Track block comment nesting (simplified).
            in_block_comment = update_block_comment_depth(line, in_block_comment);

            if in_block_comment > 0 {
                continue;
            }

            // Detect val block boundaries.
            if trimmed.starts_with("val ") || trimmed.starts_with("assume val ") {
                in_val = true;
            } else if trimmed.is_empty()
                || trimmed.starts_with("let ")
                || trimmed.starts_with("let rec ")
                || trimmed.starts_with("type ")
                || trimmed.starts_with("noeq type ")
                || trimmed.starts_with("module ")
                || trimmed.starts_with("open ")
                || trimmed.starts_with("include ")
                || trimmed.starts_with("friend ")
            {
                in_val = false;
            }

            if !in_val {
                continue;
            }

            // Scan this line for suspicious binders.
            if let Some(binder) = find_suspicious_binder(line) {
                let line_num = line_idx + 1;
                let open_col = byte_to_char_col(line, binder.open_byte);
                let close_col = byte_to_char_col(line, binder.close_byte);

                // Build auto-fix: insert `(` after `: ` and `)` before closing `)`.
                let type_start = binder.colon_byte + 1;
                // Skip whitespace after colon.
                let type_start_trimmed = line[type_start..]
                    .find(|c: char| !c.is_whitespace())
                    .map(|off| type_start + off)
                    .unwrap_or(type_start);

                let fix = Fix {
                    message: "Wrap type in parens: `(name: (type))` to declare a \
                              function-typed parameter"
                        .to_string(),
                    edits: vec![
                        // Insert `(` before the type expression
                        Edit {
                            file: file.to_path_buf(),
                            range: Range::new(
                                line_num,
                                byte_to_char_col(line, type_start_trimmed),
                                line_num,
                                byte_to_char_col(line, type_start_trimmed),
                            ),
                            new_text: "(".to_string(),
                        },
                        // Insert `)` before the closing `)`
                        Edit {
                            file: file.to_path_buf(),
                            range: Range::new(
                                line_num,
                                close_col,
                                line_num,
                                close_col,
                            ),
                            new_text: ")".to_string(),
                        },
                    ],
                    confidence: FixConfidence::High,
                    unsafe_reason: None,
                    safety_level: super::rules::FixSafetyLevel::Safe,
                    reversible: true,
                    requires_review: false,
                };

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST020,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::new(line_num, open_col, line_num, close_col + 1),
                    message: format!(
                        "`(name: type -> ...)` in val parses as `(name:type) -> ...`. \
                         Wrap the type in parens: `(name: (type -> ...))`."
                    ),
                    fix: Some(fix),
                });
            }
        }

        diagnostics
    }
}

/// Count net block-comment depth change across a line.
///
/// Returns the updated depth after processing all `(*` and `*)` pairs.
fn update_block_comment_depth(line: &str, mut depth: u32) -> u32 {
    let bytes = line.as_bytes();
    let mut i = 0;
    while i + 1 < bytes.len() {
        if bytes[i] == b'(' && bytes[i + 1] == b'*' {
            depth += 1;
            i += 2;
        } else if bytes[i] == b'*' && bytes[i + 1] == b')' {
            depth = depth.saturating_sub(1);
            i += 2;
        } else {
            i += 1;
        }
    }
    depth
}

/// Strip block comment regions `(* ... *)` from a line, replacing them with spaces.
///
/// Handles nested comments. Returns the cleaned string with comment content replaced
/// by spaces (to preserve byte offsets for column computation).
fn strip_block_comments(line: &str) -> String {
    let bytes = line.as_bytes();
    let len = bytes.len();
    let mut result = String::with_capacity(len);
    let mut i = 0;
    let mut depth: u32 = 0;

    while i < len {
        if i + 1 < len && bytes[i] == b'(' && bytes[i + 1] == b'*' {
            depth += 1;
            result.push(' ');
            result.push(' ');
            i += 2;
        } else if depth > 0 && i + 1 < len && bytes[i] == b'*' && bytes[i + 1] == b')' {
            depth -= 1;
            result.push(' ');
            result.push(' ');
            i += 2;
        } else if depth > 0 {
            result.push(' ');
            i += 1;
        } else {
            result.push(bytes[i] as char);
            i += 1;
        }
    }

    result
}

/// Scan a single line for a `(identifier: TYPE -> TYPE)` pattern at paren depth 1.
///
/// Returns `Some(SuspiciousBinder)` if found, `None` otherwise.
///
/// Algorithm:
/// 1. Find `(` that starts a binder (followed by `identifier :`)
/// 2. Track paren depth from that `(`
/// 3. If we see `->` at depth 1 (same level), AND the type is not already
///    wrapped in parens right after the colon, flag it
fn find_suspicious_binder(line: &str) -> Option<SuspiciousBinder> {
    let bytes = line.as_bytes();
    let len = bytes.len();
    let mut i = 0;

    while i < len {
        // Skip line comments.
        if i + 1 < len && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            break;
        }
        // Skip block comments opening.
        if i + 1 < len && bytes[i] == b'(' && bytes[i + 1] == b'*' {
            // Skip past this block comment (simplified: find matching `*)`)
            let mut depth = 1u32;
            i += 2;
            while i + 1 < len && depth > 0 {
                if bytes[i] == b'(' && bytes[i + 1] == b'*' {
                    depth += 1;
                    i += 2;
                } else if bytes[i] == b'*' && bytes[i + 1] == b')' {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            continue;
        }
        // Skip string literals.
        if bytes[i] == b'"' {
            i += 1;
            while i < len {
                if bytes[i] == b'\\' {
                    i += 2;
                } else if bytes[i] == b'"' {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
            continue;
        }

        if bytes[i] == b'(' {
            // Try to parse `(identifier : ...)`
            if let Some(result) = try_parse_binder(line, i) {
                return Some(result);
            }
        }

        i += 1;
    }

    None
}

/// Try to parse a binder starting at `open_pos` (which points at `(`).
///
/// Looks for pattern: `(IDENT : TYPE_EXPR -> ... )` where:
/// - IDENT is a lowercase identifier or `_`
/// - There is a `:` separator
/// - There is a `->` at paren depth 1 (relative to this opening paren)
/// - The type after `:` is NOT already wrapped in parens
fn try_parse_binder(line: &str, open_pos: usize) -> Option<SuspiciousBinder> {
    let bytes = line.as_bytes();
    let len = bytes.len();
    let mut i = open_pos + 1;

    // Skip whitespace after `(`
    while i < len && bytes[i].is_ascii_whitespace() {
        i += 1;
    }

    // Expect an identifier: [a-z_][a-zA-Z0-9_']*
    let _ident_start = i;
    if i >= len || !(bytes[i].is_ascii_lowercase() || bytes[i] == b'_') {
        return None;
    }
    i += 1;
    while i < len && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'\'') {
        i += 1;
    }
    let _ident_end = i;

    // Skip whitespace before `:`
    while i < len && bytes[i].is_ascii_whitespace() {
        i += 1;
    }

    // Expect `:`
    if i >= len || bytes[i] != b':' {
        return None;
    }
    let colon_byte = i;
    i += 1;

    // Skip whitespace after `:`
    while i < len && bytes[i].is_ascii_whitespace() {
        i += 1;
    }

    // Check if type is already wrapped in parens: `(name: (...))`
    // If the first non-whitespace char after `:` is `(`, track if it matches
    // the entire type expression up to the closing `)`.
    let type_start = i;
    if i < len && bytes[i] == b'(' {
        // Check if the opening paren at type_start encompasses all the way
        // to the closing `)` of the binder. If so, the type is already wrapped.
        if is_type_already_wrapped(line, type_start, open_pos) {
            return None;
        }
    }

    // Now scan forward at depth 1, looking for `->` and the closing `)`.
    let mut depth: u32 = 1; // We already consumed the opening `(`
    let mut found_arrow = false;
    let mut j = type_start;

    while j < len && depth > 0 {
        match bytes[j] {
            b'(' => {
                // Check for block comment `(*`
                if j + 1 < len && bytes[j + 1] == b'*' {
                    // Skip block comment
                    let mut cdepth = 1u32;
                    j += 2;
                    while j + 1 < len && cdepth > 0 {
                        if bytes[j] == b'(' && bytes[j + 1] == b'*' {
                            cdepth += 1;
                            j += 2;
                        } else if bytes[j] == b'*' && bytes[j + 1] == b')' {
                            cdepth -= 1;
                            j += 2;
                        } else {
                            j += 1;
                        }
                    }
                    continue;
                }
                depth += 1;
                j += 1;
            }
            b')' => {
                depth -= 1;
                if depth == 0 {
                    // Found closing paren of the binder.
                    if found_arrow {
                        return Some(SuspiciousBinder {
                            open_byte: open_pos,
                            close_byte: j,
                            colon_byte,
                        });
                    }
                    return None;
                }
                j += 1;
            }
            b'-' if depth == 1 && j + 1 < len && bytes[j + 1] == b'>' => {
                found_arrow = true;
                j += 2;
            }
            b'"' => {
                // Skip string literal
                j += 1;
                while j < len {
                    if bytes[j] == b'\\' {
                        j += 2;
                    } else if bytes[j] == b'"' {
                        j += 1;
                        break;
                    } else {
                        j += 1;
                    }
                }
            }
            _ => {
                j += 1;
            }
        }
    }

    None
}

/// Check if the type after `:` is already wrapped in matching parens.
///
/// Specifically, checks if the `(` at `type_start` closes right before the
/// binder's closing `)`, meaning the user already wrote `(name: (type -> ...))`.
fn is_type_already_wrapped(line: &str, type_start: usize, _binder_open: usize) -> bool {
    let bytes = line.as_bytes();
    let len = bytes.len();

    // Track paren depth starting from `type_start`'s `(`
    let mut inner_depth: u32 = 1;
    let mut j = type_start + 1;

    while j < len && inner_depth > 0 {
        match bytes[j] {
            b'(' => {
                // Skip block comments
                if j + 1 < len && bytes[j + 1] == b'*' {
                    let mut cdepth = 1u32;
                    j += 2;
                    while j + 1 < len && cdepth > 0 {
                        if bytes[j] == b'(' && bytes[j + 1] == b'*' {
                            cdepth += 1;
                            j += 2;
                        } else if bytes[j] == b'*' && bytes[j + 1] == b')' {
                            cdepth -= 1;
                            j += 2;
                        } else {
                            j += 1;
                        }
                    }
                    continue;
                }
                inner_depth += 1;
                j += 1;
            }
            b')' => {
                inner_depth -= 1;
                if inner_depth == 0 {
                    // The inner `(` closed at position `j`.
                    // Check: is the NEXT non-whitespace char the binder's closing `)`?
                    let mut k = j + 1;
                    while k < len && bytes[k].is_ascii_whitespace() {
                        k += 1;
                    }
                    // The binder's closing `)` is the next `)` at the binder's depth.
                    // If `k` points at `)`, the type is already wrapped.
                    return k < len && bytes[k] == b')';
                }
                j += 1;
            }
            b'"' => {
                j += 1;
                while j < len {
                    if bytes[j] == b'\\' {
                        j += 2;
                    } else if bytes[j] == b'"' {
                        j += 1;
                        break;
                    } else {
                        j += 1;
                    }
                }
            }
            _ => {
                j += 1;
            }
        }
    }

    false
}

// ==========================================================================
// FST042: Lemma ensures ambiguity
// ==========================================================================

/// FST042: Detect `Lemma (EXPR)` without `ensures`/`requires`/`decreases`.
///
/// In F*, `Lemma (P)` desugars to `Lemma (requires P) (ensures fun _ -> True)`,
/// which is the opposite of what most users intend. The correct form is
/// `Lemma (ensures P)`.
///
/// This rule fires on `Lemma (EXPR)` where the first token inside parens is
/// NOT `ensures`, `requires`, or `decreases`. It does NOT fire on bare
/// `Lemma unit` or `Lemma True` (no parens).
pub struct LemmaEnsuresAmbiguityRule;

impl LemmaEnsuresAmbiguityRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for LemmaEnsuresAmbiguityRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST042
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_comment_depth: u32 = 0;

        for (line_idx, line) in content.lines().enumerate() {
            // Track block comment depth across lines.
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);

            // Skip lines entirely within block comments.
            // (Simplified: if depth was >0 before and still >0, skip.)
            if block_comment_depth > 0 && !line.contains("*)") {
                continue;
            }

            // Scan for `Lemma` followed by `(` on this line.
            if let Some(diag) = scan_line_for_lemma_ambiguity(file, line, line_idx + 1) {
                diagnostics.push(diag);
            }
        }

        diagnostics
    }
}

/// Scan a single line for ambiguous `Lemma (EXPR)` patterns.
///
/// Returns a diagnostic if `Lemma (...)` is found where the first token
/// inside parens is not `ensures`, `requires`, or `decreases`.
fn scan_line_for_lemma_ambiguity(
    file: &Path,
    line: &str,
    line_num: usize,
) -> Option<Diagnostic> {
    let bytes = line.as_bytes();
    let len = bytes.len();
    let mut i = 0;

    while i < len {
        // Skip block comment regions within the line.
        if i + 1 < len && bytes[i] == b'(' && bytes[i + 1] == b'*' {
            let mut depth = 1u32;
            i += 2;
            while i + 1 < len && depth > 0 {
                if bytes[i] == b'(' && bytes[i + 1] == b'*' {
                    depth += 1;
                    i += 2;
                } else if bytes[i] == b'*' && bytes[i + 1] == b')' {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            continue;
        }

        // Skip string literals.
        if bytes[i] == b'"' {
            i += 1;
            while i < len {
                if bytes[i] == b'\\' {
                    i += 2;
                } else if bytes[i] == b'"' {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
            continue;
        }

        // Skip line comments.
        if i + 1 < len && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            break;
        }

        // Look for 'L' to start matching "Lemma"
        if bytes[i] == b'L'
            && i + 5 <= len
            && &bytes[i..i + 5] == b"Lemma"
        {
            // Ensure "Lemma" is a standalone word (not part of a larger identifier).
            let before_ok = i == 0
                || !bytes[i - 1].is_ascii_alphanumeric() && bytes[i - 1] != b'_';
            let after_ok = i + 5 >= len
                || !bytes[i + 5].is_ascii_alphanumeric() && bytes[i + 5] != b'_';

            if before_ok && after_ok {
                let lemma_start = i;
                let mut j = i + 5;

                // Skip whitespace between "Lemma" and "("
                while j < len && bytes[j].is_ascii_whitespace() {
                    j += 1;
                }

                // Must be followed by "("
                if j < len && bytes[j] == b'(' {
                    // Check it's not a block comment opening "(* "
                    if j + 1 < len && bytes[j + 1] == b'*' {
                        i = j + 2;
                        continue;
                    }

                    let paren_start = j;
                    j += 1;

                    // Skip whitespace after "("
                    while j < len && bytes[j].is_ascii_whitespace() {
                        j += 1;
                    }

                    // Check if the first token inside parens is a keyword.
                    let is_keyword = starts_with_keyword(bytes, j, len);

                    if !is_keyword {
                        // Find matching close paren for the range.
                        let close_pos = find_matching_paren(bytes, paren_start, len);
                        let end_col = if let Some(cp) = close_pos {
                            byte_to_char_col(line, cp) + 1
                        } else {
                            byte_to_char_col(line, len.saturating_sub(1)) + 1
                        };

                        let start_col = byte_to_char_col(line, lemma_start);

                        return Some(Diagnostic {
                            rule: RuleCode::FST042,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::new(line_num, start_col, line_num, end_col),
                            message: "`Lemma (P)` without `ensures` means \
                                      `Lemma (requires P) (ensures True)` in F*. \
                                      Use `Lemma (ensures P)` to specify the postcondition."
                                .to_string(),
                            fix: None,
                        });
                    }
                }
            }
        }

        i += 1;
    }

    None
}

/// Check if the byte slice starting at `pos` begins with `ensures`, `requires`,
/// or `decreases` followed by a non-identifier character.
fn starts_with_keyword(bytes: &[u8], pos: usize, len: usize) -> bool {
    for keyword in &[b"ensures" as &[u8], b"requires", b"decreases"] {
        let kw_len = keyword.len();
        if pos + kw_len <= len && &bytes[pos..pos + kw_len] == *keyword {
            // Must be followed by non-identifier char (or end of input).
            if pos + kw_len >= len
                || (!bytes[pos + kw_len].is_ascii_alphanumeric()
                    && bytes[pos + kw_len] != b'_'
                    && bytes[pos + kw_len] != b'\'')
            {
                return true;
            }
        }
    }
    false
}

/// Find the matching closing paren for the opening paren at `open_pos`.
///
/// Returns `Some(close_pos)` or `None` if unmatched within the line.
fn find_matching_paren(bytes: &[u8], open_pos: usize, len: usize) -> Option<usize> {
    let mut depth: u32 = 0;
    let mut j = open_pos;

    while j < len {
        match bytes[j] {
            b'(' => {
                // Skip block comments
                if j + 1 < len && bytes[j + 1] == b'*' {
                    let mut cd = 1u32;
                    j += 2;
                    while j + 1 < len && cd > 0 {
                        if bytes[j] == b'(' && bytes[j + 1] == b'*' {
                            cd += 1;
                            j += 2;
                        } else if bytes[j] == b'*' && bytes[j + 1] == b')' {
                            cd -= 1;
                            j += 2;
                        } else {
                            j += 1;
                        }
                    }
                    continue;
                }
                depth += 1;
                j += 1;
            }
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(j);
                }
                j += 1;
            }
            b'"' => {
                j += 1;
                while j < len {
                    if bytes[j] == b'\\' {
                        j += 2;
                    } else if bytes[j] == b'"' {
                        j += 1;
                        break;
                    } else {
                        j += 1;
                    }
                }
            }
            _ => {
                j += 1;
            }
        }
    }

    None
}

// ==========================================================================
// FST021: Keyword as identifier
// ==========================================================================

/// F* reserved keywords that cause cryptic parse errors when used as
/// parameter or binding names.
const FSTAR_RESERVED_KEYWORDS: &[&str] = &[
    "total",
    "effect",
    "match",
    "friend",
    "include",
    "module",
    "open",
    "private",
    "unfold",
    "inline",
    "opaque",
    "new_effect",
    "sub_effect",
    "layered_effect",
    "reifiable",
    "reflectable",
];

/// FST021: Detect F* reserved keywords used as parameter or binding names.
///
/// Keywords like `total`, `effect`, `match` etc. cause cryptic parse errors
/// when used as identifiers. This rule flags patterns like `(total: int)` or
/// `let match = 5`.
pub struct KeywordAsIdentifierRule;

impl KeywordAsIdentifierRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for KeywordAsIdentifierRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST021
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_comment_depth: u32 = 0;

        for (line_idx, line) in content.lines().enumerate() {
            let prev_depth = block_comment_depth;
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);

            // If entire line is inside a block comment, skip.
            if prev_depth > 0 && block_comment_depth > 0 {
                continue;
            }
            // If depth was >0 at start or depth changed, the line has comment regions.
            // For simplicity, skip lines that start or end inside block comments.
            if prev_depth > 0 {
                continue;
            }

            let trimmed = line.trim();

            // Skip line comments.
            let effective = if let Some(pos) = trimmed.find("//") {
                &trimmed[..pos]
            } else {
                trimmed
            };

            // Strip block comment regions from effective text.
            let effective = strip_block_comments(effective);
            let effective = effective.as_str();

            // Check for `(keyword:` or `(keyword :` patterns (parameter binders).
            for &kw in FSTAR_RESERVED_KEYWORDS {
                // Pattern: `(keyword:` or `(keyword :`
                let paren_kw = format!("({}", kw);
                let mut search_from = 0;
                while let Some(pos) = effective[search_from..].find(&paren_kw) {
                    let abs_pos = search_from + pos;
                    let after_kw = abs_pos + paren_kw.len();
                    if after_kw < effective.len() {
                        let next_ch = effective.as_bytes()[after_kw];
                        if next_ch == b':' || (next_ch == b' ' && effective[after_kw..].trim_start().starts_with(':')) {
                            let col = byte_to_char_col(line, line.find(&effective[abs_pos..abs_pos + paren_kw.len()]).unwrap_or(0));
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST021,
                                severity: DiagnosticSeverity::Warning,
                                file: file.to_path_buf(),
                                range: Range::new(line_idx + 1, col, line_idx + 1, col + kw.len() + 1),
                                message: format!(
                                    "`{}` is a reserved F* keyword and cannot be used as a \
                                     parameter name. Rename it (e.g., `{}_val` or `h{}`).",
                                    kw, kw, &kw[..1]
                                ),
                                fix: None,
                            });
                            break;
                        }
                    }
                    search_from = abs_pos + 1;
                }

                // Pattern: `let keyword =` (binding name).
                let let_kw = format!("let {} ", kw);
                if effective.starts_with(&let_kw) || effective.contains(&format!(" let {} ", kw)) {
                    // Make sure it's followed by `=` and not part of a longer identifier.
                    let after_let_kw = if effective.starts_with(&let_kw) {
                        &effective[let_kw.len()..]
                    } else if let Some(p) = effective.find(&format!(" let {} ", kw)) {
                        &effective[p + format!(" let {} ", kw).len()..]
                    } else {
                        continue;
                    };
                    let next_token = after_let_kw.trim_start();
                    if next_token.starts_with('=') || next_token.starts_with(':') {
                        let byte_pos = line.find(&let_kw)
                            .or_else(|| line.find(&format!(" let {} ", kw)).map(|p| p + 1))
                            .unwrap_or(0);
                        let col = byte_to_char_col(line, byte_pos);
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST021,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::new(line_idx + 1, col, line_idx + 1, col + let_kw.len()),
                            message: format!(
                                "`{}` is a reserved F* keyword and cannot be used as a \
                                 binding name. Rename it (e.g., `{}_val` or `h{}`).",
                                kw, kw, &kw[..1]
                            ),
                            fix: None,
                        });
                    }
                }
            }
        }

        diagnostics
    }
}

// ==========================================================================
// FST022: Missing noeq
// ==========================================================================

/// FST022: Detect record types with function-typed fields missing `noeq`.
///
/// Without `noeq`, F* tries to derive decidable equality for the type.
/// This fails for record fields containing function types (`a -> b`),
/// causing Error 76. The fix is to add `noeq` before `type`.
pub struct MissingNoeqRule;

impl MissingNoeqRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for MissingNoeqRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST022
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_comment_depth: u32 = 0;

        let lines: Vec<&str> = content.lines().collect();
        let mut i = 0;

        while i < lines.len() {
            let line = lines[i];
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);
            if block_comment_depth > 0 {
                i += 1;
                continue;
            }

            let trimmed = line.trim();

            // Look for `type` declarations NOT preceded by `noeq` or `unopteq`.
            let is_type_decl = trimmed.starts_with("type ")
                || trimmed.starts_with("and ");
            let already_qualified = trimmed.starts_with("noeq type ")
                || trimmed.starts_with("unopteq type ")
                || trimmed.starts_with("noeq ")
                || trimmed.starts_with("unopteq ");

            if !is_type_decl || already_qualified {
                i += 1;
                continue;
            }

            // Check if the previous non-empty line has `noeq` or `unopteq`.
            let mut prev_has_noeq = false;
            if i > 0 {
                for j in (0..i).rev() {
                    let prev_trimmed = lines[j].trim();
                    if prev_trimmed.is_empty() {
                        break;
                    }
                    if prev_trimmed == "noeq" || prev_trimmed == "unopteq" {
                        prev_has_noeq = true;
                    }
                    break;
                }
            }

            if prev_has_noeq {
                i += 1;
                continue;
            }

            // Collect the type body: scan until we hit the next top-level
            // declaration or an empty line after the body.
            let type_start = i;
            let mut has_record_brace = false;
            let mut has_function_field = false;
            let mut j = i;

            // Check if this line has `= {` indicating a record.
            while j < lines.len() {
                let body_line = lines[j].trim();

                // Stop at blank lines after we've seen content, or at new declarations.
                if j > type_start && body_line.is_empty() {
                    break;
                }
                if j > type_start
                    && (body_line.starts_with("let ")
                        || body_line.starts_with("val ")
                        || body_line.starts_with("type ")
                        || body_line.starts_with("noeq type ")
                        || body_line.starts_with("unopteq type ")
                        || body_line.starts_with("open ")
                        || body_line.starts_with("module "))
                {
                    break;
                }

                if body_line.contains('{') {
                    has_record_brace = true;
                }

                // Check for function-typed fields: `field_name: ... -> ...`
                // Look for `:` followed by content containing `->` (at this level).
                if has_record_brace {
                    if let Some(colon_pos) = body_line.find(':') {
                        let after_colon = &body_line[colon_pos + 1..];
                        // Strip any trailing `;` or `}`
                        let field_type = after_colon.trim().trim_end_matches(';').trim_end_matches('}').trim();
                        if field_type.contains("->") {
                            has_function_field = true;
                        }
                    }
                }

                if body_line.contains('}') && has_record_brace {
                    // End of record body.
                    j += 1;
                    break;
                }

                j += 1;
            }

            if has_record_brace && has_function_field {
                let line_num = type_start + 1;
                let type_keyword_col = byte_to_char_col(line, line.find("type ").unwrap_or(0));

                // Build auto-fix: insert `noeq ` before `type`.
                let fix = Fix {
                    message: "Add `noeq` qualifier to prevent failed equality derivation \
                              on function-typed fields"
                        .to_string(),
                    edits: vec![Edit {
                        file: file.to_path_buf(),
                        range: Range::new(line_num, type_keyword_col, line_num, type_keyword_col),
                        new_text: "noeq ".to_string(),
                    }],
                    confidence: FixConfidence::High,
                    unsafe_reason: None,
                    safety_level: super::rules::FixSafetyLevel::Safe,
                    reversible: true,
                    requires_review: false,
                };

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST022,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::new(line_num, type_keyword_col, line_num, type_keyword_col + 4),
                    message: "Record type has function-typed fields but is missing `noeq`. \
                              F* will fail to derive decidable equality (Error 76). \
                              Add `noeq` before `type`."
                        .to_string(),
                    fix: Some(fix),
                });
            }

            i = j.max(i + 1);
        }

        diagnostics
    }
}

// ==========================================================================
// FST023: Unguarded forall
// ==========================================================================

/// FST023: Detect `forall` in ensures/postconditions without SMTPat triggers.
///
/// Unguarded universal quantifiers in postconditions can cause Z3 to diverge
/// because it has no pattern to guide instantiation. Either add an `[SMTPat ...]`
/// or `[SMTPatOr ...]` annotation, or restructure the proof.
pub struct UnguardedForallRule;

impl UnguardedForallRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for UnguardedForallRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST023
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_comment_depth: u32 = 0;

        // Strategy: find definitions that contain `forall` in ensures/postcondition
        // context, then check if there's a corresponding SMTPat in the same definition.
        //
        // We scan line-by-line, tracking whether we're in an ensures clause or
        // Lemma postcondition, and whether we've seen SMTPat in the same definition.

        let lines: Vec<&str> = content.lines().collect();
        let mut i = 0;

        while i < lines.len() {
            let line = lines[i];
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);
            if block_comment_depth > 0 {
                i += 1;
                continue;
            }

            let trimmed = line.trim();

            // Skip line comments.
            if trimmed.starts_with("//") {
                i += 1;
                continue;
            }

            // Detect definition boundaries: `val` or `let` declarations.
            let is_def_start = trimmed.starts_with("val ")
                || trimmed.starts_with("assume val ")
                || trimmed.starts_with("let ")
                || trimmed.starts_with("let rec ");

            if !is_def_start {
                i += 1;
                continue;
            }

            // Collect the entire definition scope (until next top-level decl or blank line).
            let def_start = i;
            let mut def_end = i + 1;
            while def_end < lines.len() {
                let dt = lines[def_end].trim();
                if dt.is_empty() {
                    break;
                }
                // New top-level declaration.
                if dt.starts_with("val ")
                    || dt.starts_with("assume val ")
                    || dt.starts_with("let ")
                    || dt.starts_with("let rec ")
                    || dt.starts_with("type ")
                    || dt.starts_with("noeq type ")
                    || dt.starts_with("open ")
                    || dt.starts_with("module ")
                {
                    break;
                }
                def_end += 1;
            }

            // Scan the definition for: ensures/Lemma with forall, and SMTPat.
            let mut has_forall_in_ensures = false;
            let mut forall_line: usize = 0;
            let mut forall_col: usize = 0;
            let mut has_smt_pat = false;
            let mut in_ensures = false;
            let mut in_requires = false;

            for k in def_start..def_end {
                let def_line = lines[k].trim();

                // Track context.
                if def_line.contains("ensures") {
                    in_ensures = true;
                    in_requires = false;
                }
                if def_line.contains("requires") {
                    in_requires = true;
                    in_ensures = false;
                }

                // Lemma postconditions (the first arg to `Lemma (...)` without
                // `ensures` keyword is treated as the precondition, but
                // `Lemma (ensures ...)` is postcondition context).
                // For simplicity, also check for forall in Lemma context.
                let in_lemma_context = def_line.contains("Lemma");

                if in_lemma_context {
                    in_ensures = true;
                }

                // Check for SMTPat or SMTPatOr.
                if def_line.contains("SMTPat") || def_line.contains("SMTPatOr") {
                    has_smt_pat = true;
                }

                // Check for `forall` in ensures context.
                if (in_ensures && !in_requires) && !has_forall_in_ensures {
                    if let Some(pos) = def_line.find("forall") {
                        // Verify it's a standalone word.
                        let before_ok = pos == 0
                            || !def_line.as_bytes()[pos - 1].is_ascii_alphanumeric()
                                && def_line.as_bytes()[pos - 1] != b'_';
                        let after_pos = pos + 6;
                        let after_ok = after_pos >= def_line.len()
                            || !def_line.as_bytes()[after_pos].is_ascii_alphanumeric()
                                && def_line.as_bytes()[after_pos] != b'_';
                        if before_ok && after_ok {
                            has_forall_in_ensures = true;
                            forall_line = k + 1;
                            forall_col = byte_to_char_col(lines[k], lines[k].find("forall").unwrap_or(0));
                        }
                    }
                }
            }

            if has_forall_in_ensures && !has_smt_pat {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST023,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::new(forall_line, forall_col, forall_line, forall_col + 6),
                    message: "Unguarded `forall` in postcondition without `[SMTPat ...]`. \
                              This can cause Z3 to diverge. Add an SMTPat trigger or \
                              restructure the proof."
                        .to_string(),
                    fix: None,
                });
            }

            i = def_end;
        }

        diagnostics
    }
}

// ==========================================================================
// FST030: Function equality
// ==========================================================================

/// FST030: Detect direct equality comparison of functions.
///
/// Function equality (`f == g`) is undecidable in F*. Use pointwise equality
/// via `FunctionalExtensionality.feq` or `on_domain` instead.
///
/// This rule uses a conservative heuristic: it only flags `IDENT == IDENT`
/// or `IDENT = IDENT` patterns inside `assert` or `Lemma` contexts where
/// both sides are bare identifiers (no arguments applied).
pub struct FunctionEqualityRule;

impl FunctionEqualityRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for FunctionEqualityRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST030
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_comment_depth: u32 = 0;

        for (line_idx, line) in content.lines().enumerate() {
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);
            if block_comment_depth > 0 && !line.contains("*)") {
                continue;
            }

            let trimmed = line.trim();

            // Skip line comments.
            if trimmed.starts_with("//") {
                continue;
            }

            // Only check in assert/Lemma contexts (conservative).
            let in_assert_context = trimmed.contains("assert")
                || trimmed.contains("Lemma")
                || trimmed.contains("ensures");

            if !in_assert_context {
                continue;
            }

            // Look for patterns: `IDENT == IDENT` or `IDENT = IDENT` where
            // both are bare lowercase identifiers (no application).
            // We search for `==` first, then `=` (single).
            for eq_op in &["==", "="] {
                let mut search_from = 0;
                while let Some(eq_pos) = trimmed[search_from..].find(eq_op) {
                    let abs_eq = search_from + eq_pos;

                    // For single `=`, skip if it's part of `==`, `=>`, `<=`, `>=`, `<>`, `==>`, `/=`
                    if *eq_op == "=" {
                        if abs_eq + 1 < trimmed.len() && trimmed.as_bytes()[abs_eq + 1] == b'=' {
                            search_from = abs_eq + 1;
                            continue;
                        }
                        if abs_eq + 1 < trimmed.len() && trimmed.as_bytes()[abs_eq + 1] == b'>' {
                            search_from = abs_eq + 1;
                            continue;
                        }
                        if abs_eq > 0 {
                            let prev = trimmed.as_bytes()[abs_eq - 1];
                            if prev == b'<' || prev == b'>' || prev == b'!' || prev == b'/' || prev == b'=' {
                                search_from = abs_eq + 1;
                                continue;
                            }
                        }
                    }

                    // Extract tokens before and after the operator.
                    let before = trimmed[..abs_eq].trim_end();
                    let after_start = abs_eq + eq_op.len();
                    let after = if after_start < trimmed.len() {
                        trimmed[after_start..].trim_start()
                    } else {
                        ""
                    };

                    let lhs_raw = last_token(before);
                    let rhs_raw = first_token(after);

                    // Strip surrounding parens to handle `assert (foo == bar)`.
                    let lhs_token = lhs_raw.trim_start_matches('(').trim_end_matches(')');
                    let rhs_token = rhs_raw.trim_start_matches('(').trim_end_matches(')');

                    // Both must be bare lowercase identifiers (no digits, no
                    // parens, no application).
                    if is_bare_function_ident(lhs_token) && is_bare_function_ident(rhs_token) {
                        // Extra guard: skip if LHS == RHS (reflexivity, common pattern).
                        if lhs_token != rhs_token {
                            let byte_pos = line.find(trimmed).unwrap_or(0) + abs_eq;
                            let col = byte_to_char_col(line, byte_pos);
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST030,
                                severity: DiagnosticSeverity::Warning,
                                file: file.to_path_buf(),
                                range: Range::new(
                                    line_idx + 1,
                                    col,
                                    line_idx + 1,
                                    col + eq_op.len(),
                                ),
                                message: format!(
                                    "Direct function equality `{} {} {}` is undecidable in F*. \
                                     Use `FunctionalExtensionality.feq` or `on_domain` for \
                                     pointwise equality instead.",
                                    lhs_token, eq_op, rhs_token
                                ),
                                fix: None,
                            });
                            // Only flag once per line to reduce noise.
                            break;
                        }
                    }

                    search_from = abs_eq + eq_op.len();
                }
                // If we already found a diagnostic on this line, skip to next line.
                if diagnostics.last().is_some_and(|d| d.range.start_line == line_idx + 1) {
                    break;
                }
            }
        }

        diagnostics
    }
}

/// Check if a token looks like a bare function identifier.
///
/// A bare function identifier is a lowercase identifier with no applied
/// arguments (no parens after it), no numeric suffix suggesting a value,
/// and at least 2 characters long to avoid single-letter value variables.
fn is_bare_function_ident(token: &str) -> bool {
    if token.is_empty() {
        return false;
    }
    let first = token.as_bytes()[0];
    // Must start with lowercase letter or underscore.
    if !first.is_ascii_lowercase() && first != b'_' {
        return false;
    }
    // Must be a valid identifier (alphanumeric, _, ').
    if !token.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'') {
        return false;
    }
    // Must be at least 2 chars to avoid flagging `x == y` value comparisons.
    if token.len() < 2 {
        return false;
    }
    // Skip common value-variable names.
    let value_names = ["xs", "ys", "hd", "tl", "fst", "snd", "lhs", "rhs", "acc"];
    if value_names.contains(&token) {
        return false;
    }
    true
}

// ==========================================================================
// Tests
// ==========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn check(content: &str) -> Vec<Diagnostic> {
        let rule = MissingMulOpenRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    // ----- No false positives -----

    #[test]
    fn test_no_diagnostic_when_open_fstar_mul_present() {
        let content = "\
module Test

open FStar.Mul

let result = x * y
";
        assert!(check(content).is_empty());
    }

    #[test]
    fn test_no_diagnostic_for_tuple_type_in_val() {
        let content = "\
module Test

val f : int * int -> int
";
        assert!(check(content).is_empty());
    }

    #[test]
    fn test_no_diagnostic_for_tuple_type_in_type_decl() {
        let content = "\
module Test

type pair = int * string
";
        assert!(check(content).is_empty());
    }

    #[test]
    fn test_no_diagnostic_for_star_in_comment() {
        let content = "\
module Test

(* x * y is multiplication *)
let z = 1
";
        assert!(check(content).is_empty());
    }

    #[test]
    fn test_no_diagnostic_when_no_star_at_all() {
        let content = "\
module Test

let x = 1 + 2
";
        assert!(check(content).is_empty());
    }

    // ----- True positives -----

    #[test]
    fn test_detects_multiplication_in_let_binding() {
        let content = "\
module Test

let result = x * y
";
        let diags = check(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST027);
        assert!(diags[0].fix.is_some());
    }

    #[test]
    fn test_detects_numeric_multiplication() {
        let content = "\
module Test

let result = n * 2
";
        let diags = check(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST027);
    }

    #[test]
    fn test_detects_multiplication_in_assert() {
        let content = "\
module Test

let _ = assert (x * y > 0)
";
        let diags = check(content);
        assert_eq!(diags.len(), 1);
    }

    #[test]
    fn test_detects_multiplication_in_ensures() {
        let content = "\
module Test

let f (x: nat) (y: nat)
  : Pure nat
    (requires x > 0)
    (ensures fun r -> r = x * y)
  = x * y
";
        let diags = check(content);
        assert_eq!(diags.len(), 1, "Should emit exactly one diagnostic per file");
    }

    // ----- Auto-fix tests -----

    #[test]
    fn test_fix_inserts_after_last_open() {
        let content = "\
module Test

open FStar.List.Tot
open FStar.Seq

let result = a * b
";
        let diags = check(content);
        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().expect("should have fix");
        assert_eq!(fix.edits.len(), 1);
        // `open FStar.Seq` is on line 4, so insert on line 5 (right after last open)
        assert_eq!(fix.edits[0].range.start_line, 5);
        assert_eq!(fix.edits[0].new_text, "open FStar.Mul\n");
    }

    #[test]
    fn test_fix_inserts_after_module_when_no_opens() {
        let content = "\
module Test

let result = a * b
";
        let diags = check(content);
        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().expect("should have fix");
        assert_eq!(fix.edits.len(), 1);
        // `module Test` is on line 1, so insert on line 3 (after blank line)
        assert_eq!(fix.edits[0].range.start_line, 3);
    }

    #[test]
    fn test_fix_confidence_is_high() {
        let content = "\
module Test

let result = x * y
";
        let diags = check(content);
        let fix = diags[0].fix.as_ref().expect("should have fix");
        assert_eq!(fix.confidence, FixConfidence::High);
        assert!(fix.is_safe());
    }

    // ----- Edge cases -----

    #[test]
    fn test_star_in_string_literal_ignored() {
        let content = r#"module Test

let s = "x * y"
"#;
        assert!(check(content).is_empty());
    }

    #[test]
    fn test_uppercase_types_both_sides_is_tuple() {
        // Type names starting with uppercase on both sides → tuple, not multiplication
        let content = "\
module Test

let f (x: Nat * Bool) = x
";
        // This is in a let binding but `Nat * Bool` looks like a tuple type annotation
        assert!(check(content).is_empty());
    }

    #[test]
    fn test_paren_before_star_is_multiplication() {
        let content = "\
module Test

let result = (a + b) * c
";
        let diags = check(content);
        assert_eq!(diags.len(), 1);
    }

    // =====================================================================
    // FST020: ValBinderArrowRule tests
    // =====================================================================

    fn check_val_binder(content: &str) -> Vec<Diagnostic> {
        let rule = ValBinderArrowRule::new();
        let path = PathBuf::from("Test.fsti");
        rule.check(&path, content)
    }

    // ----- True positives -----

    #[test]
    fn test_val_binder_arrow_simple() {
        let content = "\
module Test

val apply : (callback: int -> int) -> int -> int
";
        let diags = check_val_binder(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST020);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Warning);
    }

    #[test]
    fn test_val_binder_arrow_multi_arrow() {
        let content = "\
module Test

val map : (f: nat -> nat -> bool) -> list nat -> list bool
";
        let diags = check_val_binder(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST020);
    }

    #[test]
    fn test_val_binder_arrow_assume_val() {
        let content = "\
module Test

assume val process : (handler: string -> unit) -> nat
";
        let diags = check_val_binder(content);
        assert_eq!(diags.len(), 1);
    }

    #[test]
    fn test_val_binder_arrow_continuation_line() {
        // The binder is on a continuation line of a val declaration.
        let content = "\
module Test

val complex_function :
  (transform: int -> int) -> list int -> list int
";
        let diags = check_val_binder(content);
        assert_eq!(diags.len(), 1);
    }

    // ----- True negatives -----

    #[test]
    fn test_val_binder_already_wrapped() {
        let content = "\
module Test

val apply : (callback: (int -> int)) -> int -> int
";
        let diags = check_val_binder(content);
        assert!(diags.is_empty(), "Already wrapped type should not trigger");
    }

    #[test]
    fn test_val_binder_no_arrow() {
        let content = "\
module Test

val add : (x: int) -> (y: int) -> int
";
        let diags = check_val_binder(content);
        assert!(diags.is_empty(), "Binder without arrow in type should not trigger");
    }

    #[test]
    fn test_val_binder_return_type_arrow() {
        // `-> int` in the return type is not inside a paren-binder.
        let content = "\
module Test

val add : int -> int -> int
";
        let diags = check_val_binder(content);
        assert!(diags.is_empty(), "Bare arrows in val (no paren binder) should not trigger");
    }

    #[test]
    fn test_val_binder_not_in_let() {
        let content = "\
module Test

let apply (callback: int -> int) (x: int) : int = callback x
";
        let diags = check_val_binder(content);
        assert!(diags.is_empty(), "Let bindings should not trigger FST020");
    }

    #[test]
    fn test_val_binder_uppercase_constructor() {
        // `(Some: int -> option int)` — uppercase names are not identifier binders.
        let content = "\
module Test

val f : (X: int -> int) -> int
";
        let diags = check_val_binder(content);
        // Uppercase names are not caught (identifier must start lowercase or `_`).
        assert!(diags.is_empty());
    }

    #[test]
    fn test_val_binder_nested_parens_in_type() {
        // `(f: (a -> b) -> c)` — there's an arrow at depth 1 (`-> c`),
        // and the type is NOT already fully wrapped since `(a -> b)` only
        // covers part of it. This SHOULD trigger.
        let content = "\
module Test

val compose : (f: (a -> b) -> c) -> a -> c
";
        let diags = check_val_binder(content);
        assert_eq!(diags.len(), 1, "Arrow at depth 1 after inner parens should trigger");
    }

    // ----- Auto-fix tests -----

    #[test]
    fn test_val_binder_arrow_fix_edits() {
        let content = "\
module Test

val apply : (callback: int -> int) -> int -> int
";
        let diags = check_val_binder(content);
        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().expect("should have auto-fix");
        assert_eq!(fix.edits.len(), 2, "Fix should have two edits (insert open and close parens)");

        // First edit inserts `(` before the type.
        assert_eq!(fix.edits[0].new_text, "(");
        // Second edit inserts `)` before the closing `)`.
        assert_eq!(fix.edits[1].new_text, ")");

        assert_eq!(fix.confidence, FixConfidence::High);
        assert!(fix.is_safe());
    }

    #[test]
    fn test_val_binder_arrow_fix_positions() {
        // "val apply : (callback: int -> int) -> int -> int"
        //              ^open     ^colon  ^type_start  ^close_paren
        // The type starts at 'int' (after ": "), close paren is at position of ')'.
        let content = "\
module Test

val apply : (callback: int -> int) -> int -> int
";
        let diags = check_val_binder(content);
        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().unwrap();

        // The `(` should be inserted right before "int" (the type start).
        // "val apply : (callback: int -> int) -> int -> int"
        //  columns:     1234567890123456789...
        // `(` is at col 13 (1-indexed), `callback` starts at col 14,
        // `:` is at col 22, space, `int` starts at col 24.
        // The first edit inserts at the column of `int`.
        let insert_open = &fix.edits[0];
        assert_eq!(insert_open.new_text, "(");

        let insert_close = &fix.edits[1];
        assert_eq!(insert_close.new_text, ")");
    }

    #[test]
    fn test_val_binder_in_comment_ignored() {
        let content = "\
module Test

(* val apply : (callback: int -> int) -> int *)
val safe : (x: int) -> int
";
        let diags = check_val_binder(content);
        assert!(diags.is_empty());
    }

    // =====================================================================
    // FST042: LemmaEnsuresAmbiguityRule tests
    // =====================================================================

    fn check_lemma_ensures(content: &str) -> Vec<Diagnostic> {
        let rule = LemmaEnsuresAmbiguityRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    // ----- True positives -----

    #[test]
    fn test_lemma_ensures_ambiguous_simple() {
        let content = "\
module Test

val add_zero_right : x:nat -> Lemma (x + 0 == x)
";
        let diags = check_lemma_ensures(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST042);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Warning);
        assert!(diags[0].fix.is_none(), "FST042 should not have an auto-fix");
    }

    #[test]
    fn test_lemma_ensures_ambiguous_conjunction() {
        let content = "\
module Test

val my_lemma : x:nat -> y:nat -> Lemma (x + y == y + x /\\ x >= 0)
";
        let diags = check_lemma_ensures(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST042);
    }

    #[test]
    fn test_lemma_ensures_ambiguous_in_let() {
        let content = "\
module Test

let my_lemma (x: nat) : Lemma (x + 0 == x) = ()
";
        let diags = check_lemma_ensures(content);
        assert_eq!(diags.len(), 1);
    }

    // ----- True negatives -----

    #[test]
    fn test_lemma_ensures_explicit_ensures() {
        let content = "\
module Test

val add_zero_right : x:nat -> Lemma (ensures (x + 0 == x))
";
        let diags = check_lemma_ensures(content);
        assert!(diags.is_empty(), "Explicit `ensures` should not trigger");
    }

    #[test]
    fn test_lemma_ensures_explicit_requires_ensures() {
        let content = "\
module Test

val my_lemma : x:nat -> Lemma (requires (x > 0)) (ensures (x >= 1))
";
        let diags = check_lemma_ensures(content);
        assert!(diags.is_empty(), "`requires`/`ensures` keywords should not trigger");
    }

    #[test]
    fn test_lemma_ensures_bare_unit() {
        // `Lemma unit` is not parenthesized so should not trigger.
        let content = "\
module Test

val trivial : Lemma unit
";
        let diags = check_lemma_ensures(content);
        assert!(diags.is_empty(), "Bare `Lemma unit` (no parens) should not trigger");
    }

    #[test]
    fn test_lemma_ensures_bare_true() {
        // `Lemma True` is intentional (requires True, ensures True).
        let content = "\
module Test

val trivial : Lemma True
";
        let diags = check_lemma_ensures(content);
        assert!(diags.is_empty(), "Bare `Lemma True` (no parens) should not trigger");
    }

    #[test]
    fn test_lemma_ensures_in_comment() {
        let content = "\
module Test

(* Lemma (P) is ambiguous *)
val safe : x:nat -> Lemma (ensures (x >= 0))
";
        let diags = check_lemma_ensures(content);
        assert!(diags.is_empty(), "Lemma in comment should not trigger");
    }

    #[test]
    fn test_lemma_ensures_with_decreases() {
        let content = "\
module Test

val my_lemma : x:nat -> Lemma (decreases x)
";
        let diags = check_lemma_ensures(content);
        assert!(diags.is_empty(), "`decreases` keyword should not trigger");
    }

    #[test]
    fn test_lemma_ensures_not_standalone_word() {
        // "MyLemma" contains "Lemma" but it's not a standalone word.
        let content = "\
module Test

val f : x:nat -> MyLemma (x + 0 == x)
";
        let diags = check_lemma_ensures(content);
        assert!(diags.is_empty(), "Substring match should not trigger");
    }

    // =====================================================================
    // FST021: KeywordAsIdentifierRule tests
    // =====================================================================

    fn check_keyword_ident(content: &str) -> Vec<Diagnostic> {
        let rule = KeywordAsIdentifierRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_keyword_ident_paren_binder() {
        let content = "\
module Test

val f : (total: int) -> int
";
        let diags = check_keyword_ident(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST021);
        assert!(diags[0].message.contains("total"));
    }

    #[test]
    fn test_keyword_ident_let_binding() {
        let content = "\
module Test

let match = 5
";
        let diags = check_keyword_ident(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST021);
        assert!(diags[0].message.contains("match"));
    }

    #[test]
    fn test_keyword_ident_prefix_ok() {
        // `total_count` is NOT a keyword — should not trigger.
        let content = "\
module Test

let total_count = 5
";
        let diags = check_keyword_ident(content);
        assert!(diags.is_empty(), "`total_count` is not a keyword, should not trigger");
    }

    #[test]
    fn test_keyword_ident_in_comment() {
        let content = "\
module Test

(* let match = 5 *)
let x = 1
";
        let diags = check_keyword_ident(content);
        assert!(diags.is_empty(), "Keywords in comments should not trigger");
    }

    // =====================================================================
    // FST022: MissingNoeqRule tests
    // =====================================================================

    fn check_missing_noeq(content: &str) -> Vec<Diagnostic> {
        let rule = MissingNoeqRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_missing_noeq_function_field() {
        let content = "\
module Test

type my_record = {
  callback: int -> int;
  value: nat;
}
";
        let diags = check_missing_noeq(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST022);
        assert!(diags[0].fix.is_some());
    }

    #[test]
    fn test_missing_noeq_already_has_noeq() {
        let content = "\
module Test

noeq type my_record = {
  callback: int -> int;
  value: nat;
}
";
        let diags = check_missing_noeq(content);
        assert!(diags.is_empty(), "Already has `noeq`, should not trigger");
    }

    #[test]
    fn test_missing_noeq_no_function_fields() {
        let content = "\
module Test

type point = {
  x: int;
  y: int;
}
";
        let diags = check_missing_noeq(content);
        assert!(diags.is_empty(), "No function fields, should not trigger");
    }

    #[test]
    fn test_missing_noeq_fix_inserts_noeq() {
        let content = "\
module Test

type my_record = {
  callback: int -> int;
}
";
        let diags = check_missing_noeq(content);
        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().expect("should have fix");
        assert_eq!(fix.edits.len(), 1);
        assert_eq!(fix.edits[0].new_text, "noeq ");
    }

    // =====================================================================
    // FST023: UnguardedForallRule tests
    // =====================================================================

    fn check_unguarded_forall(content: &str) -> Vec<Diagnostic> {
        let rule = UnguardedForallRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_unguarded_forall_in_ensures() {
        let content = "\
module Test

val my_lemma : x:nat -> Lemma
  (ensures (forall y. x + y == y + x))
";
        let diags = check_unguarded_forall(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST023);
        assert!(diags[0].message.contains("forall"));
    }

    #[test]
    fn test_unguarded_forall_with_smtpat() {
        let content = "\
module Test

val my_lemma : x:nat -> Lemma
  (ensures (forall y. x + y == y + x))
  [SMTPat (x + 0)]
";
        let diags = check_unguarded_forall(content);
        assert!(diags.is_empty(), "Has SMTPat, should not trigger");
    }

    #[test]
    fn test_unguarded_forall_only_in_requires() {
        let content = "\
module Test

val my_lemma : x:nat -> Pure nat
  (requires (forall y. y > 0))
  (ensures fun r -> r > 0)
";
        let diags = check_unguarded_forall(content);
        assert!(diags.is_empty(), "`forall` only in requires should not trigger");
    }

    #[test]
    fn test_unguarded_forall_in_comment() {
        let content = "\
module Test

(* ensures (forall x. P x) *)
val safe : nat -> Lemma (ensures True)
";
        let diags = check_unguarded_forall(content);
        assert!(diags.is_empty(), "`forall` in comment should not trigger");
    }

    // =====================================================================
    // FST030: FunctionEqualityRule tests
    // =====================================================================

    fn check_function_equality(content: &str) -> Vec<Diagnostic> {
        let rule = FunctionEqualityRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_function_equality_bare_idents() {
        let content = "\
module Test

let _ = assert (callback == handler)
";
        let diags = check_function_equality(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST030);
        assert!(diags[0].message.contains("feq"));
    }

    #[test]
    fn test_function_equality_applied_ok() {
        // `f x == g x` — both sides are applied, this is value equality.
        let content = "\
module Test

let _ = assert (f x == g x)
";
        let diags = check_function_equality(content);
        assert!(diags.is_empty(), "Applied functions should not trigger");
    }

    #[test]
    fn test_function_equality_single_char_ok() {
        // `x == y` — single-char vars are value variables, not functions.
        let content = "\
module Test

let _ = assert (x == y)
";
        let diags = check_function_equality(content);
        assert!(diags.is_empty(), "Single-char variables should not trigger");
    }
}
