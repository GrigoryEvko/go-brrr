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

use super::rules::{
    Diagnostic, DiagnosticSeverity, Edit, Fix, FixConfidence, FixSafetyLevel, Range, Rule, RuleCode,
};

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
        safety_level: FixSafetyLevel::Safe,
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
                    safety_level: FixSafetyLevel::Safe,
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
        let mut in_record_type = false;
        let mut record_brace_depth: u32 = 0;
        // Track constructor-style type defs: `| Ctor : field1 -> ... -> T`.
        // In these, `Lemma (P)` is a field type, not a return effect.
        let mut in_ctor_type = false;
        // Track whether we're inside a val/let declaration (multi-line aware).
        let mut in_val_decl = false;

        for (line_idx, line) in content.lines().enumerate() {
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);
            if block_comment_depth > 0 && !line.contains("*)") {
                continue;
            }

            let stripped = strip_line_comment(line);
            let trimmed = stripped.trim();

            // --- Track record type blocks ---
            // Inside `noeq type ... = { field: x -> Lemma (P); ... }`,
            // `Lemma (P)` is a type annotation where the semantics are clear
            // to the author. Suppress entirely.
            if !in_record_type
                && (trimmed.starts_with("type ") || trimmed.starts_with("noeq type ")
                    || trimmed.starts_with("and "))
                && trimmed.contains('=')
                && stripped.contains('{')
            {
                in_record_type = true;
                record_brace_depth = 0;
            }

            if in_record_type {
                for &b in stripped.as_bytes() {
                    if b == b'{' {
                        record_brace_depth += 1;
                    } else if b == b'}' {
                        record_brace_depth = record_brace_depth.saturating_sub(1);
                        if record_brace_depth == 0 {
                            in_record_type = false;
                        }
                    }
                }
                continue;
            }

            // --- Track constructor-style type definitions ---
            // `| Ctor : field -> field -> ... -> T` — fields here use `Lemma (P)` intentionally.
            // Enter on `| Name :` pattern, exit on blank line, new top-level decl, or `| Name :` again.
            if trimmed.starts_with("| ") && (trimmed.contains(" : ") || trimmed.ends_with(" :")) {
                // Constructor field definition line.
                in_ctor_type = true;
            } else if in_ctor_type {
                // Stay in ctor mode for continuation lines (indented, start with `->` or contain `->`)
                if !trimmed.is_empty()
                    && !trimmed.starts_with("let ")
                    && !trimmed.starts_with("val ")
                    && !trimmed.starts_with("type ")
                    && !trimmed.starts_with("noeq type ")
                    && !trimmed.starts_with("open ")
                    && !trimmed.starts_with("module ")
                    && !trimmed.starts_with("| ") // new constructor ends previous
                {
                    // Continuation of constructor fields — still in_ctor_type.
                } else {
                    in_ctor_type = false;
                    // Re-check if this line starts a new constructor.
                    if trimmed.starts_with("| ") && (trimmed.contains(" : ") || trimmed.ends_with(" :")) {
                        in_ctor_type = true;
                    }
                }
            }

            if in_ctor_type {
                // Inside constructor fields: Lemma (P) is a field type annotation.
                // Don't flag — this is intentional.
                // But still scan for Lemma at the top-level (after the final `-> T`).
                // We'll let it through and rely on the paren-depth heuristic below.
            }

            // --- Track val/let declaration context for severity ---
            if trimmed.starts_with("val ") || trimmed.starts_with("let ")
                || trimmed.starts_with("let rec ") || trimmed.starts_with("and ")
            {
                in_val_decl = true;
            }
            // A new top-level declaration or blank line ends the val context.
            if trimmed.is_empty()
                || trimmed.starts_with("type ")
                || trimmed.starts_with("noeq type ")
                || trimmed.starts_with("open ")
                || trimmed.starts_with("module ")
                || trimmed.starts_with("include ")
            {
                in_val_decl = false;
            }

            if let Some(mut diag) = scan_line_for_lemma_ambiguity(file, line, line_idx + 1) {
                // --- Context-dependent severity ---
                // If `Lemma (P)` appears inside a nested function type in a binder
                // (not a val/let return type), downgrade to Hint. These are typically
                // intentional type annotations where the author knows the semantics.
                if let Some(lemma_pos) = stripped.find("Lemma") {
                    let before_lemma = &stripped[..lemma_pos];

                    // Heuristic: count unclosed parens before `Lemma`.
                    // If paren depth > 0, `Lemma` is nested inside a parenthesized expression,
                    // likely a binder type like `(f: x:a -> Lemma (P))`.
                    let mut paren_depth: i32 = 0;
                    for &b in before_lemma.as_bytes() {
                        if b == b'(' { paren_depth += 1; }
                        if b == b')' { paren_depth -= 1; }
                    }

                    if in_ctor_type {
                        // Inside a constructor field definition — intentional type annotation.
                        diag.severity = DiagnosticSeverity::Hint;
                    } else if paren_depth > 0 {
                        // Nested inside parens — likely a binder type annotation.
                        diag.severity = DiagnosticSeverity::Hint;
                    } else if !in_val_decl && before_lemma.contains("->") {
                        // Not in a val/let context but has `->` before — ambiguous,
                        // could be a continuation line or a nested type. Downgrade to Info.
                        diag.severity = DiagnosticSeverity::Info;
                    }
                    // else: top-level val/let return type — keep as Warning.
                }

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
                            let snippet = effective.get(abs_pos..abs_pos + paren_kw.len()).unwrap_or(&paren_kw);
                            let col = byte_to_char_col(line, line.find(snippet).unwrap_or(0));
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
                    safety_level: FixSafetyLevel::Safe,
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
                    // ALSO verify they are truly standalone: if the token before lhs_token
                    // is also an identifier, then lhs_token is actually the last argument
                    // of a function application (e.g., `fold cm a b expr1 == ...`).
                    if is_bare_function_ident(lhs_token) && is_bare_function_ident(rhs_token) {
                        // Check LHS is truly bare: the token before lhs_raw must not be an ident.
                        let before_lhs = before[..before.len() - lhs_raw.len()].trim_end();
                        let prev_tok = last_token(before_lhs);
                        let prev_stripped = prev_tok.trim_start_matches('(').trim_end_matches(')');
                        if is_fstar_ident(prev_stripped) && !["assert", "assert_norm", "assume", "ensures", "requires", "forall", "exists", "fun"].contains(&prev_stripped) {
                            search_from = abs_eq + eq_op.len();
                            continue;
                        }
                        // Check RHS is truly bare: the token after rhs_raw must not be an ident.
                        let after_rhs = after[rhs_raw.len()..].trim_start();
                        let next_tok = first_token(after_rhs);
                        let next_stripped = next_tok.trim_start_matches('(').trim_end_matches(')');
                        if is_fstar_ident(next_stripped) && ![")", "]", "}", ";", "in", "then", "else", "with", "and", "end", ""].contains(&next_stripped) {
                            search_from = abs_eq + eq_op.len();
                            continue;
                        }
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


// ==========================================================================
// Shared helpers for FST024+ rules
// ==========================================================================

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'\''
}


fn is_fstar_ident(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let first = s.as_bytes()[0];
    if !first.is_ascii_alphabetic() && first != b'_' {
        return false;
    }
    s.bytes().all(|b| is_ident_char(b) || b == b'.')
}


fn strip_line_comment(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut i = 0;
    let mut in_string = false;
    while i < bytes.len() {
        if in_string {
            if bytes[i] == b'\\' {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if bytes[i] == b'"' {
            in_string = true;
            i += 1;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            return &line[..i];
        }
        i += 1;
    }
    line
}


fn line_in_block_comment(depth_before: u32, line: &str) -> bool {
    if depth_before > 0 {
        // Check if we ever drop to 0 on this line
        let bytes = line.as_bytes();
        let mut d = depth_before;
        let mut i = 0;
        while i + 1 < bytes.len() {
            if bytes[i] == b'(' && bytes[i + 1] == b'*' {
                d += 1;
                i += 2;
            } else if bytes[i] == b'*' && bytes[i + 1] == b')' {
                d = d.saturating_sub(1);
                if d == 0 {
                    return false; // code follows after comment close
                }
                i += 2;
            } else {
                i += 1;
            }
        }
        return true;
    }
    false
}


///
/// Handles single-line `(* ... *)` blocks by replacing their content with spaces.
/// Does NOT handle multi-line block comments — use `update_block_comment_depth` for that.
fn strip_comments_full(line: &str, in_block_comment: bool) -> (String, bool) {
    let mut result = String::with_capacity(line.len());
    let bytes = line.as_bytes();
    let mut i = 0;
    let mut in_block = in_block_comment;

    while i < bytes.len() {
        if in_block {
            // Look for `*)`
            if i + 1 < bytes.len() && bytes[i] == b'*' && bytes[i + 1] == b')' {
                in_block = false;
                result.push(' ');
                result.push(' ');
                i += 2;
            } else {
                result.push(' ');
                i += 1;
            }
        } else if i + 1 < bytes.len() && bytes[i] == b'(' && bytes[i + 1] == b'*' {
            in_block = true;
            result.push(' ');
            result.push(' ');
            i += 2;
        } else if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            // Rest of line is a comment.
            break;
        } else {
            result.push(bytes[i] as char);
            i += 1;
        }
    }

    (result, in_block)
}


fn is_word_at(line: &str, pos: usize, keyword: &str) -> bool {
    let bytes = line.as_bytes();
    let kw_len = keyword.len();
    if pos + kw_len > bytes.len() {
        return false;
    }
    if &bytes[pos..pos + kw_len] != keyword.as_bytes() {
        return false;
    }
    let before_ok = pos == 0 || !is_ident_char(bytes[pos - 1]);
    let after_ok = pos + kw_len >= bytes.len() || !is_ident_char(bytes[pos + kw_len]);
    before_ok && after_ok
}


// ==========================================================================
// FST024: DecreasesBoundRule
// ==========================================================================

/// FST024: Detect `decreases` clauses referencing names not bound in function parameters.
///
/// In `let rec f (x: t) (y: t) : ... (decreases z) = ...`, if `z` is not `x`
/// or `y`, F* silently creates a fresh variable instead of using the intended
/// parameter, leading to a confusing verification failure.
pub struct DecreasesBoundRule;

impl DecreasesBoundRule {
    pub fn new() -> Self {
        Self
    }
}

/// Extract parameter names from a `let rec` signature line and any continuation
/// lines up to `=` or `decreases`.
///
/// Returns `(params, decreases_line_idx, decreases_col, decreases_body)` or `None`.
fn parse_let_rec_signature(lines: &[&str], start: usize) -> Option<(Vec<String>, usize, usize, String)> {
    let first_trimmed = lines[start].trim();
    if !first_trimmed.starts_with("let rec ") && !first_trimmed.starts_with("and ") {
        return None;
    }

    // Collect the entire signature text across continuation lines until `=` at depth 0.
    let mut sig_text = String::new();
    // Track which original lines each byte range maps to.
    let mut line_map: Vec<(usize, usize)> = Vec::new(); // (line_idx, byte_offset_in_sig_text)
    let mut end_line = start;

    for i in start..lines.len() {
        let lt = lines[i].trim();
        if i > start
            && (lt.starts_with("let ") || lt.starts_with("val ")
                || lt.starts_with("type ") || lt.starts_with("open ")
                || lt.starts_with("module ") || lt.is_empty())
        {
            break;
        }
        line_map.push((i, sig_text.len()));
        if !sig_text.is_empty() {
            sig_text.push(' ');
        }
        sig_text.push_str(lt);
        end_line = i;

        // Stop after we see `= ` at paren depth 0 that is the definition body.
        // Simple heuristic: if the line ends with `=` or contains ` = ` outside parens.
        if lt.ends_with(" =") || lt.ends_with("\t=") || lt == "=" {
            break;
        }
    }

    // Extract parameter names: tokens inside `(name:` or bare `(name)` patterns.
    let mut params: Vec<String> = Vec::new();
    let sig_bytes = sig_text.as_bytes();
    let mut i = 0;

    // Skip `let rec NAME` or `and NAME`.
    if sig_text.starts_with("let rec ") {
        i = 8;
    } else if sig_text.starts_with("and ") {
        i = 4;
    }
    // Skip function name.
    while i < sig_bytes.len() && sig_bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    while i < sig_bytes.len() && is_ident_char(sig_bytes[i]) {
        i += 1;
    }

    // Now scan for parameter binders.
    let mut paren_depth: u32 = 0;
    while i < sig_bytes.len() {
        match sig_bytes[i] {
            b'(' => {
                if paren_depth == 0 {
                    // Try to extract parameter name after `(`.
                    let mut j = i + 1;
                    while j < sig_bytes.len() && sig_bytes[j].is_ascii_whitespace() {
                        j += 1;
                    }
                    // Optional `#` for implicit.
                    if j < sig_bytes.len() && sig_bytes[j] == b'#' {
                        j += 1;
                    }
                    let name_start = j;
                    while j < sig_bytes.len() && is_ident_char(sig_bytes[j]) {
                        j += 1;
                    }
                    if j > name_start {
                        let name = &sig_text[name_start..j];
                        // Skip whitespace, check for `:` or `)`.
                        let mut k = j;
                        while k < sig_bytes.len() && sig_bytes[k].is_ascii_whitespace() {
                            k += 1;
                        }
                        if k < sig_bytes.len() && (sig_bytes[k] == b':' || sig_bytes[k] == b')') {
                            params.push(name.to_string());
                        }
                    }
                }
                paren_depth += 1;
                i += 1;
            }
            b')' => {
                paren_depth = paren_depth.saturating_sub(1);
                i += 1;
            }
            _ => {
                // Bare parameters (no parens): `let rec f x y = ...`
                if paren_depth == 0 && sig_bytes[i].is_ascii_whitespace() {
                    let mut j = i + 1;
                    while j < sig_bytes.len() && sig_bytes[j].is_ascii_whitespace() {
                        j += 1;
                    }
                    let name_start = j;
                    while j < sig_bytes.len() && is_ident_char(sig_bytes[j]) {
                        j += 1;
                    }
                    if j > name_start {
                        let candidate = &sig_text[name_start..j];
                        // Stop at `:` (type annotation start) or `=` (body start).
                        if candidate != ":" && candidate != "=" && candidate != "decreases"
                            && candidate != "requires" && candidate != "ensures"
                            && candidate != "Tot" && candidate != "Pure" && candidate != "Lemma"
                            && candidate != "GTot" && candidate != "Dv" && candidate != "ST"
                            && candidate != "Stack" && candidate != "Ghost"
                        {
                            // Check the next non-whitespace char isn't `:` with complex type.
                            let mut k = j;
                            while k < sig_bytes.len() && sig_bytes[k].is_ascii_whitespace() {
                                k += 1;
                            }
                            if k >= sig_bytes.len() || sig_bytes[k] != b':' {
                                // It's a bare parameter.
                                if !candidate.starts_with(|c: char| c.is_ascii_uppercase()) {
                                    params.push(candidate.to_string());
                                }
                            }
                        }
                    }
                }
                i += 1;
            }
        }

        // If we hit `:` at depth 0, we're in the return type annotation; stop collecting params.
        if paren_depth == 0 && i < sig_bytes.len() && sig_bytes[i] == b':' {
            break;
        }
    }

    // Find `(decreases ...)` in the signature.
    for li in start..=end_line {
        let lt = lines[li];
        let effective = strip_line_comment(lt);
        if let Some(dec_pos) = effective.find("decreases") {
            let before = if dec_pos > 0 { effective.as_bytes()[dec_pos - 1] } else { b' ' };
            let after_pos = dec_pos + 9;
            let after = if after_pos < effective.len() { effective.as_bytes()[after_pos] } else { b' ' };
            if !is_ident_char(before) && !is_ident_char(after) {
                // Extract the decreases body: everything after `decreases` until `)` or end.
                let body_start = after_pos;
                let body = effective[body_start..].trim().trim_start_matches('(').trim_end_matches(')').trim();
                let col = byte_to_char_col(lt, lt.find("decreases").unwrap_or(0));
                return Some((params, li, col, body.to_string()));
            }
        }
    }

    None
}

/// F* builtins allowed in decreases clauses without being parameters.
const DECREASES_BUILTINS: &[&str] = &[
    "lex_t", "LexTop", "LexCons", "Cons", "Nil", "true", "false",
    "fst", "snd", "length", "List.length", "List.Tot.length",
    "FStar.List.Tot.length", "Seq.length", "FStar.Seq.length",
];

impl Rule for DecreasesBoundRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST024
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut block_comment_depth: u32 = 0;
        let mut i = 0;

        while i < lines.len() {
            block_comment_depth = update_block_comment_depth(lines[i], block_comment_depth);
            if block_comment_depth > 0 {
                i += 1;
                continue;
            }

            let trimmed = lines[i].trim();
            if trimmed.starts_with("let rec ") || trimmed.starts_with("and ") {
                if let Some((params, dec_line, dec_col, dec_body)) =
                    parse_let_rec_signature(&lines, i)
                {
                    // Extract identifiers from the decreases body.
                    let dec_idents: Vec<&str> = dec_body
                        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != '\'' && c != '.')
                        .filter(|s| !s.is_empty() && is_fstar_ident(s))
                        .collect();

                    for ident in &dec_idents {
                        // Skip numeric literals, builtins, and qualified names with dots.
                        if ident.chars().next().map_or(true, |c| c.is_ascii_digit()) {
                            continue;
                        }
                        if DECREASES_BUILTINS.contains(ident) {
                            continue;
                        }
                        // Check if the base name (before any dots) is a parameter.
                        let base = ident.split('.').last().unwrap_or(ident);
                        if !params.iter().any(|p| p == base || p == *ident) {
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST024,
                                severity: DiagnosticSeverity::Warning,
                                file: file.to_path_buf(),
                                range: Range::new(dec_line + 1, dec_col, dec_line + 1, dec_col + 9),
                                message: format!(
                                    "`decreases` references `{}` which is not a parameter of this \
                                     function. This silently creates a fresh variable. \
                                     Parameters: [{}].",
                                    ident,
                                    params.join(", ")
                                ),
                                fix: None,
                            });
                            break; // One diagnostic per decreases clause.
                        }
                    }
                }
            }

            i += 1;
        }

        diagnostics
    }
}

// ==========================================================================
// FST025: AssumeTypeVsValRule
// ==========================================================================

/// FST025: Detect `assume type` with function arrows that likely should be `assume val`.
///
/// `assume type f : int -> int` assumes a *type* exists with that signature.
/// If the type has arrows, the user likely meant `assume val f : int -> int`
/// to assume a *value* (function) exists.
pub struct AssumeTypeVsValRule;

impl AssumeTypeVsValRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for AssumeTypeVsValRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST025
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_comment_depth: u32 = 0;

        for (line_idx, line) in content.lines().enumerate() {
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);
            if block_comment_depth > 0 {
                continue;
            }

            let trimmed = strip_line_comment(line).trim();

            // Match `assume type NAME ...` (possibly with `:` and type body).
            if !trimmed.starts_with("assume type ") {
                continue;
            }

            let after_assume_type = &trimmed["assume type ".len()..];

            // Check if the rest of the declaration (on this line) contains `->`.
            if after_assume_type.contains("->") {
                let col = byte_to_char_col(line, line.find("assume type").unwrap_or(0));
                let name = after_assume_type
                    .split(|c: char| c.is_whitespace() || c == ':')
                    .next()
                    .unwrap_or("?");

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST025,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::new(line_idx + 1, col, line_idx + 1, col + "assume type".len()),
                    message: format!(
                        "`assume type {}` has function arrows (`->`). Did you mean \
                         `assume val {} : ...`? `assume type` assumes a type constructor \
                         exists, not a value.",
                        name, name
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }
}

// ==========================================================================
// FST026: RevealInTotRule
// ==========================================================================

/// FST026: Detect `reveal` used in a `Tot` (total) computation context.
///
/// `reveal` from `FStar.Ghost` has the `GTot` effect -- it can only be used in
/// `Ghost` or `GTot` contexts, not in `Tot`. When used in a `Tot` function, F*
/// rejects it with a confusing effect mismatch error.
pub struct RevealInTotRule;

impl RevealInTotRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for RevealInTotRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST026
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut block_comment_depth: u32 = 0;

        // Two-pass approach:
        // 1. Identify functions with explicit `Tot` effect annotation.
        // 2. Within those function bodies, look for `reveal` / `reveal_opaque` calls.

        let mut i = 0;
        while i < lines.len() {
            block_comment_depth = update_block_comment_depth(lines[i], block_comment_depth);
            if block_comment_depth > 0 {
                i += 1;
                continue;
            }

            let trimmed = lines[i].trim();

            // Detect function/val with explicit Tot annotation.
            let has_tot_annotation = has_explicit_tot(trimmed);

            if !has_tot_annotation {
                // Also check multi-line sigs: val on previous lines, `: Tot` on this line.
                // Skip for simplicity -- only fire on the line with Tot.
                i += 1;
                continue;
            }

            // Found a Tot-annotated definition. Scan its body for `reveal` calls.
            let def_start = i;
            let mut def_end = i + 1;
            while def_end < lines.len() {
                let dt = lines[def_end].trim();
                if dt.is_empty() {
                    break;
                }
                if def_end > def_start
                    && (dt.starts_with("val ") || dt.starts_with("let ")
                        || dt.starts_with("let rec ") || dt.starts_with("type ")
                        || dt.starts_with("open ") || dt.starts_with("module ")
                        || dt.starts_with("assume "))
                {
                    break;
                }
                def_end += 1;
            }

            // Scan body for `reveal` or `reveal_opaque`.
            for k in def_start..def_end {
                let body_line = strip_line_comment(lines[k]);
                for keyword in &["reveal_opaque", "reveal"] {
                    if let Some(pos) = body_line.find(keyword) {
                        let kw_len = keyword.len();
                        let before_ok = pos == 0 || !is_ident_char(body_line.as_bytes()[pos - 1]);
                        let after_ok = pos + kw_len >= body_line.len()
                            || !is_ident_char(body_line.as_bytes()[pos + kw_len]);
                        if before_ok && after_ok {
                            let col = byte_to_char_col(lines[k], lines[k].find(keyword).unwrap_or(0));
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST026,
                                severity: DiagnosticSeverity::Error,
                                file: file.to_path_buf(),
                                range: Range::new(k + 1, col, k + 1, col + kw_len),
                                message: format!(
                                    "`{}` has GTot effect and cannot be used in a Tot context. \
                                     Change the function's effect to `GTot` or `Ghost`, or use \
                                     `Ghost.elim_pure` to bridge the effect boundary.",
                                    keyword
                                ),
                                fix: None,
                            });
                            break; // One diagnostic per keyword per line.
                        }
                    }
                }
            }

            i = def_end;
        }

        diagnostics
    }
}

/// Check if a line contains an explicit `Tot` as the RETURN effect of a definition.
///
/// Only matches `Tot` as the function's own return effect, NOT `Tot` inside
/// parameter types like `(f:a -> Tot b)`.
fn has_explicit_tot(line: &str) -> bool {
    let bytes = line.as_bytes();
    let len = bytes.len();
    let mut i = 0;

    while i + 3 <= len {
        if &bytes[i..i + 3] == b"Tot" {
            let before_ok = i == 0 || !is_ident_char(bytes[i - 1]);
            let after_ok = i + 3 >= len || !is_ident_char(bytes[i + 3]);
            if before_ok && after_ok {
                let prefix = line[..i].trim_end();
                if prefix.ends_with(':') || prefix.ends_with("->") {
                    // Verify this Tot is NOT inside parentheses (parameter type).
                    // Count unclosed '(' before this position.
                    let paren_depth: i32 = line[..i].chars()
                        .map(|c| match c { '(' => 1, ')' => -1, _ => 0 })
                        .sum();
                    if paren_depth <= 0 {
                        return true;
                    }
                    // paren_depth > 0 means Tot is inside a parameter type like (f:a -> Tot b)
                }
            }
        }
        i += 1;
    }

    false
}

// ==========================================================================
// FST029: PatternDisjunctionRule
// ==========================================================================

/// FST029: Detect `{:pattern ...} \/ ...` which creates disjunctive triggers.
///
/// In SMT patterns, `\/` separates alternative trigger sets. Users often write
/// `{:pattern (f x) \/ (g x)}` thinking it is logical OR, when it actually
/// creates two alternative patterns. The correct conjunctive multi-trigger
/// syntax uses `;`: `{:pattern (f x); (g x)}`.
pub struct PatternDisjunctionRule;

impl PatternDisjunctionRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for PatternDisjunctionRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST029
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_comment_depth: u32 = 0;

        for (line_idx, line) in content.lines().enumerate() {
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);
            if block_comment_depth > 0 {
                continue;
            }

            let effective = strip_line_comment(line);

            // Find `{:pattern` blocks.
            let mut search_from = 0;
            while let Some(pat_pos) = effective[search_from..].find("{:pattern") {
                let abs_pos = search_from + pat_pos;
                let after = &effective[abs_pos..];

                // Find the closing `}` for this pattern block.
                let block_end = find_brace_close(after);
                let block = if let Some(end) = block_end {
                    &after[..end + 1]
                } else {
                    after
                };

                // Check if the block contains `\/` (disjunctive trigger separator).
                if block.contains(r"\/") {
                    let disj_offset = block.find(r"\/").unwrap_or(0);
                    let disj_abs = abs_pos + disj_offset;
                    let snippet = effective.get(disj_abs..disj_abs + 2).unwrap_or(r"\/");
                    let col = byte_to_char_col(line, line.find(snippet).unwrap_or(disj_abs));

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST029,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::new(line_idx + 1, col, line_idx + 1, col + 2),
                        message: "`{:pattern ...} \\/` creates a disjunctive trigger (two \
                                  alternative pattern sets), not a logical OR. For a conjunctive \
                                  multi-trigger, use `;` instead: `{:pattern (f x); (g x)}`."
                            .to_string(),
                        fix: None,
                    });
                }

                search_from = abs_pos + block.len().max(1);
            }
        }

        diagnostics
    }
}

/// Find the closing `}` for a `{:pattern ...}` block, handling nested braces.
fn find_brace_close(s: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let mut depth: u32 = 0;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'{' => depth += 1,
            b'}' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

// ==========================================================================
// FST035: SimpCommGuardRule
// ==========================================================================

/// FST035: Detect `[@@simp_comm]` lemmas without an argument ordering guard.
///
/// A commutativity lemma `f a b == f b a` with `[@@simp_comm]` can loop the
/// simplifier indefinitely unless it has a guard like `a <= b` to break the
/// symmetry.
pub struct SimpCommGuardRule;

impl SimpCommGuardRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for SimpCommGuardRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST035
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut block_comment_depth: u32 = 0;

        for (line_idx, line) in lines.iter().enumerate() {
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);
            if block_comment_depth > 0 {
                continue;
            }

            let trimmed = line.trim();

            // Look for `simp_comm` in attributes.
            if !trimmed.contains("simp_comm") {
                continue;
            }
            // Verify it's in an attribute context `[@@` or `[@@@`.
            if !trimmed.contains("[@@") {
                continue;
            }
            // Verify `simp_comm` is a standalone attribute name.
            if let Some(pos) = trimmed.find("simp_comm") {
                let before_ok = pos == 0 || !is_ident_char(trimmed.as_bytes()[pos - 1]);
                let after_pos = pos + 9;
                let after_ok = after_pos >= trimmed.len() || !is_ident_char(trimmed.as_bytes()[after_pos]);
                if !before_ok || !after_ok {
                    continue;
                }
            }

            // Found `[@@simp_comm]`. Scan the next val/let declaration and its body
            // for an ordering guard (`<=`, `<`, `>=`, `>`).
            let mut has_guard = false;
            let attr_line = line_idx;

            for k in (line_idx + 1)..lines.len().min(line_idx + 15) {
                let dt = lines[k].trim();
                if dt.is_empty() {
                    continue;
                }
                // Check for ordering guards in requires or body.
                if dt.contains("<=") || dt.contains(">=")
                    || (dt.contains('<') && !dt.contains("<:") && !dt.contains("<<"))
                    || (dt.contains('>') && !dt.contains("->") && !dt.contains(">>"))
                {
                    has_guard = true;
                    break;
                }
                // Stop at next top-level declaration beyond the current one.
                if k > line_idx + 1
                    && (dt.starts_with("val ") || dt.starts_with("let ")
                        || dt.starts_with("type ") || dt.starts_with("open ")
                        || dt.starts_with("[@@"))
                {
                    break;
                }
            }

            if !has_guard {
                let col = byte_to_char_col(
                    line,
                    line.find("simp_comm").unwrap_or(0),
                );
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST035,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::new(attr_line + 1, col, attr_line + 1, col + 9),
                    message: "`[@@simp_comm]` lemma has no argument-ordering guard. \
                              Without a guard like `requires (a <= b)`, the simplifier \
                              may loop: `f a b -> f b a -> f a b -> ...`."
                        .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }
}

// ==========================================================================
// FST036: DollarBinderRule
// ==========================================================================

/// FST036: Suggest `$f` binder for implicit parameters with higher-order types.
///
/// In F*, `$f` means "always expect this argument explicitly -- don't try to
/// infer it". This is useful for implicit parameters with function types
/// (especially those taking `Lemma` or `Tac` results).
pub struct DollarBinderRule;

impl DollarBinderRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for DollarBinderRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST036
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_comment_depth: u32 = 0;

        for (line_idx, line) in content.lines().enumerate() {
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);
            if block_comment_depth > 0 {
                continue;
            }

            let effective = strip_line_comment(line);
            let trimmed = effective.trim();

            // Look for `(#name: ... -> Lemma` or `(#name: ... -> Tac` patterns.
            // These suggest the parameter is higher-order and would benefit from `$`.
            let bytes = trimmed.as_bytes();
            let len = bytes.len();
            let mut i = 0;

            while i + 3 < len {
                // Find `(#`
                if bytes[i] == b'(' && bytes[i + 1] == b'#' {
                    let paren_start = i;
                    i += 2;
                    // Skip whitespace.
                    while i < len && bytes[i].is_ascii_whitespace() {
                        i += 1;
                    }
                    // Read identifier name.
                    let name_start = i;
                    while i < len && is_ident_char(bytes[i]) {
                        i += 1;
                    }
                    if i > name_start {
                        let name = &trimmed[name_start..i];
                        // Skip to `:`.
                        while i < len && bytes[i].is_ascii_whitespace() {
                            i += 1;
                        }
                        if i < len && bytes[i] == b':' {
                            i += 1;
                            // Scan until matching `)` and check for `-> Lemma` or `-> Tac`.
                            let type_start = i;
                            let mut depth: u32 = 1;
                            while i < len && depth > 0 {
                                match bytes[i] {
                                    b'(' => { depth += 1; }
                                    b')' => { depth -= 1; }
                                    _ => {}
                                }
                                if depth > 0 { i += 1; }
                            }
                            let type_body = &trimmed[type_start..i];
                            // Check for higher-order patterns.
                            let is_higher_order = type_body.contains("-> Lemma")
                                || type_body.contains("-> Tac ")
                                || type_body.contains("-> Tac)")
                                || type_body.contains("-> Tot ")
                                || type_body.contains("-> GTot ");

                            if is_higher_order {
                                let snippet = trimmed.get(paren_start..paren_start + 2).unwrap_or("($");
                                let col = byte_to_char_col(
                                    line,
                                    line.find(snippet).unwrap_or(0),
                                );
                                diagnostics.push(Diagnostic {
                                    rule: RuleCode::FST036,
                                    severity: DiagnosticSeverity::Hint,
                                    file: file.to_path_buf(),
                                    range: Range::new(line_idx + 1, col, line_idx + 1, col + 2 + name.len()),
                                    message: format!(
                                        "Consider using `(${}` instead of `(#{}` for this higher-order \
                                         implicit parameter. `$` prevents F* from trying to infer \
                                         the argument automatically.",
                                        name, name
                                    ),
                                    fix: None,
                                });
                            }
                        }
                    }
                } else {
                    i += 1;
                }
            }
        }

        diagnostics
    }
}

// ==========================================================================
// FST039: UnfoldAliasRule (FIXABLE)
// ==========================================================================

/// FST039: Detect simple type aliases missing the `unfold` qualifier.
///
/// A simple alias like `let my_type = existing_type` without `[@@unfold]`
/// creates a new definition that the normalizer won't automatically expand,
/// causing unexpected type mismatches.
pub struct UnfoldAliasRule;

impl UnfoldAliasRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for UnfoldAliasRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST039
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut block_comment_depth: u32 = 0;

        let mut i = 0;
        while i < lines.len() {
            block_comment_depth = update_block_comment_depth(lines[i], block_comment_depth);
            if block_comment_depth > 0 {
                i += 1;
                continue;
            }

            let trimmed = strip_line_comment(lines[i]).trim().to_string();

            // Check for `let NAME = SIMPLE_RHS` at top level (no `rec`, no params).
            if !trimmed.starts_with("let ") || trimmed.starts_with("let rec ") {
                i += 1;
                continue;
            }

            let after_let = &trimmed["let ".len()..];

            // Skip if it already has `inline_for_extraction` or `unfold`.
            // Check previous lines for attributes.
            let mut has_unfold_attr = false;
            if i > 0 {
                for k in (0..i).rev() {
                    let prev = lines[k].trim();
                    if prev.is_empty() {
                        break;
                    }
                    if prev.contains("unfold") || prev.contains("inline_for_extraction")
                        || prev.contains("inline_let")
                    {
                        has_unfold_attr = true;
                        break;
                    }
                    // Only look at attribute lines.
                    if !prev.starts_with("[@@") && !prev.starts_with("[@@@") {
                        break;
                    }
                }
            }
            // Also check the let line itself.
            if trimmed.contains("unfold") || trimmed.contains("inline_for_extraction") {
                has_unfold_attr = true;
            }

            if has_unfold_attr {
                i += 1;
                continue;
            }

            // Parse: `let NAME = RHS` where NAME has no parameters.
            // Split at first `=`.
            if let Some(eq_pos) = after_let.find('=') {
                let lhs = after_let[..eq_pos].trim();
                let rhs = after_let[eq_pos + 1..].trim();

                // LHS must be a single identifier (no parameters, no type annotation).
                if !is_simple_ident(lhs) {
                    i += 1;
                    continue;
                }

                // RHS must be a simple identifier or qualified name (no computation).
                if rhs.is_empty() || !is_simple_type_rhs(rhs) {
                    i += 1;
                    continue;
                }

                // Skip if the name starts with underscore (private/temp).
                if lhs.starts_with('_') {
                    i += 1;
                    continue;
                }

                let line_num = i + 1;
                let col = byte_to_char_col(lines[i], lines[i].find("let ").unwrap_or(0));

                // Build auto-fix: insert `[@@unfold]\n` before the `let` line.
                let indent = &lines[i][..lines[i].len() - lines[i].trim_start().len()];
                let fix = Fix {
                    message: format!("Add `[@@unfold]` to type alias `{}`", lhs),
                    edits: vec![Edit {
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        new_text: format!("{}[@@unfold]\n", indent),
                    }],
                    confidence: FixConfidence::Medium,
                    unsafe_reason: None,
                    safety_level: FixSafetyLevel::Caution,
                    reversible: true,
                    requires_review: true,
                };

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST039,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::new(line_num, col, line_num, col + "let ".len() + lhs.len()),
                    message: format!(
                        "Simple type alias `{}` should be marked `[@@unfold]` so the \
                         normalizer expands it automatically. Without `unfold`, F* treats \
                         it as an opaque definition, causing type mismatches.",
                        lhs
                    ),
                    fix: Some(fix),
                });
            }

            i += 1;
        }

        diagnostics
    }
}

/// Check if a string is a simple F* identifier (no spaces, no special chars).
fn is_simple_ident(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let first = s.as_bytes()[0];
    if !first.is_ascii_alphabetic() && first != b'_' {
        return false;
    }
    s.bytes().all(|b| is_ident_char(b))
}

/// Check if an RHS is a simple type alias (just an identifier or qualified name).
///
/// Examples that qualify: `nat`, `FStar.UInt32.t`, `my_other_type`
/// Examples that don't: `x + 1`, `fun x -> x`, `match ...`, `if ...`
fn is_simple_type_rhs(s: &str) -> bool {
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return false;
    }
    // Must not contain operators or keywords suggesting computation.
    if trimmed.contains("fun ") || trimmed.contains("match ")
        || trimmed.contains("if ") || trimmed.contains("let ")
        || trimmed.contains("begin") || trimmed.contains('(')
        || trimmed.contains('{') || trimmed.contains('[')
        || trimmed.contains('+') || trimmed.contains('-')
        || trimmed.contains('*') || trimmed.contains('/')
    {
        return false;
    }
    // Must be a single token: identifier with optional dots.
    let first = trimmed.as_bytes()[0];
    if !first.is_ascii_alphabetic() && first != b'_' {
        return false;
    }
    trimmed.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'' || b == b'.')
}

// ==========================================================================
// FST040: AttributeTargetRule
// ==========================================================================

/// FST040: Detect `@@@` vs `@@` attribute target mismatch.
///
/// - `[@@attr]` applies to the NEXT definition/term.
/// - `[@@@attr]` applies to the ENCLOSING module/declaration.
///
/// Common mistake: using `@@@` with per-definition attributes like
/// `inline_for_extraction`, or `@@` with module-level attributes.
pub struct AttributeTargetRule;

impl AttributeTargetRule {
    pub fn new() -> Self {
        Self
    }
}

/// Attributes that are almost always per-definition (should use `@@`).
const PER_DEFINITION_ATTRS: &[&str] = &[
    "inline_for_extraction",
    "noextract",
    "unfold",
    "strict_on_arguments",
    "plugin",
    "CInline",
    "CMacro",
    "CPrologue",
    "CEpilogue",
    "deprecated",
    "warn_on_use",
    "simp",
    "simp_comm",
    "erasable",
    "do_not_unrefine",
    "specialize",
];

/// Attributes that are almost always module-level (should use `@@@`).
const MODULE_LEVEL_ATTRS: &[&str] = &[
    "expect_failure",
    "expect_lax_failure",
];

impl Rule for AttributeTargetRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST040
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_comment_depth: u32 = 0;

        for (line_idx, line) in content.lines().enumerate() {
            block_comment_depth = update_block_comment_depth(line, block_comment_depth);
            if block_comment_depth > 0 {
                continue;
            }

            // Strip both block comments `(* ... *)` and line comments `// ...`
            // so that attributes inside comments are not flagged.
            let no_block = strip_block_comments(line);
            let effective = strip_line_comment(&no_block);
            let trimmed = effective.trim();

            // Check for `[@@@attr]` with per-definition attributes.
            if trimmed.contains("[@@@") {
                for &attr in PER_DEFINITION_ATTRS {
                    let pattern = format!("[@@@{}", attr);
                    if let Some(pos) = trimmed.find(&pattern) {
                        // Verify the attribute name ends properly.
                        let after_pos = pos + pattern.len();
                        let after_ok = after_pos >= trimmed.len()
                            || !is_ident_char(trimmed.as_bytes()[after_pos]);
                        if after_ok {
                            let col = byte_to_char_col(
                                line,
                                line.find(&pattern).unwrap_or(0),
                            );
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST040,
                                severity: DiagnosticSeverity::Warning,
                                file: file.to_path_buf(),
                                range: Range::new(line_idx + 1, col, line_idx + 1, col + pattern.len() + 1),
                                message: format!(
                                    "`[@@@{}]` applies module-wide. Did you mean `[@@{}]` \
                                     to apply only to the next definition?",
                                    attr, attr
                                ),
                                fix: None,
                            });
                            break; // One diagnostic per line.
                        }
                    }
                }
            }

            // Check for `[@@attr]` (exactly two `@`) with module-level attributes.
            // Must NOT be `[@@@` (three `@`).
            if trimmed.contains("[@@") && !trimmed.contains("[@@@") {
                for &attr in MODULE_LEVEL_ATTRS {
                    let pattern = format!("[@@{}", attr);
                    if let Some(pos) = trimmed.find(&pattern) {
                        // Make sure it's exactly `[@@` and not `[@@@`.
                        // We already checked !contains("[@@@"), so this is safe.
                        let after_pos = pos + pattern.len();
                        let after_ok = after_pos >= trimmed.len()
                            || !is_ident_char(trimmed.as_bytes()[after_pos]);
                        if after_ok {
                            let col = byte_to_char_col(
                                line,
                                line.find(&pattern).unwrap_or(0),
                            );
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST040,
                                severity: DiagnosticSeverity::Warning,
                                file: file.to_path_buf(),
                                range: Range::new(line_idx + 1, col, line_idx + 1, col + pattern.len() + 1),
                                message: format!(
                                    "`[@@{}]` applies to the next definition only. Did you mean \
                                     `[@@@{}]` to apply to the enclosing module/scope?",
                                    attr, attr
                                ),
                                fix: None,
                            });
                            break;
                        }
                    }
                }
            }
        }

        diagnostics
    }
}

// ==========================================================================
// Tests
// ==========================================================================


// ==========================================================================
// FST028: StrictOnArgumentsRule
// ==========================================================================

/// FST028: Detect pattern matching on implicit arguments without `[@@strict_on_arguments]`.
///
/// When a function matches on an implicit `#a` argument, it won't reduce unless
/// that argument is concrete. Adding `[@@strict_on_arguments [...]]` tells the
/// normalizer to be strict on specific arguments.
pub struct StrictOnArgumentsRule;

impl StrictOnArgumentsRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for StrictOnArgumentsRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST028
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_depth: u32 = 0;
        let lines: Vec<&str> = content.lines().collect();

        let mut i = 0;
        while i < lines.len() {
            let line = lines[i];
            if line_in_block_comment(block_depth, line) {
                block_depth = update_block_comment_depth(line, block_depth);
                i += 1;
                continue;
            }
            block_depth = update_block_comment_depth(line, block_depth);

            let trimmed = strip_line_comment(line).trim();

            // Look for `let` or `let rec` function definitions
            let is_let = trimmed.starts_with("let ")
                || trimmed.starts_with("let rec ")
                || trimmed.starts_with("and ");

            if !is_let {
                i += 1;
                continue;
            }

            // Check for strict_on_arguments attribute in preceding lines (up to 5 lines back)
            let has_strict = has_attribute_before(&lines, i, "strict_on_arguments");

            if has_strict {
                i += 1;
                continue;
            }

            // Extract implicit parameter names from the definition line and continuation
            let implicit_params = extract_implicit_params(trimmed);
            if implicit_params.is_empty() {
                i += 1;
                continue;
            }

            // Collect the function body (lines until next top-level definition or blank)
            let body_start = i;
            let body = collect_function_body(&lines, body_start);

            // Check if any implicit param is matched on
            for param in &implicit_params {
                let match_pattern = format!("match {}", param);
                let match_pattern2 = format!("match ({}", param);
                if body.contains(&match_pattern) || body.contains(&match_pattern2) {
                    let line_num = i + 1;
                    let col = line.find("let").unwrap_or(0);
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST028,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::new(
                            line_num,
                            byte_to_char_col(line, col),
                            line_num,
                            byte_to_char_col(line, col + trimmed.len().min(line.len())),
                        ),
                        message: format!(
                            "Function matches on implicit argument `{}` but lacks \
                             `[@@strict_on_arguments [...]]` — it won't reduce unless \
                             the implicit is concrete.",
                            param
                        ),
                        fix: None,
                    });
                    break; // one diagnostic per function
                }
            }

            i += 1;
        }

        diagnostics
    }
}

/// Check if an attribute string appears in the lines preceding index `line_idx`.
fn has_attribute_before(lines: &[&str], line_idx: usize, attr: &str) -> bool {
    let start = line_idx.saturating_sub(5);
    for j in start..line_idx {
        if lines[j].contains(attr) {
            return true;
        }
    }
    false
}

/// Extract implicit parameter names from a function definition line.
///
/// Looks for `#name` or `(#name:` patterns. Returns the bare names without `#`.
fn extract_implicit_params(def_line: &str) -> Vec<String> {
    let mut params = Vec::new();
    let bytes = def_line.as_bytes();
    let len = bytes.len();
    let mut i = 0;

    while i < len {
        if bytes[i] == b'#' {
            i += 1;
            // Read identifier after #
            let start = i;
            while i < len && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'\'') {
                i += 1;
            }
            if i > start {
                let name = &def_line[start..i];
                params.push(name.to_string());
            }
        } else if bytes[i] == b'=' && (i + 1 >= len || bytes[i + 1] != b'=') {
            // Stop at the definition body
            break;
        } else {
            i += 1;
        }
    }

    params
}

/// Collect the body of a function starting at `start_idx`.
///
/// Concatenates lines from `start_idx` to the next blank line or top-level
/// definition, returning the joined text.
fn collect_function_body(lines: &[&str], start_idx: usize) -> String {
    let mut body = String::new();
    for j in start_idx..lines.len().min(start_idx + 50) {
        let t = lines[j].trim();
        if j > start_idx
            && (t.starts_with("let ") || t.starts_with("val ")
                || t.starts_with("type ") || t.starts_with("module ")
                || t.starts_with("open "))
            && !t.starts_with("let (")
        {
            break;
        }
        body.push(' ');
        body.push_str(t);
    }
    body
}

// ==========================================================================
// FST031: OpaqueWithoutRevealRule
// ==========================================================================

/// FST031: Detect `[@@opaque_to_smt]` definitions never `reveal_opaque`d in the same file.
///
/// A definition marked `opaque_to_smt` hides its body from the SMT solver.
/// If there's no corresponding `reveal_opaque` call in the file, the definition
/// is effectively invisible to proofs, which may be unintentional.
pub struct OpaqueWithoutRevealRule;

impl OpaqueWithoutRevealRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for OpaqueWithoutRevealRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST031
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_depth: u32 = 0;
        let lines: Vec<&str> = content.lines().collect();

        let mut i = 0;
        while i < lines.len() {
            let line = lines[i];
            let prev_depth = block_depth;
            block_depth = update_block_comment_depth(line, block_depth);

            if line_in_block_comment(prev_depth, line) {
                i += 1;
                continue;
            }

            let code = strip_line_comment(line);

            // Look for opaque_to_smt attribute
            if !code.contains("opaque_to_smt") {
                i += 1;
                continue;
            }

            // Confirm it's an attribute (within [@@...])
            if !code.contains("[@@") && !code.contains("[@@ ") {
                i += 1;
                continue;
            }

            // Find the name of the next definition (val or let on same or following lines)
            let def_name = find_next_definition_name(&lines, i);
            if let Some((name, def_line_idx)) = def_name {
                // Search the entire file for reveal_opaque with this name
                let quoted_name = format!("`{}", name);
                let string_name = format!("\"{}\"", name);
                // Also check for qualified names ending with .name
                let dot_name = format!(".{}", name);

                let mut found_reveal = false;
                for line in &lines {
                    if line.contains("reveal_opaque") {
                        if line.contains(&quoted_name)
                            || line.contains(&string_name)
                            || line.contains(&dot_name)
                        {
                            found_reveal = true;
                            break;
                        }
                    }
                    // Also check for norm_spec with unfold
                    if line.contains("norm_spec") && line.contains(&name) {
                        found_reveal = true;
                        break;
                    }
                }

                if !found_reveal {
                    let diag_line = def_line_idx + 1;
                    let col = lines[def_line_idx]
                        .find(&name)
                        .unwrap_or(0);
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST031,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::new(
                            diag_line,
                            byte_to_char_col(lines[def_line_idx], col),
                            diag_line,
                            byte_to_char_col(lines[def_line_idx], col + name.len()),
                        ),
                        message: format!(
                            "`{}` is marked `opaque_to_smt` but `reveal_opaque` is never \
                             called for it in this file — its definition is invisible to proofs.",
                            name
                        ),
                        fix: None,
                    });
                }
            }

            i += 1;
        }

        diagnostics
    }
}

/// Find the name of the next `val` or `let` definition after line `start_idx`.
///
/// Returns `Some((name, line_index))` or `None`.
fn find_next_definition_name(lines: &[&str], start_idx: usize) -> Option<(String, usize)> {
    for j in start_idx..lines.len().min(start_idx + 5) {
        let trimmed = lines[j].trim();
        // Try val
        if let Some(rest) = trimmed.strip_prefix("val ") {
            let name = rest.split(|c: char| c == ':' || c.is_whitespace())
                .next()
                .unwrap_or("");
            if !name.is_empty() {
                return Some((name.to_string(), j));
            }
        }
        // Try let / let rec
        for prefix in &["let rec ", "let "] {
            if let Some(rest) = trimmed.strip_prefix(prefix) {
                let name = rest.split(|c: char| {
                    c == ':' || c == '(' || c == '#' || c.is_whitespace()
                })
                    .next()
                    .unwrap_or("");
                if !name.is_empty() && name != "rec" {
                    return Some((name.to_string(), j));
                }
            }
        }
    }
    None
}

// ==========================================================================
// FST034: SimpCandidateRule
// ==========================================================================

/// FST034: Detect equality lemmas that could be `[@@simp]` candidates.
///
/// A lemma whose postcondition is `ensures (f x == g x)` or `ensures (f x = g x)`
/// is a rewrite rule suitable for the `[@@simp]` attribute. Suggests adding it
/// when absent.
pub struct SimpCandidateRule;

impl SimpCandidateRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for SimpCandidateRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST034
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_depth: u32 = 0;
        let lines: Vec<&str> = content.lines().collect();

        let mut i = 0;
        while i < lines.len() {
            let line = lines[i];
            let prev_depth = block_depth;
            block_depth = update_block_comment_depth(line, block_depth);

            if line_in_block_comment(prev_depth, line) {
                i += 1;
                continue;
            }

            let trimmed = strip_line_comment(line).trim_start();

            // Look for `val` declarations with `Lemma`
            if !trimmed.starts_with("val ") {
                i += 1;
                continue;
            }

            // Check if already has [@@simp]
            if has_attribute_before(&lines, i, "simp") {
                i += 1;
                continue;
            }

            // Collect the val signature (may span multiple lines)
            let sig = collect_val_signature(&lines, i);

            // Check for Lemma return type with ensures containing == or =
            if !sig.contains("Lemma") {
                i += 1;
                continue;
            }

            if let Some(ensures_part) = extract_ensures(&sig) {
                // Check for equality: == or = (but not ==> which is implication)
                let has_eq = has_double_equals(&ensures_part)
                    || has_bare_equals(&ensures_part);
                if has_eq {
                    let line_num = i + 1;
                    let col = line.find("val").unwrap_or(0);
                    let name = trimmed.strip_prefix("val ")
                        .and_then(|r| r.split(|c: char| c == ':' || c.is_whitespace()).next())
                        .unwrap_or("?");
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST034,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::new(
                            line_num,
                            byte_to_char_col(line, col),
                            line_num,
                            byte_to_char_col(line, col + 3),
                        ),
                        message: format!(
                            "Lemma `{}` has an equality postcondition — \
                             consider adding `[@@simp]` to use it as a rewrite rule.",
                            name
                        ),
                        fix: None,
                    });
                }
            }

            i += 1;
        }

        diagnostics
    }
}

/// Collect a val signature spanning multiple lines until the next top-level declaration.
fn collect_val_signature(lines: &[&str], start: usize) -> String {
    let mut sig = String::new();
    for j in start..lines.len().min(start + 15) {
        let t = lines[j].trim();
        if j > start
            && (t.starts_with("let ") || t.starts_with("val ")
                || t.starts_with("type ") || t.starts_with("module ")
                || t.starts_with("open ") || t.is_empty())
        {
            break;
        }
        sig.push(' ');
        sig.push_str(t);
    }
    sig
}

/// Extract the ensures clause content from a signature string.
fn extract_ensures(sig: &str) -> Option<String> {
    // Find `ensures` or `ensures (`
    let idx = sig.find("ensures")?;
    let rest = &sig[idx + 7..]; // skip "ensures"
    Some(rest.to_string())
}

/// Check if a string contains `==` that is NOT part of `==>`.
fn has_double_equals(s: &str) -> bool {
    let bytes = s.as_bytes();
    for i in 0..bytes.len().saturating_sub(1) {
        if bytes[i] == b'=' && bytes[i + 1] == b'=' {
            // Not ==> (implication)
            let next2 = if i + 2 < bytes.len() { bytes[i + 2] } else { b' ' };
            if next2 != b'>' {
                return true;
            }
        }
    }
    false
}

/// Check if a string contains bare `=` (not `==`, `==>`, `<=`, `>=`, `!=`).
fn has_bare_equals(s: &str) -> bool {
    let bytes = s.as_bytes();
    for i in 0..bytes.len() {
        if bytes[i] == b'=' {
            let prev = if i > 0 { bytes[i - 1] } else { b' ' };
            let next = if i + 1 < bytes.len() { bytes[i + 1] } else { b' ' };
            // Not ==, !=, <=, >=, ==>
            if prev != b'=' && prev != b'!' && prev != b'<' && prev != b'>'
                && next != b'=' && next != b'>'
            {
                return true;
            }
        }
    }
    false
}

// ==========================================================================
// FST037: TotVsGtotRule
// ==========================================================================

/// FST037: Detect `erased` parameters in `Tot` context.
///
/// In F*, `erased` values can only be consumed in `GTot` (ghost) context. A
/// function that takes an `erased` parameter but has a `Tot` effect is always
/// wrong — it will fail type checking.
pub struct TotVsGtotRule;

impl TotVsGtotRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for TotVsGtotRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST037
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_depth: u32 = 0;
        let lines: Vec<&str> = content.lines().collect();

        let mut i = 0;
        while i < lines.len() {
            let line = lines[i];
            let prev_depth = block_depth;
            block_depth = update_block_comment_depth(line, block_depth);

            if line_in_block_comment(prev_depth, line) {
                i += 1;
                continue;
            }

            let trimmed = strip_line_comment(line).trim_start();

            // Look for val declarations
            if !trimmed.starts_with("val ") && !trimmed.starts_with("assume val ") {
                i += 1;
                continue;
            }

            let sig = collect_val_signature(&lines, i);

            // Check: has `erased` in parameters AND `Tot` in return type (not GTot)
            if !sig.contains("erased") {
                i += 1;
                continue;
            }

            // Find arrow-separated parts — the last segment is the return type
            // Simple heuristic: look for `Tot ` (with space) after the last `->`
            // and `erased` before it
            if has_erased_tot_mismatch(&sig) {
                let line_num = i + 1;
                let col = line.find("val")
                    .or_else(|| line.find("assume"))
                    .unwrap_or(0);
                let name = extract_val_name(trimmed);
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST037,
                    severity: DiagnosticSeverity::Error,
                    file: file.to_path_buf(),
                    range: Range::new(
                        line_num,
                        byte_to_char_col(line, col),
                        line_num,
                        byte_to_char_col(line, col + trimmed.len().min(line.len())),
                    ),
                    message: format!(
                        "Function `{}` takes `erased` parameter but returns `Tot` — \
                         `erased` values can only be consumed in `GTot` context.",
                        name
                    ),
                    fix: None,
                });
            }

            i += 1;
        }

        diagnostics
    }
}

/// Check if a signature has the erased-in-Tot mismatch.
///
/// Returns true if `erased` appears in parameter position and `Tot` (not `GTot`)
/// appears as the return effect.
fn has_erased_tot_mismatch(sig: &str) -> bool {
    // Find the last `->` to split parameters from return type
    let last_arrow = sig.rfind("->");
    if let Some(arrow_pos) = last_arrow {
        let params = &sig[..arrow_pos];
        let ret = &sig[arrow_pos..];

        // Parameters must contain `erased`
        if !params.contains("erased") {
            return false;
        }

        // Return type must contain `Tot` but not `GTot`
        // Pattern: `-> Tot ` or `-> Pure ` (Tot is the default non-ghost effect)
        if ret.contains("Tot ") || ret.contains("Tot(") {
            // Make sure it's not GTot
            if !ret.contains("GTot") {
                return true;
            }
        }

        // Also detect: `erased a -> b` where `b` has no effect annotation
        // (default is Tot). But this is harder to detect without parsing,
        // so only flag explicit `Tot`.
    }
    false
}

/// Extract the name from a `val` declaration line.
fn extract_val_name(trimmed: &str) -> &str {
    let rest = trimmed
        .strip_prefix("assume val ")
        .or_else(|| trimmed.strip_prefix("val "))
        .unwrap_or(trimmed);
    rest.split(|c: char| c == ':' || c.is_whitespace())
        .next()
        .unwrap_or("?")
}

// ==========================================================================
// FST038: IntroduceWithRule
// ==========================================================================

/// FST038: Suggest `introduce forall ... with` for structured universal proofs.
///
/// When code uses `Classical.forall_intro` or similar manual patterns, the
/// structured `introduce forall x. P x with (proof)` syntax is cleaner.
pub struct IntroduceWithRule;

impl IntroduceWithRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for IntroduceWithRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST038
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_depth: u32 = 0;

        let patterns = [
            ("Classical.forall_intro", "introduce forall x. P x with (proof)"),
            ("Classical.forall_intro_2", "introduce forall x y. P x y with (proof)"),
            ("Classical.forall_intro_3", "introduce forall x y z. P x y z with (proof)"),
            ("Classical.impl_intro", "introduce implies P with (proof)"),
        ];

        for (line_idx, line) in content.lines().enumerate() {
            let prev_depth = block_depth;
            block_depth = update_block_comment_depth(line, block_depth);

            if line_in_block_comment(prev_depth, line) {
                continue;
            }

            let code = strip_line_comment(line);

            for &(pattern, suggestion) in &patterns {
                if let Some(byte_pos) = code.find(pattern) {
                    let line_num = line_idx + 1;
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST038,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::new(
                            line_num,
                            byte_to_char_col(line, byte_pos),
                            line_num,
                            byte_to_char_col(line, byte_pos + pattern.len()),
                        ),
                        message: format!(
                            "Consider using `{}` instead of `{}` for structured proof.",
                            suggestion, pattern
                        ),
                        fix: None,
                    });
                    break; // one diagnostic per line
                }
            }
        }

        diagnostics
    }
}

// ==========================================================================
// FST041: RequiresTrueOkRule
// ==========================================================================

/// FST041: Flag `requires True` paired with removal hints.
///
/// In F*, `requires True` is intentional — it documents that the caller's
/// proof obligation is trivially satisfied. This rule detects `requires True`
/// near TODO/FIXME comments suggesting removal, and warns that removal is wrong.
pub struct RequiresTrueOkRule;

impl RequiresTrueOkRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for RequiresTrueOkRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST041
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_depth: u32 = 0;
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let prev_depth = block_depth;
            block_depth = update_block_comment_depth(line, block_depth);

            if line_in_block_comment(prev_depth, line) {
                continue;
            }

            let code = strip_line_comment(line);

            // Look for `requires True` (with various whitespace/paren combos)
            if !contains_requires_true(code) {
                continue;
            }

            // Check nearby lines (same line comment, +/- 2 lines) for removal hints
            let has_removal_hint = nearby_has_removal_hint(&lines, line_idx);

            if has_removal_hint {
                let byte_pos = code.find("requires").unwrap_or(0);
                let line_num = line_idx + 1;
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST041,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::new(
                        line_num,
                        byte_to_char_col(line, byte_pos),
                        line_num,
                        byte_to_char_col(line, byte_pos + 8),
                    ),
                    message: "`requires True` is intentional in F* — it ensures the \
                              caller's proof obligation is trivially satisfied. \
                              Do not remove it."
                        .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }
}

/// Check if a code line contains `requires True` (with optional parens).
fn contains_requires_true(code: &str) -> bool {
    // Match patterns: `requires True`, `(requires True)`, `requires (True)`
    let Some(idx) = code.find("requires") else { return false };
    let after = code[idx + 8..].trim_start();
    let after = after.strip_prefix('(').unwrap_or(after);
    let after = after.trim_start();
    after.starts_with("True")
}

/// Check if nearby lines contain TODO/FIXME comments about removing requires True.
fn nearby_has_removal_hint(lines: &[&str], line_idx: usize) -> bool {
    let start = line_idx.saturating_sub(2);
    let end = (line_idx + 3).min(lines.len());

    let removal_keywords = ["TODO", "FIXME", "HACK", "remove", "redundant", "unnecessary"];

    for j in start..end {
        let line_lower = lines[j].to_lowercase();
        // Check if line has both a removal keyword and mentions "requires" or "True"
        if removal_keywords.iter().any(|kw| lines[j].contains(kw) || line_lower.contains(&kw.to_lowercase())) {
            if line_lower.contains("requires") || line_lower.contains("true") {
                return true;
            }
        }
    }
    false
}

// ==========================================================================
// FST043: TickVsExplicitRule
// ==========================================================================

/// FST043: Detect inconsistent implicit variable syntax in the same declaration.
///
/// F* supports two ways to introduce implicit type variables:
/// - Tick syntax: `'a`, `'b` (auto-bound)
/// - Explicit binders: `#a:Type`, `(#b:Type)`
///
/// Mixing both in one declaration is confusing and should be avoided.
pub struct TickVsExplicitRule;

impl TickVsExplicitRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for TickVsExplicitRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST043
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_depth: u32 = 0;
        let lines: Vec<&str> = content.lines().collect();

        let mut i = 0;
        while i < lines.len() {
            let line = lines[i];
            let prev_depth = block_depth;
            block_depth = update_block_comment_depth(line, block_depth);

            if line_in_block_comment(prev_depth, line) {
                i += 1;
                continue;
            }

            let trimmed = strip_line_comment(line).trim_start();

            // Only check val and let declarations
            let is_decl = trimmed.starts_with("val ")
                || trimmed.starts_with("let ")
                || trimmed.starts_with("let rec ");

            if !is_decl {
                i += 1;
                continue;
            }

            // Collect the full signature
            let sig = if trimmed.starts_with("val ") {
                collect_val_signature(&lines, i)
            } else {
                // For let, take until =
                let mut s = String::new();
                for j in i..lines.len().min(i + 10) {
                    let t = lines[j].trim();
                    s.push(' ');
                    s.push_str(t);
                    if t.contains('=') {
                        break;
                    }
                }
                s
            };

            let has_tick = has_tick_variables(&sig);
            let has_explicit = has_explicit_implicit_binders(&sig);

            if has_tick && has_explicit {
                let line_num = i + 1;
                let col = line.find("val")
                    .or_else(|| line.find("let"))
                    .unwrap_or(0);
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST043,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::new(
                        line_num,
                        byte_to_char_col(line, col),
                        line_num,
                        byte_to_char_col(line, col + trimmed.len().min(line.len())),
                    ),
                    message: "Inconsistent implicit syntax — mixing tick variables (`'a`) \
                              with explicit `#` binders (`#a:Type`) in the same declaration. \
                              Pick one style."
                        .to_string(),
                    fix: None,
                });
            }

            i += 1;
        }

        diagnostics
    }
}

/// Check if a signature contains tick variables (`'a`, `'b`, etc.).
///
/// Tick variables: `'` followed by a lowercase letter, not inside a string.
fn has_tick_variables(sig: &str) -> bool {
    let bytes = sig.as_bytes();
    let len = bytes.len();
    let mut i = 0;
    let mut in_string = false;

    while i < len {
        if in_string {
            if bytes[i] == b'\\' {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if bytes[i] == b'"' {
            in_string = true;
            i += 1;
            continue;
        }
        if bytes[i] == b'\'' && i + 1 < len && bytes[i + 1].is_ascii_lowercase() {
            // Make sure it's not part of an identifier (e.g., `x'a` continuation)
            if i == 0 || !bytes[i - 1].is_ascii_alphanumeric() && bytes[i - 1] != b'_' {
                return true;
            }
        }
        i += 1;
    }
    false
}

/// Check if a signature contains explicit implicit binders (`#a`, `(#a:Type)`).
fn has_explicit_implicit_binders(sig: &str) -> bool {
    let bytes = sig.as_bytes();
    let len = bytes.len();
    let mut i = 0;
    let mut in_string = false;

    while i < len {
        if in_string {
            if bytes[i] == b'\\' {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if bytes[i] == b'"' {
            in_string = true;
            i += 1;
            continue;
        }
        if bytes[i] == b'#' && i + 1 < len && bytes[i + 1].is_ascii_lowercase() {
            // Check it's a binder position (preceded by whitespace, `(`, or start)
            if i == 0 || bytes[i - 1].is_ascii_whitespace() || bytes[i - 1] == b'(' {
                return true;
            }
        }
        i += 1;
    }
    false
}

// ==========================================================================
// FST044: MissingDecreasesRule
// ==========================================================================

/// FST044: Detect `let rec` without a `decreases` clause.
///
/// Recursive functions should have explicit `decreases` clauses for clear
/// termination proofs. F* can infer structural recursion in simple cases,
/// but an explicit clause documents the termination argument.
pub struct MissingDecreasesRule;

impl MissingDecreasesRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for MissingDecreasesRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST044
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_depth: u32 = 0;
        let lines: Vec<&str> = content.lines().collect();

        let mut i = 0;
        while i < lines.len() {
            let line = lines[i];
            let prev_depth = block_depth;
            block_depth = update_block_comment_depth(line, block_depth);

            if line_in_block_comment(prev_depth, line) {
                i += 1;
                continue;
            }

            let trimmed = strip_line_comment(line).trim_start();

            // Look for `let rec` definitions
            if !trimmed.starts_with("let rec ") {
                i += 1;
                continue;
            }

            // Extract function name
            let rest = &trimmed[8..]; // skip "let rec "
            let func_name = rest
                .split(|c: char| c == ':' || c == '(' || c == '#' || c.is_whitespace())
                .next()
                .unwrap_or("?");

            if func_name.is_empty() || func_name == "?" {
                i += 1;
                continue;
            }

            // Collect the function signature + body
            let body = collect_function_body(&lines, i);

            // Check if the function actually calls itself
            if !is_actually_recursive(func_name, &body) {
                i += 1;
                continue;
            }

            // Check for `decreases` clause
            if body.contains("decreases") {
                i += 1;
                continue;
            }

            // Detect structural recursion patterns.
            // If the function matches on one of its parameters AND the recursive call
            // passes a subterm from that match, F* can infer the decreasing measure.
            // Severity depends on confidence:
            //  - match on a parameter + recursive call with subterm → suppress (FP)
            //  - match present but can't confirm parameter match → Hint (likely structural)
            //  - no match at all → Info (user should add decreases)
            let has_match = body.contains("match ") && body.contains(" with");
            if has_match {
                // Extract parameter names from the function signature (between func_name and `=`).
                let sig_start = body.find(func_name).unwrap_or(0) + func_name.len();
                let sig_end = body.find(" =").or_else(|| body.find("\n=")).unwrap_or(body.len());
                let sig = if sig_start < sig_end { &body[sig_start..sig_end] } else { "" };

                // Collect parameter names (words after `(` or `#(` that look like identifiers).
                let mut params: Vec<&str> = Vec::new();
                for word in sig.split_whitespace() {
                    let w = word.trim_start_matches('(').trim_start_matches('#')
                        .trim_end_matches(')').trim_end_matches(':');
                    if !w.is_empty() && w.bytes().next().map_or(false, |b| b.is_ascii_lowercase() || b == b'_')
                        && w.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'')
                    {
                        params.push(w);
                    }
                }

                // Check if any `match X` has X as one of the parameters.
                let body_after_eq = body.get(sig_end..).unwrap_or("");
                let mut matches_param = false;
                let mut search = 0;
                while let Some(m) = body_after_eq[search..].find("match ") {
                    let mstart = search + m + 6;
                    let match_target = body_after_eq[mstart..].split_whitespace().next().unwrap_or("");
                    if params.contains(&match_target) {
                        matches_param = true;
                        break;
                    }
                    search = mstart;
                }

                if matches_param {
                    // High confidence: matching on a parameter → F* infers decreases.
                    // Suppress entirely — this is the standard F* pattern.
                    i += 1;
                    continue;
                }
                // match present but not on a parameter → still likely structural, but less certain.
                // Emit as Hint.
            }

            let severity = if has_match {
                DiagnosticSeverity::Hint
            } else {
                DiagnosticSeverity::Info
            };

            let line_num = i + 1;
            let col = line.find("let rec").unwrap_or(0);
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST044,
                severity,
                file: file.to_path_buf(),
                range: Range::new(
                    line_num,
                    byte_to_char_col(line, col),
                    line_num,
                    byte_to_char_col(line, col + 7 + func_name.len() + 1),
                ),
                message: format!(
                    "Recursive function `{}` has no `decreases` clause — \
                     add one for explicit termination proof.",
                    func_name
                ),
                fix: None,
            });

            i += 1;
        }

        diagnostics
    }
}

/// Check if a function body actually contains a recursive call to `func_name`.
fn is_actually_recursive(func_name: &str, body: &str) -> bool {
    // Look for the function name after `=` in a call position.
    // It must appear as a standalone token (not part of a larger identifier).
    let name_len = func_name.len();
    let bytes = body.as_bytes();
    let name_bytes = func_name.as_bytes();
    let mut found_equals = false;

    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'=' && !found_equals {
            // Check it's not == or =>
            let next = if i + 1 < bytes.len() { bytes[i + 1] } else { b' ' };
            if next != b'=' && next != b'>' {
                found_equals = true;
            }
        }
        if found_equals && i + name_len <= bytes.len() && &bytes[i..i + name_len] == name_bytes {
            // Check word boundaries
            let before_ok = i == 0
                || !bytes[i - 1].is_ascii_alphanumeric() && bytes[i - 1] != b'_' && bytes[i - 1] != b'\'';
            let after_ok = i + name_len >= bytes.len()
                || !bytes[i + name_len].is_ascii_alphanumeric()
                    && bytes[i + name_len] != b'_'
                    && bytes[i + name_len] != b'\'';
            if before_ok && after_ok {
                return true;
            }
        }
        i += 1;
    }
    false
}

// ==========================================================================
// Tests
// ==========================================================================


// ==========================================================================
// FST032: UniverseHintRule
// ==========================================================================

/// FST032: Hint about universe annotations (`Type u#0` -> `Type0`, `Type u#1` -> `Type1`).
pub struct UniverseHintRule;

impl UniverseHintRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for UniverseHintRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST032
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut in_block_comment = false;

        for (line_idx, line) in content.lines().enumerate() {
            let (effective, still_in_block) = strip_comments_full(line, in_block_comment);
            in_block_comment = still_in_block;

            // Scan for `Type u#0` and `Type u#1` patterns.
            let bytes = effective.as_bytes();
            let mut i = 0;
            while i + 8 <= bytes.len() {
                // Look for "Type u#"
                if &bytes[i..i + 7] == b"Type u#" {
                    // Verify `Type` is a standalone word.
                    let before_ok = i == 0 || !is_ident_char(bytes[i - 1]);
                    if !before_ok {
                        i += 1;
                        continue;
                    }

                    let digit_start = i + 7;
                    if digit_start < bytes.len() && bytes[digit_start] == b'0' {
                        let after = digit_start + 1;
                        let after_ok =
                            after >= bytes.len() || !bytes[after].is_ascii_alphanumeric();
                        if after_ok {
                            let col = byte_to_char_col(line, i);
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST032,
                                severity: DiagnosticSeverity::Hint,
                                file: file.to_path_buf(),
                                range: Range::new(
                                    line_idx + 1,
                                    col,
                                    line_idx + 1,
                                    col + 8, // "Type u#0"
                                ),
                                message: "`Type u#0` can be written as `Type0` for clarity."
                                    .to_string(),
                                fix: None,
                            });
                        }
                    } else if digit_start < bytes.len() && bytes[digit_start] == b'1' {
                        let after = digit_start + 1;
                        let after_ok =
                            after >= bytes.len() || !bytes[after].is_ascii_alphanumeric();
                        if after_ok {
                            let col = byte_to_char_col(line, i);
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST032,
                                severity: DiagnosticSeverity::Hint,
                                file: file.to_path_buf(),
                                range: Range::new(
                                    line_idx + 1,
                                    col,
                                    line_idx + 1,
                                    col + 8, // "Type u#1"
                                ),
                                message: "`Type u#1` can be written as `Type1` for clarity."
                                    .to_string(),
                                fix: None,
                            });
                        }
                    }
                    i = digit_start + 1;
                } else {
                    i += 1;
                }
            }
        }

        diagnostics
    }
}

// ==========================================================================
// FST033: TacticSuggestionRule
// ==========================================================================

/// FST033: Suggest tactic-based proofs when z3rlimit is very high.
///
/// When `#push-options` or `#set-options` sets `z3rlimit` to >= 100, this
/// hints that the proof might benefit from a tactic-based approach.
pub struct TacticSuggestionRule;

impl TacticSuggestionRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for TacticSuggestionRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST033
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_depth: u32 = 0;

        for (line_idx, line) in content.lines().enumerate() {
            block_depth = update_block_comment_depth(line, block_depth);
            if block_depth > 0 {
                continue;
            }

            let effective = strip_line_comment(line);
            let trimmed = effective.trim();

            // Match `#push-options` or `#set-options` containing z3rlimit.
            if !(trimmed.starts_with("#push-options") || trimmed.starts_with("#set-options")) {
                continue;
            }

            // Extract z3rlimit value.
            if let Some(rlimit_pos) = trimmed.find("z3rlimit") {
                let after = &trimmed[rlimit_pos + "z3rlimit".len()..];
                // Skip whitespace and optional `_factor`.
                let after = after.trim_start();
                // Could be `z3rlimit N` or `z3rlimit_factor N` — only handle plain z3rlimit.
                if after.starts_with('_') {
                    // z3rlimit_factor — skip, different semantics.
                    continue;
                }
                // Parse the numeric value.
                let digits: String = after.chars().take_while(|c| c.is_ascii_digit()).collect();
                if let Ok(limit) = digits.parse::<u64>() {
                    if limit >= 100 {
                        let col = byte_to_char_col(
                            line,
                            line.find("z3rlimit").unwrap_or(0),
                        );
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST033,
                            severity: DiagnosticSeverity::Hint,
                            file: file.to_path_buf(),
                            range: Range::new(line_idx + 1, col, line_idx + 1, col + 8),
                            message: format!(
                                "z3rlimit {} is high. Consider using tactics (`assert ... by`, \
                                 `calc`, `norm`) for more robust proofs that don't depend on \
                                 SMT heuristics.",
                                limit
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
// FST045: NoeqVsUnopteqRule (FIXABLE)
// ==========================================================================

/// FST045: Suggest `unopteq` when `noeq` is used on a record with no function-typed fields.
///
/// `noeq` suppresses all equality. `unopteq` suppresses only auto-generated
/// equality but still permits manually defining decidable equality later.
pub struct NoeqVsUnopteqRule;

impl NoeqVsUnopteqRule {
    pub fn new() -> Self {
        Self
    }
}

/// Check if any field type in a record body contains a function arrow `->`.
///
/// Scans from the opening `{` to the closing `}` of the record body.
/// Returns `true` if any field has a function type (contains `->`).
fn record_has_function_fields(lines: &[&str], start_line: usize) -> bool {
    let mut brace_depth: u32 = 0;
    let mut found_open = false;

    for i in start_line..lines.len() {
        let effective = strip_line_comment(lines[i]);
        for (j, b) in effective.bytes().enumerate() {
            match b {
                b'{' => {
                    brace_depth += 1;
                    found_open = true;
                }
                b'}' => {
                    brace_depth = brace_depth.saturating_sub(1);
                    if found_open && brace_depth == 0 {
                        return false;
                    }
                }
                b'-' if found_open && brace_depth > 0 => {
                    if j + 1 < effective.len() && effective.as_bytes()[j + 1] == b'>' {
                        return true;
                    }
                }
                _ => {}
            }
        }
        // Stop searching after 50 lines to avoid runaway scans.
        if i > start_line + 50 {
            break;
        }
    }
    false
}

impl Rule for NoeqVsUnopteqRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST045
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut block_depth: u32 = 0;

        for (line_idx, line) in lines.iter().enumerate() {
            block_depth = update_block_comment_depth(line, block_depth);
            if block_depth > 0 {
                continue;
            }

            let effective = strip_line_comment(line);
            let trimmed = effective.trim();

            // Match `noeq type`.
            if !trimmed.starts_with("noeq type ") {
                continue;
            }

            // Check if any field has a function type.
            if record_has_function_fields(&lines, line_idx) {
                // Has function fields — `noeq` is appropriate.
                continue;
            }

            // Find the byte position of `noeq` in the original line.
            let noeq_pos = match line.find("noeq") {
                Some(p) => p,
                None => continue,
            };
            let col = byte_to_char_col(line, noeq_pos);

            let fix = Fix {
                message: "Replace `noeq` with `unopteq`".to_string(),
                edits: vec![Edit {
                    file: file.to_path_buf(),
                    range: Range::new(line_idx + 1, col, line_idx + 1, col + 4), // "noeq" is 4 chars
                    new_text: "unopteq".to_string(),
                }],
                confidence: FixConfidence::Medium,
                unsafe_reason: None,
                safety_level: FixSafetyLevel::Caution,
                reversible: true,
                requires_review: true,
            };

            diagnostics.push(Diagnostic {
                rule: RuleCode::FST045,
                severity: DiagnosticSeverity::Info,
                file: file.to_path_buf(),
                range: Range::new(line_idx + 1, col, line_idx + 1, col + 4),
                message:
                    "`noeq` suppresses all equality for this type. Since no fields have \
                     function types, consider `unopteq` instead — it only suppresses \
                     auto-generated equality, allowing you to define decidable equality manually."
                        .to_string(),
                fix: Some(fix),
            });
        }

        diagnostics
    }
}

// ==========================================================================
// FST046: ErasableSuggestionRule
// ==========================================================================

/// FST046: Suggest `[@@ erasable]` for types where all fields are proof-only.
///
/// A type whose fields are all `prop`, `Type0`, `squash`, or `erased` is
/// clearly proof-only and should be marked erasable so extraction removes it.
pub struct ErasableSuggestionRule;

impl ErasableSuggestionRule {
    pub fn new() -> Self {
        Self
    }
}

/// Proof-only type keywords that indicate a field is not computationally relevant.
const PROOF_ONLY_TYPES: &[&str] = &[
    "prop", "Type0", "Type", "squash", "erased", "unit", "b2t",
];

/// Check if a field type is proof-only (contains only proof-related types).
fn is_proof_only_field(field_type: &str) -> bool {
    let trimmed = field_type.trim().trim_end_matches(';');
    // The field type must contain at least one proof-only keyword
    // and must NOT contain computational types.
    PROOF_ONLY_TYPES.iter().any(|kw| {
        let bytes = trimmed.as_bytes();
        let kw_bytes = kw.as_bytes();
        let kw_len = kw_bytes.len();
        let mut i = 0;
        while i + kw_len <= bytes.len() {
            if &bytes[i..i + kw_len] == kw_bytes {
                let before = i == 0 || !is_ident_char(bytes[i - 1]);
                let after = i + kw_len >= bytes.len() || !is_ident_char(bytes[i + kw_len]);
                if before && after {
                    return true;
                }
            }
            i += 1;
        }
        false
    })
}

impl Rule for ErasableSuggestionRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST046
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut block_depth: u32 = 0;
        let mut i = 0;

        while i < lines.len() {
            block_depth = update_block_comment_depth(lines[i], block_depth);
            if block_depth > 0 {
                i += 1;
                continue;
            }

            let trimmed = strip_line_comment(lines[i]).trim();

            // Match type declarations (possibly with `noeq` or `unopteq` prefix).
            let type_keyword_pos = if trimmed.starts_with("type ") {
                Some(0)
            } else if trimmed.starts_with("noeq type ") {
                Some(5)
            } else if trimmed.starts_with("unopteq type ") {
                Some(8)
            } else {
                None
            };

            if type_keyword_pos.is_none() {
                i += 1;
                continue;
            }

            // Check if it already has `[@@ erasable]` on preceding lines.
            let mut has_erasable = false;
            if i > 0 {
                for k in (0..i).rev() {
                    let prev = lines[k].trim();
                    if prev.is_empty() {
                        break;
                    }
                    if prev.contains("erasable") {
                        has_erasable = true;
                        break;
                    }
                    if !prev.starts_with("[@@") && !prev.starts_with("[@@@") {
                        break;
                    }
                }
            }
            if has_erasable || trimmed.contains("erasable") {
                i += 1;
                continue;
            }

            // Find the record body `{ ... }` and check ALL fields.
            let mut brace_depth: u32 = 0;
            let mut found_open = false;
            let mut all_fields_proof_only = true;
            let mut has_fields = false;
            let mut scan_end = i;

            'outer: for k in i..lines.len().min(i + 50) {
                let eff = strip_line_comment(lines[k]);
                for (j, b) in eff.bytes().enumerate() {
                    match b {
                        b'{' => {
                            brace_depth += 1;
                            found_open = true;
                        }
                        b'}' => {
                            brace_depth = brace_depth.saturating_sub(1);
                            if found_open && brace_depth == 0 {
                                scan_end = k;
                                break 'outer;
                            }
                        }
                        b':' if found_open && brace_depth == 1 => {
                            // Found a field separator — the type follows the `:`.
                            let field_type = &eff[j + 1..];
                            has_fields = true;
                            if !is_proof_only_field(field_type) {
                                all_fields_proof_only = false;
                                break 'outer;
                            }
                        }
                        _ => {}
                    }
                }
            }

            if found_open && has_fields && all_fields_proof_only {
                let col = byte_to_char_col(lines[i], lines[i].find("type").unwrap_or(0));
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST046,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::new(i + 1, col, i + 1, col + 4),
                    message:
                        "All fields of this type are proof-only (`prop`, `Type0`, `squash`, \
                         `erased`). Consider adding `[@@ erasable]` so extraction erases it."
                            .to_string(),
                    fix: None,
                });
            }

            i = scan_end + 1;
        }

        diagnostics
    }
}

// ==========================================================================
// FST047: SumVsOrRule
// ==========================================================================

/// FST047: Detect `Prims.sum`/`Inl`/`Inr` in ghost/lemma contexts where `\/` is appropriate.
pub struct SumVsOrRule;

impl SumVsOrRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for SumVsOrRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST047
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut block_depth: u32 = 0;
        let mut in_ghost_context = false;

        for (line_idx, line) in content.lines().enumerate() {
            block_depth = update_block_comment_depth(line, block_depth);
            if block_depth > 0 {
                continue;
            }

            let effective = strip_line_comment(line);
            let trimmed = effective.trim();

            // Track ghost/lemma context.
            if trimmed.starts_with("val ") || trimmed.starts_with("let ") {
                in_ghost_context = trimmed.contains("Lemma")
                    || trimmed.contains("GTot")
                    || trimmed.contains("Ghost");
            }
            // Also set context if the line itself mentions these effects.
            if trimmed.contains("Lemma") || trimmed.contains("GTot") || trimmed.contains("Ghost") {
                in_ghost_context = true;
            }
            // Reset on blank lines or new top-level declarations.
            if trimmed.is_empty() {
                in_ghost_context = false;
            }

            if !in_ghost_context {
                continue;
            }

            // Check for `Prims.sum` usage.
            if let Some(pos) = effective.find("Prims.sum") {
                if is_word_at(effective, pos, "Prims.sum") {
                    let col = byte_to_char_col(line, pos);
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST047,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::new(line_idx + 1, col, line_idx + 1, col + 9),
                        message:
                            "`Prims.sum` is constructive disjunction (with `Inl`/`Inr`). \
                             In a ghost/lemma context, propositional disjunction `\\/` is \
                             usually more appropriate and proof-irrelevant."
                                .to_string(),
                        fix: None,
                    });
                }
            }

            // Check for standalone `sum` as a type (not `Prims.sum`).
            if !effective.contains("Prims.sum") {
                let bytes = effective.as_bytes();
                let mut j = 0;
                while j + 3 <= bytes.len() {
                    if &bytes[j..j + 3] == b"sum" && is_word_at(effective, j, "sum") {
                        // Verify it's in a type position (after `:` or in a type annotation).
                        let before = effective[..j].trim_end();
                        if before.ends_with(':') || before.ends_with("->") || before.ends_with('(')
                        {
                            let col = byte_to_char_col(line, j);
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST047,
                                severity: DiagnosticSeverity::Info,
                                file: file.to_path_buf(),
                                range: Range::new(line_idx + 1, col, line_idx + 1, col + 3),
                                message:
                                    "`sum` is constructive disjunction. In a ghost/lemma \
                                     context, propositional `\\/` is usually more appropriate."
                                        .to_string(),
                                fix: None,
                            });
                            break;
                        }
                    }
                    j += 1;
                }
            }

            // Check for `Inl`/`Inr` constructors in ghost context.
            for ctor in &["Inl", "Inr"] {
                if let Some(pos) = effective.find(ctor) {
                    if is_word_at(effective, pos, ctor) {
                        let col = byte_to_char_col(line, pos);
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST047,
                            severity: DiagnosticSeverity::Info,
                            file: file.to_path_buf(),
                            range: Range::new(line_idx + 1, col, line_idx + 1, col + 3),
                            message: format!(
                                "`{}` is a constructor of `Prims.sum` (constructive disjunction). \
                                 In a ghost/lemma context, consider using `\\/` (propositional \
                                 disjunction) instead.",
                                ctor
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
// FST048: MissingPluginRule
// ==========================================================================

/// FST048: Detect tactic definitions with `Tac` effect missing `[@@plugin]`.
///
/// The `[@@plugin]` attribute compiles tactics to native OCaml, providing
/// 10-100x speedup for complex tactics.
pub struct MissingPluginRule;

impl MissingPluginRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for MissingPluginRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST048
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut block_depth: u32 = 0;

        for (line_idx, line) in lines.iter().enumerate() {
            block_depth = update_block_comment_depth(line, block_depth);
            if block_depth > 0 {
                continue;
            }

            let effective = strip_line_comment(line);
            let trimmed = effective.trim();

            // Look for `let` definitions with `Tac` effect in the signature.
            let is_let = trimmed.starts_with("let ")
                || trimmed.starts_with("let rec ")
                || trimmed.starts_with("and ");
            if !is_let {
                continue;
            }

            // Check if the signature (this line or next few lines) mentions `Tac`.
            let mut has_tac = false;
            let mut has_multi_step = false;
            let scan_end = lines.len().min(line_idx + 30);

            for k in line_idx..scan_end {
                let raw_line = lines[k];
                let kt = strip_line_comment(raw_line).trim();
                if kt.is_empty() {
                    break;
                }
                // Stop at new TOP-LEVEL declarations (not indented body `let ... in`).
                if k > line_idx {
                    let is_top_level = !raw_line.starts_with(' ') && !raw_line.starts_with('\t');
                    if is_top_level
                        && (kt.starts_with("val ") || kt.starts_with("let ")
                            || kt.starts_with("type ") || kt.starts_with("open ")
                            || kt.starts_with("module "))
                    {
                        break;
                    }
                }

                // Check for Tac effect.
                if !has_tac {
                    let bytes = kt.as_bytes();
                    let mut j = 0;
                    while j + 3 <= bytes.len() {
                        if &bytes[j..j + 3] == b"Tac" {
                            let before = j == 0 || !is_ident_char(bytes[j - 1]);
                            let after = j + 3 >= bytes.len() || !is_ident_char(bytes[j + 3]);
                            if before && after {
                                has_tac = true;
                                break;
                            }
                        }
                        j += 1;
                    }
                }

                // Check for multi-step body (`;` or `let ... in`).
                // Only count indicators in body lines (after the definition line).
                if k > line_idx && has_tac {
                    if kt.contains(';') || kt.contains("let ") || kt.contains("begin") {
                        has_multi_step = true;
                    }
                }
            }

            if !has_tac || !has_multi_step {
                continue;
            }

            // Check if `[@@plugin]` is already present on preceding attribute lines.
            let mut has_plugin = false;
            if line_idx > 0 {
                for k in (0..line_idx).rev() {
                    let prev = lines[k].trim();
                    if prev.is_empty() {
                        break;
                    }
                    if prev.contains("plugin") {
                        has_plugin = true;
                        break;
                    }
                    if !prev.starts_with("[@@") && !prev.starts_with("[@@@") {
                        break;
                    }
                }
            }
            if trimmed.contains("plugin") {
                has_plugin = true;
            }

            if has_plugin {
                continue;
            }

            let col = byte_to_char_col(line, line.find("let").unwrap_or(0));
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST048,
                severity: DiagnosticSeverity::Hint,
                file: file.to_path_buf(),
                range: Range::new(line_idx + 1, col, line_idx + 1, col + 3),
                message:
                    "Complex tactic definition missing `[@@plugin]`. Native compilation \
                     via `[@@plugin]` can speed up tactic execution 10-100x."
                        .to_string(),
                fix: None,
            });
        }

        diagnostics
    }
}

// ==========================================================================
// FST049: AutoClassificationRule
// ==========================================================================

/// FST049: Guidance on `[@@auto]` lemma usage.
///
/// Warns when `[@@auto]` is on a complex lemma without SMT patterns, which
/// may cause the simplifier to slow down.
pub struct AutoClassificationRule;

impl AutoClassificationRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for AutoClassificationRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST049
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut block_depth: u32 = 0;

        for (line_idx, line) in lines.iter().enumerate() {
            block_depth = update_block_comment_depth(line, block_depth);
            if block_depth > 0 {
                continue;
            }

            let trimmed = line.trim();

            // Find `[@@auto]` or `[@@@auto]` attributes.
            if !trimmed.contains("auto") || !trimmed.contains("[@@") {
                continue;
            }

            // Verify `auto` is standalone in an attribute context.
            let has_auto_attr = {
                let mut found = false;
                if let Some(bracket_pos) = trimmed.find("[@@") {
                    let after_bracket = &trimmed[bracket_pos..];
                    if let Some(auto_pos) = after_bracket.find("auto") {
                        let abs = auto_pos;
                        let bytes = after_bracket.as_bytes();
                        let before = abs == 0 || !is_ident_char(bytes[abs - 1]);
                        let after_end = abs + 4;
                        let after = after_end >= bytes.len() || !is_ident_char(bytes[after_end]);
                        if before && after {
                            found = true;
                        }
                    }
                }
                found
            };

            if !has_auto_attr {
                continue;
            }

            // Scan the following declaration for SMT patterns or complexity indicators.
            let mut has_smt_pat = false;
            let mut has_complex_body = false;
            let scan_end = lines.len().min(line_idx + 20);

            for k in (line_idx + 1)..scan_end {
                let kt = lines[k].trim();
                if kt.is_empty() {
                    break;
                }
                if k > line_idx + 1
                    && (kt.starts_with("[@@") || kt.starts_with("val ")
                        || kt.starts_with("let rec ") || kt.starts_with("type ")
                        || kt.starts_with("open "))
                {
                    break;
                }

                if kt.contains("SMTPat") || kt.contains("SMTPatOr") || kt.contains("{:pattern") {
                    has_smt_pat = true;
                }
                // Complexity indicators: many parameters or complex structure.
                if kt.contains("forall") || kt.contains("exists")
                    || (kt.contains("->") && kt.matches("->").count() > 3)
                {
                    has_complex_body = true;
                }
            }

            if has_complex_body && !has_smt_pat {
                let col = byte_to_char_col(line, line.find("auto").unwrap_or(0));
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST049,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::new(line_idx + 1, col, line_idx + 1, col + 4),
                    message:
                        "`[@@auto]` on a complex lemma without SMT patterns may cause \
                         slowdowns. Add `[SMTPat ...]` to guide the solver, or verify that \
                         the auto-instantiation is intentional."
                            .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }
}

// ==========================================================================
// FST050: SquashBridgeRule
// ==========================================================================

/// FST050: Suggest `give_proof`/`get_proof` from `FStar.Squash` for bridging
/// propositional and computational contexts.
pub struct SquashBridgeRule;

impl SquashBridgeRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for SquashBridgeRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST050
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut in_block_comment = false;

        for (line_idx, line) in content.lines().enumerate() {
            let (effective, still_in_block) = strip_comments_full(line, in_block_comment);
            in_block_comment = still_in_block;

            // Detect `return_squash` calls — suggest `give_proof` instead.
            if let Some(pos) = effective.find("return_squash") {
                if is_word_at(&effective, pos, "return_squash") {
                    let col = byte_to_char_col(line, pos);
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST050,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::new(line_idx + 1, col, line_idx + 1, col + 13),
                        message:
                            "`return_squash` can be replaced with the more readable \
                             `FStar.Squash.give_proof` for constructing squashed proofs."
                                .to_string(),
                        fix: None,
                    });
                }
            }

            // Detect `Squash.join_squash` — suggest `get_proof`.
            if let Some(pos) = effective.find("join_squash") {
                if is_word_at(&effective, pos, "join_squash") {
                    let col = byte_to_char_col(line, pos);
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST050,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::new(line_idx + 1, col, line_idx + 1, col + 11),
                        message:
                            "`join_squash` can be replaced with the more readable \
                             `FStar.Squash.get_proof` for extracting squashed proofs."
                                .to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }
}

// ==========================================================================
// FST051: DoNotUnrefineRule
// ==========================================================================

/// FST051: Detect refined type aliases missing `[@@do_not_unrefine]`.
///
/// When `let nat = x:int{x >= 0}` is defined, the normalizer may unrefine it
/// back to `int`. Adding `[@@do_not_unrefine]` preserves the refinement.
pub struct DoNotUnrefineRule;

impl DoNotUnrefineRule {
    pub fn new() -> Self {
        Self
    }
}

impl Rule for DoNotUnrefineRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST051
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut block_depth: u32 = 0;

        let mut i = 0;
        while i < lines.len() {
            block_depth = update_block_comment_depth(lines[i], block_depth);
            if block_depth > 0 {
                i += 1;
                continue;
            }

            let effective = strip_line_comment(lines[i]);
            let trimmed = effective.trim();

            // Match `let NAME = ...` (simple let bindings, not `let rec`).
            if !trimmed.starts_with("let ") || trimmed.starts_with("let rec ") {
                i += 1;
                continue;
            }

            // Check if the RHS contains a refinement type: `{` ... `|` ... `}` or `{` ... `}`.
            // Collect the full definition (may span lines).
            let mut def_text = String::new();
            let def_start = i;
            for k in i..lines.len().min(i + 10) {
                let kt = strip_line_comment(lines[k]).trim();
                if k > i
                    && (kt.starts_with("val ") || kt.starts_with("let ")
                        || kt.starts_with("type ") || kt.starts_with("open ")
                        || kt.starts_with("module ") || kt.is_empty())
                {
                    break;
                }
                if !def_text.is_empty() {
                    def_text.push(' ');
                }
                def_text.push_str(kt);
            }

            // Find `=` and check RHS for refinement.
            if let Some(eq_pos) = def_text.find('=') {
                let rhs = def_text[eq_pos + 1..].trim();

                // Check for refinement patterns:
                // - `x:t{P x}` or `(x:t{P x})`
                // - `{x:t | P x}`
                let has_refinement = rhs.contains('{') && rhs.contains('}')
                    && (rhs.contains('|') || rhs.contains(':'));

                if !has_refinement {
                    i += 1;
                    continue;
                }

                // Verify LHS is a simple identifier (no parameters).
                let lhs = def_text["let ".len()..eq_pos].trim();
                // Strip type annotation if present.
                let lhs_name = lhs.split(':').next().unwrap_or(lhs).trim();
                if lhs_name.contains(' ') || lhs_name.is_empty() {
                    i += 1;
                    continue;
                }
                // Must be an identifier.
                if !lhs_name.bytes().all(|b| is_ident_char(b)) {
                    i += 1;
                    continue;
                }

                // Check if `do_not_unrefine` attribute already exists.
                let mut has_attr = false;
                if def_start > 0 {
                    for k in (0..def_start).rev() {
                        let prev = lines[k].trim();
                        if prev.is_empty() {
                            break;
                        }
                        if prev.contains("do_not_unrefine") {
                            has_attr = true;
                            break;
                        }
                        if !prev.starts_with("[@@") && !prev.starts_with("[@@@") {
                            break;
                        }
                    }
                }
                if trimmed.contains("do_not_unrefine") {
                    has_attr = true;
                }

                if !has_attr {
                    let col = byte_to_char_col(
                        lines[def_start],
                        lines[def_start].find("let").unwrap_or(0),
                    );
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST051,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::new(
                            def_start + 1,
                            col,
                            def_start + 1,
                            col + 3 + 1 + lhs_name.len(),
                        ),
                        message: format!(
                            "Refined type alias `{}` may be unrefined by the normalizer. \
                             Add `[@@do_not_unrefine]` to preserve the refinement at all times.",
                            lhs_name
                        ),
                        fix: None,
                    });
                }
            }

            i += 1;
        }

        diagnostics
    }
}

// ==========================================================================
// Tests
// ==========================================================================


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

    // --- Batch A tests (FST024, FST025, FST026, FST029, FST035, FST036, FST039, FST040) ---

    // =====================================================================
    // FST024: DecreasesBoundRule
    // =====================================================================

    fn check_decreases(content: &str) -> Vec<Diagnostic> {
        let rule = DecreasesBoundRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_decreases_unbound_name() {
        let content = "\
module Test

let rec factorial (n: nat) : Tot nat (decreases m) =
  if n = 0 then 1 else n * factorial (n - 1)
";
        let diags = check_decreases(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST024);
        assert!(diags[0].message.contains("m"));
        assert!(diags[0].message.contains("not a parameter"));
    }

    #[test]
    fn test_decreases_bound_name_ok() {
        let content = "\
module Test

let rec factorial (n: nat) : Tot nat (decreases n) =
  if n = 0 then 1 else n * factorial (n - 1)
";
        let diags = check_decreases(content);
        assert!(diags.is_empty(), "Parameter `n` is bound, should not trigger");
    }

    #[test]
    fn test_decreases_no_decreases_clause() {
        let content = "\
module Test

let rec factorial (n: nat) : Tot nat =
  if n = 0 then 1 else n * factorial (n - 1)
";
        let diags = check_decreases(content);
        assert!(diags.is_empty(), "No decreases clause, should not trigger");
    }

    #[test]
    fn test_decreases_with_builtin() {
        let content = "\
module Test

let rec f (xs: list nat) : Tot nat (decreases (List.length xs)) =
  match xs with
  | [] -> 0
  | _ :: tl -> 1 + f tl
";
        let diags = check_decreases(content);
        // `List.length` is a builtin, `xs` is a parameter.
        assert!(diags.is_empty(), "Known builtins in decreases should not trigger");
    }

    // =====================================================================
    // FST025: AssumeTypeVsValRule
    // =====================================================================

    fn check_assume_type(content: &str) -> Vec<Diagnostic> {
        let rule = AssumeTypeVsValRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_assume_type_with_arrows() {
        let content = "\
module Test

assume type process : int -> int -> bool
";
        let diags = check_assume_type(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST025);
        assert!(diags[0].message.contains("assume val"));
    }

    #[test]
    fn test_assume_type_without_arrows() {
        let content = "\
module Test

assume type abstract_state
";
        let diags = check_assume_type(content);
        assert!(diags.is_empty(), "No arrows, valid assume type");
    }

    #[test]
    fn test_assume_val_not_flagged() {
        let content = "\
module Test

assume val process : int -> int -> bool
";
        let diags = check_assume_type(content);
        assert!(diags.is_empty(), "assume val should never trigger this rule");
    }

    // =====================================================================
    // FST026: RevealInTotRule
    // =====================================================================

    fn check_reveal_in_tot(content: &str) -> Vec<Diagnostic> {
        let rule = RevealInTotRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_reveal_in_tot_context() {
        let content = "\
module Test

let f (x: erased nat) : Tot nat =
  reveal x
";
        let diags = check_reveal_in_tot(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST026);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Error);
        assert!(diags[0].message.contains("GTot"));
    }

    #[test]
    fn test_reveal_in_gtot_context_ok() {
        let content = "\
module Test

let f (x: erased nat) : GTot nat =
  reveal x
";
        let diags = check_reveal_in_tot(content);
        assert!(diags.is_empty(), "reveal in GTot is fine");
    }

    #[test]
    fn test_reveal_opaque_in_tot() {
        let content = "\
module Test

let f (x: nat) : Tot nat =
  reveal_opaque (`%my_def) x;
  x + 1
";
        let diags = check_reveal_in_tot(content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("reveal_opaque"));
    }

    #[test]
    fn test_no_reveal_no_diagnostic() {
        let content = "\
module Test

let f (x: nat) : Tot nat =
  x + 1
";
        let diags = check_reveal_in_tot(content);
        assert!(diags.is_empty());
    }

    // =====================================================================
    // FST029: PatternDisjunctionRule
    // =====================================================================

    fn check_pattern_disj(content: &str) -> Vec<Diagnostic> {
        let rule = PatternDisjunctionRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_pattern_disjunction_detected() {
        let content = r#"module Test

val lemma1 : x:nat -> y:nat -> Lemma
  (ensures (forall z. f x z == f z x))
  {:pattern (f x y) \/ (f y x)}
"#;
        let diags = check_pattern_disj(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST029);
        assert!(diags[0].message.contains("disjunctive"));
    }

    #[test]
    fn test_pattern_conjunction_ok() {
        let content = "\
module Test

val lemma1 : x:nat -> y:nat -> Lemma
  (ensures (forall z. f x z == f z x))
  {:pattern (f x y); (f y x)}
";
        let diags = check_pattern_disj(content);
        assert!(diags.is_empty(), "Semicolon-separated is conjunctive, should not trigger");
    }

    #[test]
    fn test_pattern_no_pattern_block() {
        let content = r#"module Test

let x = a \/ b
"#;
        let diags = check_pattern_disj(content);
        assert!(diags.is_empty(), "\\/ outside {{:pattern}} should not trigger");
    }

    // =====================================================================
    // FST035: SimpCommGuardRule
    // =====================================================================

    fn check_simp_comm(content: &str) -> Vec<Diagnostic> {
        let rule = SimpCommGuardRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_simp_comm_without_guard() {
        let content = "\
module Test

[@@simp_comm]
val add_comm : a:nat -> b:nat -> Lemma (a + b == b + a)
";
        let diags = check_simp_comm(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST035);
        assert!(diags[0].message.contains("ordering guard"));
    }

    #[test]
    fn test_simp_comm_with_guard() {
        let content = "\
module Test

[@@simp_comm]
val add_comm : a:nat -> b:nat -> Lemma
  (requires (a <= b))
  (ensures (a + b == b + a))
";
        let diags = check_simp_comm(content);
        assert!(diags.is_empty(), "Has `<=` guard, should not trigger");
    }

    #[test]
    fn test_no_simp_comm_attribute() {
        let content = "\
module Test

[@@simp]
val add_zero : a:nat -> Lemma (a + 0 == a)
";
        let diags = check_simp_comm(content);
        assert!(diags.is_empty(), "simp (not simp_comm) should not trigger");
    }

    // =====================================================================
    // FST036: DollarBinderRule
    // =====================================================================

    fn check_dollar_binder(content: &str) -> Vec<Diagnostic> {
        let rule = DollarBinderRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_dollar_binder_suggests_for_lemma_param() {
        let content = "\
module Test

val apply_lemma : (#proof: nat -> Lemma True) -> nat -> unit
";
        let diags = check_dollar_binder(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST036);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Hint);
        assert!(diags[0].message.contains("$proof"));
    }

    #[test]
    fn test_dollar_binder_no_higher_order() {
        let content = "\
module Test

val f : (#n: nat) -> list nat -> nat
";
        let diags = check_dollar_binder(content);
        assert!(diags.is_empty(), "Simple implicit param should not trigger");
    }

    #[test]
    fn test_dollar_binder_tac_param() {
        let content = "\
module Test

val run_tac : (#t: unit -> Tac nat) -> nat
";
        let diags = check_dollar_binder(content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("$t"));
    }

    // =====================================================================
    // FST039: UnfoldAliasRule
    // =====================================================================

    fn check_unfold_alias(content: &str) -> Vec<Diagnostic> {
        let rule = UnfoldAliasRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_unfold_alias_simple() {
        let content = "\
module Test

let my_nat = nat
";
        let diags = check_unfold_alias(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST039);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Info);
        assert!(diags[0].fix.is_some());
        let fix = diags[0].fix.as_ref().unwrap();
        assert!(fix.edits[0].new_text.contains("[@@unfold]"));
    }

    #[test]
    fn test_unfold_alias_qualified() {
        let content = "\
module Test

let u32 = FStar.UInt32.t
";
        let diags = check_unfold_alias(content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("u32"));
    }

    #[test]
    fn test_unfold_alias_already_has_unfold() {
        let content = "\
module Test

[@@unfold]
let my_nat = nat
";
        let diags = check_unfold_alias(content);
        assert!(diags.is_empty(), "Already has [@@unfold], should not trigger");
    }

    #[test]
    fn test_unfold_alias_computation_rhs() {
        let content = "\
module Test

let result = x + 1
";
        let diags = check_unfold_alias(content);
        assert!(diags.is_empty(), "Computation RHS is not a simple alias");
    }

    #[test]
    fn test_unfold_alias_function_def() {
        let content = "\
module Test

let apply f x = f x
";
        let diags = check_unfold_alias(content);
        assert!(diags.is_empty(), "Function with parameters is not a simple alias");
    }

    #[test]
    fn test_unfold_alias_inline_for_extraction() {
        let content = "\
module Test

[@@inline_for_extraction]
let my_nat = nat
";
        let diags = check_unfold_alias(content);
        assert!(diags.is_empty(), "inline_for_extraction serves same purpose");
    }

    // =====================================================================
    // FST040: AttributeTargetRule
    // =====================================================================

    fn check_attr_target(content: &str) -> Vec<Diagnostic> {
        let rule = AttributeTargetRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_attr_triple_at_per_definition() {
        let content = "\
module Test

[@@@inline_for_extraction]
let f x = x + 1
";
        let diags = check_attr_target(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST040);
        assert!(diags[0].message.contains("[@@inline_for_extraction]"));
    }

    #[test]
    fn test_attr_double_at_module_level() {
        let content = "\
module Test

[@@expect_failure]
let f x = x + 1
";
        let diags = check_attr_target(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST040);
        assert!(diags[0].message.contains("[@@@expect_failure]"));
    }

    #[test]
    fn test_attr_correct_double_at() {
        let content = "\
module Test

[@@inline_for_extraction]
let f x = x + 1
";
        let diags = check_attr_target(content);
        assert!(diags.is_empty(), "Correct usage should not trigger");
    }

    #[test]
    fn test_attr_correct_triple_at() {
        let content = "\
module Test

[@@@expect_failure]
let f x = x + 1
";
        let diags = check_attr_target(content);
        assert!(diags.is_empty(), "Correct usage should not trigger");
    }

    #[test]
    fn test_attr_in_comment_ignored() {
        let content = "\
module Test

(* [@@@inline_for_extraction] *)
let f x = x + 1
";
        let diags = check_attr_target(content);
        assert!(diags.is_empty(), "Attribute in comment should not trigger");
    }

    // --- Batch B tests (FST028, FST031, FST034, FST037, FST038, FST041, FST043, FST044) ---

    fn check_fst028(content: &str) -> Vec<Diagnostic> {
        let rule = StrictOnArgumentsRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    fn check_fst031(content: &str) -> Vec<Diagnostic> {
        let rule = OpaqueWithoutRevealRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    fn check_fst034(content: &str) -> Vec<Diagnostic> {
        let rule = SimpCandidateRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    fn check_fst037(content: &str) -> Vec<Diagnostic> {
        let rule = TotVsGtotRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    fn check_fst038(content: &str) -> Vec<Diagnostic> {
        let rule = IntroduceWithRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    fn check_fst041(content: &str) -> Vec<Diagnostic> {
        let rule = RequiresTrueOkRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    fn check_fst043(content: &str) -> Vec<Diagnostic> {
        let rule = TickVsExplicitRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    fn check_fst044(content: &str) -> Vec<Diagnostic> {
        let rule = MissingDecreasesRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    // ---- FST028: StrictOnArgumentsRule ----

    #[test]
    fn fst028_triggers_on_match_implicit() {
        let code = "\
let my_func (#a:Type) (x: a) : a =
  match a with
  | Int -> x + 1
  | _ -> x
";
        let diags = check_fst028(code);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST028);
        assert!(diags[0].message.contains("strict_on_arguments"));
    }

    #[test]
    fn fst028_no_trigger_with_attribute() {
        let code = "\
[@@strict_on_arguments [0]]
let my_func (#a:Type) (x: a) : a =
  match a with
  | Int -> x + 1
  | _ -> x
";
        let diags = check_fst028(code);
        assert_eq!(diags.len(), 0);
    }

    #[test]
    fn fst028_no_trigger_no_match() {
        let code = "\
let my_func (#a:Type) (x: a) : a = x
";
        let diags = check_fst028(code);
        assert_eq!(diags.len(), 0);
    }

    // ---- FST031: OpaqueWithoutRevealRule ----

    #[test]
    fn fst031_triggers_no_reveal() {
        let code = "\
[@@opaque_to_smt]
let secret_value : nat = 42

let use_it () = secret_value + 1
";
        let diags = check_fst031(code);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST031);
        assert!(diags[0].message.contains("secret_value"));
    }

    #[test]
    fn fst031_no_trigger_with_reveal() {
        let code = "\
[@@opaque_to_smt]
let secret_value : nat = 42

let use_it () =
  reveal_opaque (`secret_value) ;
  secret_value + 1
";
        let diags = check_fst031(code);
        assert_eq!(diags.len(), 0);
    }

    #[test]
    fn fst031_no_trigger_with_norm_spec() {
        let code = "\
[@@opaque_to_smt]
let helper : nat = 10

let use_it () =
  norm_spec [delta_only [helper]] ;
  helper + 1
";
        let diags = check_fst031(code);
        assert_eq!(diags.len(), 0);
    }

    // ---- FST034: SimpCandidateRule ----

    #[test]
    fn fst034_triggers_equality_lemma() {
        let code = "\
val add_zero : x:nat -> Lemma (ensures (x + 0 == x))
";
        let diags = check_fst034(code);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST034);
        assert!(diags[0].message.contains("simp"));
    }

    #[test]
    fn fst034_no_trigger_with_simp() {
        let code = "\
[@@simp]
val add_zero : x:nat -> Lemma (ensures (x + 0 == x))
";
        let diags = check_fst034(code);
        assert_eq!(diags.len(), 0);
    }

    #[test]
    fn fst034_no_trigger_non_equality() {
        let code = "\
val my_lemma : x:nat -> Lemma (ensures (x > 0 ==> x >= 1))
";
        let diags = check_fst034(code);
        // ==> is not equality, and > is not =, so no trigger
        assert_eq!(diags.len(), 0);
    }

    // ---- FST037: TotVsGtotRule ----

    #[test]
    fn fst037_triggers_erased_tot() {
        let code = "\
val bad_func : erased nat -> Tot nat
";
        let diags = check_fst037(code);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST037);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Error);
    }

    #[test]
    fn fst037_no_trigger_erased_gtot() {
        let code = "\
val ok_func : erased nat -> GTot nat
";
        let diags = check_fst037(code);
        assert_eq!(diags.len(), 0);
    }

    #[test]
    fn fst037_no_trigger_no_erased() {
        let code = "\
val normal_func : nat -> Tot nat
";
        let diags = check_fst037(code);
        assert_eq!(diags.len(), 0);
    }

    // ---- FST038: IntroduceWithRule ----

    #[test]
    fn fst038_triggers_classical_forall_intro() {
        let code = "\
let proof () =
  Classical.forall_intro (fun x -> helper x)
";
        let diags = check_fst038(code);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST038);
        assert!(diags[0].message.contains("introduce forall"));
    }

    #[test]
    fn fst038_no_trigger_no_classical() {
        let code = "\
let proof () =
  introduce forall x. P x with (helper x)
";
        let diags = check_fst038(code);
        assert_eq!(diags.len(), 0);
    }

    #[test]
    fn fst038_triggers_impl_intro() {
        let code = "\
let proof () =
  Classical.impl_intro (fun _ -> ())
";
        let diags = check_fst038(code);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("introduce implies"));
    }

    // ---- FST041: RequiresTrueOkRule ----

    #[test]
    fn fst041_triggers_with_todo() {
        let code = "\
// TODO: remove requires True
val my_func : x:nat -> Pure nat (requires True) (ensures fun r -> r > x)
";
        let diags = check_fst041(code);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST041);
        assert!(diags[0].message.contains("intentional"));
    }

    #[test]
    fn fst041_no_trigger_no_comment() {
        let code = "\
val my_func : x:nat -> Pure nat (requires True) (ensures fun r -> r > x)
";
        let diags = check_fst041(code);
        assert_eq!(diags.len(), 0);
    }

    #[test]
    fn fst041_triggers_with_fixme() {
        let code = "\
val my_func : x:nat -> Pure nat (requires True) (ensures fun r -> r > x)
// FIXME: redundant requires True
";
        let diags = check_fst041(code);
        assert_eq!(diags.len(), 1);
    }

    // ---- FST043: TickVsExplicitRule ----

    #[test]
    fn fst043_triggers_mixed() {
        let code = "\
val my_func : #a:Type -> 'b -> a -> 'b
";
        let diags = check_fst043(code);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST043);
        assert!(diags[0].message.contains("Inconsistent"));
    }

    #[test]
    fn fst043_no_trigger_tick_only() {
        let code = "\
val my_func : 'a -> 'b -> 'a
";
        let diags = check_fst043(code);
        assert_eq!(diags.len(), 0);
    }

    #[test]
    fn fst043_no_trigger_explicit_only() {
        let code = "\
val my_func : #a:Type -> #b:Type -> a -> b
";
        let diags = check_fst043(code);
        assert_eq!(diags.len(), 0);
    }

    // ---- FST044: MissingDecreasesRule ----

    #[test]
    fn fst044_triggers_recursive_no_decreases() {
        let code = "\
let rec factorial (n:nat) : nat =
  if n = 0 then 1
  else n * factorial (n - 1)
";
        let diags = check_fst044(code);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST044);
        assert!(diags[0].message.contains("factorial"));
    }

    #[test]
    fn fst044_no_trigger_with_decreases() {
        let code = "\
let rec factorial (n:nat) : Tot nat (decreases n) =
  if n = 0 then 1
  else n * factorial (n - 1)
";
        let diags = check_fst044(code);
        assert_eq!(diags.len(), 0);
    }

    #[test]
    fn fst044_no_trigger_not_recursive() {
        let code = "\
let rec not_really_recursive (n:nat) : nat =
  n + 1
";
        let diags = check_fst044(code);
        assert_eq!(diags.len(), 0);
    }

    #[test]
    fn fst044_no_trigger_in_comment() {
        let code = "\
(* let rec broken (n:nat) : nat =
  broken (n - 1) *)
let good (n:nat) : nat = n
";
        let diags = check_fst044(code);
        assert_eq!(diags.len(), 0);
    }

    // --- Batch C tests (FST032, FST033, FST045, FST046, FST047, FST048, FST049, FST050, FST051) ---

    // =====================================================================
    // FST032: UniverseHintRule
    // =====================================================================

    fn check_universe(content: &str) -> Vec<Diagnostic> {
        let rule = UniverseHintRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_universe_u0_hint() {
        let content = "\
module Test

val my_type : Type u#0
";
        let diags = check_universe(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST032);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Hint);
        assert!(diags[0].message.contains("Type0"));
    }

    #[test]
    fn test_universe_u1_hint() {
        let content = "\
module Test

val higher_type : Type u#1
";
        let diags = check_universe(content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("Type1"));
    }

    #[test]
    fn test_universe_no_trigger_type0() {
        let content = "\
module Test

val my_type : Type0
";
        let diags = check_universe(content);
        assert!(diags.is_empty(), "Already idiomatic Type0, should not trigger");
    }

    #[test]
    fn test_universe_polymorphic_no_trigger() {
        let content = "\
module Test

val my_type : Type u#a
";
        let diags = check_universe(content);
        assert!(diags.is_empty(), "Polymorphic universe variable, should not trigger");
    }

    #[test]
    fn test_universe_in_comment_ignored() {
        let content = "\
module Test

(* Type u#0 is idiomatic *)
val my_type : Type0
";
        let diags = check_universe(content);
        assert!(diags.is_empty(), "Inside block comment, should not trigger");
    }

    // =====================================================================
    // FST033: TacticSuggestionRule
    // =====================================================================

    fn check_tactic(content: &str) -> Vec<Diagnostic> {
        let rule = TacticSuggestionRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_tactic_high_z3rlimit() {
        let content = "\
module Test

#push-options \"--z3rlimit 200\"
let hard_lemma () : Lemma True = ()
";
        let diags = check_tactic(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST033);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Hint);
        assert!(diags[0].message.contains("200"));
        assert!(diags[0].message.contains("tactics"));
    }

    #[test]
    fn test_tactic_low_z3rlimit_no_trigger() {
        let content = "\
module Test

#push-options \"--z3rlimit 50\"
let easy_lemma () : Lemma True = ()
";
        let diags = check_tactic(content);
        assert!(diags.is_empty(), "z3rlimit 50 is reasonable, should not trigger");
    }

    #[test]
    fn test_tactic_set_options_high() {
        let content = "\
module Test

#set-options \"--z3rlimit 500 --fuel 4\"
";
        let diags = check_tactic(content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("500"));
    }

    #[test]
    fn test_tactic_z3rlimit_factor_ignored() {
        let content = "\
module Test

#push-options \"--z3rlimit_factor 100\"
";
        let diags = check_tactic(content);
        assert!(diags.is_empty(), "z3rlimit_factor is different, should not trigger");
    }

    // =====================================================================
    // FST045: NoeqVsUnopteqRule
    // =====================================================================

    fn check_noeq(content: &str) -> Vec<Diagnostic> {
        let rule = NoeqVsUnopteqRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_noeq_without_function_fields() {
        let content = "\
module Test

noeq type my_record = {
  x: nat;
  y: int;
  z: bool;
}
";
        let diags = check_noeq(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST045);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Info);
        assert!(diags[0].message.contains("unopteq"));
        assert!(diags[0].fix.is_some());
        let fix = diags[0].fix.as_ref().unwrap();
        assert_eq!(fix.edits[0].new_text, "unopteq");
    }

    #[test]
    fn test_noeq_with_function_field() {
        let content = "\
module Test

noeq type callback_record = {
  handler: int -> int;
  name: string;
}
";
        let diags = check_noeq(content);
        assert!(diags.is_empty(), "Has function field, noeq is appropriate");
    }

    #[test]
    fn test_unopteq_already_used() {
        let content = "\
module Test

unopteq type my_record = {
  x: nat;
  y: int;
}
";
        let diags = check_noeq(content);
        assert!(diags.is_empty(), "Already using unopteq, should not trigger");
    }

    // =====================================================================
    // FST046: ErasableSuggestionRule
    // =====================================================================

    fn check_erasable(content: &str) -> Vec<Diagnostic> {
        let rule = ErasableSuggestionRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_erasable_all_proof_fields() {
        let content = "\
module Test

type proof_bundle = {
  p1: prop;
  p2: squash nat;
  p3: Type0;
}
";
        let diags = check_erasable(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST046);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Hint);
        assert!(diags[0].message.contains("erasable"));
    }

    #[test]
    fn test_erasable_has_computational_field() {
        let content = "\
module Test

type data_record = {
  value: nat;
  count: int;
}
";
        let diags = check_erasable(content);
        assert!(diags.is_empty(), "Has computational fields, should not trigger");
    }

    #[test]
    fn test_erasable_already_marked() {
        let content = "\
module Test

[@@ erasable]
type proof_bundle = {
  p1: prop;
  p2: squash nat;
}
";
        let diags = check_erasable(content);
        assert!(diags.is_empty(), "Already has [@@ erasable], should not trigger");
    }

    // =====================================================================
    // FST047: SumVsOrRule
    // =====================================================================

    fn check_sum_vs_or(content: &str) -> Vec<Diagnostic> {
        let rule = SumVsOrRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_sum_in_lemma_context() {
        let content = "\
module Test

val my_lemma : x:nat -> Lemma
  (requires Prims.sum (x > 0) (x = 0))
  (ensures True)
";
        let diags = check_sum_vs_or(content);
        assert!(!diags.is_empty());
        assert!(diags.iter().any(|d| d.rule == RuleCode::FST047));
        assert!(diags.iter().any(|d| d.message.contains("constructive")));
    }

    #[test]
    fn test_inl_in_ghost_context() {
        let content = "\
module Test

let ghost_fn (x: nat) : GTot (sum bool bool) =
  Inl true
";
        let diags = check_sum_vs_or(content);
        assert!(!diags.is_empty());
        assert!(diags.iter().any(|d| d.message.contains("Inl")));
    }

    #[test]
    fn test_sum_in_computational_context() {
        let content = "\
module Test

let f (x: sum int bool) : int =
  match x with
  | Inl n -> n
  | Inr _ -> 0
";
        let diags = check_sum_vs_or(content);
        assert!(diags.is_empty(), "sum in Tot context is fine");
    }

    // =====================================================================
    // FST048: MissingPluginRule
    // =====================================================================

    fn check_plugin(content: &str) -> Vec<Diagnostic> {
        let rule = MissingPluginRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_missing_plugin_complex_tactic() {
        let content = "\
module Test

let my_tactic () : Tac unit =
  let g = cur_goal () in
  let _ = intro () in
  norm [];
  trefl ()
";
        let diags = check_plugin(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST048);
        assert!(diags[0].message.contains("[@@plugin]"));
    }

    #[test]
    fn test_plugin_already_present() {
        let content = "\
module Test

[@@plugin]
let my_tactic () : Tac unit =
  let g = cur_goal () in
  norm [];
  trefl ()
";
        let diags = check_plugin(content);
        assert!(diags.is_empty(), "Already has [@@plugin], should not trigger");
    }

    #[test]
    fn test_simple_tactic_no_trigger() {
        let content = "\
module Test

let simple_tac () : Tac unit =
  trivial ()
";
        let diags = check_plugin(content);
        assert!(diags.is_empty(), "Simple one-step tactic, should not trigger");
    }

    // =====================================================================
    // FST049: AutoClassificationRule
    // =====================================================================

    fn check_auto(content: &str) -> Vec<Diagnostic> {
        let rule = AutoClassificationRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_auto_complex_no_pattern() {
        let content = "\
module Test

[@@auto]
val complex_lemma : x:nat -> y:nat -> z:nat -> w:nat -> Lemma
  (forall a b c d. a + b + c + d == d + c + b + a)
";
        let diags = check_auto(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST049);
        assert!(diags[0].message.contains("slowdowns"));
    }

    #[test]
    fn test_auto_with_smt_pattern() {
        let content = "\
module Test

[@@auto]
val simple_lemma : x:nat -> Lemma
  (ensures x + 0 == x)
  [SMTPat (x + 0)]
";
        let diags = check_auto(content);
        assert!(diags.is_empty(), "Has SMTPat, auto is guided");
    }

    #[test]
    fn test_no_auto_attribute() {
        let content = "\
module Test

val regular_lemma : x:nat -> Lemma
  (forall y. x + y == y + x)
";
        let diags = check_auto(content);
        assert!(diags.is_empty(), "No [@@auto] attribute, should not trigger");
    }

    // =====================================================================
    // FST050: SquashBridgeRule
    // =====================================================================

    fn check_squash(content: &str) -> Vec<Diagnostic> {
        let rule = SquashBridgeRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_return_squash_hint() {
        let content = "\
module Test

let proof (x: nat) : squash (x >= 0) =
  return_squash ()
";
        let diags = check_squash(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST050);
        assert!(diags[0].message.contains("give_proof"));
    }

    #[test]
    fn test_join_squash_hint() {
        let content = "\
module Test

let extract (s: squash (squash p)) : squash p =
  join_squash s
";
        let diags = check_squash(content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("get_proof"));
    }

    #[test]
    fn test_no_squash_operations() {
        let content = "\
module Test

let f (x: nat) : nat = x + 1
";
        let diags = check_squash(content);
        assert!(diags.is_empty(), "No squash operations, should not trigger");
    }

    #[test]
    fn test_squash_in_comment_ignored() {
        let content = "\
module Test

(* Use return_squash to construct proofs *)
let f (x: nat) : nat = x
";
        let diags = check_squash(content);
        assert!(diags.is_empty(), "Inside block comment, should not trigger");
    }

    // =====================================================================
    // FST051: DoNotUnrefineRule
    // =====================================================================

    fn check_unrefine(content: &str) -> Vec<Diagnostic> {
        let rule = DoNotUnrefineRule::new();
        let path = PathBuf::from("Test.fst");
        rule.check(&path, content)
    }

    #[test]
    fn test_refined_alias_missing_attr() {
        let content = "\
module Test

let my_nat = x:int{x >= 0}
";
        let diags = check_unrefine(content);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST051);
        assert!(diags[0].message.contains("do_not_unrefine"));
    }

    #[test]
    fn test_refined_alias_with_attr() {
        let content = "\
module Test

[@@do_not_unrefine]
let my_nat = x:int{x >= 0}
";
        let diags = check_unrefine(content);
        assert!(diags.is_empty(), "Already has the attribute, should not trigger");
    }

    #[test]
    fn test_non_refined_alias() {
        let content = "\
module Test

let my_int = int
";
        let diags = check_unrefine(content);
        assert!(diags.is_empty(), "No refinement, should not trigger");
    }

    #[test]
    fn test_refined_with_pipe_syntax() {
        let content = "\
module Test

let pos = {x:int | x > 0}
";
        let diags = check_unrefine(content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("pos"));
    }

    #[test]
    fn test_function_not_alias() {
        let content = "\
module Test

let f x = x + {v:int | v > 0}
";
        // f has parameter x, so LHS is not simple — should not trigger.
        let diags = check_unrefine(content);
        assert!(diags.is_empty(), "Function with params, not a type alias");
    }
}
