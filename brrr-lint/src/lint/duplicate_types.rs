//! FST001: Duplicate type definition detection.
//!
//! Port of remove_fst_duplicate_types.py.
//!
//! When a type is fully defined (with = and body) in the .fsti interface file,
//! F* expects the .fst implementation file to NOT redefine it.
//!
//! Handles:
//! - Simple type aliases: type foo = nat
//! - noeq/unopteq types: noeq type bar = { field : nat }
//! - unfold types: unfold type my_nat = nat
//! - inline_for_extraction types
//! - ADT types: type color = | Red | Green | Blue
//! - Record types: type person = { name: string; age: nat }
//! - Mutual recursion: type a = ... and b = ... and c = ... (single block)
//! - Attributes before types: [@...] type t = ... (including multi-line)
//! - Doc comments in removal range: (** doc *) type t = ...
//! - F* directives: #push-options, #pop-options, #set-options
//! - Type declarations (without =) in .fsti are NOT considered concrete
//! - assume type declarations: `assume type t` is abstract, never concrete
//! - Private types in .fst are NOT removed (implementation details)
//! - Refinement types in constructors: braces tracked for depth
//! - Type abbreviations: type foo = nat (single-line alias)
//! - Cross-file matching by qualified name: BrrrTypes.foo matches foo
//!
//! SAFETY FEATURES (Critical for autofix):
//! - Exact definition matching: Only offers fix if .fst and .fsti definitions are IDENTICAL
//! - Definition normalization: Strips comments and normalizes whitespace for comparison
//! - Preview support: Fix includes preview of what will be removed
//! - Validation: validate_fix function checks removal safety
//! - Reference detection: Warns about potential dependent code
//! - Mutual recursion: entire block matched/removed atomically

use lazy_static::lazy_static;
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use tracing::warn;

use super::rules::{Diagnostic, DiagnosticSeverity, Edit, Fix, Range, Rule, RuleCode};

lazy_static! {
    // All valid type modifiers that can precede 'type' keyword
    static ref TYPE_MODIFIERS: &'static [&'static str] = &[
        "inline_for_extraction",
        "noextract",
        "private",
        "abstract",
        "unfold",
        "noeq",
        "unopteq",
    ];

    // Build modifier pattern
    static ref MODIFIER_PATTERN: String = {
        let mods = TYPE_MODIFIERS.join("|");
        format!(r"(?:(?:{})\s+)*", mods)
    };

    // Pattern for detecting type definitions
    static ref TYPE_START_PATTERN: Regex = Regex::new(
        &format!(r"^{}type\s+([a-zA-Z_][a-zA-Z0-9_']*)", *MODIFIER_PATTERN)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern for 'and' continuation of mutual recursion
    static ref AND_TYPE_PATTERN: Regex = Regex::new(
        r"^and\s+([a-zA-Z_][a-zA-Z0-9_']*)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern for 'assume type' declarations (abstract, never concrete)
    static ref ASSUME_TYPE_PATTERN: Regex = Regex::new(
        r"^assume\s+type\s+([a-zA-Z_][a-zA-Z0-9_']*)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern to check if a type line has 'private' modifier
    static ref PRIVATE_TYPE_PATTERN: Regex = Regex::new(
        &format!(r"^(?:(?:{})\s+)*private\s+(?:(?:{})\s+)*type\s+",
                 TYPE_MODIFIERS.join("|"), TYPE_MODIFIERS.join("|"))
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern for F* directives that do NOT terminate type definitions
    static ref FST_DIRECTIVE_PATTERN: Regex = Regex::new(
        r"^#(push-options|pop-options|set-options|restart-solver)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Terminators: constructs that definitely end a type definition block
    static ref TERMINATORS: &'static [&'static str] = &[
        "val ",
        "let ",
        "let rec ",
        "unfold let ",
        "inline_for_extraction let ",
        "noextract let ",
        "assume val ",
        "assume type ",
        "friend ",
        "open ",
        "module ",
        "instance ",
        "class ",
        "effect ",
        "layered_effect ",
        "sub_effect ",
        "new_effect ",
        "total_effect ",
    ];

    // Pattern to strip line comments: (?m) makes $ match end-of-line, not just end-of-string
    // This fixes the bug where only the last // comment was removed
    static ref LINE_COMMENT_PATTERN: Regex = Regex::new(r"(?m)//.*$").unwrap_or_else(|e| panic!("regex: {e}"));
}

/// A parsed type definition from F* code.
#[derive(Debug, Clone)]
pub struct TypeDefinition {
    pub block: String,
    pub start_line: usize, // 0-indexed
    pub end_line: usize,   // 0-indexed, inclusive
    pub is_private: bool,
    /// Whether this is an `assume type` declaration (always abstract).
    pub is_assume: bool,
    /// All type names in the mutual recursion block (including main + and types).
    /// Empty for non-mutual-recursion definitions.
    pub mutual_names: Vec<String>,
}

/// Check if line is a section header comment like (* ==== *).
fn is_section_header(line: &str) -> bool {
    let stripped = line.trim();
    (stripped.starts_with("(** ==") || stripped.starts_with("(* =="))
        || (stripped.starts_with("(*") && stripped.contains("===="))
}

/// Check if a line that starts with `[@` has a matching closing `]`.
///
/// Tracks bracket depth to handle nested brackets like `[@@ attr [inner]]`.
/// Returns false if the attribute continues on the next line.
fn line_has_closing_bracket(line: &str) -> bool {
    let mut depth = 0i32;
    let mut in_string = false;
    for ch in line.chars() {
        if in_string {
            if ch == '"' {
                in_string = false;
            }
            // Skip escaped characters handled simply: we just look for unescaped "
            continue;
        }
        match ch {
            '"' => in_string = true,
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth <= 0 {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Find the end of a type definition block starting at start_index.
/// Returns the index of the last line of the type block (inclusive).
///
/// Tracks comment depth and string state across lines using [`scan_line_state`]
/// so that terminators inside multi-line comments or string literals are
/// correctly ignored.
///
/// Handles:
/// - Multi-line `(* *)` comments (nested): a `val` or `let` keyword inside
///   a comment does NOT terminate the type block
/// - String literals with comment-like patterns: `"(*"` does not open a
///   comment, `"*)"` does not close one
/// - Escaped backslashes in strings: `"\\"` is one backslash, not an escape
///   of the next character
/// - `noeq type` definitions: recognized by `TYPE_START_PATTERN` as new types
/// - Record types: a closing `}` at column 0 terminates the record body
/// - Type aliases (single-line `type foo = bar`): terminated by the next
///   declaration at column 0
/// - Indented variant constructors (`| Foo | Bar`): continue as part of the
///   type body since they do not start at column 0
/// - `and` keyword: continues mutual recursion instead of terminating
fn find_type_block_end(lines: &[&str], start_index: usize) -> usize {
    let mut comment_depth: i32 = 0;
    let mut in_string = false;

    // Process the start line to establish initial comment/string state.
    // A type definition line like `type foo = (* start comment` would set
    // comment_depth = 1, carrying into subsequent lines.
    scan_line_state(lines[start_index], &mut comment_depth, &mut in_string);

    let mut j = start_index + 1;

    while j < lines.len() {
        let curr_line = lines[j];
        let curr_stripped = curr_line.trim();

        // Capture comment depth BEFORE scanning this line. If the line
        // started inside a comment (depth > 0), its column-0 content is
        // comment text, not a real declaration -- skip termination checks.
        let line_start_depth = comment_depth;
        scan_line_state(curr_line, &mut comment_depth, &mut in_string);

        // Line started or ended inside a multi-line comment: skip all
        // termination checks. A `val` or `type` keyword inside a comment
        // must not end the type block.
        if line_start_depth > 0 || comment_depth > 0 {
            j += 1;
            continue;
        }

        // Skip empty lines
        if curr_stripped.is_empty() {
            j += 1;
            continue;
        }

        // Record body closing brace at column 0 ends the type block.
        // In F*, multi-line record types are written as:
        //   noeq type foo = {
        //     field1: t1;
        //     field2: t2
        //   }
        // The closing `}` at column 0 indicates the record body is complete
        // (variant constructor braces like `| Foo of { x: int }` are indented
        // and will not match this check).
        //
        // Refinement braces like `{x = 0}` inside constructor parameters are
        // normally indented, but we double-check: a bare `}` at column 0 is
        // only a record terminator if the line is JUST `}` (possibly with
        // whitespace/comment after). If it has significant code after `}`, it
        // could be part of a refinement continuation and we don't terminate.
        if curr_line.starts_with('}') {
            let after_brace = curr_stripped.trim_start_matches('}').trim();
            let is_record_close = after_brace.is_empty()
                || after_brace.starts_with("(*")
                || after_brace.starts_with("//");

            if is_record_close {
                // Check if 'and' follows for mutual recursion
                let mut peek = j + 1;
                while peek < lines.len() && lines[peek].trim().is_empty() {
                    peek += 1;
                }
                if peek < lines.len() && AND_TYPE_PATTERN.is_match(lines[peek].trim()) {
                    j += 1;
                    continue;
                }
                return j;
            }
        }

        // F* directives don't terminate type definitions
        if FST_DIRECTIVE_PATTERN.is_match(curr_stripped) {
            j += 1;
            continue;
        }

        // Indented attributes don't terminate type definitions (they're
        // part of the type body, e.g. on a constructor). Column-0 attributes
        // belong to the NEXT declaration and signal the end of this block.
        if curr_stripped.starts_with("[@")
            && (curr_line.starts_with(' ') || curr_line.starts_with('\t'))
        {
            // Indented attribute: skip it (handle multi-line)
            if !line_has_closing_bracket(curr_stripped) {
                j += 1;
                while j < lines.len() {
                    let attr_line = lines[j].trim();
                    if line_has_closing_bracket(attr_line) {
                        break;
                    }
                    j += 1;
                }
            }
            j += 1;
            continue;
        }

        // Must be at column 0 (not indented) to be a terminator
        if !curr_line.is_empty() && !curr_line.starts_with(' ') && !curr_line.starts_with('\t') {
            // Check for 'and' continuation of mutual recursion
            if AND_TYPE_PATTERN.is_match(curr_stripped) {
                j += 1;
                continue;
            }

            // Check for terminators
            for term in TERMINATORS.iter() {
                if curr_stripped.starts_with(term) {
                    // Found terminator, go back to skip trailing blank lines
                    let mut end_line = j - 1;
                    while end_line > start_index && lines[end_line].trim().is_empty() {
                        end_line -= 1;
                    }
                    return end_line;
                }
            }

            // New type definition (not 'and')
            if TYPE_START_PATTERN.is_match(curr_stripped) {
                let mut end_line = j - 1;
                while end_line > start_index && lines[end_line].trim().is_empty() {
                    end_line -= 1;
                }
                return end_line;
            }

            // Section headers terminate
            if is_section_header(curr_line) {
                let mut end_line = j - 1;
                while end_line > start_index && lines[end_line].trim().is_empty() {
                    end_line -= 1;
                }
                return end_line;
            }

            // Column-0 attribute `[@` is a prefix for the NEXT declaration
            if curr_stripped.starts_with("[@") {
                let mut end_line = j - 1;
                while end_line > start_index && lines[end_line].trim().is_empty() {
                    end_line -= 1;
                }
                return end_line;
            }
        }

        j += 1;
    }

    // Reached end of file
    let mut end_line = j - 1;
    while end_line > start_index && lines[end_line].trim().is_empty() {
        end_line -= 1;
    }
    end_line
}

/// Extract type names from 'and' continuations in a mutual recursion block.
fn extract_and_types(block: &str) -> Vec<String> {
    let mut and_types = Vec::new();
    for line in block.lines() {
        let stripped = line.trim();
        if let Some(caps) = AND_TYPE_PATTERN.captures(stripped) {
            if let Some(m) = caps.get(1) {
                and_types.push(m.as_str().to_string());
            }
        }
    }
    and_types
}

/// Check if a type block contains a private type definition.
fn is_private_type(block: &str) -> bool {
    let first_line = block.lines().next().map(|l| l.trim()).unwrap_or("");
    PRIVATE_TYPE_PATTERN.is_match(first_line)
}

/// Count `(*` and `*)` comment delimiter tokens in a line, ignoring those
/// inside string literals and `//` line comments.
///
/// Returns `(opens, closes)` where `opens` is the number of `(*` tokens
/// (including `(**` doc-comment openers) and `closes` is the number of `*)`
/// tokens. Scans left-to-right so `(*` is matched before `*)`, correctly
/// handling the ambiguous `(*)` sequence as `(*` + `)`.
///
/// State machine: Normal -> InString -> InLineComment
/// - `//` outside strings stops scanning (rest of line is a comment)
/// - String literals (`"..."`) are tracked: unescaped `"` toggles the
///   `in_string` flag, and escaped characters (pair-consumption:
///   each `\` + next char consumed together) are skipped
/// - Comment delimiters inside strings or after `//` are ignored
fn count_comment_delimiters(s: &str) -> (usize, usize) {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut opens = 0usize;
    let mut closes = 0usize;
    let mut in_string = false;
    let mut i = 0;

    while i < len {
        if in_string {
            if bytes[i] == b'\\' && i + 1 < len {
                // Skip escaped character (handles \\, \", \n, etc.)
                i += 2;
            } else if bytes[i] == b'"' {
                in_string = false;
                i += 1;
            } else {
                i += 1;
            }
        } else {
            if bytes[i] == b'"' {
                in_string = true;
                i += 1;
            } else if i + 1 < len && bytes[i] == b'/' && bytes[i + 1] == b'/' {
                // Line comment: rest of line is comment text, stop scanning.
                break;
            } else if i + 1 < len && bytes[i] == b'(' && bytes[i + 1] == b'*' {
                opens += 1;
                i += 2; // Consume both chars; prevents `(*)` double-counting
            } else if i + 1 < len && bytes[i] == b'*' && bytes[i + 1] == b')' {
                closes += 1;
                i += 2;
            } else {
                i += 1;
            }
        }
    }

    (opens, closes)
}

/// Scan a line character-by-character, updating comment and string state
/// that persists across lines.
///
/// State machine: Normal -> InBlockComment(depth) -> InString -> InLineComment
/// Tracks nested `(* *)` comment depth and `"..."` string literal state.
/// Both states carry across line boundaries (multi-line comments and,
/// theoretically, multi-line strings).
///
/// Handles:
/// - `//` line comments at depth 0: rest of line is ignored
///   (inside block comments, `//` is just text per F*/OCaml convention)
/// - Escaped characters in strings: `\"` does not end the string,
///   `\\` is a single backslash (pair-consumption approach)
/// - Strings inside comments: F*/OCaml convention respects string literals
///   within comments, so `(* "*)" *)` is one comment
/// - Comment delimiters inside strings are ignored
/// - The `(*)` sequence: `(*` is consumed first, so `*` cannot also
///   start a `*)` close
fn scan_line_state(
    line: &str,
    comment_depth: &mut i32,
    in_string: &mut bool,
) {
    let bytes = line.as_bytes();
    let len = bytes.len();
    let mut i = 0;

    while i < len {
        if *in_string {
            if bytes[i] == b'\\' && i + 1 < len {
                // Pair-consumption: skip escaped character
                i += 2;
            } else if bytes[i] == b'"' {
                *in_string = false;
                i += 1;
            } else {
                i += 1;
            }
        } else if *comment_depth > 0 {
            // Inside a comment: track nested comments and strings
            if bytes[i] == b'"' {
                *in_string = true;
                i += 1;
            } else if i + 1 < len && bytes[i] == b'(' && bytes[i + 1] == b'*' {
                *comment_depth += 1;
                i += 2;
            } else if i + 1 < len && bytes[i] == b'*' && bytes[i + 1] == b')' {
                *comment_depth -= 1;
                i += 2;
            } else {
                i += 1;
            }
        } else {
            // Outside comments and strings (Normal state)
            if bytes[i] == b'"' {
                *in_string = true;
                i += 1;
            } else if i + 1 < len && bytes[i] == b'/' && bytes[i + 1] == b'/' {
                // Line comment at depth 0: rest of line is comment text.
                // Inside block comments, // is just text (F*/OCaml convention),
                // but we only reach this branch at depth 0.
                break;
            } else if i + 1 < len && bytes[i] == b'(' && bytes[i + 1] == b'*' {
                *comment_depth += 1;
                i += 2;
            } else {
                i += 1;
            }
        }
    }
}

/// Strip F* nested block comments, replacing each with `replacement`.
///
/// Properly handles:
/// - Nested comments: `(* outer (* inner *) outer *)` is ONE comment
/// - Strings inside comments: `(* "*)" *)` does not close at the inner `*)`
///   (F*/OCaml convention: string literals are respected inside comments)
/// - Escaped characters inside strings (both at top level and in comments)
/// - String literals at top level are preserved (not stripped)
fn strip_nested_block_comments(text: &str, replacement: &str) -> String {
    let chars: Vec<char> = text.chars().collect();
    let n = chars.len();
    let mut result = String::with_capacity(n);
    let mut i = 0;
    let mut comment_depth: usize = 0;
    let mut in_comment_string = false;

    while i < n {
        if comment_depth > 0 {
            // Inside a comment block
            if in_comment_string {
                // Inside a string within a comment
                if chars[i] == '\\' && i + 1 < n {
                    i += 2;
                } else if chars[i] == '"' {
                    in_comment_string = false;
                    i += 1;
                } else {
                    i += 1;
                }
            } else {
                if chars[i] == '"' {
                    in_comment_string = true;
                    i += 1;
                } else if i + 1 < n && chars[i] == '(' && chars[i + 1] == '*' {
                    comment_depth += 1;
                    i += 2;
                } else if i + 1 < n && chars[i] == '*' && chars[i + 1] == ')' {
                    comment_depth -= 1;
                    if comment_depth == 0 {
                        // Exiting outermost comment: emit replacement
                        result.push_str(replacement);
                        in_comment_string = false;
                    }
                    i += 2;
                } else {
                    i += 1;
                }
            }
        } else {
            // Outside any comment (Normal state)
            if chars[i] == '"' {
                // Preserve string literals at top level (not inside comments)
                result.push(chars[i]);
                i += 1;
                while i < n && chars[i] != '"' {
                    result.push(chars[i]);
                    if chars[i] == '\\' && i + 1 < n {
                        i += 1;
                        result.push(chars[i]);
                    }
                    i += 1;
                }
                if i < n {
                    result.push(chars[i]); // closing quote
                    i += 1;
                }
            } else if i + 1 < n && chars[i] == '/' && chars[i + 1] == '/' {
                // Line comment: preserve everything until newline (we only strip
                // block comments, not line comments). This prevents `// (* text *)`
                // from being misinterpreted as a block comment open/close.
                result.push(chars[i]);
                i += 1;
                while i < n && chars[i] != '\n' {
                    result.push(chars[i]);
                    i += 1;
                }
            } else if i + 1 < n && chars[i] == '(' && chars[i + 1] == '*' {
                comment_depth += 1;
                in_comment_string = false;
                i += 2;
            } else {
                result.push(chars[i]);
                i += 1;
            }
        }
    }

    result
}

/// Check if a line consists solely of standalone type/declaration modifiers.
///
/// In HACL* and other F* codebases, modifiers like `inline_for_extraction noextract`
/// often appear on their own line immediately before a `type`/`let`/`val` declaration.
/// These lines are semantically part of the declaration and must be included in the
/// removal range when removing duplicate type definitions.
///
/// Example patterns from HACL*:
/// ```text
/// inline_for_extraction noextract
/// type limb_t = UInt64.t
///
/// inline_for_extraction
/// let helper x = x + 1
/// ```
fn is_standalone_modifier_line(line: &str) -> bool {
    let stripped = line.trim();
    if stripped.is_empty() {
        return false;
    }
    // All tokens on the line must be recognized modifiers
    let tokens: Vec<&str> = stripped.split_whitespace().collect();
    if tokens.is_empty() {
        return false;
    }
    tokens.iter().all(|t| TYPE_MODIFIERS.contains(t))
}

/// Find the start of attribute and doc-comment prefix lines before a type definition.
///
/// Scans backward from `type_start` to include:
/// - Attribute annotations (`[@...]`, `[@@...]`, `[@@@ ...]`)
/// - Doc comments only: `(** ... *)` block doc comments, `/// ...` line doc comments
/// - Multi-line doc comment blocks (with proper nesting depth tracking)
/// - Standalone modifier lines (`inline_for_extraction noextract`, etc.)
///
/// EXCLUDES from the range:
/// - Regular block comments `(* ... *)` (not documentation, may be section dividers)
/// - Regular line comments `// ...` (not doc comments)
///
/// This distinction follows F*/OCaml convention where `(**` marks a doc comment
/// that attaches to the next declaration, while `(*` is a general comment.
///
/// When scanning backward through multi-line comments, `*)` increases comment
/// depth (entering from the bottom) and `(*`/`(**` decreases it. Once the
/// opening is reached, we check if it starts with `(**` (doc) or just `(*`
/// (regular). Only doc comment blocks are included in the range.
///
/// Empty lines break the prefix chain at depth 0.
fn find_attribute_prefix_lines(lines: &[&str], type_start: usize) -> usize {
    let mut actual_start = type_start;
    let mut comment_depth: i32 = 0;

    let mut j = type_start;
    while j > 0 {
        j -= 1;
        let stripped = lines[j].trim();

        // Count comment delimiters on this line
        let (opens, closes) = count_comment_delimiters(stripped);

        // Going backward: *) increases depth (entering comment from bottom),
        // (* decreases depth (reaching comment opening from bottom)
        comment_depth += closes as i32;
        let inside_comment = comment_depth > 0;
        comment_depth -= opens as i32;
        if comment_depth < 0 {
            comment_depth = 0;
        }

        // Line was (at least partially) inside a multi-line comment block
        if inside_comment {
            // If comment_depth is now 0, we've reached the opening line.
            // Check if it's a doc comment (** or just a regular comment (*
            if comment_depth == 0 {
                if stripped.starts_with("(**") {
                    // Doc comment: include all lines from opening to here
                    actual_start = j;
                    continue;
                } else {
                    // Regular comment block: stop the prefix scan
                    break;
                }
            }
            // Still inside multi-line comment, keep scanning backward
            continue;
        }

        // At depth 0: empty line breaks the prefix chain
        if stripped.is_empty() {
            break;
        }

        // Self-contained single-line block comment (both (* and *) on same line)
        if opens > 0 && closes > 0 && comment_depth == 0 {
            // Only include if it's a doc comment (**)
            if stripped.starts_with("(**") {
                actual_start = j;
                continue;
            } else {
                // Regular comment - stop
                break;
            }
        }

        // Line comment: only include doc line comments (///)
        if stripped.starts_with("///") {
            actual_start = j;
            continue;
        }
        if stripped.starts_with("//") {
            // Regular line comment - stop
            break;
        }

        // Attribute annotations (all bracket forms: [@], [@@], [@@@]).
        // For multi-line attributes, scan further backward: if a line
        // contains `]` but not `[`, it's the tail of a multi-line attribute.
        if stripped.starts_with("[@") {
            actual_start = j;
            continue;
        }

        // Tail portion of a multi-line attribute: line has `]` but no `[@`
        // opening on this line. Check if this is a continuation line of an
        // attribute that opened on an earlier line.
        if stripped.ends_with(']') && !stripped.starts_with('[') && !stripped.starts_with("(*") {
            // This could be the tail of a multi-line attribute; include it
            // and keep scanning backward for the opening `[@`.
            actual_start = j;
            continue;
        }

        // Standalone modifier lines (e.g., `inline_for_extraction noextract`)
        // These are semantically part of the declaration that follows.
        if is_standalone_modifier_line(lines[j]) {
            actual_start = j;
            continue;
        }

        // Non-doc-comment, non-attribute, non-modifier, non-empty at depth 0 -> stop
        break;
    }

    actual_start
}

/// Find all type definitions with their line ranges.
/// Returns HashMap of type_name -> TypeDefinition
pub fn find_type_definitions(content: &str) -> HashMap<String, TypeDefinition> {
    let lines: Vec<&str> = content.lines().collect();
    let mut types: HashMap<String, TypeDefinition> = HashMap::new();

    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        let stripped = line.trim();

        // Handle `assume type` declarations: always abstract, never concrete
        if let Some(caps) = ASSUME_TYPE_PATTERN.captures(stripped) {
            if let Some(m) = caps.get(1) {
                let type_name = m.as_str().to_string();
                let actual_start = find_attribute_prefix_lines(&lines, i);
                // assume type is typically single-line
                let end_line = i;
                let block: String = lines[actual_start..=end_line].join("\n");
                types.insert(
                    type_name,
                    TypeDefinition {
                        block,
                        start_line: actual_start,
                        end_line,
                        is_private: false,
                        is_assume: true,
                        mutual_names: vec![],
                    },
                );
                i = end_line + 1;
                continue;
            }
        }

        if let Some(caps) = TYPE_START_PATTERN.captures(stripped) {
            // Skip if this appears to be inside a comment
            if stripped.starts_with("(*") && stripped.contains("type ") {
                i += 1;
                continue;
            }

            if let Some(m) = caps.get(1) {
                let type_name = m.as_str().to_string();

                // Find attribute prefix
                let actual_start = find_attribute_prefix_lines(&lines, i);

                // Find the end of the type definition block
                let end_line = find_type_block_end(&lines, i);

                let block: String = lines[actual_start..=end_line].join("\n");
                let is_private = is_private_type(&block);
                let and_types = extract_and_types(&block);

                // Build mutual recursion name list
                let mutual_names = if and_types.is_empty() {
                    vec![]
                } else {
                    let mut names = vec![type_name.clone()];
                    names.extend(and_types.iter().cloned());
                    names
                };

                // Add main type
                types.insert(
                    type_name.clone(),
                    TypeDefinition {
                        block: block.clone(),
                        start_line: actual_start,
                        end_line,
                        is_private,
                        is_assume: false,
                        mutual_names: mutual_names.clone(),
                    },
                );

                // Also add 'and' types as separate entries
                // They share the same block range and privacy
                for and_type in &and_types {
                    types.insert(
                        and_type.clone(),
                        TypeDefinition {
                            block: block.clone(),
                            start_line: actual_start,
                            end_line,
                            is_private,
                            is_assume: false,
                            mutual_names: mutual_names.clone(),
                        },
                    );
                }

                i = end_line + 1;
                continue;
            }
        }

        i += 1;
    }

    types
}

/// Extract the module name from file content (first `module X` line).
///
/// Used for cross-file qualified name matching: `BrrrTypes.foo` should match
/// the unqualified name `foo` in the same module.
fn extract_module_name(content: &str) -> Option<String> {
    for line in content.lines() {
        let stripped = line.trim();
        if stripped.starts_with("module ") {
            let rest = stripped.strip_prefix("module ")?.trim();
            // Module name may have a dot-separated path
            return Some(rest.to_string());
        }
    }
    None
}

/// Strip a qualified module prefix from a type name, if present.
///
/// For example, `BrrrTypes.foo` becomes `foo` when the module name is
/// `BrrrTypes`. Returns the name unchanged if no prefix matches.
fn strip_module_prefix<'a>(type_name: &'a str, module_name: &str) -> &'a str {
    if let Some(stripped) = type_name.strip_prefix(module_name) {
        if let Some(rest) = stripped.strip_prefix('.') {
            return rest;
        }
    }
    type_name
}

/// Try to match a type name from .fst against .fsti types, handling
/// qualified name prefixes.
///
/// Looks up:
/// 1. Exact name match
/// 2. Qualified name match (e.g., `Module.foo` in .fst matches `foo` in .fsti)
fn lookup_fsti_type<'a>(
    fsti_concrete: &'a HashMap<&String, &TypeDefinition>,
    type_name: &str,
    fst_module: &Option<String>,
    fsti_module: &Option<String>,
) -> Option<&'a &'a TypeDefinition> {
    // Exact match first
    for (name, td) in fsti_concrete.iter() {
        if name.as_str() == type_name {
            return Some(td);
        }
    }

    // Try stripping module prefix from type_name
    if let Some(ref mod_name) = fst_module {
        let stripped = strip_module_prefix(type_name, mod_name);
        if stripped != type_name {
            for (name, td) in fsti_concrete.iter() {
                if name.as_str() == stripped {
                    return Some(td);
                }
            }
        }
    }

    // Try adding module prefix to match qualified names in .fsti
    if let Some(ref mod_name) = fsti_module {
        let qualified = format!("{}.{}", mod_name, type_name);
        for (name, td) in fsti_concrete.iter() {
            if name.as_str() == qualified.as_str() {
                return Some(td);
            }
        }
    }

    None
}

/// Result of fix validation.
#[derive(Debug, Clone)]
pub struct FixValidation {
    /// Whether the fix is safe to apply.
    pub is_safe: bool,
    /// Detailed reason if not safe, or confirmation if safe.
    pub reason: String,
    /// Preview of the content that will be removed.
    pub removal_preview: String,
    /// List of potential issues (warnings even if safe).
    pub warnings: Vec<String>,
}

impl FixValidation {
    fn safe(preview: String) -> Self {
        Self {
            is_safe: true,
            reason: "Definitions match exactly; safe to remove".to_string(),
            removal_preview: preview,
            warnings: vec![],
        }
    }

    fn safe_with_warnings(preview: String, warnings: Vec<String>) -> Self {
        Self {
            is_safe: true,
            reason: "Definitions match; safe to remove with warnings".to_string(),
            removal_preview: preview,
            warnings,
        }
    }

    fn unsafe_mismatch(fst_def: &str, fsti_def: &str) -> Self {
        Self {
            is_safe: false,
            reason: format!(
                "Type definitions differ:\n  .fst:  {}\n  .fsti: {}",
                fst_def.lines().next().unwrap_or(""),
                fsti_def.lines().next().unwrap_or("")
            ),
            removal_preview: String::new(),
            warnings: vec![],
        }
    }

}

/// Normalize a type definition block for comparison.
///
/// This function:
/// 1. Removes all comments (block and line)
/// 2. Normalizes whitespace (collapses multiple spaces/newlines)
/// 3. Trims leading/trailing whitespace
/// 4. Removes attribute annotations ([@...]) for semantic comparison
///
/// The goal is to compare the SEMANTIC content of two type definitions,
/// ignoring formatting differences and comments.
fn normalize_type_definition(block: &str) -> String {
    // Step 1: Remove block comments (handles nesting and strings inside comments)
    let without_block_comments = strip_nested_block_comments(block, " ");

    // Step 2: Remove line comments
    let without_comments = LINE_COMMENT_PATTERN.replace_all(&without_block_comments, "");

    // Step 3: Normalize whitespace - replace all whitespace sequences with single space
    let normalized: String = without_comments
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");

    // Step 4: Remove attribute annotations for semantic comparison
    // Attributes like [@...] or [@@...] don't affect the type's semantic meaning
    lazy_static! {
        static ref ATTR_PATTERN: Regex = Regex::new(r"\[@+[^\]]*\]").unwrap_or_else(|e| panic!("regex: {e}"));
    }
    let without_attrs = ATTR_PATTERN.replace_all(&normalized, "").to_string();

    // Final cleanup
    without_attrs.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Compare two type definition blocks for semantic equivalence.
///
/// Returns true if the definitions are semantically identical
/// (same type structure, ignoring comments and whitespace).
pub fn definitions_match(fst_block: &str, fsti_block: &str) -> bool {
    let norm_fst = normalize_type_definition(fst_block);
    let norm_fsti = normalize_type_definition(fsti_block);
    norm_fst == norm_fsti
}

/// Extract the core type signature from a block (type name + parameters + body).
///
/// This is a more lenient comparison that checks if the structural parts match.
fn extract_type_signature(block: &str) -> Option<String> {
    let normalized = normalize_type_definition(block);

    // Find the type keyword and extract everything after it
    normalized.find("type ").map(|idx| normalized[idx..].to_string())
}

/// Check if two type definitions have matching signatures.
///
/// This is a more lenient check than `definitions_match` that allows
/// for minor differences in modifiers (like `inline_for_extraction`).
pub fn signatures_match(fst_block: &str, fsti_block: &str) -> bool {
    match (extract_type_signature(fst_block), extract_type_signature(fsti_block)) {
        (Some(fst_sig), Some(fsti_sig)) => fst_sig == fsti_sig,
        _ => false,
    }
}

/// Detect potential references to a type within a file.
///
/// Returns a list of line numbers where the type name appears outside
/// of its own definition block.
fn find_type_references(content: &str, type_name: &str, def_start: usize, def_end: usize) -> Vec<usize> {
    let mut references = Vec::new();

    // Build a word-boundary pattern for the type name
    let pattern = format!(r"\b{}\b", regex::escape(type_name));
    let Ok(re) = Regex::new(&pattern) else { return Vec::new() };

    for (line_idx, line) in content.lines().enumerate() {
        // Skip lines within the definition block
        if line_idx >= def_start && line_idx <= def_end {
            continue;
        }

        // Skip comment-only lines
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.starts_with("(*") {
            continue;
        }

        // Check if type name appears in this line
        if re.is_match(line) {
            references.push(line_idx + 1); // 1-indexed
        }
    }

    references
}

/// Validate whether a fix is safe to apply.
///
/// This function performs comprehensive safety checks:
/// 1. Verifies that the type definitions in .fst and .fsti match exactly
/// 2. Checks for references to the type in the .fst file
/// 3. Validates that removal won't break the file structure
///
/// Returns a FixValidation with detailed information about safety.
pub fn validate_fix(
    fst_content: &str,
    _fsti_content: &str,
    type_name: &str,
    fst_typedef: &TypeDefinition,
    fsti_typedef: &TypeDefinition,
) -> FixValidation {
    // Safety check 1: Verify definitions match exactly
    if !definitions_match(&fst_typedef.block, &fsti_typedef.block) {
        // Try more lenient signature matching
        if !signatures_match(&fst_typedef.block, &fsti_typedef.block) {
            return FixValidation::unsafe_mismatch(&fst_typedef.block, &fsti_typedef.block);
        }
        // Signatures match but full definitions don't - warn but allow
        let warnings = vec![
            "Definitions have minor differences (comments/attributes)".to_string(),
        ];
        let preview = create_removal_preview(&fst_typedef.block, fst_typedef.start_line);
        return FixValidation::safe_with_warnings(preview, warnings);
    }

    // Safety check 2: Check for references outside the definition
    let references = find_type_references(
        fst_content,
        type_name,
        fst_typedef.start_line,
        fst_typedef.end_line,
    );

    let preview = create_removal_preview(&fst_typedef.block, fst_typedef.start_line);

    if !references.is_empty() {
        // This is actually OK - the type will still be available from .fsti
        // But we warn the user about it
        let warnings = vec![format!(
            "Type `{}` is referenced at lines: {:?} (will use .fsti definition)",
            type_name, references
        )];
        return FixValidation::safe_with_warnings(preview, warnings);
    }

    FixValidation::safe(preview)
}

/// Create a preview of what will be removed.
fn create_removal_preview(block: &str, start_line: usize) -> String {
    let lines: Vec<&str> = block.lines().collect();
    let preview_lines = if lines.len() > 5 {
        format!(
            "Lines {}-{} ({} lines):\n  {}\n  {}\n  ...\n  {}",
            start_line + 1,
            start_line + lines.len(),
            lines.len(),
            lines[0],
            lines[1],
            lines[lines.len() - 1]
        )
    } else {
        format!(
            "Lines {}-{}:\n{}",
            start_line + 1,
            start_line + lines.len(),
            block
                .lines()
                .map(|l| format!("  {}", l))
                .collect::<Vec<_>>()
                .join("\n")
        )
    };
    preview_lines
}

/// Check if a type block is a concrete definition (has bare `=` at depth 0).
///
/// Type declarations like `type foo` or `type foo : Type0` without `=`
/// are abstract -- they must be implemented in .fst.
///
/// `assume type` declarations are always abstract regardless of content.
///
/// The `=` that defines a type body always appears at bracket depth 0
/// (not inside parentheses, braces, or square brackets). An `=` inside
/// a refinement like `type t (x: int{x = 0}) : Type` is at depth > 0
/// and does NOT make the type concrete.
///
/// Additionally, `==`, `>=`, `<=`, `!=`, and `=>` are operators, not
/// type body definitions. Only a bare `=` counts.
fn is_concrete_definition(block: &str) -> bool {
    // `assume type` is always abstract
    let first_content_line = block.lines()
        .map(|l| l.trim())
        .find(|l| !l.is_empty() && !l.starts_with("(*") && !l.starts_with("//") && !l.starts_with("[@"));
    if let Some(first) = first_content_line {
        if first.starts_with("assume ") {
            return false;
        }
    }
    // Remove comments first to avoid matching = inside comments.
    let cleaned = strip_nested_block_comments(block, "");
    let cleaned = LINE_COMMENT_PATTERN.replace_all(&cleaned, "");

    let chars: Vec<char> = cleaned.chars().collect();
    let len = chars.len();

    // Track bracket depth: (, {, [ increase depth; ), }, ] decrease it.
    // Only a bare '=' at depth 0 counts as a type body definition.
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut i = 0;

    while i < len {
        let ch = chars[i];

        // Simple string literal tracking (F* uses double quotes)
        if ch == '"' && (i == 0 || chars[i - 1] != '\\') {
            in_string = !in_string;
            i += 1;
            continue;
        }
        if in_string {
            i += 1;
            continue;
        }

        match ch {
            '(' | '{' | '[' => depth += 1,
            ')' | '}' | ']' => {
                if depth > 0 {
                    depth -= 1;
                }
            }
            '=' if depth == 0 => {
                // Reject compound operators: ==, >=, <=, !=, =>
                let prev = if i > 0 { chars[i - 1] } else { ' ' };
                let next = if i + 1 < len { chars[i + 1] } else { ' ' };

                let is_compound = prev == '!' || prev == '<' || prev == '>'
                    || prev == '=' || next == '=' || next == '>';

                if !is_compound {
                    return true;
                }
            }
            _ => {}
        }
        i += 1;
    }

    false
}

/// FST001: Duplicate type definitions in .fst/.fsti pairs.
pub struct DuplicateTypesRule;

impl DuplicateTypesRule {
    pub fn new() -> Self {
        Self
    }
}

impl Default for DuplicateTypesRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for DuplicateTypesRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST001
    }

    fn check(&self, _file: &Path, _content: &str) -> Vec<Diagnostic> {
        // This rule requires pair checking
        vec![]
    }

    fn requires_pair(&self) -> bool {
        true
    }

    /// Check for duplicate type definitions between .fst and .fsti files.
    ///
    /// Returns diagnostics with fixes to remove duplicate types from the .fst file.
    ///
    /// **SAFETY**: This function validates that type definitions match EXACTLY
    /// before offering an autofix. If definitions differ, no fix is offered
    /// (only a warning diagnostic).
    ///
    /// **Note**: After applying the generated fixes, the resulting content may have
    /// multiple consecutive blank lines. Use [`cleanup_consecutive_blanks`] as a
    /// post-processing step to normalize whitespace, or run a code formatter.
    fn check_pair(
        &self,
        fst_file: &Path,
        fst_content: &str,
        _fsti_file: &Path,
        fsti_content: &str,
    ) -> Vec<Diagnostic> {
        let fst_types = find_type_definitions(fst_content);
        let fsti_types = find_type_definitions(fsti_content);

        let fst_module = extract_module_name(fst_content);
        let fsti_module = extract_module_name(fsti_content);

        let mut diagnostics = Vec::new();

        // Find concrete types in .fsti (those with = sign and not assume type)
        let fsti_concrete: HashMap<&String, &TypeDefinition> = fsti_types
            .iter()
            .filter(|(_, typedef)| !typedef.is_assume && is_concrete_definition(&typedef.block))
            .collect();

        // Track which ranges we've already marked for removal
        // (multiple types in mutual recursion share the same range)
        let mut removed_ranges: HashSet<(usize, usize)> = HashSet::new();

        for (type_name, fst_typedef) in &fst_types {
            // Skip assume type declarations - they are always abstract
            if fst_typedef.is_assume {
                continue;
            }

            // Skip private types - they are implementation details
            if fst_typedef.is_private {
                continue;
            }

            if let Some(fsti_typedef) = lookup_fsti_type(
                &fsti_concrete,
                type_name,
                &fst_module,
                &fsti_module,
            ) {
                let range_key = (fst_typedef.start_line, fst_typedef.end_line);
                if !removed_ranges.contains(&range_key) {
                    removed_ranges.insert(range_key);

                    // CRITICAL SAFETY: Validate the fix before offering it
                    let validation = validate_fix(
                        fst_content,
                        fsti_content,
                        type_name,
                        fst_typedef,
                        fsti_typedef,
                    );

                    // Build the diagnostic message
                    let mut message = if fst_typedef.mutual_names.is_empty() {
                        format!(
                            "Type `{}` is defined in both .fst and .fsti.",
                            type_name
                        )
                    } else {
                        format!(
                            "Mutual recursion block ({}) is defined in both .fst and .fsti.",
                            fst_typedef.mutual_names.join(", ")
                        )
                    };

                    // Determine if we can offer a fix
                    let fix = if validation.is_safe {
                        // Add preview info to the message
                        if !validation.warnings.is_empty() {
                            message.push_str("\n\nWarnings:");
                            for warning in &validation.warnings {
                                message.push_str(&format!("\n  - {}", warning));
                            }
                        }
                        message.push_str("\n\nSafe to remove the duplicate from .fst.");

                        // Create fix with detailed message including preview
                        // Safety level depends on whether there are warnings:
                        // - No warnings + exact match = Safe (auto-apply)
                        // - Warnings present = Caution (show warning when applying)
                        let edits = vec![Edit {
                            file: fst_file.to_path_buf(),
                            // Convert 0-indexed to 1-indexed for Range.
                            // end_line is 0-indexed inclusive, so +1 converts to 1-indexed.
                            // Do NOT add +2 here: that deletes one line beyond the type
                            // definition, which corrupts the file when there is no trailing
                            // blank line. Consecutive blank lines left after removal are
                            // cleaned up by the post-processing step in build_fixed_content.
                            range: Range::new(
                                fst_typedef.start_line + 1,
                                1,
                                fst_typedef.end_line + 1,
                                1,
                            ),
                            new_text: String::new(),
                        }];

                        let fix = if validation.warnings.is_empty() {
                            // Definitions match exactly - safe to auto-apply
                            Fix::safe(
                                format!(
                                    "Remove duplicate type `{}` (definitions match exactly)\n\nPreview:\n{}",
                                    type_name, validation.removal_preview
                                ),
                                edits,
                            )
                            .with_reversible(false)  // Deletion is not easily reversible
                        } else {
                            // Definitions match with minor differences - caution
                            Fix::caution(
                                format!(
                                    "Remove duplicate type `{}` (definitions match with minor differences)\n\nPreview:\n{}",
                                    type_name, validation.removal_preview
                                ),
                                edits,
                            )
                            .with_reversible(false)
                            .with_requires_review(true)
                        };

                        Some(fix)
                    } else {
                        // Definitions don't match - DO NOT offer autofix
                        message.push_str(&format!(
                            "\n\nNO AUTOFIX: {}\n\nManual review required.",
                            validation.reason
                        ));
                        None
                    };

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST001,
                        severity: DiagnosticSeverity::Warning,
                        file: fst_file.to_path_buf(),
                        range: Range::new(
                            fst_typedef.start_line + 1,
                            1,
                            fst_typedef.end_line + 1,
                            1,
                        ),
                        message,
                        fix,
                    });
                }
            }
        }

        diagnostics
    }
}

/// Clean up multiple consecutive blank lines in content, keeping at most one.
///
/// This function should be called after applying fixes that remove type blocks,
/// as the removal may leave behind multiple consecutive blank lines.
///
/// # Example
/// ```ignore
/// use fstar_lsp::lint::duplicate_types::cleanup_consecutive_blanks;
///
/// let content = "line1\n\n\n\nline2";
/// let cleaned = cleanup_consecutive_blanks(content);
/// assert_eq!(cleaned, "line1\n\nline2");
/// ```
pub fn cleanup_consecutive_blanks(content: &str) -> String {
    let mut result = Vec::new();
    let mut prev_blank = false;

    for line in content.lines() {
        let is_blank = line.trim().is_empty();
        if is_blank && prev_blank {
            // Skip consecutive blank line
            continue;
        }
        result.push(line);
        prev_blank = is_blank;
    }

    // Preserve trailing newline if original had one
    let mut output = result.join("\n");
    if content.ends_with('\n') {
        output.push('\n');
    }

    output
}

/// Resolve a path to its canonical form for use as a HashMap key.
///
/// Attempts `std::fs::canonicalize` first (resolves symlinks and relative
/// components). Falls back to the original path when canonicalization fails
/// (e.g., the file does not exist on disk, as in unit tests with synthetic
/// paths).
fn canonicalize_for_key(path: &Path) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

/// Find pairs of .fst and .fsti files.
///
/// Matches files by their full canonicalized path with the extension stripped,
/// so files with the same name in different directories (e.g.,
/// `src/A/Types.fst` and `src/B/Types.fst`) are correctly distinguished.
///
/// Symlinks are resolved via `std::fs::canonicalize` before matching, so a
/// symlinked `.fst` file and its real `.fsti` counterpart are paired correctly.
///
/// Warns (via `tracing::warn`) when a `.fst` file has no `.fsti` counterpart
/// and vice versa, unless the companion exists on disk but was not included in
/// the input `files` slice.
pub fn find_fst_fsti_pairs(files: &[PathBuf]) -> Vec<(PathBuf, PathBuf)> {
    let mut pairs = Vec::new();

    // Map: canonical path without extension -> original PathBuf
    let mut fst_files: HashMap<PathBuf, PathBuf> = HashMap::new();
    let mut fsti_files: HashMap<PathBuf, PathBuf> = HashMap::new();

    for file in files {
        let ext_str = file.extension().and_then(|e| e.to_str());
        let canonical = canonicalize_for_key(file);
        let key = canonical.with_extension("");

        match ext_str {
            Some("fst") => {
                fst_files.insert(key, file.clone());
            }
            Some("fsti") => {
                fsti_files.insert(key, file.clone());
            }
            _ => {}
        }
    }

    // Track which fsti keys were matched so we can warn about orphans
    let mut matched_fsti_keys: HashSet<PathBuf> = HashSet::new();

    for (key, fst_path) in &fst_files {
        if let Some(fsti_path) = fsti_files.get(key) {
            // Both .fst and .fsti were in the input list
            pairs.push((fst_path.clone(), fsti_path.clone()));
            matched_fsti_keys.insert(key.clone());
        } else {
            // .fsti was not in the input list; check if it exists on disk
            let fsti_on_disk = fst_path.with_extension("fsti");
            if fsti_on_disk.exists() {
                pairs.push((fst_path.clone(), fsti_on_disk));
            } else {
                warn!(
                    "No .fsti counterpart found for {}",
                    fst_path.display()
                );
            }
        }
    }

    // Warn about .fsti files whose .fst counterpart is missing
    for (key, fsti_path) in &fsti_files {
        if matched_fsti_keys.contains(key) || fst_files.contains_key(key) {
            continue;
        }
        // .fst was not in the input list; check if it exists on disk
        let fst_on_disk = fsti_path.with_extension("fst");
        if fst_on_disk.exists() {
            pairs.push((fst_on_disk, fsti_path.clone()));
        } else {
            warn!(
                "No .fst counterpart found for {}",
                fsti_path.display()
            );
        }
    }

    pairs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_simple_type() {
        let content = r#"
module Test

type mytype = int

let x = 1
"#;
        let types = find_type_definitions(content);
        assert!(types.contains_key("mytype"));
    }

    #[test]
    fn test_find_noeq_type() {
        let content = r#"
noeq type buffer (a: Type) = {
    content: seq a;
    length: nat
}
"#;
        let types = find_type_definitions(content);
        assert!(types.contains_key("buffer"));
    }

    #[test]
    fn test_find_mutual_recursion() {
        let content = r#"
type expr =
  | Var of string
  | App of expr * expr

and pattern =
  | PVar of string
  | PWild
"#;
        let types = find_type_definitions(content);
        assert!(types.contains_key("expr"));
        assert!(types.contains_key("pattern"));
        // Both should share the same block
        assert_eq!(types["expr"].start_line, types["pattern"].start_line);
    }

    #[test]
    fn test_private_type_detection() {
        let content = r#"
private type internal_state = {
    counter: nat
}
"#;
        let types = find_type_definitions(content);
        assert!(types.contains_key("internal_state"));
        assert!(types["internal_state"].is_private);
    }

    #[test]
    fn test_concrete_definition() {
        assert!(is_concrete_definition("type foo = int"));
        assert!(is_concrete_definition("noeq type bar = { x: int }"));
        assert!(!is_concrete_definition("type abstract_t"));
        assert!(!is_concrete_definition("type constrained : Type0"));
    }

    #[test]
    fn test_concrete_definition_with_comments() {
        // BUG FIX: Line comments with = should not be considered concrete
        assert!(!is_concrete_definition(
            "// Comment with = sign\n// Another comment = here\ntype abstract_t"
        ));

        // BUG FIX: Block comments with stars inside should be stripped correctly
        assert!(!is_concrete_definition(
            "(* Comment * with star and = inside *)\ntype abstract_t"
        ));

        // Still correctly identifies concrete types
        assert!(is_concrete_definition(
            "// Comment with = sign\ntype foo = int"
        ));
        assert!(is_concrete_definition("(* comment *) type bar = nat"));
    }

    #[test]
    fn test_cleanup_consecutive_blanks() {
        // Multiple consecutive blank lines should be reduced to one
        assert_eq!(
            cleanup_consecutive_blanks("line1\n\n\n\nline2"),
            "line1\n\nline2"
        );

        // Single blank line should be preserved
        assert_eq!(
            cleanup_consecutive_blanks("line1\n\nline2"),
            "line1\n\nline2"
        );

        // No blank lines should remain unchanged
        assert_eq!(cleanup_consecutive_blanks("line1\nline2"), "line1\nline2");

        // Trailing newline should be preserved
        assert_eq!(
            cleanup_consecutive_blanks("line1\n\n\nline2\n"),
            "line1\n\nline2\n"
        );

        // Empty content
        assert_eq!(cleanup_consecutive_blanks(""), "");

        // Only blank lines
        assert_eq!(cleanup_consecutive_blanks("\n\n\n"), "\n");

        // Mixed whitespace lines (tabs and spaces count as blank)
        assert_eq!(
            cleanup_consecutive_blanks("line1\n  \n\t\n\nline2"),
            "line1\n  \nline2"
        );
    }

    #[test]
    fn test_detect_duplicate() {
        let fst_content = r#"
module Test

type mytype = int

let foo x = x
"#;
        let fsti_content = r#"
module Test

type mytype = int

val foo: int -> int
"#;

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("Test.fst"),
            fst_content,
            &PathBuf::from("Test.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty());
        assert!(diagnostics[0].message.contains("mytype"));
    }

    // ---- FALSE POSITIVE tests: abstract .fsti + concrete .fst is VALID ----

    #[test]
    fn test_no_false_positive_abstract_fsti_concrete_fst() {
        // Abstract type in .fsti, concrete in .fst => NOT a duplicate
        let fsti_content = "module Test\n\ntype t\n\nval foo: t -> int\n";
        let fst_content = "module Test\n\ntype t = int\n\nlet foo x = x\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("Test.fst"),
            fst_content,
            &PathBuf::from("Test.fsti"),
            fsti_content,
        );

        assert!(diagnostics.is_empty(), "Abstract .fsti + concrete .fst should NOT be flagged");
    }

    #[test]
    fn test_no_false_positive_abstract_with_kind() {
        // type t : Type0 in .fsti (abstract with kind annotation)
        let fsti_content = "module Test\n\ntype t : Type0\n\nval foo: t -> int\n";
        let fst_content = "module Test\n\ntype t = nat\n\nlet foo x = x\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("Test.fst"),
            fst_content,
            &PathBuf::from("Test.fsti"),
            fsti_content,
        );

        assert!(diagnostics.is_empty(), "Abstract type with kind annotation should NOT be flagged");
    }

    #[test]
    fn test_no_false_positive_abstract_eqtype() {
        // type t : eqtype in .fsti
        let fsti_content = "module Test\n\ntype t : eqtype\n";
        let fst_content = "module Test\n\ntype t = | A | B | C\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("Test.fst"),
            fst_content,
            &PathBuf::from("Test.fsti"),
            fsti_content,
        );

        assert!(diagnostics.is_empty(), "Abstract eqtype should NOT be flagged");
    }

    // ---- is_concrete_definition: depth-aware = detection ----

    #[test]
    fn test_concrete_equals_inside_refinement_not_concrete() {
        // type t (x: int{x = 0}) : Type  -- the = is inside braces, NOT a type body
        assert!(!is_concrete_definition(
            "type t (x: int{x = 0}) : Type"
        ));
    }

    #[test]
    fn test_concrete_equals_inside_parens_not_concrete() {
        // type t (x: int) (y: (z:int{z = x})) : Type
        assert!(!is_concrete_definition(
            "type t (x: int) (y: (z:int{z = x})) : Type"
        ));
    }

    #[test]
    fn test_concrete_multiline_abstract_with_refinement() {
        // Multi-line abstract type with = inside parameter refinement
        let block = "type my_type\n  (x: nat{x = 0})\n  : Type";
        assert!(!is_concrete_definition(block),
            "Abstract type with = inside refinement should NOT be concrete");
    }

    #[test]
    fn test_concrete_multiline_concrete_with_refinement() {
        // Multi-line concrete type: the = for the body is at depth 0
        let block = "type my_type\n  (x: nat{x = 0})\n  : Type =\n  | Mk : my_type";
        assert!(is_concrete_definition(block),
            "Concrete type with = at depth 0 should be detected");
    }

    #[test]
    fn test_concrete_double_equals_not_concrete() {
        // == is propositional equality, not a type body definition
        assert!(!is_concrete_definition(
            "type t (x: nat) : (y:Type{x == 0})"
        ));
    }

    #[test]
    fn test_concrete_operators_not_concrete() {
        // >=, <=, != should not be confused with =
        assert!(!is_concrete_definition("type t (x: nat{x >= 0}) : Type"));
        assert!(!is_concrete_definition("type t (x: nat{x <= 10}) : Type"));
        assert!(!is_concrete_definition("type t (x: nat{x != 0}) : Type"));
    }

    #[test]
    fn test_concrete_arrow_equals_not_concrete() {
        // => is match/implication arrow, not type body
        assert!(!is_concrete_definition("type t (x: nat{x > 0 ==> True}) : Type"));
    }

    #[test]
    fn test_concrete_adt_is_concrete() {
        // Standard ADT with = at depth 0
        assert!(is_concrete_definition("type color =\n  | Red\n  | Green\n  | Blue"));
    }

    #[test]
    fn test_concrete_record_is_concrete() {
        assert!(is_concrete_definition("noeq type rec = {\n  x: int;\n  y: int\n}"));
    }

    #[test]
    fn test_concrete_type_alias_is_concrete() {
        assert!(is_concrete_definition("type my_nat = nat"));
    }

    // ---- unopteq modifier support ----

    #[test]
    fn test_find_unopteq_type() {
        let content = "module Test\n\nunopteq type dtuple4\n  (a: Type) (b: a -> Type)\n  = | Mk : a -> dtuple4 a b\n";
        let types = find_type_definitions(content);
        assert!(types.contains_key("dtuple4"), "unopteq types should be detected");
    }

    #[test]
    fn test_detect_duplicate_unopteq() {
        let fsti_content = "module T\n\nunopteq type t = | A | B\n";
        let fst_content = "module T\n\nunopteq type t = | A | B\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty(), "Duplicate unopteq types should be flagged");
    }

    // ---- TRUE DUPLICATE detection (should still work) ----

    #[test]
    fn test_true_duplicate_noeq_record() {
        let fsti_content = "module T\n\nnoeq type state = {\n  counter: nat;\n  data: list int\n}\n";
        let fst_content = "module T\n\nnoeq type state = {\n  counter: nat;\n  data: list int\n}\n\nlet init = { counter = 0; data = [] }\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty(), "Identical noeq record in both files should be flagged");
    }

    #[test]
    fn test_true_duplicate_type_alias() {
        let fsti_content = "module T\n\ntype byte = UInt8.t\n";
        let fst_content = "module T\n\ntype byte = UInt8.t\n\nlet zero : byte = 0uy\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty(), "Identical type alias in both files should be flagged");
    }

    // ---- Private types should NOT be flagged ----

    #[test]
    fn test_private_type_not_flagged() {
        let fsti_content = "module T\n\ntype t = int\n";
        let fst_content = "module T\n\ntype t = int\n\nprivate type internal = nat\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        // Should flag 't' but not 'internal'
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].message.contains("t"));
    }

    // ---- Real-world pattern: multiline parameterized concrete type ----

    #[test]
    fn test_multiline_parameterized_concrete() {
        // Pattern from LowParse.Repr.fsti: multiline type with = on later line
        let block = "noeq inline_for_extraction\ntype field_accessor (#k1 #k2:strong_parser_kind)\n                    (#t1 #t2:Type)\n                    (p1 : LP.parser k1 t1)\n                    (p2 : LP.parser k2 t2) =\n  | FieldAccessor :\n     (acc:LP.accessor g) ->\n     field_accessor p1 p2";
        assert!(is_concrete_definition(block),
            "Multiline concrete type with = on later line should be detected");
    }

    // ---- Edge case: = inside string literal ----

    #[test]
    fn test_equals_in_string_not_concrete() {
        // Hypothetical: = inside a string in a type annotation
        assert!(!is_concrete_definition(
            "type t (x: string{x = \"hello = world\"}) : Type"
        ));
    }

    // ===========================================================================
    // SAFETY VALIDATION TESTS
    // ===========================================================================

    #[test]
    fn test_definitions_match_identical() {
        let fst_block = "noeq type labeled_type = {\n  base_type : brrr_type;\n  label     : sec_level;\n}";
        let fsti_block = "noeq type labeled_type = {\n  base_type : brrr_type;\n  label     : sec_level;\n}";

        assert!(definitions_match(fst_block, fsti_block));
    }

    #[test]
    fn test_definitions_match_with_whitespace_diff() {
        let fst_block = "noeq type labeled_type = {\n  base_type : brrr_type;\n  label     : sec_level;\n}";
        let fsti_block = "noeq type labeled_type = { base_type : brrr_type; label : sec_level; }";

        assert!(definitions_match(fst_block, fsti_block));
    }

    #[test]
    fn test_definitions_match_with_comment_diff() {
        let fst_block = "(** Labeled type *)\nnoeq type labeled_type = {\n  base_type : brrr_type;\n  label     : sec_level;\n}";
        let fsti_block = "noeq type labeled_type = {\n  base_type : brrr_type;\n  label     : sec_level;\n}";

        assert!(definitions_match(fst_block, fsti_block));
    }

    #[test]
    fn test_definitions_dont_match_different_fields() {
        let fst_block = "noeq type labeled_type = {\n  base_type : brrr_type;\n  label     : sec_level;\n  extra     : nat;\n}";
        let fsti_block = "noeq type labeled_type = {\n  base_type : brrr_type;\n  label     : sec_level;\n}";

        assert!(!definitions_match(fst_block, fsti_block));
    }

    #[test]
    fn test_definitions_dont_match_different_types() {
        let fst_block = "type sec_level = | Public | Secret";
        let fsti_block = "type sec_level = | Public | Private | Secret";

        assert!(!definitions_match(fst_block, fsti_block));
    }

    #[test]
    fn test_no_autofix_when_definitions_differ() {
        // .fsti has a different definition than .fst
        let fsti_content = "module T\n\ntype color = | Red | Green | Blue\n";
        let fst_content = "module T\n\ntype color = | Red | Green\n"; // Missing Blue!

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        // Should produce a diagnostic but WITHOUT a fix
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].fix.is_none(), "Should NOT offer autofix when definitions differ");
        assert!(diagnostics[0].message.contains("NO AUTOFIX"));
    }

    #[test]
    fn test_autofix_offered_when_definitions_match() {
        let fsti_content = "module T\n\ntype sec_level =\n  | Public\n  | Secret\n";
        let fst_content = "module T\n\ntype sec_level =\n  | Public\n  | Secret\n\nlet x = 1\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].fix.is_some(), "Should offer autofix when definitions match");
        assert!(diagnostics[0].message.contains("Safe to remove"));
    }

    // ===========================================================================
    // REAL-WORLD PATTERNS FROM BrrrInformationFlow
    // ===========================================================================

    #[test]
    fn test_brrr_sec_level_type() {
        // Pattern from BrrrInformationFlow.fst/fsti
        let fsti_content = r#"module BrrrInformationFlow

type sec_level =
  | Public       : sec_level
  | Confidential : sec_level
  | Secret       : sec_level
  | TopSecret    : sec_level

val sec_leq (l1 l2: sec_level) : bool
"#;
        let fst_content = r#"module BrrrInformationFlow

type sec_level =
  | Public       : sec_level
  | Confidential : sec_level
  | Secret       : sec_level
  | TopSecret    : sec_level

let sec_leq (l1 l2: sec_level) : bool =
  match l1, l2 with
  | Public, _ -> true
  | _, TopSecret -> true
  | Secret, Secret -> true
  | Confidential, Confidential -> true
  | _, _ -> false
"#;

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("BrrrInformationFlow.fst"),
            fst_content,
            &PathBuf::from("BrrrInformationFlow.fsti"),
            fsti_content,
        );

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].fix.is_some(), "Identical sec_level should have autofix");
    }

    #[test]
    fn test_brrr_labeled_type_noeq() {
        // Pattern from BrrrInformationFlow - noeq record type
        let fsti_content = r#"module BrrrInformationFlow

noeq type labeled_type = {
  base_type : brrr_type;
  label     : sec_level;
}

val label_type (t: brrr_type) (l: sec_level) : labeled_type
"#;
        let fst_content = r#"module BrrrInformationFlow

noeq type labeled_type = {
  base_type : brrr_type;
  label     : sec_level;
}

let label_type (t: brrr_type) (l: sec_level) : labeled_type =
  { base_type = t; label = l }
"#;

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("BrrrInformationFlow.fst"),
            fst_content,
            &PathBuf::from("BrrrInformationFlow.fsti"),
            fsti_content,
        );

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].fix.is_some(), "Identical noeq record should have autofix");
    }

    #[test]
    fn test_brrr_sec_check_result_adt() {
        // Pattern from BrrrInformationFlow - ADT with multiple constructors
        let fsti_content = r#"module BrrrInformationFlow

noeq type sec_check_result =
  | SecOk  : labeled_type -> sec_ctx -> sec_check_result
  | SecErr : string -> sec_check_result

val check_flow (ctx: sec_ctx) (e: expr) : sec_check_result
"#;
        let fst_content = r#"module BrrrInformationFlow

noeq type sec_check_result =
  | SecOk  : labeled_type -> sec_ctx -> sec_check_result
  | SecErr : string -> sec_check_result

let check_flow (ctx: sec_ctx) (e: expr) : sec_check_result =
  SecOk (public_type TUnit) ctx
"#;

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("BrrrInformationFlow.fst"),
            fst_content,
            &PathBuf::from("BrrrInformationFlow.fsti"),
            fsti_content,
        );

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].fix.is_some(), "Identical ADT should have autofix");
    }

    #[test]
    fn test_brrr_security_label_combined() {
        // Pattern from BrrrInformationFlow - combined confidentiality/integrity
        let fsti_content = r#"module BrrrInformationFlow

noeq type security_label = {
  confidentiality : sec_level;
  integrity       : integrity_level_full;
}

val security_label_leq (l1 l2: security_label) : bool
"#;
        let fst_content = r#"module BrrrInformationFlow

noeq type security_label = {
  confidentiality : sec_level;
  integrity       : integrity_level_full;
}

let security_label_leq (l1 l2: security_label) : bool =
  sec_leq l1.confidentiality l2.confidentiality &&
  integrity_leq_full l1.integrity l2.integrity
"#;

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("BrrrInformationFlow.fst"),
            fst_content,
            &PathBuf::from("BrrrInformationFlow.fsti"),
            fsti_content,
        );

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].fix.is_some());
    }

    #[test]
    fn test_no_autofix_modified_adt_variant() {
        // Modified ADT - should NOT offer autofix
        let fsti_content = r#"module T

type termination_behavior =
  | MustTerminate    : termination_behavior
  | MayDiverge       : termination_behavior
  | MustDiverge      : termination_behavior
"#;
        let fst_content = r#"module T

type termination_behavior =
  | MustTerminate    : termination_behavior
  | MayDiverge       : termination_behavior
  | Unknown          : termination_behavior
"#;

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].fix.is_none(), "Different ADT variants should NOT have autofix");
    }

    #[test]
    fn test_no_autofix_modified_record_field() {
        // Modified record field type - should NOT offer autofix
        let fsti_content = r#"module T

noeq type declass_policy = {
  declass_name : string;
  allowed_patterns : list string;
  max_declass : option nat;
}
"#;
        let fst_content = r#"module T

noeq type declass_policy = {
  declass_name : string;
  allowed_patterns : list string;
  max_declass : nat;
}
"#;

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].fix.is_none(), "Different field types should NOT have autofix");
    }

    // ===========================================================================
    // DRY-RUN TESTS
    // ===========================================================================

    // ===========================================================================
    // NORMALIZE DEFINITION TESTS
    // ===========================================================================

    #[test]
    fn test_normalize_removes_comments() {
        let block = "(* This is a comment *)\ntype t = int";
        let normalized = normalize_type_definition(block);
        assert!(!normalized.contains("comment"));
        assert!(normalized.contains("type t = int"));
    }

    #[test]
    fn test_normalize_removes_line_comments() {
        let block = "// Line comment\ntype t = int // trailing";
        let normalized = normalize_type_definition(block);
        assert!(!normalized.contains("comment"));
        assert!(!normalized.contains("trailing"));
    }

    #[test]
    fn test_normalize_removes_attributes() {
        let block = "[@attribute] [@@another]\ntype t = int";
        let normalized = normalize_type_definition(block);
        assert!(!normalized.contains("attribute"));
        assert!(normalized.contains("type t = int"));
    }

    #[test]
    fn test_normalize_whitespace_collapse() {
        let block = "type   t    =    int";
        let normalized = normalize_type_definition(block);
        assert_eq!(normalized, "type t = int");
    }

    // ===========================================================================
    // VALIDATE_FIX TESTS
    // ===========================================================================

    #[test]
    fn test_validate_fix_safe() {
        let fst_content = "module T\n\ntype t = int\n\nlet x = 1\n";
        let fsti_content = "module T\n\ntype t = int\n";

        let fst_types = find_type_definitions(fst_content);
        let fsti_types = find_type_definitions(fsti_content);

        let fst_typedef = fst_types.get("t").unwrap();
        let fsti_typedef = fsti_types.get("t").unwrap();

        let validation = validate_fix(fst_content, fsti_content, "t", fst_typedef, fsti_typedef);

        assert!(validation.is_safe);
        assert!(!validation.removal_preview.is_empty());
    }

    #[test]
    fn test_validate_fix_unsafe_mismatch() {
        let fst_content = "module T\n\ntype t = nat\n";
        let fsti_content = "module T\n\ntype t = int\n";

        let fst_types = find_type_definitions(fst_content);
        let fsti_types = find_type_definitions(fsti_content);

        let fst_typedef = fst_types.get("t").unwrap();
        let fsti_typedef = fsti_types.get("t").unwrap();

        let validation = validate_fix(fst_content, fsti_content, "t", fst_typedef, fsti_typedef);

        assert!(!validation.is_safe);
        assert!(validation.reason.contains("differ"));
    }

    #[test]
    fn test_validate_fix_with_references() {
        let fst_content = "module T\n\ntype t = int\n\nlet x : t = 0\nlet y : t = 1\n";
        let fsti_content = "module T\n\ntype t = int\n";

        let fst_types = find_type_definitions(fst_content);
        let fsti_types = find_type_definitions(fsti_content);

        let fst_typedef = fst_types.get("t").unwrap();
        let fsti_typedef = fsti_types.get("t").unwrap();

        let validation = validate_fix(fst_content, fsti_content, "t", fst_typedef, fsti_typedef);

        // Should still be safe (type available from .fsti) but with warnings
        assert!(validation.is_safe);
        assert!(!validation.warnings.is_empty(), "Should warn about references");
    }

    // ===========================================================================
    // COMMENT PREFIX DETECTION TESTS (find_attribute_prefix_lines)
    // ===========================================================================

    #[test]
    fn test_count_comment_delimiters_single_line() {
        assert_eq!(count_comment_delimiters("(* comment *)"), (1, 1));
        assert_eq!(count_comment_delimiters("(** doc comment *)"), (1, 1));
        assert_eq!(count_comment_delimiters("no delimiters here"), (0, 0));
        assert_eq!(count_comment_delimiters("(* start only"), (1, 0));
        assert_eq!(count_comment_delimiters("end only *)"), (0, 1));
        assert_eq!(count_comment_delimiters("(* outer (* inner *) outer *)"), (2, 2));
    }

    #[test]
    fn test_prefix_single_line_doc_comment() {
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "(** Documentation for this type *)",
            "type foo = int",
        ];
        // type_start = 3 (the "type foo = int" line)
        assert_eq!(find_attribute_prefix_lines(&lines, 3), 2);
    }

    #[test]
    fn test_prefix_multi_line_doc_comment_block() {
        // Doc comments (** ...) should be included in prefix
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "(** This is a",
            "    multi-line doc comment",
            "    about the type *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 5), 2);
    }

    #[test]
    fn test_prefix_multi_line_regular_comment_excluded() {
        // Regular comments (* ...) should NOT be included in prefix
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "(* This is a",
            "   multi-line comment",
            "   about the type *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 5), 5);
    }

    #[test]
    fn test_prefix_comment_plus_attribute() {
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "(** Doc comment *)",
            "[@attribute]",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 4), 2);
    }

    #[test]
    fn test_prefix_section_header_comment() {
        // Section header comments (* ... *) are regular comments, NOT doc comments.
        // They should NOT be included in the type's prefix range.
        let lines: Vec<&str> = vec![
            "let x = 1",
            "",
            "(* === Types === *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 3), 3);
    }

    #[test]
    fn test_prefix_empty_line_breaks_chain_at_depth_zero() {
        let lines: Vec<&str> = vec![
            "(* Comment *)",
            "",
            "type foo = int",
        ];
        // Empty line at depth 0 should break the chain
        assert_eq!(find_attribute_prefix_lines(&lines, 2), 2);
    }

    #[test]
    fn test_prefix_nested_doc_comments() {
        // Nested doc comment (** outer (* inner *) still outer *) should be included
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "(** outer (* inner *) still outer *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 3), 2);
    }

    #[test]
    fn test_prefix_nested_regular_comments_excluded() {
        // Nested regular comment (* outer (* inner *) *) should NOT be included
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "(* outer (* inner *) still outer *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 3), 3);
    }

    #[test]
    fn test_prefix_empty_line_inside_multiline_doc_comment() {
        // Doc comment with blank line inside should still be fully included
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "(** multi-line doc comment",
            "",
            "    with blank line inside *)",
            "type foo = int",
        ];
        // The empty line is inside the doc comment block (depth > 0), so include it
        assert_eq!(find_attribute_prefix_lines(&lines, 5), 2);
    }

    #[test]
    fn test_prefix_empty_line_inside_multiline_regular_comment_excluded() {
        // Regular multi-line comment should NOT be included even with blank line inside
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "(* multi-line comment",
            "",
            "   with blank line inside *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 5), 5);
    }

    #[test]
    fn test_prefix_line_comment_before_type_excluded() {
        // Regular // line comments are NOT doc comments; should NOT be included
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "// Line comment about the type",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 3), 3);
    }

    #[test]
    fn test_prefix_doc_line_comment_before_type() {
        // Doc line comments /// SHOULD be included
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "/// Doc line comment about the type",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 3), 2);
    }

    #[test]
    fn test_prefix_multiple_line_comments_excluded() {
        // Regular // comments should NOT be included in prefix
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "// First comment",
            "// Second comment",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 4), 4);
    }

    #[test]
    fn test_prefix_multiple_doc_line_comments() {
        // Doc line comments /// SHOULD be included
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "/// First doc comment",
            "/// Second doc comment",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 4), 2);
    }

    #[test]
    fn test_prefix_mixed_doc_comment_and_attributes() {
        // Regular // between doc comment and attributes breaks the chain.
        // Only the attributes below the // are included.
        let lines: Vec<&str> = vec![
            "let x = 1",
            "",
            "(** Doc comment for type *)",
            "// Additional note",
            "[@@some_attribute]",
            "[@another]",
            "type foo = int",
        ];
        // Scanning backward from 6: attrs at 5,4 included, // at 3 breaks chain
        assert_eq!(find_attribute_prefix_lines(&lines, 6), 4);
    }

    #[test]
    fn test_prefix_doc_comment_directly_above_attributes() {
        // Doc comment directly adjacent to attributes should all be included
        let lines: Vec<&str> = vec![
            "let x = 1",
            "",
            "(** Doc comment for type *)",
            "[@@some_attribute]",
            "[@another]",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 5), 2);
    }

    #[test]
    fn test_prefix_only_attributes_still_works() {
        let lines: Vec<&str> = vec![
            "let x = 1",
            "",
            "[@attr1]",
            "[@@attr2]",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 4), 2);
    }

    #[test]
    fn test_prefix_no_prefix() {
        let lines: Vec<&str> = vec![
            "let x = 1",
            "",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 2), 2);
    }

    #[test]
    fn test_prefix_at_line_zero() {
        let lines: Vec<&str> = vec![
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 0), 0);
    }

    #[test]
    fn test_prefix_regular_comment_at_line_zero_excluded() {
        // Regular comment at line 0 should NOT be included
        let lines: Vec<&str> = vec![
            "(* Top-level comment *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 1), 1);
    }

    #[test]
    fn test_prefix_doc_comment_at_line_zero() {
        // Doc comment at line 0 SHOULD be included
        let lines: Vec<&str> = vec![
            "(** Top-level doc comment *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 1), 0);
    }

    #[test]
    fn test_prefix_stops_at_regular_comment() {
        // Regular comment (* ... *) should NOT be included in prefix
        let lines: Vec<&str> = vec![
            "let x = 1",
            "(* Comment about type *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 2), 2);
    }

    #[test]
    fn test_prefix_stops_at_code_line_after_doc() {
        // Doc comment should be included but code line should not
        let lines: Vec<&str> = vec![
            "let x = 1",
            "(** Doc comment about type *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 2), 1);
    }

    #[test]
    fn test_prefix_regular_comment_adjacent_excluded() {
        // Regular comment (* ... *) adjacent to type should NOT be included
        let lines: Vec<&str> = vec![
            "(* Old comment *)",
            "",
            "(* Actual comment *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 3), 3);
    }

    #[test]
    fn test_prefix_doc_comment_adjacent_included() {
        // Doc comment (** ... *) adjacent to type SHOULD be included
        let lines: Vec<&str> = vec![
            "(* Old comment *)",
            "",
            "(** Actual doc comment *)",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 3), 2);
    }

    // Verify the full pipeline: comments before type are included in the block
    #[test]
    fn test_find_type_definitions_includes_doc_comment() {
        let content = "module Test\n\n(** Doc comment *)\ntype foo = int\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        let foo = types.get("foo").unwrap();
        // start_line should be the doc comment line (line index 2)
        assert_eq!(foo.start_line, 2);
        assert!(foo.block.contains("Doc comment"));
    }

    #[test]
    fn test_find_type_definitions_excludes_regular_multiline_comment() {
        // Regular multi-line comment (* ... *) should NOT be included in the type's range
        let content = "module Test\n\n(* Multi-line\n   comment *)\ntype foo = int\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        let foo = types.get("foo").unwrap();
        assert_eq!(foo.start_line, 4, "Regular comment should not be in type range");
        assert!(!foo.block.contains("Multi-line"));
    }

    #[test]
    fn test_find_type_definitions_includes_doc_multiline_comment() {
        // Doc multi-line comment (** ... *) SHOULD be included in the type's range
        let content = "module Test\n\n(** Multi-line\n    doc comment *)\ntype foo = int\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        let foo = types.get("foo").unwrap();
        assert_eq!(foo.start_line, 2, "Doc comment should be in type range");
        assert!(foo.block.contains("Multi-line"));
    }

    #[test]
    fn test_find_type_definitions_comment_separated_by_blank_not_included() {
        let content = "module Test\n\n(* Unrelated comment *)\n\ntype foo = int\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        let foo = types.get("foo").unwrap();
        // start_line should be the type line (line index 4), NOT the comment
        assert_eq!(foo.start_line, 4);
        assert!(!foo.block.contains("Unrelated"));
    }

    // =========================================================================
    // strip_nested_block_comments: nesting-aware comment stripping tests
    // =========================================================================

    #[test]
    fn test_strip_nested_simple() {
        assert_eq!(
            strip_nested_block_comments("code (* comment *) more", " "),
            "code   more"
        );
    }

    #[test]
    fn test_strip_nested_no_comments() {
        assert_eq!(
            strip_nested_block_comments("no comments here", " "),
            "no comments here"
        );
    }

    #[test]
    fn test_strip_nested_depth_two() {
        // (* outer (* inner *) outer *) is ONE comment
        assert_eq!(
            strip_nested_block_comments("before (* outer (* inner *) outer *) after", " "),
            "before   after"
        );
    }

    #[test]
    fn test_strip_nested_depth_three() {
        assert_eq!(
            strip_nested_block_comments("x (* a (* b (* c *) b *) a *) y", ""),
            "x  y"
        );
    }

    #[test]
    fn test_strip_nested_multiple_comments() {
        assert_eq!(
            strip_nested_block_comments("a (* b *) c (* d *) e", " "),
            "a   c   e"
        );
    }

    #[test]
    fn test_strip_nested_string_inside_comment() {
        // F* convention: strings inside comments are respected
        // (* "*)" *) is ONE comment (the *) inside the string is ignored)
        assert_eq!(
            strip_nested_block_comments(r#"before (* "*)" *) after"#, " "),
            "before   after"
        );
    }

    #[test]
    fn test_strip_nested_string_with_escaped_quote_in_comment() {
        // (* "ab\"*)" *) - the string contains ab"*) and the real close is the last *)
        assert_eq!(
            strip_nested_block_comments(r#"X (* "ab\"*)" *) Y"#, ""),
            "X  Y"
        );
    }

    #[test]
    fn test_strip_nested_string_with_escaped_backslash_in_comment() {
        // (* "ab\\" *) - the string is "ab\" (escaped backslash),
        // then *) closes the comment
        assert_eq!(
            strip_nested_block_comments(r#"X (* "ab\\" *) Y"#, ""),
            "X  Y"
        );
    }

    #[test]
    fn test_strip_nested_preserves_top_level_strings() {
        // Strings outside comments are preserved
        assert_eq!(
            strip_nested_block_comments(r#""kept" (* removed *) "also kept""#, ""),
            r#""kept"  "also kept""#
        );
    }

    #[test]
    fn test_strip_nested_string_with_comment_marker_preserved() {
        // "(*" in a top-level string is NOT a comment open
        assert_eq!(
            strip_nested_block_comments(r#""(*" code "*)""#, ""),
            r#""(*" code "*)""#
        );
    }

    #[test]
    fn test_strip_nested_empty_replacement() {
        assert_eq!(
            strip_nested_block_comments("a (* b *) c", ""),
            "a  c"
        );
    }

    #[test]
    fn test_strip_nested_empty_input() {
        assert_eq!(strip_nested_block_comments("", " "), "");
    }

    #[test]
    fn test_strip_nested_unclosed_comment() {
        // Unclosed comment: everything after (* is consumed
        assert_eq!(
            strip_nested_block_comments("before (* unclosed", " "),
            "before "
        );
    }

    #[test]
    fn test_strip_nested_concrete_definition_with_nested_comment() {
        // Regression: is_concrete_definition should handle nested comments
        let block = "(* outer (* = *) outer *)\ntype abstract_t";
        assert!(!is_concrete_definition(block),
            "Nested comment containing = should not make type concrete");
    }

    #[test]
    fn test_strip_nested_normalize_with_nested_comment() {
        // Regression: normalize_type_definition should handle nested comments
        let block = "(* outer (* inner *) outer *)\ntype t = int";
        let normalized = normalize_type_definition(block);
        assert!(!normalized.contains("outer"));
        assert!(!normalized.contains("inner"));
        assert!(normalized.contains("type t = int"));
    }

    #[test]
    fn test_strip_nested_normalize_with_string_in_comment() {
        // String inside comment should not interfere with normalization
        let block = "(* \"*) not closed\" *)\ntype t = int";
        let normalized = normalize_type_definition(block);
        assert!(normalized.contains("type t = int"));
        assert!(!normalized.contains("not closed"));
    }

    // =========================================================================
    // count_comment_delimiters: string-awareness tests
    // =========================================================================

    #[test]
    fn test_count_delimiters_string_with_open() {
        // "(*" inside a string should NOT be counted
        assert_eq!(count_comment_delimiters(r#"let x = "(*""#), (0, 0));
    }

    #[test]
    fn test_count_delimiters_string_with_close() {
        // "*)" inside a string should NOT be counted
        assert_eq!(count_comment_delimiters(r#"let x = "*)""#), (0, 0));
    }

    #[test]
    fn test_count_delimiters_string_then_real_comment() {
        assert_eq!(
            count_comment_delimiters(r#"let x = "(*" (* real *)"#),
            (1, 1)
        );
    }

    #[test]
    fn test_count_delimiters_escaped_quote_in_string() {
        // "hello\"(*" - the (* is still inside the string
        assert_eq!(
            count_comment_delimiters(r#"let x = "hello\"(*""#),
            (0, 0)
        );
    }

    #[test]
    fn test_count_delimiters_escaped_backslash_before_quote() {
        // "test\\" -> string ends after \\, then (* is OUTSIDE
        assert_eq!(
            count_comment_delimiters(r#""test\\" (* c *)"#),
            (1, 1)
        );
    }

    // =========================================================================
    // scan_line_state: cross-line state tracking tests
    // =========================================================================

    #[test]
    fn test_scan_line_state_basic_comment() {
        let mut depth: i32 = 0;
        let mut in_str = false;
        scan_line_state("(* comment *)", &mut depth, &mut in_str);
        assert_eq!(depth, 0);
        assert!(!in_str);
    }

    #[test]
    fn test_scan_line_state_open_comment_carries() {
        let mut depth: i32 = 0;
        let mut in_str = false;
        scan_line_state("(* start of comment", &mut depth, &mut in_str);
        assert_eq!(depth, 1, "Open comment should carry to next line");
        assert!(!in_str);
    }

    #[test]
    fn test_scan_line_state_close_comment_from_previous() {
        let mut depth: i32 = 1;
        let mut in_str = false;
        scan_line_state("end of comment *)", &mut depth, &mut in_str);
        assert_eq!(depth, 0, "Close should bring depth back to 0");
    }

    #[test]
    fn test_scan_line_state_string_with_comment_pattern() {
        let mut depth: i32 = 0;
        let mut in_str = false;
        scan_line_state(r#"let x = "(*" rest"#, &mut depth, &mut in_str);
        assert_eq!(depth, 0, "Comment marker inside string should be ignored");
    }

    #[test]
    fn test_scan_line_state_escaped_backslash_in_string() {
        let mut depth: i32 = 0;
        let mut in_str = false;
        // "test\\" -> string content is test\, then (* is outside
        scan_line_state(r#""test\\" (*"#, &mut depth, &mut in_str);
        assert_eq!(depth, 1, "After escaped backslash, (* should open comment");
    }

    #[test]
    fn test_scan_line_state_string_inside_comment() {
        let mut depth: i32 = 1; // Already in a comment
        let mut in_str = false;
        // "*)" inside a string in a comment should NOT close the comment
        scan_line_state(r#""*)" still in comment"#, &mut depth, &mut in_str);
        assert_eq!(depth, 1, "Close inside comment-string should be ignored");
    }

    // =========================================================================
    // find_type_block_end: comment-aware boundary detection tests
    // =========================================================================

    #[test]
    fn test_type_block_end_comment_with_string_containing_comment_pattern() {
        // The (* where string might be "(*" *) comment should not confuse
        // the boundary detection
        let lines: Vec<&str> = vec![
            r#"type foo = | Foo of string   (* where string might be "(*" *)"#,
            "type bar = int",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 0, "type foo should be single-line, bar is a new type");
    }

    #[test]
    fn test_type_block_end_multiline_comment_with_terminator() {
        // A `val` keyword inside a multi-line comment must NOT terminate the type
        let lines: Vec<&str> = vec![
            "type foo =",
            "  | Bar",
            "(* multi-line comment",
            "val this_is_not_a_terminator",
            "*)",
            "  | Baz",
            "val real_val : int",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 5, "Block should include | Baz, terminating before real val");
    }

    #[test]
    fn test_type_block_end_multiline_comment_with_type_keyword() {
        // A `type` keyword inside a multi-line comment must NOT terminate
        let lines: Vec<&str> = vec![
            "type foo =",
            "  | Bar",
            "(* documentation",
            "type this_is_in_comment",
            "*)",
            "  | Baz",
            "type real_type = int",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 5, "Block should include | Baz, not stop at type-in-comment");
    }

    #[test]
    fn test_type_block_end_record_type_closing_brace() {
        // Record type with } at column 0 should terminate
        let lines: Vec<&str> = vec![
            "noeq type baz = {",
            "  field1: int;",
            "  field2: string",
            "}",
            "let x = 1",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 3, "Record should end at closing brace");
    }

    #[test]
    fn test_type_block_end_record_then_and() {
        // Record type followed by `and` for mutual recursion
        let lines: Vec<&str> = vec![
            "noeq type foo = {",
            "  x: int;",
            "}",
            "",
            "and bar = | B1 | B2",
            "val next : int",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 4, "Block should include `and bar` after record close");
    }

    #[test]
    fn test_type_block_end_noeq_type_terminates() {
        // A new `noeq type` at column 0 terminates the previous type
        let lines: Vec<&str> = vec![
            "type foo = | A | B",
            "",
            "noeq type bar = {",
            "  x: int",
            "}",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 0, "noeq type at column 0 should terminate");
    }

    #[test]
    fn test_type_block_end_type_alias_single_line() {
        // Single-line type alias followed by another declaration
        let lines: Vec<&str> = vec![
            "type my_nat = nat",
            "val f : my_nat -> int",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 0, "Type alias is single line");
    }

    #[test]
    fn test_type_block_end_indented_variant_constructors() {
        // Indented variant constructors continue the type body
        let lines: Vec<&str> = vec![
            "type color =",
            "  | Red",
            "  | Green",
            "  | Blue",
            "val paint : color -> unit",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 3, "Indented variants are part of the type body");
    }

    #[test]
    fn test_type_block_end_and_mutual_recursion() {
        // `and` at column 0 continues mutual recursion
        let lines: Vec<&str> = vec![
            "type expr =",
            "  | Var of string",
            "  | App of expr * expr",
            "",
            "and pattern =",
            "  | PVar of string",
            "  | PWild",
            "val eval : expr -> int",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 6, "Block should include `and pattern` and its constructors");
    }

    #[test]
    fn test_type_block_end_string_with_close_comment_in_type_line() {
        // String containing *) on the type line itself
        let lines: Vec<&str> = vec![
            r#"type foo = | Foo of string   (* "some *) string" *)"#,
            "type bar = int",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 0, "String inside comment should not affect boundary");
    }

    #[test]
    fn test_type_block_end_comment_spanning_multiple_lines_with_let() {
        // `let` inside a multi-line comment should NOT terminate
        let lines: Vec<&str> = vec![
            "type t =",
            "  | A",
            "  (* This is a long",
            "     let x = 1",
            "     comment *)",
            "  | B",
            "let real = 1",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 5, "let inside comment should not terminate type block");
    }

    #[test]
    fn test_type_block_end_eof() {
        // Type at end of file with no terminator
        let lines: Vec<&str> = vec![
            "type t =",
            "  | A",
            "  | B",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 2, "Should reach end of file");
    }

    #[test]
    fn test_type_block_end_eof_with_trailing_blanks() {
        let lines: Vec<&str> = vec![
            "type t = int",
            "",
            "",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 0, "Trailing blanks should be stripped");
    }

    // Full integration test: comment containing string with "(*" pattern.
    // In F*, comments nest, so `(* ... (* ... *) ... *)` is one comment.
    // The string `"(*"` inside a comment prevents the `(*` from opening a
    // nested level, which is the key pattern this fix handles.
    //
    // A blank line separates foo from bar to prevent find_attribute_prefix_lines
    // (backward doc-comment scanner) from greedily merging them via the
    // self-contained inline comment on the foo line.
    #[test]
    fn test_type_block_string_comment_pattern_integration() {
        let content = r#"(* Type with string containing "(*" inside *)
type foo = | Foo of string   (* where string might be "(*" *)

type bar = int

(* Record type *)
type baz = {
  field1: int;
  field2: string
}
"#;
        let types = find_type_definitions(content);

        assert!(types.contains_key("foo"), "Should find type foo");
        assert!(types.contains_key("bar"), "Should find type bar");
        assert!(types.contains_key("baz"), "Should find type baz");

        // foo and bar must have different end_lines (separate type blocks).
        // find_type_block_end correctly detects `type bar` as a new type start,
        // ending foo's block before bar's line.
        let foo = &types["foo"];
        let bar = &types["bar"];
        assert_ne!(
            foo.end_line, bar.end_line,
            "foo and bar should be separate type blocks with different end_lines"
        );

        // Verify foo's block contains its content
        assert!(
            foo.block.contains("Foo"),
            "foo block should contain its constructor"
        );

        // Verify bar's block contains its content
        assert!(
            bar.block.contains("int"),
            "bar block should contain 'int'"
        );

        // baz should include the closing brace
        let baz = &types["baz"];
        assert!(
            baz.block.contains("}"),
            "baz block should include closing brace"
        );
    }

    // Integration test: nested F* comment `(* outer (* inner *) *)` spanning
    // the line before a type should NOT swallow the type definition.
    #[test]
    fn test_type_block_nested_comment_before_type() {
        let content = "(* Comment with nested (* inner *) comment *)\ntype foo = int\ntype bar = nat\n";
        let types = find_type_definitions(content);

        assert!(types.contains_key("foo"), "Should find type foo");
        assert!(types.contains_key("bar"), "Should find type bar");

        let foo = &types["foo"];
        let bar = &types["bar"];
        assert_ne!(foo.start_line, bar.start_line,
            "foo and bar must be separate type blocks");
    }

    // Integration test: multi-line comment with `val` keyword inside should
    // NOT split the type block.
    #[test]
    fn test_type_block_multiline_comment_integration() {
        let content = "type foo =\n  | Bar\n(* documentation\nval fake_terminator\n*)\n  | Baz\nval real : int\n";
        let types = find_type_definitions(content);

        let foo = &types["foo"];
        assert!(
            foo.block.contains("Baz"),
            "foo block should include | Baz (val inside comment must not terminate)"
        );
        assert!(
            !foo.block.contains("real"),
            "foo block should NOT include val real"
        );
    }

    // =========================================================================
    // find_fst_fsti_pairs: path-based pairing tests
    // =========================================================================

    #[test]
    fn test_pairs_basic_matching() {
        // Simple case: one .fst and one .fsti with same directory and stem
        let files = vec![
            PathBuf::from("/project/src/Types.fst"),
            PathBuf::from("/project/src/Types.fsti"),
        ];
        let pairs = find_fst_fsti_pairs(&files);
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].0, PathBuf::from("/project/src/Types.fst"));
        assert_eq!(pairs[0].1, PathBuf::from("/project/src/Types.fsti"));
    }

    #[test]
    fn test_pairs_same_name_different_directories() {
        // BUG FIX: Two files with the same stem in different directories
        // must produce TWO separate pairs, not one.
        let files = vec![
            PathBuf::from("/project/src/A/Types.fst"),
            PathBuf::from("/project/src/A/Types.fsti"),
            PathBuf::from("/project/src/B/Types.fst"),
            PathBuf::from("/project/src/B/Types.fsti"),
        ];
        let pairs = find_fst_fsti_pairs(&files);
        assert_eq!(
            pairs.len(),
            2,
            "Same-named files in different directories must produce separate pairs"
        );

        // Verify that A/Types.fst is paired with A/Types.fsti (not B/Types.fsti)
        let a_pair = pairs.iter().find(|(fst, _)| {
            fst == &PathBuf::from("/project/src/A/Types.fst")
        });
        assert!(a_pair.is_some(), "A/Types.fst must have a pair");
        assert_eq!(
            a_pair.unwrap().1,
            PathBuf::from("/project/src/A/Types.fsti"),
            "A/Types.fst must be paired with A/Types.fsti, not B/Types.fsti"
        );

        let b_pair = pairs.iter().find(|(fst, _)| {
            fst == &PathBuf::from("/project/src/B/Types.fst")
        });
        assert!(b_pair.is_some(), "B/Types.fst must have a pair");
        assert_eq!(
            b_pair.unwrap().1,
            PathBuf::from("/project/src/B/Types.fsti"),
            "B/Types.fst must be paired with B/Types.fsti, not A/Types.fsti"
        );
    }

    #[test]
    fn test_pairs_three_directories_same_name() {
        // Stress test: three directories all containing the same file name
        let files = vec![
            PathBuf::from("/p/A/M.fst"),
            PathBuf::from("/p/A/M.fsti"),
            PathBuf::from("/p/B/M.fst"),
            PathBuf::from("/p/B/M.fsti"),
            PathBuf::from("/p/C/M.fst"),
            PathBuf::from("/p/C/M.fsti"),
        ];
        let pairs = find_fst_fsti_pairs(&files);
        assert_eq!(
            pairs.len(),
            3,
            "Three directories with same-named files must produce three pairs"
        );
    }

    #[test]
    fn test_pairs_no_fsti_counterpart() {
        // .fst file with no .fsti counterpart in the input list and no file on disk
        let files = vec![PathBuf::from("/nonexistent/Orphan.fst")];
        // Should not panic, returns empty (the warn is emitted to tracing)
        let pairs = find_fst_fsti_pairs(&files);
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_pairs_no_fst_counterpart() {
        // .fsti file with no .fst counterpart
        let files = vec![PathBuf::from("/nonexistent/Orphan.fsti")];
        let pairs = find_fst_fsti_pairs(&files);
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_pairs_mixed_paired_and_unpaired() {
        // Mix of paired and unpaired files
        let files = vec![
            PathBuf::from("/p/A.fst"),
            PathBuf::from("/p/A.fsti"),
            PathBuf::from("/nonexistent/B.fst"),   // no .fsti
            PathBuf::from("/nonexistent/C.fsti"),   // no .fst
        ];
        let pairs = find_fst_fsti_pairs(&files);
        // Only A should pair
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].0, PathBuf::from("/p/A.fst"));
        assert_eq!(pairs[0].1, PathBuf::from("/p/A.fsti"));
    }

    #[test]
    fn test_pairs_ignores_non_fstar_files() {
        let files = vec![
            PathBuf::from("/p/Test.fst"),
            PathBuf::from("/p/Test.fsti"),
            PathBuf::from("/p/Test.rs"),
            PathBuf::from("/p/Test.ml"),
        ];
        let pairs = find_fst_fsti_pairs(&files);
        assert_eq!(pairs.len(), 1);
    }

    #[test]
    fn test_pairs_empty_input() {
        let files: Vec<PathBuf> = vec![];
        let pairs = find_fst_fsti_pairs(&files);
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_pairs_symlink_resolution() {
        // Test with real files and symlinks on disk using a temp directory.
        // This verifies that canonicalize_for_key resolves symlinks so that
        // a symlinked .fst file is correctly paired with the real .fsti file.
        use std::fs;

        let temp = tempfile::TempDir::new().expect("failed to create temp dir");
        let real_dir = temp.path().join("real");
        let link_dir = temp.path().join("link");
        fs::create_dir(&real_dir).unwrap();

        // Create real files
        fs::write(real_dir.join("Module.fst"), "module Module\nlet x = 1\n").unwrap();
        fs::write(real_dir.join("Module.fsti"), "module Module\nval x : int\n").unwrap();

        // Create a symlink directory pointing to real_dir
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink(&real_dir, &link_dir).unwrap();

            let files = vec![
                link_dir.join("Module.fst"),  // symlink path
                real_dir.join("Module.fsti"), // real path
            ];
            let pairs = find_fst_fsti_pairs(&files);
            assert_eq!(
                pairs.len(),
                1,
                "Symlinked .fst and real .fsti should pair via canonical path resolution"
            );
        }
    }

    #[test]
    fn test_pairs_fsti_on_disk_fallback() {
        // When .fsti is not in the input list but exists on disk, it should
        // still be found and paired.
        use std::fs;

        let temp = tempfile::TempDir::new().expect("failed to create temp dir");
        fs::write(temp.path().join("M.fst"), "module M\n").unwrap();
        fs::write(temp.path().join("M.fsti"), "module M\n").unwrap();

        // Only pass the .fst file
        let files = vec![temp.path().join("M.fst")];
        let pairs = find_fst_fsti_pairs(&files);
        assert_eq!(pairs.len(), 1, ".fsti on disk should be found as fallback");
        assert!(pairs[0].1.ends_with("M.fsti"));
    }

    #[test]
    fn test_pairs_fst_on_disk_fallback() {
        // When .fst is not in the input list but exists on disk, it should
        // still be found and paired.
        use std::fs;

        let temp = tempfile::TempDir::new().expect("failed to create temp dir");
        fs::write(temp.path().join("N.fst"), "module N\n").unwrap();
        fs::write(temp.path().join("N.fsti"), "module N\n").unwrap();

        // Only pass the .fsti file
        let files = vec![temp.path().join("N.fsti")];
        let pairs = find_fst_fsti_pairs(&files);
        assert_eq!(pairs.len(), 1, ".fst on disk should be found as fallback");
        assert!(pairs[0].0.ends_with("N.fst"));
    }

    #[test]
    fn test_pairs_same_name_different_dirs_on_disk() {
        // Real filesystem test: same-named files in different directories
        use std::fs;

        let temp = tempfile::TempDir::new().expect("failed to create temp dir");
        let dir_a = temp.path().join("A");
        let dir_b = temp.path().join("B");
        fs::create_dir(&dir_a).unwrap();
        fs::create_dir(&dir_b).unwrap();

        fs::write(dir_a.join("Types.fst"), "module Types\ntype t = int\n").unwrap();
        fs::write(dir_a.join("Types.fsti"), "module Types\ntype t = int\n").unwrap();
        fs::write(dir_b.join("Types.fst"), "module Types\ntype t = nat\n").unwrap();
        fs::write(dir_b.join("Types.fsti"), "module Types\ntype t = nat\n").unwrap();

        let files = vec![
            dir_a.join("Types.fst"),
            dir_a.join("Types.fsti"),
            dir_b.join("Types.fst"),
            dir_b.join("Types.fsti"),
        ];
        let pairs = find_fst_fsti_pairs(&files);
        assert_eq!(
            pairs.len(),
            2,
            "Real filesystem: same-named files in different dirs must produce 2 pairs"
        );

        // Verify correct pairing (not cross-directory)
        for (fst, fsti) in &pairs {
            assert_eq!(
                fst.parent(),
                fsti.parent(),
                "Each .fst must pair with .fsti from the SAME directory, got {:?} paired with {:?}",
                fst,
                fsti
            );
        }
    }

    #[test]
    fn test_canonicalize_for_key_nonexistent_path() {
        // When the file does not exist, canonicalize_for_key should fall
        // back to the original path without panicking.
        let fake = PathBuf::from("/absolutely/does/not/exist/File.fst");
        let result = canonicalize_for_key(&fake);
        assert_eq!(result, fake);
    }

    #[test]
    fn test_canonicalize_for_key_real_path() {
        use std::fs;
        let temp = tempfile::TempDir::new().expect("failed to create temp dir");
        let file = temp.path().join("Real.fst");
        fs::write(&file, "module Real\n").unwrap();

        let result = canonicalize_for_key(&file);
        // Should return the canonical (absolute, resolved) path
        assert!(result.is_absolute());
        assert!(result.ends_with("Real.fst"));
    }

    // =========================================================================
    // Attribute prefix and removal range tests
    // =========================================================================

    #[test]
    fn test_attribute_prefix_included_in_range() {
        // Attribute on own line before type definition
        let content = "module T\n\n[@@ CInline]\ntype my_t = int\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        assert!(types.contains_key("my_t"), "my_t should be found");
        let td = &types["my_t"];
        // The attribute line (line index 2) should be included in start_line
        assert_eq!(td.start_line, 2, "start_line should include the attribute prefix");
        assert_eq!(td.end_line, 3, "end_line should be the type line");
    }

    #[test]
    fn test_multiple_attribute_lines_in_range() {
        // Multiple attribute lines before type
        let content = "module T\n\n[@@\"opaque_to_smt\"]\n[@@ CInline]\ntype my_t = int\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        let td = &types["my_t"];
        assert_eq!(td.start_line, 2, "start_line should include first attribute line");
        assert_eq!(td.end_line, 4);
    }

    #[test]
    fn test_comment_and_attribute_in_range() {
        // Comment + attribute before type
        let content = "module T\n\n(** Documentation *)\n[@@ erasable]\ntype my_t = int\n";
        let types = find_type_definitions(content);
        let td = &types["my_t"];
        assert_eq!(td.start_line, 2, "start_line should include comment before attribute");
    }

    #[test]
    fn test_standalone_modifier_line_in_range() {
        // Standalone modifier line before type (HACL* pattern)
        let content = "module T\n\ninline_for_extraction noextract\ntype limb_t = UInt64.t\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        // The modifier line may or may not be recognized as part of the type pattern.
        // If the type line is `type limb_t = UInt64.t`, find_type_definitions starts
        // at that line. find_attribute_prefix_lines scans backward and should include
        // the `inline_for_extraction noextract` line.
        let td = &types["limb_t"];
        assert_eq!(td.start_line, 2,
            "start_line should include standalone modifier line");
    }

    #[test]
    fn test_standalone_modifier_is_standalone() {
        assert!(is_standalone_modifier_line("inline_for_extraction noextract"));
        assert!(is_standalone_modifier_line("inline_for_extraction"));
        assert!(is_standalone_modifier_line("noextract"));
        assert!(is_standalone_modifier_line("noeq"));
        assert!(is_standalone_modifier_line("unfold"));
        assert!(is_standalone_modifier_line("private"));
        assert!(is_standalone_modifier_line("  inline_for_extraction noextract  "));
    }

    #[test]
    fn test_non_modifier_not_standalone() {
        assert!(!is_standalone_modifier_line("let x = 1"));
        assert!(!is_standalone_modifier_line("val foo : int"));
        assert!(!is_standalone_modifier_line("type t = int"));
        assert!(!is_standalone_modifier_line(""));
        assert!(!is_standalone_modifier_line("inline_for_extraction type foo = int"));
    }

    #[test]
    fn test_duplicate_with_attribute_prefix_fix_range() {
        // Both .fst and .fsti have attribute + type. The fix should remove
        // starting from the attribute line, not just the type line.
        let fsti_content = "module T\n\n[@@ CInline]\ntype my_t = int\n\nval foo : int\n";
        let fst_content = "module T\n\n[@@ CInline]\ntype my_t = int\n\nlet foo = 42\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty(), "Duplicate type with attribute should be flagged");
        let diag = &diagnostics[0];
        // Range should start at the attribute line (line 3, 1-indexed = line index 2 + 1)
        assert_eq!(diag.range.start_line, 3,
            "Diagnostic range should start at attribute line");

        // The fix edit should also start at the attribute line
        if let Some(ref fix) = diag.fix {
            assert_eq!(fix.edits[0].range.start_line, 3,
                "Fix removal range should include the attribute prefix");
        }
    }

    #[test]
    fn test_duplicate_with_multi_attr_fix_range() {
        // Multi-attribute syntax [@@attr1; attr2] before type
        let fsti_content = "module T\n\n[@@va_qattr; erasable]\ntype ghost_t = int\n";
        let fst_content = "module T\n\n[@@va_qattr; erasable]\ntype ghost_t = int\n\nlet x = 1\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty(), "Duplicate with multi-attr should be flagged");
        let diag = &diagnostics[0];
        assert_eq!(diag.range.start_line, 3,
            "Range should include multi-attribute line");
    }

    #[test]
    fn test_duplicate_with_standalone_modifier_fix_range() {
        // HACL* pattern: standalone modifier on own line
        let fsti_content = "module T\n\ninline_for_extraction noextract\ntype my_t = nat\n";
        let fst_content = "module T\n\ninline_for_extraction noextract\ntype my_t = nat\n\nlet x = 1\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty(), "Duplicate with standalone modifier should be flagged");
        let diag = &diagnostics[0];
        assert_eq!(diag.range.start_line, 3,
            "Range should include standalone modifier line");
    }

    #[test]
    fn test_duplicate_with_comment_attr_modifier_stack() {
        // Full stack: comment + attribute + modifier + type
        let common = "(** Important type *)\n[@@ opaque_to_smt]\ninline_for_extraction\ntype my_t = nat";
        let fsti_content = format!("module T\n\n{}\n\nval foo : int\n", common);
        let fst_content = format!("module T\n\n{}\n\nlet foo = 42\n", common);

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            &fst_content,
            &PathBuf::from("T.fsti"),
            &fsti_content,
        );

        assert!(!diagnostics.is_empty(), "Full stack duplicate should be flagged");
        let diag = &diagnostics[0];
        // Line indices: module=0, empty=1, comment=2, attr=3, modifier=4, type=5
        // 1-indexed: comment=3
        assert_eq!(diag.range.start_line, 3,
            "Range should include comment at top of the stack");
    }

    #[test]
    fn test_normalize_strips_attributes_for_comparison() {
        // Definitions that differ only in attributes should match
        let block1 = "[@@ CInline]\ntype my_t = int";
        let block2 = "type my_t = int";
        assert!(definitions_match(block1, block2),
            "Definitions differing only in attributes should match");
    }

    #[test]
    fn test_normalize_strips_different_attributes() {
        // Both have attributes but different ones
        let block1 = "[@@ CInline]\ntype my_t = int";
        let block2 = "[@@\"opaque_to_smt\"]\ntype my_t = int";
        assert!(definitions_match(block1, block2),
            "Definitions with different attributes should still match semantically");
    }

    // =========================================================================
    // ASSUME TYPE TESTS
    // =========================================================================

    #[test]
    fn test_assume_type_detected() {
        let content = "module T\n\nassume type abstract_t\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        assert!(types.contains_key("abstract_t"), "assume type should be detected");
        assert!(types["abstract_t"].is_assume, "assume type should be marked as assume");
    }

    #[test]
    fn test_assume_type_is_not_concrete() {
        assert!(!is_concrete_definition("assume type abstract_t"));
        assert!(!is_concrete_definition("assume type abstract_t : Type0"));
    }

    #[test]
    fn test_assume_type_in_fsti_does_not_flag() {
        // assume type in .fsti is abstract - concrete .fst should NOT be flagged
        let fsti_content = "module T\n\nassume type t\n\nval foo : t -> int\n";
        let fst_content = "module T\n\ntype t = int\n\nlet foo x = x\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(diagnostics.is_empty(),
            "assume type in .fsti should not flag concrete .fst definition");
    }

    #[test]
    fn test_assume_type_in_fst_not_flagged() {
        // assume type in .fst should not be flagged even if same name exists in .fsti
        let fsti_content = "module T\n\ntype t = int\n";
        let fst_content = "module T\n\nassume type t\n\nlet x = 1\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(diagnostics.is_empty(),
            "assume type in .fst should be skipped entirely");
    }

    #[test]
    fn test_assume_type_terminates_previous_block() {
        // `assume type` at column 0 should terminate the previous type block
        let lines: Vec<&str> = vec![
            "type foo =",
            "  | A",
            "  | B",
            "assume type bar",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 2, "assume type should terminate the previous type block");
    }

    // =========================================================================
    // MUTUAL RECURSION SINGLE-BLOCK TESTS
    // =========================================================================

    #[test]
    fn test_mutual_recursion_names_tracked() {
        let content = "module T\n\nnoeq type brrr_type =\n  | TPrim : prim_kind -> brrr_type\n\nand func_type = {\n  params : list int;\n  ret : brrr_type\n}\n\nand param_type = {\n  ty : brrr_type\n}\n\nlet x = 1\n";
        let types = find_type_definitions(content);

        assert!(types.contains_key("brrr_type"));
        assert!(types.contains_key("func_type"));
        assert!(types.contains_key("param_type"));

        // All should share the same block range
        let bt = &types["brrr_type"];
        let ft = &types["func_type"];
        let pt = &types["param_type"];
        assert_eq!(bt.start_line, ft.start_line);
        assert_eq!(bt.start_line, pt.start_line);
        assert_eq!(bt.end_line, ft.end_line);
        assert_eq!(bt.end_line, pt.end_line);

        // mutual_names should contain all three
        assert_eq!(bt.mutual_names.len(), 3);
        assert!(bt.mutual_names.contains(&"brrr_type".to_string()));
        assert!(bt.mutual_names.contains(&"func_type".to_string()));
        assert!(bt.mutual_names.contains(&"param_type".to_string()));
    }

    #[test]
    fn test_mutual_recursion_single_diagnostic() {
        // A mutual recursion block that appears in both .fst and .fsti
        // should produce only ONE diagnostic (not one per type in the block)
        let common = "noeq type expr =\n  | Var of string\n  | App of expr * expr\n\nand pattern =\n  | PVar of string\n  | PWild";
        let fsti_content = format!("module T\n\n{}\n\nval eval : expr -> int\n", common);
        let fst_content = format!("module T\n\n{}\n\nlet eval e = 0\n", common);

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            &fst_content,
            &PathBuf::from("T.fsti"),
            &fsti_content,
        );

        // Should produce exactly 1 diagnostic (deduped by range)
        assert_eq!(diagnostics.len(), 1,
            "Mutual recursion block should produce only one diagnostic");
        assert!(diagnostics[0].message.contains("expr"),
            "Diagnostic should mention type names");
    }

    #[test]
    fn test_mutual_recursion_diagnostic_message_contains_all_names() {
        let common = "type a = | X of b\nand b = | Y of a";
        let fsti_content = format!("module T\n\n{}\n", common);
        let fst_content = format!("module T\n\n{}\n\nlet x = 1\n", common);

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            &fst_content,
            &PathBuf::from("T.fsti"),
            &fsti_content,
        );

        assert!(!diagnostics.is_empty());
        let msg = &diagnostics[0].message;
        assert!(msg.contains("a") && msg.contains("b"),
            "Mutual recursion diagnostic should mention all type names, got: {}", msg);
    }

    #[test]
    fn test_non_mutual_type_has_empty_mutual_names() {
        let content = "module T\n\ntype foo = int\n";
        let types = find_type_definitions(content);
        assert!(types["foo"].mutual_names.is_empty(),
            "Non-mutual type should have empty mutual_names");
    }

    // =========================================================================
    // DOC COMMENTS IN REMOVAL RANGE TESTS
    // =========================================================================

    #[test]
    fn test_multiline_doc_comment_included_in_range() {
        let content = "module T\n\n(** Multi-line\n    doc comment\n    for this type *)\ntype foo = int\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        let foo = &types["foo"];
        assert_eq!(foo.start_line, 2,
            "Multi-line doc comment should be included in range start");
        assert!(foo.block.contains("Multi-line"));
        assert!(foo.block.contains("doc comment"));
    }

    #[test]
    fn test_doc_comment_with_attribute_included() {
        let content = "module T\n\n(** Documentation *)\n[@@ CInline]\ntype foo = int\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        let foo = &types["foo"];
        assert_eq!(foo.start_line, 2,
            "Doc comment before attribute should be included");
        assert!(foo.block.contains("Documentation"));
        assert!(foo.block.contains("CInline"));
    }

    // =========================================================================
    // MULTI-LINE ATTRIBUTE TESTS
    // =========================================================================

    #[test]
    fn test_multiline_attribute_in_prefix() {
        // Multi-line attribute where ] is on a separate line
        let lines: Vec<&str> = vec![
            "module Test",
            "",
            "[@@ some_long_attribute",
            "    with_continuation]",
            "type foo = int",
        ];
        assert_eq!(find_attribute_prefix_lines(&lines, 4), 2,
            "Multi-line attribute should be included in prefix scan");
    }

    #[test]
    fn test_multiline_attribute_block_end_skip() {
        // Multi-line attribute between types should not terminate the first type
        let lines: Vec<&str> = vec![
            "type foo =",
            "  | A",
            "  | B",
            "[@@ long_attr",
            "    continuation]",
            "type bar = int",
        ];
        let end = find_type_block_end(&lines, 0);
        // foo should end before the attribute
        assert_eq!(end, 2, "Multi-line attribute should not be part of foo's block");
    }

    #[test]
    fn test_line_has_closing_bracket_basic() {
        assert!(line_has_closing_bracket("[@@ attr]"));
        assert!(line_has_closing_bracket("[@@attr; attr2]"));
        assert!(!line_has_closing_bracket("[@@ attr"));
        assert!(!line_has_closing_bracket("    continuation"));
        assert!(line_has_closing_bracket("    continuation]"));
    }

    #[test]
    fn test_line_has_closing_bracket_nested() {
        // Nested brackets: [@@attr [inner_list]]
        assert!(line_has_closing_bracket("[@@attr [inner_list]]"));
        // Only inner closes, outer still open
        assert!(!line_has_closing_bracket("[@@attr [inner_list]"));
    }

    #[test]
    fn test_find_type_definitions_multiline_attr() {
        let content = "module T\n\n[@@ some_attr\n   arg1 arg2]\ntype foo = int\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        let foo = &types["foo"];
        assert_eq!(foo.start_line, 2,
            "Multi-line attribute should be included in type definition range");
        assert!(foo.block.contains("some_attr"));
        assert!(foo.block.contains("arg1"));
    }

    // =========================================================================
    // REFINEMENT TYPES IN CONSTRUCTORS TESTS
    // =========================================================================

    #[test]
    fn test_refinement_brace_at_col0_not_record_close() {
        // If a refinement brace somehow ends up at column 0 with code after it,
        // it should NOT terminate the type block
        let lines: Vec<&str> = vec![
            "type foo =",
            "  | Bar : x:int",
            "} -> foo",  // hypothetical: } with code after it
            "val next : int",
        ];
        let end = find_type_block_end(&lines, 0);
        // The } has "-> foo" after it, so it's not a record close
        assert_eq!(end, 2, "}} with code after should not be a record terminator");
    }

    #[test]
    fn test_refinement_type_alias_with_braces() {
        // type valid_alignment = n:pos{is_power_of_2 n && n <= 536870912}
        let content = "module T\n\ntype valid_alignment = n:pos{is_power_of_2 n && n <= 536870912}\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        assert!(types.contains_key("valid_alignment"));
        assert!(is_concrete_definition(&types["valid_alignment"].block));
    }

    #[test]
    fn test_refinement_in_constructor_does_not_confuse_concrete() {
        // The = inside {x = 0} should not make this concrete
        let block = "type t (x: int{x = 0}) : Type";
        assert!(!is_concrete_definition(block));
    }

    #[test]
    fn test_duplicate_refinement_type_alias() {
        // Real pattern: type valid_alignment = n:pos{...} in both files
        let fsti_content = "module T\n\ntype valid_alignment = n:pos{is_power_of_2 n && n <= 536870912}\n";
        let fst_content = "module T\n\ntype valid_alignment = n:pos{is_power_of_2 n && n <= 536870912}\n\nlet x = 1\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty(),
            "Identical refinement type alias should be flagged as duplicate");
        assert!(diagnostics[0].fix.is_some(),
            "Should offer autofix for identical refinement type");
    }

    // =========================================================================
    // TYPE ABBREVIATION TESTS
    // =========================================================================

    #[test]
    fn test_type_abbreviation_simple() {
        let content = "module T\n\ntype byte = UInt8.t\n";
        let types = find_type_definitions(content);
        assert!(types.contains_key("byte"));
        assert!(is_concrete_definition(&types["byte"].block));
    }

    #[test]
    fn test_type_abbreviation_with_module_prefix() {
        let content = "module T\n\ntype my_nat = FStar.UInt32.t\n";
        let types = find_type_definitions(content);
        assert!(types.contains_key("my_nat"));
    }

    // =========================================================================
    // CROSS-FILE QUALIFIED NAME MATCHING TESTS
    // =========================================================================

    #[test]
    fn test_extract_module_name() {
        assert_eq!(extract_module_name("module BrrrTypes\n\ntype t = int\n"),
            Some("BrrrTypes".to_string()));
        assert_eq!(extract_module_name("module My.Nested.Module\n"),
            Some("My.Nested.Module".to_string()));
        assert_eq!(extract_module_name("let x = 1\n"), None);
    }

    #[test]
    fn test_strip_module_prefix_basic() {
        assert_eq!(strip_module_prefix("BrrrTypes.foo", "BrrrTypes"), "foo");
        assert_eq!(strip_module_prefix("foo", "BrrrTypes"), "foo");
        assert_eq!(strip_module_prefix("OtherModule.foo", "BrrrTypes"), "OtherModule.foo");
    }

    #[test]
    fn test_strip_module_prefix_nested() {
        assert_eq!(strip_module_prefix("My.Module.foo", "My.Module"), "foo");
    }

    // =========================================================================
    // PRIVATE TYPES FILTERING TESTS
    // =========================================================================

    #[test]
    fn test_private_noeq_type_not_flagged() {
        let fsti_content = "module T\n\nnoeq type public_t = { x: int }\n";
        let fst_content = "module T\n\nnoeq type public_t = { x: int }\n\nprivate noeq type internal_t = { y: nat }\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        // Should flag public_t but NOT internal_t
        assert_eq!(diagnostics.len(), 1);
        // internal_t is private and not in .fsti, so only public_t flagged
    }

    #[test]
    fn test_private_after_modifier_not_flagged() {
        let content = "module T\n\ninline_for_extraction private type secret = int\n";
        let types = find_type_definitions(content);
        // The private modifier should be detected regardless of position
        // relative to other modifiers
        assert!(types.contains_key("secret"));
        assert!(types["secret"].is_private,
            "private type after other modifiers should be detected as private");
    }

    // =========================================================================
    // NOEQ/UNOPTEQ QUALIFIER RANGE TESTS
    // =========================================================================

    #[test]
    fn test_noeq_qualifier_in_removal_range() {
        let fsti_content = "module T\n\nnoeq type state = {\n  x: int;\n  y: nat\n}\n";
        let fst_content = "module T\n\nnoeq type state = {\n  x: int;\n  y: nat\n}\n\nlet init = { x = 0; y = 0 }\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty());
        let diag = &diagnostics[0];
        // Verify the range includes the noeq keyword line
        assert_eq!(diag.range.start_line, 3, "Range should start at noeq type line");
    }

    #[test]
    fn test_unopteq_qualifier_in_removal_range() {
        let fsti_content = "module T\n\nunopteq type dtuple = | Mk : int -> dtuple\n";
        let fst_content = "module T\n\nunopteq type dtuple = | Mk : int -> dtuple\n\nlet x = Mk 0\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty(),
            "unopteq duplicate type should produce a diagnostic");
        let diag = &diagnostics[0];
        assert!(diag.message.contains("dtuple"),
            "Diagnostic should mention the type name 'dtuple', got: {}", diag.message);
        assert_eq!(diag.range.start_line, 3,
            "Range should start at the unopteq type line");
    }

    // =========================================================================
    // REAL-WORLD PATTERN TESTS FROM brrr-lang/src/core/
    // =========================================================================

    #[test]
    fn test_brrr_type_var_alias() {
        // Pattern from BrrrTypes: simple type alias
        let fsti_content = "module BrrrTypes\n\ntype type_var = string\n";
        let fst_content = "module BrrrTypes\n\ntype type_var = string\n\nlet x = 1\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("BrrrTypes.fst"),
            fst_content,
            &PathBuf::from("BrrrTypes.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty(),
            "Identical type alias 'type_var = string' should be flagged");
    }

    #[test]
    fn test_brrr_valid_alignment_refinement() {
        // Pattern from BrrrTypes: refinement type alias
        let def = "type valid_alignment = n:pos{is_power_of_2 n && n <= 536870912}";
        let fsti_content = format!("module BrrrTypes\n\n{}\n", def);
        let fst_content = format!("module BrrrTypes\n\n{}\n\nlet x = 1\n", def);

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("BrrrTypes.fst"),
            &fst_content,
            &PathBuf::from("BrrrTypes.fsti"),
            &fsti_content,
        );

        assert!(!diagnostics.is_empty(),
            "Identical refinement type alias should be flagged");
    }

    #[test]
    fn test_brrr_mutual_recursion_block() {
        // Pattern from BrrrTypes: brrr_type + func_type + param_type mutual recursion
        let common = "noeq type brrr_type =\n  | TPrim : prim_kind -> brrr_type\n  | TFunc : func_type -> brrr_type\n\nand func_type = {\n  params : list param_type;\n  ret : brrr_type\n}\n\nand param_type = {\n  ty : brrr_type\n}";
        let fsti_content = format!("module BrrrTypes\n\n{}\n\nval f : brrr_type -> int\n", common);
        let fst_content = format!("module BrrrTypes\n\n{}\n\nlet f t = 0\n", common);

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("BrrrTypes.fst"),
            &fst_content,
            &PathBuf::from("BrrrTypes.fsti"),
            &fsti_content,
        );

        assert_eq!(diagnostics.len(), 1,
            "Entire mutual recursion block should produce one diagnostic");
        assert!(diagnostics[0].fix.is_some(),
            "Identical mutual recursion block should have autofix");
    }

    #[test]
    fn test_brrr_prim_kind_enum() {
        // Pattern from BrrrTypes: multi-constructor ADT
        let common = "type prim_kind =\n  | PUnit\n  | PBool\n  | PChar\n  | PString\n  | PBytes\n  | PNever\n  | PAny";
        let fsti_content = format!("module BrrrTypes\n\n{}\n\nval is_unit : prim_kind -> bool\n", common);
        let fst_content = format!("module BrrrTypes\n\n{}\n\nlet is_unit k = match k with | PUnit -> true | _ -> false\n", common);

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("BrrrTypes.fst"),
            &fst_content,
            &PathBuf::from("BrrrTypes.fsti"),
            &fsti_content,
        );

        assert!(!diagnostics.is_empty(),
            "Identical prim_kind ADT should be flagged");
        assert!(diagnostics[0].fix.is_some());
    }

    #[test]
    fn test_brrr_doc_comment_before_mutual_recursion() {
        // Real pattern: doc comment block before a large mutual recursion
        let fsti_content = "module T\n\n(** Core type definitions\n    for the brrr language *)\nnoeq type expr =\n  | EVar : string -> expr\n\nand pat =\n  | PVar : string -> pat\n\nval eval : expr -> int\n";
        let fst_content = "module T\n\n(** Core type definitions\n    for the brrr language *)\nnoeq type expr =\n  | EVar : string -> expr\n\nand pat =\n  | PVar : string -> pat\n\nlet eval e = 0\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(!diagnostics.is_empty());
        let diag = &diagnostics[0];
        // The range should include the doc comment
        assert_eq!(diag.range.start_line, 3,
            "Range should include doc comment before mutual recursion block");
    }

    // =========================================================================
    // EDGE CASE TESTS
    // =========================================================================

    #[test]
    fn test_abstract_type_with_kind_not_flagged() {
        // type t : Type -> Type0 in .fsti is abstract (no =)
        let fsti_content = "module T\n\ntype t : Type -> Type0\n";
        let fst_content = "module T\n\ntype t (a: Type) = option a\n";

        let rule = DuplicateTypesRule::new();
        let diagnostics = rule.check_pair(
            &PathBuf::from("T.fst"),
            fst_content,
            &PathBuf::from("T.fsti"),
            fsti_content,
        );

        assert!(diagnostics.is_empty(),
            "Abstract type with kind in .fsti should not flag concrete .fst");
    }

    #[test]
    fn test_type_after_assume_type_is_separate() {
        let content = "module T\n\nassume type abstract_t\n\ntype concrete = int\n\nlet x = 1\n";
        let types = find_type_definitions(content);
        assert!(types.contains_key("abstract_t"));
        assert!(types.contains_key("concrete"));
        assert!(types["abstract_t"].is_assume);
        assert!(!types["concrete"].is_assume);
        // They should be separate type definitions
        assert_ne!(types["abstract_t"].start_line, types["concrete"].start_line);
    }

    #[test]
    fn test_multiple_assume_types() {
        let content = "module T\n\nassume type a\nassume type b\nassume type c\n\ntype d = int\n";
        let types = find_type_definitions(content);
        assert!(types["a"].is_assume);
        assert!(types["b"].is_assume);
        assert!(types["c"].is_assume);
        assert!(!types["d"].is_assume);
        assert!(is_concrete_definition(&types["d"].block));
    }

    #[test]
    fn test_record_close_brace_comment_after() {
        // } followed by comment should still be a record terminator
        let lines: Vec<&str> = vec![
            "noeq type foo = {",
            "  x: int;",
            "} (* end of record *)",
            "let y = 1",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 2, "}} with comment should still be a record close");
    }

    #[test]
    fn test_record_close_brace_line_comment_after() {
        let lines: Vec<&str> = vec![
            "noeq type foo = {",
            "  x: int;",
            "} // end of record",
            "let y = 1",
        ];
        let end = find_type_block_end(&lines, 0);
        assert_eq!(end, 2, "}} with // comment should still be a record close");
    }

    #[test]
    fn test_mutual_recursion_with_records_and_adt() {
        // Real pattern: mixed records and ADT in mutual recursion
        let content = "module T\n\nnoeq type expr =\n  | ELit : int -> expr\n  | ECall : func -> list expr -> expr\n\nand func = {\n  name : string;\n  body : expr\n}\n\nlet x = 1\n";
        let types = find_type_definitions(content);

        assert!(types.contains_key("expr"));
        assert!(types.contains_key("func"));
        assert_eq!(types["expr"].start_line, types["func"].start_line);
        assert_eq!(types["expr"].end_line, types["func"].end_line);
        // Block should contain the closing }
        assert!(types["func"].block.contains("}"));
    }
}
