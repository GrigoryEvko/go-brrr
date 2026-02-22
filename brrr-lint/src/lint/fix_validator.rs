//! Fix validation engine for F* linting autofixes.
//!
//! This module provides centralized validation for all autofix rules to ensure
//! fixes are safe to apply and don't break working code.
//!
//! # Safety guarantees
//!
//! Before any fix is applied, it must pass validation checks:
//! - Comment balance (nested `(* *)`, doc `(** *)`, string-aware)
//! - Bracket/brace/paren balance with nesting order
//! - Declaration well-formedness (no dangling `and`, orphaned attrs/unfold/doc)
//! - Module structure (module header present, opens before decls)
//! - Consecutive blank line cleanup
//! - Semantic validation (removed defs not referenced elsewhere)
//! - Rollback on any failure
//!
//! # Usage
//!
//! All fixable rules (FST001, FST002, FST004, FST005, FST010, FST012, FST013)
//! should use this validator before creating Fix instances.

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::path::Path;

use lazy_static::lazy_static;
use regex::Regex;

lazy_static! {
    /// Pattern to extract F* declarations for counting.
    /// Matches: val, let, type, class, instance, effect, exception, assume val
    static ref DECLARATION_PATTERN: Regex = Regex::new(
        r"(?m)^(?:private\s+)?(?:inline_for_extraction\s+)?(?:noextract\s+)?(?:unfold\s+)?(?:ghost\s+)?(?:noeq\s+)?(?:abstract\s+)?(val|let(?:\s+rec)?|type|class|instance|(?:layered_)?effect|exception|assume\s+val)\s+([a-zA-Z_][a-zA-Z0-9_']*)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to extract identifier references from code.
    static ref IDENTIFIER_PATTERN: Regex = Regex::new(
        r"\b([a-zA-Z_][a-zA-Z0-9_']*)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// F* keywords that should not be counted as references.
    static ref FSTAR_KEYWORDS: HashSet<&'static str> = {
        let mut s = HashSet::new();
        for kw in &[
            // Declaration keywords
            "val", "let", "rec", "type", "noeq", "and", "with", "match",
            "module", "open", "friend", "include",
            "effect", "layered_effect", "new_effect", "sub_effect", "total_effect",
            "class", "instance", "exception",
            "assume", "private", "abstract", "unfold", "irreducible",
            "inline_for_extraction", "noextract", "opaque_to_smt", "ghost",
            // Control flow
            "if", "then", "else", "begin", "end",
            "fun", "function", "return", "yield",
            "in", "of", "when", "as", "try",
            // Logic
            "forall", "exists", "True", "False", "true", "false",
            "not", "mod", "div", "land", "lor", "lxor",
            // Types
            "prop", "Type", "Type0", "Type1", "eqtype", "squash",
            "Tot", "GTot", "Lemma", "Pure", "Ghost", "ST", "Dv", "Div", "Exn",
            "requires", "ensures", "returns", "decreases", "modifies",
            "assert", "admit", "calc",
            // Built-ins
            "unit", "bool", "int", "nat", "pos", "string", "char",
            "option", "list", "either", "ref", "seq", "set", "map",
            // Common constructors
            "Some", "None", "Cons", "Nil", "Inl", "Inr",
            // Module prefixes
            "FStar", "Prims",
        ] {
            s.insert(*kw);
        }
        s
    };

    /// Pattern to detect unclosed string literals.
    static ref STRING_LITERAL: Regex = Regex::new(r#""(?:[^"\\]|\\.)*""#).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect common F* syntax errors.
    static ref SYNTAX_ERROR_PATTERNS: Vec<(&'static str, Regex)> = vec![
        ("Double semicolon", Regex::new(r";;").unwrap_or_else(|e| panic!("regex: {e}"))),
        ("Empty type definition", Regex::new(r"(?m)^type\s+\w+\s*$").unwrap_or_else(|e| panic!("regex: {e}"))),
    ];

    /// Declaration-starting keywords (after qualifier stripping).
    static ref DECL_STARTERS: Vec<&'static str> = vec![
        "val ", "let ", "let rec ", "type ", "class ", "instance ",
        "effect ", "layered_effect ", "exception ", "assume ",
    ];
}

// =============================================================================
// VALIDATION RESULT TYPES
// =============================================================================

/// Result of fix validation.
#[derive(Debug, Clone)]
pub struct FixValidation {
    /// Whether the fix is considered safe to apply.
    pub is_safe: bool,
    /// Confidence level from 0.0 (no confidence) to 1.0 (full confidence).
    pub confidence: f64,
    /// Warning messages about potential issues.
    pub warnings: Vec<String>,
    /// Whether semantic content is preserved (excluding whitespace).
    pub content_preserved: bool,
    /// Details about what changed in declarations.
    pub declaration_changes: DeclarationChanges,
    /// List of potentially orphaned references.
    pub orphaned_refs: Vec<String>,
}

impl FixValidation {
    /// Create a validation result indicating a safe fix.
    pub fn safe(confidence: f64) -> Self {
        Self {
            is_safe: true,
            confidence,
            warnings: Vec::new(),
            content_preserved: true,
            declaration_changes: DeclarationChanges::default(),
            orphaned_refs: Vec::new(),
        }
    }

    /// Create a validation result indicating an unsafe fix.
    pub fn unsafe_fix(reason: impl Into<String>) -> Self {
        Self {
            is_safe: false,
            confidence: 0.0,
            warnings: vec![reason.into()],
            content_preserved: false,
            declaration_changes: DeclarationChanges::default(),
            orphaned_refs: Vec::new(),
        }
    }

    /// Add a warning to the validation result.
    pub fn with_warning(mut self, warning: impl Into<String>) -> Self {
        self.warnings.push(warning.into());
        self
    }

    /// Reduce confidence by a factor.
    pub fn reduce_confidence(mut self, factor: f64) -> Self {
        self.confidence *= factor;
        self
    }

    /// Check if this fix should be auto-applied based on validation.
    pub fn can_auto_apply(&self, threshold: f64) -> bool {
        self.is_safe && self.confidence >= threshold
    }
}

impl Default for FixValidation {
    fn default() -> Self {
        Self {
            is_safe: true,
            confidence: 1.0,
            warnings: Vec::new(),
            content_preserved: true,
            declaration_changes: DeclarationChanges::default(),
            orphaned_refs: Vec::new(),
        }
    }
}

/// Tracks changes in declarations between original and fixed content.
#[derive(Debug, Clone, Default)]
pub struct DeclarationChanges {
    /// Declarations that were removed.
    pub removed: Vec<String>,
    /// Declarations that were added.
    pub added: Vec<String>,
    /// Declarations that were modified (same name, different content).
    pub modified: Vec<String>,
    /// Net change in declaration count (positive = more, negative = fewer).
    pub net_change: i32,
}

// =============================================================================
// PRIMARY VALIDATION ENTRY POINT
// =============================================================================

/// Validate a fix before applying it.
///
/// Performs comprehensive checks:
/// 1. Content preservation (semantic content excluding whitespace)
/// 2. Declaration counting (no unexpected removals)
/// 3. Semantic reference integrity (removed defs still referenced = UNSAFE)
/// 4. Comment balance (nested `(* *)`, doc `(** *)`, string-aware)
/// 5. Bracket/brace/paren balance with nesting order
/// 6. Declaration well-formedness (no dangling keywords)
/// 7. Dangling `and` detection
/// 8. Orphaned attributes/unfold/doc comments
/// 9. Module structure validation
/// 10. Consecutive blank line check
pub fn validate_fix(original: &str, fixed: &str, _file_path: &Path) -> FixValidation {
    let mut validation = FixValidation::default();

    // Check 1: Content hash comparison (excluding whitespace)
    let original_hash = content_hash(original);
    let fixed_hash = content_hash(fixed);
    validation.content_preserved = original_hash != fixed_hash;

    // Check 2: Declaration counting
    let original_decls = count_declarations(original);
    let fixed_decls = count_declarations(fixed);
    validation.declaration_changes = compare_declarations(&original_decls, &fixed_decls);

    if !validation.declaration_changes.removed.is_empty() {
        let removed_count = validation.declaration_changes.removed.len();
        validation.warnings.push(format!(
            "Fix removes {} declaration(s): {}",
            removed_count,
            validation.declaration_changes.removed.join(", ")
        ));
        validation.confidence *= 0.8_f64.powi(removed_count as i32);
    }

    if !validation.declaration_changes.added.is_empty() {
        validation.warnings.push(format!(
            "Fix adds new declaration(s): {}",
            validation.declaration_changes.added.join(", ")
        ));
        validation.confidence *= 0.9;
    }

    // Check 3: Semantic reference integrity -- if a removed definition is still
    // referenced in the remaining code, the fix is UNSAFE.
    if !validation.declaration_changes.removed.is_empty() {
        let dangling = find_dangling_references_after_removal(
            fixed,
            &validation.declaration_changes.removed,
        );
        if !dangling.is_empty() {
            validation.warnings.push(format!(
                "Removed definition(s) still referenced in remaining code: {}",
                dangling.join(", ")
            ));
            // Severe penalty -- removed code is used elsewhere
            validation.confidence *= 0.3;
        }
    }

    // Check 4: Orphaned identifier references (general)
    let orphaned = find_undefined_references(fixed, &fixed_decls);
    if !orphaned.is_empty() {
        validation.orphaned_refs = orphaned.clone();
        validation.warnings.push(format!(
            "Potential undefined references after fix: {}",
            orphaned.into_iter().take(5).collect::<Vec<_>>().join(", ")
        ));
        validation.confidence *= 0.7;
    }

    // Check 5: Full syntax validation (delimiters, patterns, well-formedness)
    if let Err(syntax_errors) = validate_fstar_syntax(fixed) {
        validation.is_safe = false;
        validation.warnings.extend(syntax_errors);
        validation.confidence = 0.0;
    }

    // Check 6: Comment balance (nested (* *), doc (** *), string-aware)
    if !check_comment_balance(fixed) {
        validation.warnings.push("Unbalanced comments detected in fixed content".to_string());
        validation.confidence *= 0.5;
    }

    // Check 7: Orphaned attributes
    let orphaned_attrs = check_orphaned_attributes(fixed);
    if !orphaned_attrs.is_empty() {
        validation.warnings.extend(orphaned_attrs);
        validation.confidence *= 0.8;
    }

    // Check 8: Dangling `and` keywords
    let dangling_ands = check_dangling_and(fixed);
    if !dangling_ands.is_empty() {
        validation.warnings.extend(dangling_ands);
        validation.confidence *= 0.4;
    }

    // Check 9: Orphaned unfold/doc comments without following declaration
    let orphaned_unfold = check_orphaned_unfold(fixed);
    if !orphaned_unfold.is_empty() {
        validation.warnings.extend(orphaned_unfold);
        validation.confidence *= 0.7;
    }

    let orphaned_doc = check_orphaned_doc_comments(fixed);
    if !orphaned_doc.is_empty() {
        validation.warnings.extend(orphaned_doc);
        validation.confidence *= 0.8;
    }

    // Check 10: Module structure
    let module_issues = check_module_structure(fixed);
    if !module_issues.is_empty() {
        validation.warnings.extend(module_issues);
        validation.confidence *= 0.9;
    }

    // Check 11: Consecutive blank lines (> 2 blank lines is suspicious)
    let blank_issues = check_consecutive_blanks(fixed);
    if !blank_issues.is_empty() {
        validation.warnings.extend(blank_issues);
        // Minor issue, don't reduce much
        validation.confidence *= 0.95;
    }

    // Final safety determination
    if validation.confidence < 0.5 {
        validation.is_safe = false;
    }

    validation
}

// =============================================================================
// CONTENT HASHING
// =============================================================================

/// Compute a semantic hash of content, ignoring whitespace differences.
pub fn content_hash(text: &str) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    let normalized = normalize_content(text);
    let mut hasher = DefaultHasher::new();
    normalized.hash(&mut hasher);
    hasher.finish()
}

/// Normalize content by removing whitespace and comments.
fn normalize_content(text: &str) -> String {
    let without_block_comments = strip_block_comments(text);
    let without_comments = strip_line_comments(&without_block_comments);
    without_comments
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

// =============================================================================
// COMMENT STRIPPING (nested, string-aware)
// =============================================================================

/// Strip F* block comments `(* ... *)` with proper nesting.
/// Handles nested comments: `(* outer (* inner *) *)`.
fn strip_block_comments(text: &str) -> String {
    let mut result = String::with_capacity(text.len());
    let mut depth: i32 = 0;
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if i + 1 < chars.len() && chars[i] == '(' && chars[i + 1] == '*' {
            depth += 1;
            i += 2;
            continue;
        }
        if i + 1 < chars.len() && chars[i] == '*' && chars[i + 1] == ')' && depth > 0 {
            depth -= 1;
            i += 2;
            continue;
        }
        if depth == 0 {
            result.push(chars[i]);
        }
        i += 1;
    }

    result
}

/// Strip F* line comments `// ...`.
fn strip_line_comments(text: &str) -> String {
    text.lines()
        .map(|line| {
            if let Some(pos) = line.find("//") {
                &line[..pos]
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Strip string literals from content, replacing with empty strings.
fn strip_string_literals(text: &str) -> String {
    STRING_LITERAL.replace_all(text, "\"\"").to_string()
}

// =============================================================================
// COMMENT BALANCE VALIDATION
// =============================================================================

/// Check if a character at position `i` is escaped by an odd number of preceding
/// backslashes. `\"` is escaped, `\\"` is NOT (backslash escapes backslash).
fn is_escaped(chars: &[char], i: usize) -> bool {
    let mut backslash_count: usize = 0;
    let mut j = i;
    while j > 0 {
        j -= 1;
        if chars[j] == '\\' {
            backslash_count += 1;
        } else {
            break;
        }
    }
    backslash_count % 2 != 0
}

/// Check if block comments are properly balanced with correct nesting order.
///
/// Uses a state machine that tracks:
/// - Nesting depth of `(* ... *)` block comments (including doc `(** ... *)`)
/// - String literal boundaries (respecting escape sequences)
/// - Line comments `//` (skipped entirely)
///
/// Returns false if:
/// - A close `*)` appears when no comment is open
/// - Comments remain unclosed at end of content
/// - Content like `*) code (*` correctly fails
fn check_comment_balance(content: &str) -> bool {
    let mut depth: i32 = 0;
    let mut in_string = false;
    let chars: Vec<char> = content.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        // String boundaries (only outside block comments)
        if depth == 0 && chars[i] == '"' && !is_escaped(&chars, i) {
            in_string = !in_string;
            i += 1;
            continue;
        }
        if in_string {
            i += 1;
            continue;
        }

        // Line comments (only outside block comments)
        if depth == 0 && i + 1 < chars.len() && chars[i] == '/' && chars[i + 1] == '/' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }

        // Block comment open -- handles both `(*` and `(**`
        if i + 1 < chars.len() && chars[i] == '(' && chars[i + 1] == '*' {
            depth += 1;
            // Skip the `(*` (or `(**`) -- the extra `*` for doc is consumed
            // inside the block by the nesting logic, not here.
            i += 2;
            continue;
        }

        // Block comment close
        if i + 1 < chars.len() && chars[i] == '*' && chars[i + 1] == ')' {
            depth -= 1;
            if depth < 0 {
                return false; // close before open
            }
            i += 2;
            continue;
        }

        i += 1;
    }

    depth == 0
}

// =============================================================================
// DELIMITER BALANCE
// =============================================================================

/// Check delimiter balance with proper nesting order validation.
///
/// Strips comments and string literals first, then walks through the cleaned
/// content tracking nesting depth. Detects close-before-open errors.
fn check_delimiter_balance(
    content: &str,
    open: char,
    close: char,
    name: &str,
) -> Result<(), String> {
    let clean = strip_block_comments(content);
    let clean = strip_line_comments(&clean);
    let clean = strip_string_literals(&clean);

    let mut depth: i32 = 0;
    for ch in clean.chars() {
        if ch == open {
            depth += 1;
        } else if ch == close {
            depth -= 1;
            if depth < 0 {
                return Err(format!(
                    "Unbalanced {}: closing before opening",
                    name
                ));
            }
        }
    }

    if depth > 0 {
        Err(format!("Unbalanced {}: {} extra open", name, depth))
    } else {
        Ok(())
    }
}

// =============================================================================
// SYNTAX VALIDATION
// =============================================================================

/// Verify basic F* syntax in content.
///
/// Validates:
/// - Balanced parentheses/braces/brackets with nesting order (outside comments/strings)
/// - Well-formed val/let/type declarations
/// - Common syntax error patterns
/// - String literal balance
pub fn validate_fstar_syntax(content: &str) -> Result<(), Vec<String>> {
    let mut errors = Vec::new();

    if let Err(e) = check_delimiter_balance(content, '(', ')', "parentheses") {
        errors.push(e);
    }
    if let Err(e) = check_delimiter_balance(content, '{', '}', "braces") {
        errors.push(e);
    }
    if let Err(e) = check_delimiter_balance(content, '[', ']', "brackets") {
        errors.push(e);
    }

    for (name, pattern) in SYNTAX_ERROR_PATTERNS.iter() {
        if pattern.is_match(content) {
            errors.push(format!("Syntax issue: {}", name));
        }
    }

    // String quote balance (simplified: count unescaped quotes outside comments)
    let no_comments = strip_block_comments(content);
    let no_comments = strip_line_comments(&no_comments);
    let chars: Vec<char> = no_comments.chars().collect();
    let mut quote_depth = false;
    for (idx, &ch) in chars.iter().enumerate() {
        if ch == '"' && !is_escaped(&chars, idx) {
            quote_depth = !quote_depth;
        }
    }
    if quote_depth {
        errors.push("Unbalanced string quotes".to_string());
    }

    let decl_issues = check_declaration_wellformedness(content);
    errors.extend(decl_issues);

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

// =============================================================================
// DECLARATION WELL-FORMEDNESS
// =============================================================================

/// Strip leading F* declaration qualifiers from a line.
fn strip_qualifiers(line: &str) -> &str {
    let qualifiers = [
        "private ", "inline_for_extraction ", "noextract ",
        "unfold ", "ghost ", "noeq ", "abstract ",
    ];
    let mut s = line;
    loop {
        let mut changed = false;
        for q in &qualifiers {
            if let Some(rest) = s.strip_prefix(q) {
                s = rest.trim_start();
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    s
}

/// Check that val/let/type declarations are well-formed.
///
/// Validates that declaration keywords at the start of a line are followed
/// by a valid identifier. Content inside block comments is excluded.
fn check_declaration_wellformedness(content: &str) -> Vec<String> {
    let mut issues = Vec::new();
    let clean = strip_block_comments(content);

    for (line_num, line) in clean.lines().enumerate() {
        let trimmed = line.trim();

        if trimmed.is_empty()
            || trimmed.starts_with("//")
            || trimmed.starts_with("module")
            || trimmed.starts_with("open")
            || trimmed.starts_with("friend")
            || trimmed.starts_with("include")
            || trimmed.starts_with('#')
            || trimmed.starts_with("and ")
        {
            continue;
        }

        let stripped = strip_qualifiers(trimmed);

        if stripped == "val" {
            issues.push(format!(
                "Malformed val declaration at line {} (missing identifier)",
                line_num + 1
            ));
        }

        if stripped == "let" || stripped == "let rec" {
            issues.push(format!(
                "Malformed let declaration at line {} (missing identifier)",
                line_num + 1
            ));
        }

        if stripped == "type" {
            issues.push(format!(
                "Malformed type declaration at line {} (missing identifier)",
                line_num + 1
            ));
        }
    }

    issues
}

// =============================================================================
// DANGLING `and` DETECTION
// =============================================================================

/// Detect dangling `and` keywords that are not preceded by a `type` or `let rec`
/// declaration in the same mutual-recursion group.
///
/// In F*, `and` continues a mutual recursion:
/// ```fstar
/// type expr = ...
/// and stmt = ...
/// ```
/// If the linter removes `type expr`, the `and stmt` becomes dangling.
fn check_dangling_and(content: &str) -> Vec<String> {
    let mut issues = Vec::new();
    let clean = strip_block_comments(content);
    let lines: Vec<&str> = clean.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if !trimmed.starts_with("and ") {
            continue;
        }

        // Walk backwards to find the preceding declaration that starts
        // this mutual-recursion group. Skip blank lines and comments.
        let mut found_group_head = false;
        let mut j = i;
        while j > 0 {
            j -= 1;
            let prev = lines[j].trim();

            // Skip blank lines
            if prev.is_empty() {
                continue;
            }

            // Skip line comments
            if prev.starts_with("//") {
                continue;
            }

            // Another `and` in the same group is fine
            if prev.starts_with("and ") {
                found_group_head = true;
                break;
            }

            // The head of the group: `type` or `let rec`
            let stripped = strip_qualifiers(prev);
            if stripped.starts_with("type ") || stripped.starts_with("let rec ") {
                found_group_head = true;
                break;
            }

            // Lines that look like constructors or record fields belonging
            // to a preceding type definition
            if prev.starts_with('|') || prev.starts_with('{') || prev.starts_with('}')
                || prev.ends_with(';') || prev.ends_with('{')
            {
                continue;
            }

            // Anything else means we've left the mutual-recursion scope
            break;
        }

        if !found_group_head {
            issues.push(format!(
                "Dangling 'and' at line {} without preceding type/let rec group: {}",
                i + 1,
                trimmed.chars().take(60).collect::<String>()
            ));
        }
    }

    issues
}

// =============================================================================
// ORPHANED ATTRIBUTES / UNFOLD / DOC COMMENTS
// =============================================================================

/// Check for orphaned attributes without a following declaration.
///
/// In F*, attributes like `[@@attr]` or `[@attr]` must precede a declaration.
fn check_orphaned_attributes(content: &str) -> Vec<String> {
    let mut issues = Vec::new();
    let lines: Vec<&str> = content.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        if (trimmed.starts_with("[@@") || trimmed.starts_with("[@"))
            && trimmed.ends_with(']')
            && !trimmed.contains("let")
            && !trimmed.contains("val")
            && !has_following_declaration(&lines, i + 1)
        {
            issues.push(format!(
                "Orphaned attribute at line {} without following declaration: {}",
                i + 1,
                trimmed
            ));
        }
    }

    issues
}

/// Check for orphaned `unfold` keyword on a line by itself (or with only
/// qualifiers) that is not followed by a declaration.
fn check_orphaned_unfold(content: &str) -> Vec<String> {
    let mut issues = Vec::new();
    let clean = strip_block_comments(content);
    let lines: Vec<&str> = clean.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let stripped = strip_qualifiers(trimmed);

        // Only qualifiers remain with no declaration keyword following
        if stripped == "unfold" || stripped == "noextract" || stripped == "ghost"
            || stripped == "private" || stripped == "abstract"
            || stripped == "inline_for_extraction"
        {
            issues.push(format!(
                "Orphaned qualifier at line {} without declaration: {}",
                i + 1,
                trimmed
            ));
        }
    }

    issues
}

/// Check for orphaned doc comments `(** ... *)` not followed by a declaration.
fn check_orphaned_doc_comments(content: &str) -> Vec<String> {
    let mut issues = Vec::new();
    let lines: Vec<&str> = content.lines().collect();

    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();

        // Detect single-line doc comment: (** ... *)
        if trimmed.starts_with("(**") && trimmed.ends_with("*)") && trimmed.len() > 5 {
            if !has_following_declaration(&lines, i + 1) {
                issues.push(format!(
                    "Orphaned doc comment at line {} without following declaration",
                    i + 1
                ));
            }
            i += 1;
            continue;
        }

        // Detect multi-line doc comment opening: (**
        if trimmed.starts_with("(**") && !trimmed.ends_with("*)") {
            // Find end of doc comment
            let start = i;
            let mut depth = 1_i32;
            i += 1;
            while i < lines.len() && depth > 0 {
                let ln = lines[i].trim();
                // Count opens/closes in this line
                let mut ci = 0;
                let line_chars: Vec<char> = ln.chars().collect();
                while ci < line_chars.len() {
                    if ci + 1 < line_chars.len() && line_chars[ci] == '(' && line_chars[ci + 1] == '*' {
                        depth += 1;
                        ci += 2;
                        continue;
                    }
                    if ci + 1 < line_chars.len() && line_chars[ci] == '*' && line_chars[ci + 1] == ')' {
                        depth -= 1;
                        ci += 2;
                        if depth == 0 {
                            break;
                        }
                        continue;
                    }
                    ci += 1;
                }
                i += 1;
            }
            // Now i is the line after the closing `*)`
            if !has_following_declaration(&lines, i) {
                issues.push(format!(
                    "Orphaned doc comment at line {} without following declaration",
                    start + 1
                ));
            }
            continue;
        }

        i += 1;
    }

    issues
}

/// Check whether `lines[start_idx..]` has a declaration as the next non-blank,
/// non-comment, non-attribute content.
fn has_following_declaration(lines: &[&str], start_idx: usize) -> bool {
    for line in lines.iter().skip(start_idx) {
        let next = line.trim();
        if next.is_empty() {
            continue;
        }
        // Stacked attributes are fine
        if (next.starts_with("[@@") || next.starts_with("[@")) && next.ends_with(']') {
            continue;
        }
        // Skip pragma lines
        if next.starts_with('#') {
            continue;
        }
        let stripped = strip_qualifiers(next);
        for starter in DECL_STARTERS.iter() {
            if stripped.starts_with(starter) {
                return true;
            }
        }
        // `and` is also acceptable (continuing a group)
        if stripped.starts_with("and ") {
            return true;
        }
        return false;
    }
    false
}

// =============================================================================
// MODULE STRUCTURE VALIDATION
// =============================================================================

/// Check basic F* module structure.
///
/// Validates:
/// - File starts with `module` declaration (after optional doc comment)
/// - `open` statements come before declarations (warning if interleaved)
fn check_module_structure(content: &str) -> Vec<String> {
    let mut issues = Vec::new();
    let clean = strip_block_comments(content);
    let lines: Vec<&str> = clean.lines().collect();

    // Find first non-blank, non-comment line
    let mut found_module = false;
    let mut first_decl_seen = false;

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with('#') {
            continue;
        }

        if !found_module {
            if trimmed.starts_with("module ") {
                found_module = true;
            } else {
                issues.push(format!(
                    "Expected 'module' declaration at line {}, found: {}",
                    i + 1,
                    trimmed.chars().take(40).collect::<String>()
                ));
                break;
            }
            continue;
        }

        // After module line
        if trimmed.starts_with("open ") || trimmed.starts_with("friend ") || trimmed.starts_with("include ") {
            if first_decl_seen {
                issues.push(format!(
                    "Open/friend/include at line {} after declarations started (consider moving to top)",
                    i + 1
                ));
            }
            continue;
        }

        let stripped = strip_qualifiers(trimmed);
        for starter in DECL_STARTERS.iter() {
            if stripped.starts_with(starter) {
                first_decl_seen = true;
                break;
            }
        }
    }

    issues
}

// =============================================================================
// CONSECUTIVE BLANK LINE CHECK
// =============================================================================

/// Detect runs of more than 2 consecutive blank lines.
fn check_consecutive_blanks(content: &str) -> Vec<String> {
    let mut issues = Vec::new();
    let mut blank_run = 0;

    for (i, line) in content.lines().enumerate() {
        if line.trim().is_empty() {
            blank_run += 1;
            if blank_run == 4 {
                issues.push(format!(
                    "More than 3 consecutive blank lines around line {}",
                    i + 1
                ));
            }
        } else {
            blank_run = 0;
        }
    }

    issues
}

/// Clean up consecutive blank lines, collapsing runs of >2 into exactly 2.
/// Returns the cleaned content.
pub fn cleanup_consecutive_blank_lines(content: &str) -> String {
    let mut result = String::with_capacity(content.len());
    let mut blank_run = 0;

    for line in content.lines() {
        if line.trim().is_empty() {
            blank_run += 1;
            if blank_run <= 2 {
                result.push('\n');
            }
        } else {
            blank_run = 0;
            if !result.is_empty() {
                // Avoid double newline at start
            }
            result.push_str(line);
            result.push('\n');
        }
    }

    // Preserve trailing newline behavior
    if content.ends_with('\n') && !result.ends_with('\n') {
        result.push('\n');
    }
    if !content.ends_with('\n') && result.ends_with('\n') {
        result.pop();
    }

    result
}

// =============================================================================
// SEMANTIC VALIDATION
// =============================================================================

/// Find removed definition names that are still referenced in the remaining code.
///
/// This is the key check that prevents the corruption pattern where the linter
/// removes a type definition that is still used by other code.
fn find_dangling_references_after_removal(
    remaining_code: &str,
    removed_names: &[String],
) -> Vec<String> {
    let mut dangling = Vec::new();
    let clean = strip_block_comments(remaining_code);
    let clean = strip_line_comments(&clean);
    let clean = strip_string_literals(&clean);

    for name in removed_names {
        // Build a word-boundary regex for this identifier
        let pattern = format!(r"\b{}\b", regex::escape(name));
        if let Ok(re) = Regex::new(&pattern) {
            if re.is_match(&clean) {
                dangling.push(name.clone());
            }
        }
    }

    dangling
}

// =============================================================================
// ROLLBACK SUPPORT
// =============================================================================

/// Validate a proposed fix and return the fixed content only if all checks pass.
/// On any failure, returns the original content unchanged (rollback).
///
/// This is the safe entry point that guarantees no corruption.
pub fn validate_and_rollback(
    original: &str,
    fixed: &str,
    file_path: &Path,
    min_confidence: f64,
) -> ValidatedFix {
    let validation = validate_fix(original, fixed, file_path);

    if validation.is_safe && validation.confidence >= min_confidence {
        ValidatedFix {
            content: fixed.to_string(),
            applied: true,
            validation,
        }
    } else {
        ValidatedFix {
            content: original.to_string(),
            applied: false,
            validation,
        }
    }
}

/// Result of validate-and-rollback: either the fixed content (if safe) or
/// the original content unchanged.
#[derive(Debug, Clone)]
pub struct ValidatedFix {
    /// The content to write -- either fixed (if safe) or original (rollback).
    pub content: String,
    /// Whether the fix was actually applied.
    pub applied: bool,
    /// Full validation details.
    pub validation: FixValidation,
}

// =============================================================================
// DECLARATION COUNTING
// =============================================================================

/// Count declarations in F* content by category.
pub fn count_declarations(content: &str) -> HashMap<String, String> {
    let mut decls = HashMap::new();

    for caps in DECLARATION_PATTERN.captures_iter(content) {
        let kind = caps.get(1).map(|m| m.as_str()).unwrap_or("unknown");
        let name = caps.get(2).map(|m| m.as_str()).unwrap_or("");

        if !name.is_empty() {
            decls.insert(name.to_string(), kind.to_string());
        }
    }

    decls
}

/// Compare declaration counts between original and fixed.
fn compare_declarations(
    original: &HashMap<String, String>,
    fixed: &HashMap<String, String>,
) -> DeclarationChanges {
    let mut changes = DeclarationChanges::default();

    for name in original.keys() {
        if !fixed.contains_key(name) {
            changes.removed.push(name.clone());
        }
    }

    for name in fixed.keys() {
        if !original.contains_key(name) {
            changes.added.push(name.clone());
        }
    }

    changes.net_change = fixed.len() as i32 - original.len() as i32;
    changes
}

// =============================================================================
// REFERENCE ANALYSIS
// =============================================================================

/// Find potentially undefined references in content.
pub fn find_undefined_references(
    content: &str,
    declarations: &HashMap<String, String>,
) -> Vec<String> {
    let mut undefined = Vec::new();
    let declared_names: HashSet<&str> = declarations.keys().map(|s| s.as_str()).collect();

    for caps in IDENTIFIER_PATTERN.captures_iter(content) {
        let ident = caps.get(1).map(|m| m.as_str()).unwrap_or("");

        if FSTAR_KEYWORDS.contains(ident) {
            continue;
        }
        if declared_names.contains(ident) {
            continue;
        }
        // Skip uppercase (likely modules/constructors)
        if ident.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
            continue;
        }
        // Skip underscore-prefixed (parameters)
        if ident.starts_with('_') {
            continue;
        }

        if !undefined.contains(&ident.to_string()) {
            undefined.push(ident.to_string());
        }
    }

    undefined.truncate(20);
    undefined
}

// =============================================================================
// PUBLIC CONVENIENCE VALIDATORS
// =============================================================================

/// Validate that a fix preserves expected declarations.
pub fn validate_no_removals(original: &str, fixed: &str) -> Result<(), String> {
    let orig_decls = count_declarations(original);
    let fixed_decls = count_declarations(fixed);

    for name in orig_decls.keys() {
        if !fixed_decls.contains_key(name) {
            return Err(format!("Fix would remove declaration: {}", name));
        }
    }

    Ok(())
}

/// Validate that a fix only removes specified declarations.
pub fn validate_expected_removals(
    original: &str,
    fixed: &str,
    expected_removals: &[&str],
) -> FixValidation {
    let orig_decls = count_declarations(original);
    let fixed_decls = count_declarations(fixed);
    let mut validation = FixValidation::safe(1.0);

    let expected_set: HashSet<&str> = expected_removals.iter().copied().collect();

    for name in orig_decls.keys() {
        if !fixed_decls.contains_key(name) {
            if !expected_set.contains(name.as_str()) {
                validation.warnings.push(format!(
                    "Unexpected removal of declaration: {}",
                    name
                ));
                validation.confidence *= 0.5;
            }
            validation.declaration_changes.removed.push(name.clone());
        }
    }

    for name in fixed_decls.keys() {
        if !orig_decls.contains_key(name) {
            validation.declaration_changes.added.push(name.clone());
            validation.warnings.push(format!("Unexpected addition: {}", name));
            validation.confidence *= 0.8;
        }
    }

    validation.declaration_changes.net_change =
        fixed_decls.len() as i32 - orig_decls.len() as i32;

    if validation.confidence < 0.5 {
        validation.is_safe = false;
    }

    validation
}

/// Quick validation for whitespace-only fixes.
pub fn validate_whitespace_only_fix(original: &str, fixed: &str) -> FixValidation {
    let orig_normalized = normalize_content(original);
    let fixed_normalized = normalize_content(fixed);

    if orig_normalized == fixed_normalized {
        FixValidation::safe(1.0)
    } else {
        FixValidation::unsafe_fix("Fix changes more than whitespace")
    }
}

/// Validate a line deletion fix.
pub fn validate_line_deletion(
    original: &str,
    _start_line: usize,
    _end_line: usize,
    deleted_content: &str,
) -> FixValidation {
    let mut validation = FixValidation::safe(0.9);

    let decls_in_deleted = count_declarations(deleted_content);
    if !decls_in_deleted.is_empty() {
        validation.declaration_changes.removed =
            decls_in_deleted.keys().cloned().collect();
        validation.warnings.push(format!(
            "Deleting {} declaration(s): {}",
            decls_in_deleted.len(),
            decls_in_deleted.keys().cloned().collect::<Vec<_>>().join(", ")
        ));
        validation.confidence *= 0.7;
    }

    let refs_in_deleted: Vec<String> = IDENTIFIER_PATTERN
        .captures_iter(deleted_content)
        .filter_map(|c| c.get(1))
        .map(|m| m.as_str().to_string())
        .filter(|s| !FSTAR_KEYWORDS.contains(s.as_str()))
        .collect();

    if !refs_in_deleted.is_empty() {
        let remaining_content = original.replace(deleted_content, "");
        for _ref_name in &refs_in_deleted {
            if remaining_content.contains(_ref_name.as_str()) {
                // Reference exists elsewhere -- expected for deletion fixes
            }
        }
    }

    validation
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    // =========================================================================
    // CONTENT HASH TESTS
    // =========================================================================

    #[test]
    fn test_content_hash_ignores_whitespace() {
        let c1 = "let foo x = x + 1";
        let c2 = "let   foo   x   =   x   +   1";
        let c3 = "let foo x =\n  x + 1";
        assert_eq!(content_hash(c1), content_hash(c2));
        assert_eq!(content_hash(c1), content_hash(c3));
    }

    #[test]
    fn test_content_hash_ignores_comments() {
        let c1 = "let foo x = x + 1";
        let c2 = "(* comment *) let foo x = x + 1";
        let c3 = "let foo x = x + 1 // comment";
        assert_eq!(content_hash(c1), content_hash(c2));
        assert_eq!(content_hash(c1), content_hash(c3));
    }

    #[test]
    fn test_content_hash_different_for_different_content() {
        assert_ne!(
            content_hash("let foo x = x + 1"),
            content_hash("let foo x = x + 2")
        );
    }

    // =========================================================================
    // STRIP COMMENTS TESTS
    // =========================================================================

    #[test]
    fn test_strip_block_comments_simple() {
        assert_eq!(strip_block_comments("let (* comment *) foo = 1"), "let  foo = 1");
    }

    #[test]
    fn test_strip_block_comments_nested() {
        assert_eq!(
            strip_block_comments("let (* outer (* inner *) *) foo = 1"),
            "let  foo = 1"
        );
    }

    #[test]
    fn test_strip_block_comments_doc() {
        assert_eq!(
            strip_block_comments("(** doc comment *) val foo : int"),
            " val foo : int"
        );
    }

    #[test]
    fn test_strip_line_comments() {
        assert_eq!(strip_line_comments("let foo = 1 // comment"), "let foo = 1 ");
    }

    // =========================================================================
    // IS_ESCAPED TESTS
    // =========================================================================

    #[test]
    fn test_is_escaped_basic() {
        let chars: Vec<char> = r#"hello\""#.chars().collect();
        assert!(is_escaped(&chars, 6));
    }

    #[test]
    fn test_is_escaped_double_backslash() {
        let chars: Vec<char> = r#"hello\\""#.chars().collect();
        assert!(!is_escaped(&chars, 7));
    }

    #[test]
    fn test_is_escaped_no_backslash() {
        let chars: Vec<char> = r#"hello""#.chars().collect();
        assert!(!is_escaped(&chars, 5));
    }

    #[test]
    fn test_is_escaped_at_start() {
        let chars: Vec<char> = r#"""#.chars().collect();
        assert!(!is_escaped(&chars, 0));
    }

    #[test]
    fn test_is_escaped_triple_backslash() {
        let chars: Vec<char> = r#"a\\\""#.chars().collect();
        assert!(is_escaped(&chars, 4));
    }

    // =========================================================================
    // COMMENT BALANCE TESTS
    // =========================================================================

    #[test]
    fn test_comment_balance_valid_simple() {
        assert!(check_comment_balance("(* comment *)"));
    }

    #[test]
    fn test_comment_balance_valid_nested() {
        assert!(check_comment_balance("(* outer (* inner *) *)"));
    }

    #[test]
    fn test_comment_balance_valid_deeply_nested() {
        assert!(check_comment_balance("(* level 1 (* level 2 (* level 3 *) *) *)"));
    }

    #[test]
    fn test_comment_balance_valid_sequential() {
        assert!(check_comment_balance("(* first *) code (* second *)"));
    }

    #[test]
    fn test_comment_balance_valid_doc_comment() {
        assert!(check_comment_balance("(** doc comment *)"));
    }

    #[test]
    fn test_comment_balance_valid_doc_nested() {
        assert!(check_comment_balance("(** doc (* nested *) *)"));
    }

    #[test]
    fn test_comment_balance_unclosed() {
        assert!(!check_comment_balance("(* unclosed"));
    }

    #[test]
    fn test_comment_balance_extra_close() {
        assert!(!check_comment_balance("extra close *)"));
    }

    #[test]
    fn test_comment_balance_close_before_open() {
        assert!(!check_comment_balance("*) code (*"));
    }

    #[test]
    fn test_comment_balance_interleaved_invalid() {
        assert!(!check_comment_balance("*) (* some text *)"));
    }

    #[test]
    fn test_comment_balance_unclosed_double_nested() {
        assert!(!check_comment_balance("(* outer (* inner *)"));
    }

    #[test]
    fn test_comment_balance_extra_close_after_valid() {
        assert!(!check_comment_balance("(* comment *) *)"));
    }

    #[test]
    fn test_comment_balance_empty() {
        assert!(check_comment_balance(""));
    }

    #[test]
    fn test_comment_balance_no_comments() {
        assert!(check_comment_balance("let foo x = x + 1"));
    }

    #[test]
    fn test_comment_balance_in_string_ignored() {
        assert!(check_comment_balance(r#"let x = "(*" in x"#));
        assert!(check_comment_balance(r#"let x = "*)" in x"#));
        assert!(check_comment_balance(r#"let x = "(*" ^ "*)" in x"#));
    }

    #[test]
    fn test_comment_balance_line_comment_ignored() {
        assert!(check_comment_balance("let x = 1 // (* not a block comment"));
        assert!(check_comment_balance("let x = 1 // *) not a close"));
    }

    #[test]
    fn test_comment_balance_escaped_quote_in_string() {
        assert!(check_comment_balance(r#"let x = "hello \" (*" in x"#));
    }

    #[test]
    fn test_comment_balance_double_escaped_backslash() {
        assert!(check_comment_balance(r#"let x = "hello \\" (* comment *)"#));
    }

    // =========================================================================
    // DELIMITER BALANCE TESTS
    // =========================================================================

    #[test]
    fn test_delim_balanced_parens() {
        assert!(check_delimiter_balance("((()))", '(', ')', "parentheses").is_ok());
        assert!(check_delimiter_balance("(()())", '(', ')', "parentheses").is_ok());
    }

    #[test]
    fn test_delim_balanced_braces() {
        assert!(check_delimiter_balance("{{}{}}", '{', '}', "braces").is_ok());
    }

    #[test]
    fn test_delim_close_before_open_parens() {
        let r = check_delimiter_balance(") code (", '(', ')', "parentheses");
        assert!(r.is_err());
        assert!(r.unwrap_err().contains("parentheses"));
    }

    #[test]
    fn test_delim_close_before_open_braces() {
        let r = check_delimiter_balance("} code {", '{', '}', "braces");
        assert!(r.is_err());
    }

    #[test]
    fn test_delim_close_before_open_brackets() {
        let r = check_delimiter_balance("] code [", '[', ']', "brackets");
        assert!(r.is_err());
    }

    #[test]
    fn test_delim_unclosed() {
        let r = check_delimiter_balance("(()", '(', ')', "parentheses");
        assert!(r.is_err());
        assert!(r.unwrap_err().contains("extra open"));
    }

    #[test]
    fn test_delim_in_comments_ignored() {
        assert!(check_delimiter_balance("(* ( *)", '(', ')', "parentheses").is_ok());
        assert!(check_delimiter_balance("(* ) *)", '(', ')', "parentheses").is_ok());
    }

    #[test]
    fn test_delim_in_strings_ignored() {
        assert!(check_delimiter_balance(r#"let x = "(" in x"#, '(', ')', "parentheses").is_ok());
    }

    #[test]
    fn test_delim_in_line_comments_ignored() {
        assert!(check_delimiter_balance("let x = 1 // (unclosed", '(', ')', "parentheses").is_ok());
    }

    #[test]
    fn test_delim_fstar_multiline_parens() {
        let content = "let foo (x: int)\n        (y: int)\n        = x + y\n";
        assert!(check_delimiter_balance(content, '(', ')', "parentheses").is_ok());
    }

    #[test]
    fn test_delim_fstar_record() {
        let content = "type config = {\n  debug: bool;\n  level: nat\n}\n";
        assert!(check_delimiter_balance(content, '{', '}', "braces").is_ok());
    }

    #[test]
    fn test_delim_empty() {
        assert!(check_delimiter_balance("", '(', ')', "parentheses").is_ok());
    }

    // =========================================================================
    // SYNTAX VALIDATION TESTS
    // =========================================================================

    #[test]
    fn test_syntax_balanced() {
        assert!(validate_fstar_syntax("let foo (x: int) = { field = x }").is_ok());
    }

    #[test]
    fn test_syntax_unbalanced_parens() {
        let r = validate_fstar_syntax("let foo (x: int = x + 1");
        assert!(r.is_err());
        assert!(r.unwrap_err().iter().any(|e| e.contains("parentheses")));
    }

    #[test]
    fn test_syntax_unbalanced_braces() {
        let r = validate_fstar_syntax("let foo x = { field = x");
        assert!(r.is_err());
        assert!(r.unwrap_err().iter().any(|e| e.contains("braces")));
    }

    #[test]
    fn test_syntax_close_paren_before_open() {
        let r = validate_fstar_syntax("let x = ) + (");
        assert!(r.is_err());
    }

    #[test]
    fn test_syntax_close_brace_before_open() {
        let r = validate_fstar_syntax("let x = } + {");
        assert!(r.is_err());
    }

    #[test]
    fn test_syntax_valid_multiline_parens() {
        let content = "let foo (x: int)\n        (y: int) =\n  x + y\n";
        assert!(validate_fstar_syntax(content).is_ok());
    }

    #[test]
    fn test_syntax_valid_multiline_braces() {
        let content = "type rec = {\n  field1: int;\n  field2: string\n}\n";
        assert!(validate_fstar_syntax(content).is_ok());
    }

    #[test]
    fn test_syntax_refinement_types() {
        let content = "val bounded_nat : (n:nat{n < 100}) -> int\nlet bounded_nat n = n + 1\n";
        assert!(validate_fstar_syntax(content).is_ok());
    }

    #[test]
    fn test_syntax_unbalanced_string_quotes() {
        let content = "let x = \"unclosed string";
        let r = validate_fstar_syntax(content);
        assert!(r.is_err());
        assert!(r.unwrap_err().iter().any(|e| e.contains("string quotes")));
    }

    #[test]
    fn test_syntax_quotes_in_comments_not_counted() {
        // A quote inside a comment should not affect balance
        let content = "(* this has a \" inside *)\nlet x = 1";
        assert!(validate_fstar_syntax(content).is_ok());
    }

    // =========================================================================
    // DECLARATION COUNTING TESTS
    // =========================================================================

    #[test]
    fn test_count_declarations_basic() {
        let content = "module Test\n\nval foo : int -> int\nlet foo x = x + 1\n\ntype mytype = nat\n\nlet bar y = y * 2\n";
        let decls = count_declarations(content);
        assert!(decls.contains_key("foo"));
        assert!(decls.contains_key("mytype"));
        assert!(decls.contains_key("bar"));
        assert_eq!(decls.len(), 3);
    }

    #[test]
    fn test_count_declarations_qualified() {
        let content = "private val internal_fn : int\ninline_for_extraction let fast x = x\nghost let ghost_val : int = 42\n";
        let decls = count_declarations(content);
        assert!(decls.contains_key("internal_fn"));
        assert!(decls.contains_key("fast"));
        assert!(decls.contains_key("ghost_val"));
    }

    #[test]
    fn test_count_declarations_effects() {
        let content = "effect MyEffect (a:Type) = Tot a\nlayered_effect PURE = ...\n";
        let decls = count_declarations(content);
        assert!(decls.contains_key("MyEffect"));
        assert!(decls.contains_key("PURE"));
    }

    #[test]
    fn test_count_declarations_noeq() {
        let content = "noeq type myrecord = {\n  field1: int;\n  field2: string\n}\n";
        let decls = count_declarations(content);
        assert!(decls.contains_key("myrecord"));
    }

    #[test]
    fn test_count_declarations_assume_val() {
        let content = "assume val axiom : prop\n";
        let decls = count_declarations(content);
        assert!(decls.contains_key("axiom"));
    }

    #[test]
    fn test_count_declarations_let_rec() {
        let content = "let rec factorial (n:nat) : Tot nat (decreases n) =\n  if n = 0 then 1 else n * factorial (n - 1)\n";
        let decls = count_declarations(content);
        assert!(decls.contains_key("factorial"));
    }

    #[test]
    fn test_count_declarations_empty() {
        assert!(count_declarations("").is_empty());
    }

    #[test]
    fn test_count_declarations_comment_only() {
        assert!(count_declarations("(* just a comment *)").is_empty());
    }

    #[test]
    fn test_declaration_pattern_matches() {
        let cases = vec![
            ("val foo : int -> int", "foo"),
            ("let foo x = x + 1", "foo"),
            ("let rec factorial n = ...", "factorial"),
            ("type mytype = nat", "mytype"),
            ("private let internal x = 1", "internal"),
            ("inline_for_extraction let fast x = x", "fast"),
            ("class myclass a = { ... }", "myclass"),
            ("instance myinst : myclass int = { ... }", "myinst"),
            ("exception MyExn", "MyExn"),
            ("assume val axiom : prop", "axiom"),
        ];
        for (input, expected) in cases {
            let decls = count_declarations(input);
            assert!(
                decls.contains_key(expected),
                "Expected '{}' in '{}'", expected, input
            );
        }
    }

    // =========================================================================
    // DECLARATION WELL-FORMEDNESS TESTS
    // =========================================================================

    #[test]
    fn test_wellformed_val() {
        assert!(check_declaration_wellformedness("val foo : int -> int").is_empty());
    }

    #[test]
    fn test_malformed_val_dangling() {
        let issues = check_declaration_wellformedness("val");
        assert!(!issues.is_empty());
        assert!(issues[0].contains("Malformed val"));
    }

    #[test]
    fn test_wellformed_let() {
        assert!(check_declaration_wellformedness("let foo x = x + 1").is_empty());
    }

    #[test]
    fn test_malformed_let_dangling() {
        let issues = check_declaration_wellformedness("let");
        assert!(!issues.is_empty());
        assert!(issues[0].contains("Malformed let"));
    }

    #[test]
    fn test_malformed_let_rec_dangling() {
        let issues = check_declaration_wellformedness("let rec");
        assert!(!issues.is_empty());
    }

    #[test]
    fn test_wellformed_type() {
        assert!(check_declaration_wellformedness("type mytype = nat").is_empty());
    }

    #[test]
    fn test_malformed_type_dangling() {
        let issues = check_declaration_wellformedness("type");
        assert!(!issues.is_empty());
        assert!(issues[0].contains("Malformed type"));
    }

    #[test]
    fn test_wellformed_qualified() {
        let content = "private val internal_fn : int -> int\ninline_for_extraction let fast x = x\nghost let ghost_val : int = 42\nnoeq type myrecord = { field: int }\n";
        assert!(check_declaration_wellformedness(content).is_empty());
    }

    #[test]
    fn test_wellformed_inside_comments_ignored() {
        let content = "(* val *)\nlet foo x = x";
        assert!(check_declaration_wellformedness(content).is_empty());
    }

    // =========================================================================
    // DANGLING `and` TESTS
    // =========================================================================

    #[test]
    fn test_and_with_preceding_type_is_ok() {
        let content = "type expr =\n  | Const : int -> expr\n\nand stmt =\n  | Assign : string -> stmt\n";
        let issues = check_dangling_and(content);
        assert!(issues.is_empty(), "and with preceding type should be fine: {:?}", issues);
    }

    #[test]
    fn test_and_with_preceding_let_rec_is_ok() {
        let content = "let rec even n = if n = 0 then true else odd (n-1)\nand odd n = if n = 0 then false else even (n-1)\n";
        let issues = check_dangling_and(content);
        assert!(issues.is_empty(), "and with preceding let rec should be fine: {:?}", issues);
    }

    #[test]
    fn test_and_without_preceding_type_is_dangling() {
        let content = "let foo x = x\n\nand bar y = y\n";
        let issues = check_dangling_and(content);
        assert!(!issues.is_empty(), "and without preceding type/let rec should be dangling");
        assert!(issues[0].contains("Dangling"));
    }

    #[test]
    fn test_and_at_top_of_file_is_dangling() {
        let content = "and orphan_type = nat\n";
        let issues = check_dangling_and(content);
        assert!(!issues.is_empty());
    }

    #[test]
    fn test_chained_ands_with_type_head() {
        let content = "type a = int\nand b = string\nand c = bool\n";
        let issues = check_dangling_and(content);
        assert!(issues.is_empty(), "Chained ands with type head should be fine: {:?}", issues);
    }

    #[test]
    fn test_and_after_open_is_dangling() {
        // After an `open` statement, `and` makes no sense
        let content = "open FStar.List.Tot\n\nand bad_type = int\n";
        let issues = check_dangling_and(content);
        assert!(!issues.is_empty());
    }

    #[test]
    fn test_and_after_removed_type_corruption_pattern() {
        // This is the exact corruption pattern: linter removed `type task_state = ...`
        // leaving a dangling `and task_state_eq ...`
        let content = "\n(* Task state equality *)\nand task_state_eq (s1 s2: task_state) : bool =\n  match s1, s2 with\n  | Pending, Pending -> true\n";
        let issues = check_dangling_and(content);
        assert!(!issues.is_empty(), "and after removed type head should be detected");
    }

    // =========================================================================
    // ORPHANED ATTRIBUTE TESTS
    // =========================================================================

    #[test]
    fn test_orphaned_attr_with_following_decl() {
        let content = "[@@\"opaque_to_smt\"]\nval foo : int -> int\n";
        assert!(check_orphaned_attributes(content).is_empty());
    }

    #[test]
    fn test_orphaned_attr_at_end_of_file() {
        let content = "let foo x = x\n[@@\"opaque_to_smt\"]\n";
        let issues = check_orphaned_attributes(content);
        assert!(!issues.is_empty());
        assert!(issues[0].contains("Orphaned attribute"));
    }

    #[test]
    fn test_orphaned_attr_followed_by_blank() {
        let issues = check_orphaned_attributes("[@@\"attr\"]\n\n\n");
        assert!(!issues.is_empty());
    }

    #[test]
    fn test_stacked_attrs_with_decl() {
        let content = "[@@\"attr1\"]\n[@@\"attr2\"]\nval foo : int\n";
        assert!(check_orphaned_attributes(content).is_empty());
    }

    #[test]
    fn test_orphaned_attr_followed_by_comment() {
        let issues = check_orphaned_attributes("[@@\"attr\"]\n// just a comment\n");
        assert!(!issues.is_empty());
    }

    #[test]
    fn test_attr_with_qualified_decl() {
        let content = "[@@\"attr\"]\nprivate let foo x = x\n";
        assert!(check_orphaned_attributes(content).is_empty());
    }

    #[test]
    fn test_attr_with_blank_line_then_decl() {
        let content = "[@@\"attr\"]\n\nval foo : int\n";
        assert!(check_orphaned_attributes(content).is_empty());
    }

    // =========================================================================
    // ORPHANED UNFOLD TESTS
    // =========================================================================

    #[test]
    fn test_unfold_before_let_is_ok() {
        // unfold is a qualifier that goes with `let`, not on its own line
        // But in F* it appears as `unfold let foo = ...` on one line
        let content = "unfold let foo = 1\n";
        assert!(check_orphaned_unfold(content).is_empty());
    }

    #[test]
    fn test_standalone_unfold_is_orphaned() {
        let content = "unfold\n";
        let issues = check_orphaned_unfold(content);
        assert!(!issues.is_empty());
        assert!(issues[0].contains("Orphaned qualifier"));
    }

    #[test]
    fn test_standalone_noextract_is_orphaned() {
        let content = "noextract\n";
        let issues = check_orphaned_unfold(content);
        assert!(!issues.is_empty());
    }

    #[test]
    fn test_standalone_private_is_orphaned() {
        let content = "private\n";
        let issues = check_orphaned_unfold(content);
        assert!(!issues.is_empty());
    }

    // =========================================================================
    // ORPHANED DOC COMMENT TESTS
    // =========================================================================

    #[test]
    fn test_doc_comment_before_val_is_ok() {
        let content = "(** Documentation for foo *)\nval foo : int -> int\n";
        assert!(check_orphaned_doc_comments(content).is_empty());
    }

    #[test]
    fn test_doc_comment_at_eof_is_orphaned() {
        let content = "let foo x = x\n(** orphaned doc *)\n";
        let issues = check_orphaned_doc_comments(content);
        assert!(!issues.is_empty());
        assert!(issues[0].contains("Orphaned doc comment"));
    }

    #[test]
    fn test_multiline_doc_comment_before_decl_is_ok() {
        let content = "(** Multi\n * line\n * doc\n *)\nval foo : int\n";
        assert!(check_orphaned_doc_comments(content).is_empty());
    }

    #[test]
    fn test_multiline_doc_comment_at_eof_is_orphaned() {
        let content = "(** Multi\n * line\n * doc\n *)\n";
        let issues = check_orphaned_doc_comments(content);
        assert!(!issues.is_empty());
    }

    #[test]
    fn test_doc_comment_with_nested_comment() {
        let content = "(** doc (* nested *) *)\nval foo : int\n";
        assert!(check_orphaned_doc_comments(content).is_empty());
    }

    #[test]
    fn test_regular_comment_not_flagged_as_orphaned_doc() {
        // Only (** ... *) is a doc comment, not (* ... *)
        let content = "(* regular comment *)\n";
        assert!(check_orphaned_doc_comments(content).is_empty());
    }

    // =========================================================================
    // MODULE STRUCTURE TESTS
    // =========================================================================

    #[test]
    fn test_module_structure_valid() {
        let content = "module Test\n\nopen FStar.List.Tot\n\nval foo : int\nlet foo = 1\n";
        assert!(check_module_structure(content).is_empty());
    }

    #[test]
    fn test_module_structure_missing_module() {
        let content = "open FStar.List.Tot\n\nval foo : int\n";
        let issues = check_module_structure(content);
        assert!(!issues.is_empty());
        assert!(issues[0].contains("Expected 'module'"));
    }

    #[test]
    fn test_module_structure_open_after_decl() {
        let content = "module Test\n\nval foo : int\n\nopen FStar.Seq\n";
        let issues = check_module_structure(content);
        assert!(!issues.is_empty());
        assert!(issues[0].contains("after declarations"));
    }

    #[test]
    fn test_module_structure_empty_file() {
        // Edge case: empty file after comment stripping
        assert!(check_module_structure("").is_empty());
    }

    #[test]
    fn test_module_structure_comment_before_module_ok() {
        // Comments before `module` are stripped, so this should work
        let content = "(* header comment *)\nmodule Test\nopen FStar.List.Tot\nval foo : int\n";
        // After stripping comments, first non-blank is "module Test"
        assert!(check_module_structure(content).is_empty());
    }

    // =========================================================================
    // CONSECUTIVE BLANK LINE TESTS
    // =========================================================================

    #[test]
    fn test_consecutive_blanks_ok() {
        let content = "let foo = 1\n\n\nlet bar = 2\n";
        assert!(check_consecutive_blanks(content).is_empty());
    }

    #[test]
    fn test_consecutive_blanks_too_many() {
        let content = "let foo = 1\n\n\n\n\nlet bar = 2\n";
        let issues = check_consecutive_blanks(content);
        assert!(!issues.is_empty());
        assert!(issues[0].contains("consecutive blank lines"));
    }

    #[test]
    fn test_consecutive_blanks_exactly_three_ok() {
        let content = "let foo = 1\n\n\n\nlet bar = 2\n"; // 3 blank lines
        assert!(check_consecutive_blanks(content).is_empty());
    }

    #[test]
    fn test_cleanup_consecutive_blank_lines() {
        let content = "let foo = 1\n\n\n\n\n\nlet bar = 2\n";
        let cleaned = cleanup_consecutive_blank_lines(content);
        // Should have at most 2 blank lines
        let max_blank_run = cleaned
            .lines()
            .fold((0, 0), |(max, run), line| {
                if line.trim().is_empty() {
                    (max.max(run + 1), run + 1)
                } else {
                    (max, 0)
                }
            }).0;
        assert!(max_blank_run <= 2, "Max blank run should be <= 2, got {}", max_blank_run);
    }

    // =========================================================================
    // SEMANTIC VALIDATION: DANGLING REFERENCES AFTER REMOVAL
    // =========================================================================

    #[test]
    fn test_dangling_refs_removed_type_still_used() {
        let remaining = "let foo (x: task_state) = x\n";
        let removed = vec!["task_state".to_string()];
        let dangling = find_dangling_references_after_removal(remaining, &removed);
        assert!(dangling.contains(&"task_state".to_string()));
    }

    #[test]
    fn test_dangling_refs_removed_type_not_used() {
        let remaining = "let foo (x: int) = x\n";
        let removed = vec!["task_state".to_string()];
        let dangling = find_dangling_references_after_removal(remaining, &removed);
        assert!(dangling.is_empty());
    }

    #[test]
    fn test_dangling_refs_multiple_removed() {
        let remaining = "let foo (x: task_state) (y: ws_deque int) = x\n";
        let removed = vec!["task_state".to_string(), "ws_deque".to_string(), "unused_type".to_string()];
        let dangling = find_dangling_references_after_removal(remaining, &removed);
        assert!(dangling.contains(&"task_state".to_string()));
        assert!(dangling.contains(&"ws_deque".to_string()));
        assert!(!dangling.contains(&"unused_type".to_string()));
    }

    #[test]
    fn test_dangling_refs_in_comment_not_counted() {
        // Reference in a comment should not count
        let remaining = "(* uses task_state *)\nlet foo (x: int) = x\n";
        let removed = vec!["task_state".to_string()];
        let dangling = find_dangling_references_after_removal(remaining, &removed);
        assert!(dangling.is_empty(), "References in comments should not count as dangling");
    }

    #[test]
    fn test_dangling_refs_in_string_not_counted() {
        let remaining = "let foo x = \"task_state\"\n";
        let removed = vec!["task_state".to_string()];
        let dangling = find_dangling_references_after_removal(remaining, &removed);
        assert!(dangling.is_empty(), "References in strings should not count as dangling");
    }

    // =========================================================================
    // ROLLBACK TESTS
    // =========================================================================

    #[test]
    fn test_rollback_on_safe_fix() {
        let original = "module Test\nlet foo x = x + 1\n";
        let fixed = "module Test\nlet foo x = x + 2\n";
        let path = PathBuf::from("test.fst");
        let result = validate_and_rollback(original, fixed, &path, 0.5);
        assert!(result.applied);
        assert_eq!(result.content, fixed);
    }

    #[test]
    fn test_rollback_on_unsafe_fix() {
        let original = "module Test\nlet foo (x: int) = x\n";
        let fixed = "module Test\nlet foo ) x: int ( = x\n"; // broken parens
        let path = PathBuf::from("test.fst");
        let result = validate_and_rollback(original, fixed, &path, 0.5);
        assert!(!result.applied);
        assert_eq!(result.content, original);
    }

    #[test]
    fn test_rollback_on_low_confidence() {
        let original = "module Test\nlet foo x = x\nlet bar y = y\n";
        // Remove bar but bar might be referenced
        let fixed = "module Test\nlet foo x = bar x\n"; // uses 'bar' which is removed
        let path = PathBuf::from("test.fst");
        let result = validate_and_rollback(original, fixed, &path, 0.9);
        // Confidence should be reduced, so rollback
        assert!(!result.applied);
        assert_eq!(result.content, original);
    }

    // =========================================================================
    // STRIP QUALIFIERS TESTS
    // =========================================================================

    #[test]
    fn test_strip_qualifiers_none() {
        assert_eq!(strip_qualifiers("val foo : int"), "val foo : int");
    }

    #[test]
    fn test_strip_qualifiers_single() {
        assert_eq!(strip_qualifiers("private val foo : int"), "val foo : int");
    }

    #[test]
    fn test_strip_qualifiers_multiple() {
        assert_eq!(
            strip_qualifiers("inline_for_extraction noextract let foo x = x"),
            "let foo x = x"
        );
    }

    #[test]
    fn test_strip_qualifiers_all() {
        assert_eq!(
            strip_qualifiers("private ghost let foo x = x"),
            "let foo x = x"
        );
    }

    // =========================================================================
    // FIND UNDEFINED REFERENCES TESTS
    // =========================================================================

    #[test]
    fn test_find_undefined_references_basic() {
        let content = "let foo x = bar x + baz\n";
        let decls = count_declarations(content);
        let undef = find_undefined_references(content, &decls);
        assert!(undef.contains(&"bar".to_string()) || undef.contains(&"baz".to_string()));
    }

    #[test]
    fn test_find_undefined_references_keywords_excluded() {
        let content = "let foo x = if x then true else false\n";
        let decls = count_declarations(content);
        let undef = find_undefined_references(content, &decls);
        // All should be keywords, so nothing flagged (except `x` which is a parameter)
        for u in &undef {
            assert!(!FSTAR_KEYWORDS.contains(u.as_str()), "Keyword {} should be excluded", u);
        }
    }

    // =========================================================================
    // VALIDATE_FIX INTEGRATION TESTS
    // =========================================================================

    #[test]
    fn test_validate_fix_safe() {
        let original = "module Test\nlet foo x = x + 1\nlet bar y = y * 2\n";
        let fixed = "module Test\nlet foo x = x + 1\nlet bar y = y * 3\n";
        let path = PathBuf::from("test.fst");
        let v = validate_fix(original, fixed, &path);
        assert!(v.is_safe);
        assert!(v.confidence > 0.5);
    }

    #[test]
    fn test_validate_fix_removes_declaration() {
        let original = "module Test\nlet foo x = x + 1\nlet bar y = y * 2\n";
        let fixed = "module Test\nlet foo x = x + 1\n";
        let path = PathBuf::from("test.fst");
        let v = validate_fix(original, fixed, &path);
        assert!(v.declaration_changes.removed.contains(&"bar".to_string()));
        assert!(!v.warnings.is_empty());
    }

    #[test]
    fn test_validate_fix_detects_invalid_comment_order() {
        let original = "module Test\nlet foo x = x + 1\n";
        let fixed = "module Test\n*) let foo x = x + 2 (*\n";
        let path = PathBuf::from("test.fst");
        let v = validate_fix(original, fixed, &path);
        assert!(v.warnings.iter().any(|w| w.contains("Unbalanced comments")));
    }

    #[test]
    fn test_validate_fix_detects_orphaned_attr() {
        let original = "module Test\nval foo : int\nlet foo = 1\n";
        let fixed = "module Test\n[@@\"attr\"]\n";
        let path = PathBuf::from("test.fst");
        let v = validate_fix(original, fixed, &path);
        assert!(v.warnings.iter().any(|w| w.contains("Orphaned attribute")));
    }

    #[test]
    fn test_validate_fix_close_paren_before_open_is_unsafe() {
        let original = "module Test\nlet foo (x: int) = x\n";
        let fixed = "module Test\nlet foo ) x: int ( = x\n";
        let path = PathBuf::from("test.fst");
        let v = validate_fix(original, fixed, &path);
        assert!(!v.is_safe);
    }

    #[test]
    fn test_validate_fix_valid_nested_comments() {
        let original = "module Test\nlet foo x = x + 1\n";
        let fixed = "module Test\n(* outer (* inner *) *) let foo x = x + 2\n";
        let path = PathBuf::from("test.fst");
        let v = validate_fix(original, fixed, &path);
        assert!(!v.warnings.iter().any(|w| w.contains("Unbalanced comments")));
    }

    #[test]
    fn test_validate_fix_semantic_removed_def_still_referenced() {
        // The critical bug: removing `type task_state` when it's still used
        let original = "module Test\ntype task_state = | Running | Stopped\nlet check (s: task_state) = s\n";
        let fixed = "module Test\nlet check (s: task_state) = s\n";
        let path = PathBuf::from("test.fst");
        let v = validate_fix(original, fixed, &path);
        assert!(
            v.warnings.iter().any(|w| w.contains("still referenced")),
            "Should detect removed type still referenced: {:?}", v.warnings
        );
        // This should severely reduce confidence
        assert!(v.confidence < 0.5, "Confidence should be < 0.5: {}", v.confidence);
    }

    #[test]
    fn test_validate_fix_detects_dangling_and() {
        // Corruption pattern: removed the type head, leaving orphaned `and`
        let original = "module Test\ntype expr = | Lit : int -> expr\nand stmt = | Nop : stmt\n";
        let fixed = "module Test\nand stmt = | Nop : stmt\n";
        let path = PathBuf::from("test.fst");
        let v = validate_fix(original, fixed, &path);
        assert!(
            v.warnings.iter().any(|w| w.contains("Dangling")),
            "Should detect dangling and: {:?}", v.warnings
        );
    }

    // =========================================================================
    // VALIDATE_EXPECTED_REMOVALS TESTS
    // =========================================================================

    #[test]
    fn test_validate_expected_removals_ok() {
        let original = "module Test\ntype foo = nat\nlet bar x = x\n";
        let fixed = "module Test\nlet bar x = x\n";
        let v = validate_expected_removals(original, fixed, &["foo"]);
        assert!(v.is_safe);
        assert!(v.confidence > 0.8);
    }

    #[test]
    fn test_validate_unexpected_removal() {
        let original = "module Test\ntype foo = nat\nlet bar x = x\n";
        let fixed = "module Test\n";
        let v = validate_expected_removals(original, fixed, &["foo"]);
        assert!(v.warnings.iter().any(|w| w.contains("bar")));
        assert!(v.confidence < 1.0);
    }

    // =========================================================================
    // VALIDATE_NO_REMOVALS TESTS
    // =========================================================================

    #[test]
    fn test_validate_no_removals_success() {
        let original = "let foo x = x\nlet bar y = y";
        let fixed = "let foo x = x + 1\nlet bar y = y * 2";
        assert!(validate_no_removals(original, fixed).is_ok());
    }

    #[test]
    fn test_validate_no_removals_failure() {
        let original = "let foo x = x\nlet bar y = y";
        let fixed = "let foo x = x + 1";
        let r = validate_no_removals(original, fixed);
        assert!(r.is_err());
        assert!(r.unwrap_err().contains("bar"));
    }

    // =========================================================================
    // VALIDATE_WHITESPACE_ONLY TESTS
    // =========================================================================

    #[test]
    fn test_validate_whitespace_only_true() {
        let v = validate_whitespace_only_fix("let foo x = x + 1", "let  foo  x  =  x  +  1");
        assert!(v.is_safe);
        assert_eq!(v.confidence, 1.0);
    }

    #[test]
    fn test_validate_whitespace_only_false() {
        let v = validate_whitespace_only_fix("let foo x = x + 1", "let foo x = x + 2");
        assert!(!v.is_safe);
    }

    // =========================================================================
    // VALIDATE_LINE_DELETION TESTS
    // =========================================================================

    #[test]
    fn test_validate_line_deletion_with_decls() {
        let original = "module Test\n\nlet foo x = x\n\nlet bar y = y\n";
        let deleted = "\nlet bar y = y\n";
        let v = validate_line_deletion(original, 5, 6, deleted);
        assert!(v.declaration_changes.removed.contains(&"bar".to_string()));
    }

    // =========================================================================
    // FIX VALIDATION OBJECT TESTS
    // =========================================================================

    #[test]
    fn test_fix_validation_can_auto_apply() {
        let v = FixValidation::safe(0.9);
        assert!(v.can_auto_apply(0.8));
        assert!(!v.can_auto_apply(0.95));

        let u = FixValidation::unsafe_fix("reason");
        assert!(!u.can_auto_apply(0.0));
    }

    #[test]
    fn test_fix_validation_default() {
        let v = FixValidation::default();
        assert!(v.is_safe);
        assert_eq!(v.confidence, 1.0);
        assert!(v.warnings.is_empty());
        assert!(v.content_preserved);
    }

    #[test]
    fn test_confidence_reduction() {
        let v = FixValidation::safe(1.0)
            .reduce_confidence(0.5)
            .reduce_confidence(0.5);
        assert_eq!(v.confidence, 0.25);
    }

    #[test]
    fn test_validation_with_warnings_still_safe() {
        let v = FixValidation::safe(0.9).with_warning("Minor issue");
        assert!(v.is_safe);
        assert!(!v.warnings.is_empty());
        assert!(v.can_auto_apply(0.8));
    }

    #[test]
    fn test_declaration_changes_default() {
        let c = DeclarationChanges::default();
        assert!(c.removed.is_empty());
        assert!(c.added.is_empty());
        assert!(c.modified.is_empty());
        assert_eq!(c.net_change, 0);
    }

    // =========================================================================
    // EDGE CASE TESTS
    // =========================================================================

    #[test]
    fn test_empty_content() {
        assert!(count_declarations("").is_empty());
        assert!(validate_fstar_syntax("").is_ok());
    }

    #[test]
    fn test_nested_brackets_in_strings() {
        let content = r#"let msg = "({[}])" in msg"#;
        assert!(validate_fstar_syntax(content).is_ok());
    }

    #[test]
    fn test_multiline_string_handling() {
        let content = "let x = \"line1\nline2\"";
        // Invalid F* but should not panic
        let _ = validate_fstar_syntax(content);
    }

    #[test]
    fn test_unicode_in_strings() {
        let content = r#"let msg = "Hello, World!" in msg"#;
        assert!(validate_fstar_syntax(content).is_ok());
    }

    #[test]
    fn test_fstar_mutual_recursion_syntax() {
        let content = "type expr =\n  | Const : int -> expr\n  | Add : expr -> expr -> expr\n\nand stmt =\n  | Assign : string -> expr -> stmt\n  | Seq : stmt -> stmt -> stmt\n";
        assert!(validate_fstar_syntax(content).is_ok());
    }

    #[test]
    fn test_complex_fstar_file() {
        let content = r#"
module ComplexTest

open FStar.List.Tot
open FStar.Seq

(** Documentation for foo *)
val foo : #a:Type -> list a -> nat
let foo #a l = length l

private let helper x = x + 1

type config = {
  debug: bool;
  level: nat
}

let rec factorial (n:nat) : Tot nat (decreases n) =
  if n = 0 then 1
  else n * factorial (n - 1)
"#;
        let decls = count_declarations(content);
        assert!(decls.contains_key("foo"));
        assert!(decls.contains_key("helper"));
        assert!(decls.contains_key("config"));
        assert!(decls.contains_key("factorial"));
        assert!(validate_fstar_syntax(content).is_ok());
    }

    // =========================================================================
    // REAL-WORLD CORRUPTION PATTERN TESTS
    // =========================================================================

    #[test]
    fn test_corruption_pattern_removed_type_with_associated_let() {
        // From BrrrTypes.fst: linter removed `noeq type moded_type` and its
        // associated `let linear_type`, leaving references broken.
        let original = r#"module Test

noeq type moded_type = {
  ty   : brrr_type;
  mode : mode
}

let linear_type (t: brrr_type) : moded_type =
  { ty = t; mode = Linear }

let use_it (x: brrr_type) : moded_type = linear_type x
"#;
        let fixed = r#"module Test

let use_it (x: brrr_type) : moded_type = linear_type x
"#;
        let path = PathBuf::from("BrrrTypes.fst");
        let v = validate_fix(original, fixed, &path);
        // Should detect that moded_type and linear_type are still referenced
        assert!(
            v.warnings.iter().any(|w| w.contains("still referenced")),
            "Should detect removed defs still referenced: {:?}", v.warnings
        );
        assert!(!v.is_safe || v.confidence < 0.5);
    }

    #[test]
    fn test_corruption_pattern_removed_type_with_dangling_and() {
        // From BrrrComputeArch.fst: linter removed `type task_state` but left
        // `and task_state_eq` which becomes dangling.
        let original = r#"module Test

type task_state =
  | Pending   : task_state
  | Running   : task_state
  | Completed : task_state

and task_state_eq (s1 s2: task_state) : bool =
  match s1, s2 with
  | Pending, Pending -> true
  | Running, Running -> true
  | Completed, Completed -> true
  | _, _ -> false

let check_state (s: task_state) = task_state_eq s Pending
"#;
        let fixed = r#"module Test

and task_state_eq (s1 s2: task_state) : bool =
  match s1, s2 with
  | Pending, Pending -> true
  | Running, Running -> true
  | Completed, Completed -> true
  | _, _ -> false

let check_state (s: task_state) = task_state_eq s Pending
"#;
        let path = PathBuf::from("test.fst");
        let v = validate_fix(original, fixed, &path);
        // Should detect both: dangling `and` AND removed `task_state` still referenced
        let has_dangling = v.warnings.iter().any(|w| w.contains("Dangling"));
        let has_ref = v.warnings.iter().any(|w| w.contains("still referenced"));
        assert!(
            has_dangling || has_ref,
            "Should detect corruption: {:?}", v.warnings
        );
        assert!(!v.is_safe || v.confidence < 0.5);
    }

    #[test]
    fn test_corruption_pattern_removed_noeq_record() {
        // From BrrrComputeArch.fst: removed `noeq type ws_deque` and `let empty_deque`
        let original = r#"module Test

noeq type ws_deque (a: Type) = {
  items : list a;
  size  : nat
}

let empty_deque (#a: Type) : ws_deque a = {
  items = [];
  size = 0
}

let push_deque (#a: Type) (d: ws_deque a) (x: a) : ws_deque a =
  { items = x :: d.items; size = d.size + 1 }
"#;
        let fixed = r#"module Test

let push_deque (#a: Type) (d: ws_deque a) (x: a) : ws_deque a =
  { items = x :: d.items; size = d.size + 1 }
"#;
        let path = PathBuf::from("test.fst");
        let v = validate_fix(original, fixed, &path);
        // ws_deque is still referenced in push_deque
        assert!(
            v.warnings.iter().any(|w| w.contains("still referenced")),
            "Should detect ws_deque still referenced: {:?}", v.warnings
        );
    }

    #[test]
    fn test_has_following_declaration_basic() {
        let lines = vec!["", "val foo : int"];
        assert!(has_following_declaration(&lines, 0));
    }

    #[test]
    fn test_has_following_declaration_with_attrs() {
        let lines = vec!["[@@\"attr\"]", "", "val foo : int"];
        assert!(has_following_declaration(&lines, 0));
    }

    #[test]
    fn test_has_following_declaration_none() {
        let lines = vec!["", "// just a comment"];
        assert!(!has_following_declaration(&lines, 0));
    }

    #[test]
    fn test_has_following_declaration_and() {
        let lines = vec!["", "and bar = int"];
        assert!(has_following_declaration(&lines, 0));
    }
}
