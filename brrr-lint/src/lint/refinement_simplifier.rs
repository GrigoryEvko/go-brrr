//! FST012: Refinement type simplifier.
//!
//! Detects refinement types that can be simplified or are problematic:
//!
//! 1. `x:nat{x >= 0}` - redundant, `nat` already implies `>= 0` (SAFE AUTO-FIX)
//! 2. `x:int{x >= 0}` - can be simplified to `nat` (SUGGESTION ONLY - type change!)
//! 3. `x:int{x > 0}` - can be simplified to `pos` (SUGGESTION ONLY - type change!)
//! 4. `x:pos{x > 0}` - redundant, `pos` already implies `> 0` (SAFE AUTO-FIX)
//! 5. `x:T{True}` - useless refinement (SAFE AUTO-FIX)
//! 6. `x:int{x > 5 /\ x < 3}` - unsatisfiable refinement (ERROR, no fix)
//!
//! ## Semantic Equivalence and Safety
//!
//! This rule is CONSERVATIVE by design. Type simplifications (int->nat, int->pos)
//! are marked as UNSAFE for auto-fix because:
//! - Changing types can break type inference in dependent code
//! - The verbose form might be intentional for documentation/clarity
//! - F* type unification may behave differently with aliased types
//!
//! Redundant refinement removals (nat{x >= 0} -> nat) are SAFE because:
//! - The base type remains unchanged
//! - The removed constraint is already implied by the type
//! - No semantic change occurs
//!
//! ## Semantic Equivalence Validation
//!
//! We use EXACT STRING MATCHING for refinement bodies, NOT substring matching:
//! - `x >= 0` matches ONLY the exact constraint (after whitespace trimming)
//! - `x >= 0 /\ x < 100` does NOT match (compound constraint, not equivalent to nat)
//! - `0 <= x` does NOT match (different syntactic form, even if semantically equal)
//!
//! This prevents false positives on compound refinements where simplification
//! would lose constraints.
//!
//! ## Guards Against False Positives
//!
//! - Matches inside string literals (`"..."`) are skipped.
//! - Matches inside inline block comments (`(* ... *)`) are skipped.
//! - Unsatisfiable detection only fires inside refinement braces.
//! - The old `nat{x < pow2 32}` -> `UInt32.t` suggestion was REMOVED because
//!   `nat` and machine integers have fundamentally different semantics in F*.

use lazy_static::lazy_static;
use regex::Regex;
use std::path::Path;

use super::rules::{Diagnostic, DiagnosticSeverity, Edit, Fix, FixConfidence, FixSafetyLevel, Range, Rule, RuleCode};

lazy_static! {
    /// General refinement pattern: captures (var_name, base_type, refinement_body)
    static ref REFINEMENT: Regex = Regex::new(
        r"(\w+)\s*:\s*(\w+)\s*\{([^}]+)\}"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Useless: T{True} refinement
    static ref TRUE_REFINEMENT: Regex = Regex::new(
        r"(\w+)\s*:\s*(\w+)\s*\{\s*True\s*\}"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Unsatisfiable: var > N /\ var < M inside a refinement
    static ref UNSAT_GT_LT: Regex = Regex::new(
        r"(\w+)\s*>\s*(\d+)\s*/\\\s*(\w+)\s*<\s*(\d+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Unsatisfiable: var < N /\ var > M inside a refinement (reversed order)
    static ref UNSAT_LT_GT: Regex = Regex::new(
        r"(\w+)\s*<\s*(\d+)\s*/\\\s*(\w+)\s*>\s*(\d+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect squash (x == y) pattern that may be simplifiable
    static ref SQUASH_EQ: Regex = Regex::new(
        r"\bsquash\s*\(\s*(\w+)\s*==\s*(\w+)\s*\)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect erased (erased t) double-wrapping
    static ref DOUBLE_ERASED: Regex = Regex::new(
        r"\berased\s*\(\s*erased\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect Ghost.reveal (Ghost.hide x) round-trip
    static ref REVEAL_HIDE: Regex = Regex::new(
        r"(?:Ghost\.)?reveal\s*\(\s*(?:Ghost\.)?hide\s+(\w+)\s*\)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect Ghost.hide (Ghost.reveal x) round-trip
    static ref HIDE_REVEAL: Regex = Regex::new(
        r"(?:Ghost\.)?hide\s*\(\s*(?:Ghost\.)?reveal\s+(\w+)\s*\)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect redundant `x:Type0{True}` patterns with Type0 base
    static ref TYPE0_TRUE: Regex = Regex::new(
        r"(\w+)\s*:\s*Type0?\s*\{\s*True\s*\}"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect `{False}` refinement - always unsatisfiable (empty type)
    static ref FALSE_REFINEMENT: Regex = Regex::new(
        r"(\w+)\s*:\s*(\w+)\s*\{\s*False\s*\}"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect `x >= N /\ x < N` unsatisfiable (strict upper bound equals lower bound)
    static ref UNSAT_GTE_LT: Regex = Regex::new(
        r"(\w+)\s*>=\s*(\d+)\s*/\\\s*(\w+)\s*<\s*(\d+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect `x > N /\ x <= N` unsatisfiable (strict lower bound equals upper bound)
    static ref UNSAT_GT_LTE: Regex = Regex::new(
        r"(\w+)\s*>\s*(\d+)\s*/\\\s*(\w+)\s*<=\s*(\d+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect `x = N /\ x <> N` (or `x <> N /\ x = N`) unsatisfiable
    static ref UNSAT_EQ_NEQ: Regex = Regex::new(
        r"(\w+)\s*=\s*(\d+)\s*/\\\s*(\w+)\s*<>\s*(\d+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect reversed comparison: `0 <= x` which is equivalent to `x >= 0`
    static ref REVERSED_GTE_ZERO: Regex = Regex::new(
        r"(\w+)\s*:\s*int\s*\{\s*0\s*<=\s*(\w+)\s*\}"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Detect `nat{x <> 0}` which is equivalent to `pos`
    static ref NAT_NEQ_ZERO: Regex = Regex::new(
        r"(\w+)\s*:\s*nat\s*\{\s*(\w+)\s*<>\s*0\s*\}"
    ).unwrap_or_else(|e| panic!("regex: {e}"));
}

/// Convert byte offset to character column (1-indexed).
///
/// This is necessary because regex matches return byte offsets, but LSP
/// and editor columns are character-based. For ASCII this is the same,
/// but for UTF-8 multi-byte characters they differ.
fn byte_to_char_col(s: &str, byte_offset: usize) -> usize {
    s[..byte_offset.min(s.len())].chars().count() + 1
}

/// Check if a byte offset falls inside a string literal or inline block comment.
///
/// Scans the line left-to-right tracking whether we are inside `"..."` or `(* ... *)`.
/// Returns `true` if the given byte position is inside either construct, meaning
/// any regex match at that position should be suppressed as a false positive.
///
/// State machine: Normal -> InString -> InBlockComment -> InLineComment
/// - `//` outside strings and block comments means the rest of the line is a comment
/// - Inside block comments, `//` is just text (F*/OCaml convention)
fn is_inside_string_or_comment(line: &str, byte_offset: usize) -> bool {
    let bytes = line.as_bytes();
    let mut in_string = false;
    let mut in_block_comment = false;
    let mut in_line_comment = false;
    let mut i = 0;

    while i < bytes.len() && i < byte_offset {
        if in_line_comment {
            // Everything until end of line is a comment
            i += 1;
            continue;
        }
        if in_string {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                // Skip escaped character inside string
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
        } else if in_block_comment {
            if bytes[i] == b'*' && i + 1 < bytes.len() && bytes[i + 1] == b')' {
                in_block_comment = false;
                i += 2;
                continue;
            }
        } else {
            // Normal state
            if bytes[i] == b'"' {
                in_string = true;
            } else if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
                // Line comment: everything from here to end of line is a comment
                in_line_comment = true;
                i += 2;
                continue;
            } else if bytes[i] == b'(' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
                in_block_comment = true;
                i += 2;
                continue;
            }
        }
        i += 1;
    }

    in_string || in_block_comment || in_line_comment
}

/// FST012: Refinement Type Simplifier
///
/// Analyzes F* refinement types and suggests simplifications or
/// detects unsatisfiable constraints.
pub struct RefinementSimplifierRule;

impl RefinementSimplifierRule {
    pub fn new() -> Self {
        Self
    }

    /// Check if refinement body is just "var >= 0"
    fn is_gte_zero_refinement(var_name: &str, body: &str) -> bool {
        let trimmed = body.trim();
        let pattern = format!("{} >= 0", var_name);
        trimmed == pattern || trimmed == format!("{}>=0", var_name)
    }

    /// Check if refinement body is just "var > 0"
    fn is_gt_zero_refinement(var_name: &str, body: &str) -> bool {
        let trimmed = body.trim();
        let pattern = format!("{} > 0", var_name);
        trimmed == pattern || trimmed == format!("{}>0", var_name)
    }

    /// Check for redundant nat{x >= 0} refinements.
    fn check_redundant_nat(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            for caps in REFINEMENT.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }

                let var_name = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                let base_type = caps.get(2).map(|m| m.as_str()).unwrap_or("");
                let body = caps.get(3).map(|m| m.as_str()).unwrap_or("");

                if base_type == "nat" && Self::is_gte_zero_refinement(var_name, body) {
                    let start_col = byte_to_char_col(line, full_match.start());
                    let end_col = byte_to_char_col(line, full_match.end());

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST012,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::new(line_num, start_col, line_num, end_col),
                        message: format!(
                            "Redundant refinement: `nat` is defined as `x:int{{x >= 0}}`, \
                             so `{} >= 0` adds no constraint. Use `{}:nat` instead.",
                            var_name, var_name
                        ),
                        // SAFE: Removing redundant constraint, type stays the same.
                        // No semantic change - nat already implies >= 0.
                        fix: Some(Fix::safe(
                            "Remove redundant refinement (safe: type unchanged)",
                            vec![Edit {
                                file: file.to_path_buf(),
                                range: Range::new(line_num, start_col, line_num, end_col),
                                new_text: format!("{}:nat", var_name),
                            }],
                        )
                        .with_safety_level(FixSafetyLevel::Safe)  // Type unchanged
                        .with_reversible(true)  // Can add refinement back
                        .with_requires_review(false)),  // Safe transformation
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for redundant pos{x > 0} refinements.
    fn check_redundant_pos(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            for caps in REFINEMENT.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }

                let var_name = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                let base_type = caps.get(2).map(|m| m.as_str()).unwrap_or("");
                let body = caps.get(3).map(|m| m.as_str()).unwrap_or("");

                if base_type == "pos" && Self::is_gt_zero_refinement(var_name, body) {
                    let start_col = byte_to_char_col(line, full_match.start());
                    let end_col = byte_to_char_col(line, full_match.end());

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST012,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::new(line_num, start_col, line_num, end_col),
                        message: format!(
                            "Redundant refinement: `pos` is defined as `x:int{{x > 0}}`, \
                             so `{} > 0` adds no constraint. Use `{}:pos` instead.",
                            var_name, var_name
                        ),
                        // SAFE: Removing redundant constraint, type stays the same.
                        // No semantic change - pos already implies > 0.
                        fix: Some(Fix::safe(
                            "Remove redundant refinement (safe: type unchanged)",
                            vec![Edit {
                                file: file.to_path_buf(),
                                range: Range::new(line_num, start_col, line_num, end_col),
                                new_text: format!("{}:pos", var_name),
                            }],
                        )
                        .with_safety_level(FixSafetyLevel::Safe)  // Type unchanged
                        .with_reversible(true)  // Can add refinement back
                        .with_requires_review(false)),  // Safe transformation
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for useless {True} refinements.
    fn check_true_refinement(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            // Use captures_iter to catch ALL occurrences on a line, not just the first.
            for caps in TRUE_REFINEMENT.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }

                let var_name = caps.get(1).map(|m| m.as_str()).unwrap_or("x");
                let type_name = caps.get(2).map(|m| m.as_str()).unwrap_or("T");
                let start_col = byte_to_char_col(line, full_match.start());
                let end_col = byte_to_char_col(line, full_match.end());

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST012,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::new(line_num, start_col, line_num, end_col),
                    message: format!(
                        "Useless refinement: `{{True}}` is always satisfied, adding no constraint. \
                         Use `{}:{}` instead.",
                        var_name, type_name
                    ),
                    // SAFE: True is always satisfied, removing it changes nothing.
                    fix: Some(Fix::safe(
                        "Remove useless {True} refinement (safe: True is tautology)",
                        vec![Edit {
                            file: file.to_path_buf(),
                            range: Range::new(line_num, start_col, line_num, end_col),
                            new_text: format!("{}:{}", var_name, type_name),
                        }],
                    )
                    .with_safety_level(FixSafetyLevel::Safe)  // True is tautology
                    .with_reversible(true)  // Can add {True} back
                    .with_requires_review(false)),  // Safe transformation
                });
            }
        }

        diagnostics
    }

    /// Check for int{x >= 0} that could be nat.
    fn check_int_to_nat(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            for caps in REFINEMENT.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }

                let var_name = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                let base_type = caps.get(2).map(|m| m.as_str()).unwrap_or("");
                let body = caps.get(3).map(|m| m.as_str()).unwrap_or("");

                if base_type == "int" && Self::is_gte_zero_refinement(var_name, body) {
                    let start_col = byte_to_char_col(line, full_match.start());
                    let end_col = byte_to_char_col(line, full_match.end());

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST012,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::new(line_num, start_col, line_num, end_col),
                        message: format!(
                            "Consider using `nat` instead of `int{{{} >= 0}}`. \
                             The `nat` type is defined as `x:int{{x >= 0}}` in Prims. \
                             NOTE: This changes the type, which may affect type inference. \
                             Keep the verbose form if it aids documentation or if dependent \
                             code expects the explicit refinement.",
                            var_name
                        ),
                        // UNSAFE: This CHANGES THE TYPE from int{...} to nat.
                        // While semantically equivalent, this can affect:
                        // - Type inference in dependent code
                        // - Code that pattern-matches on the type
                        // - Documentation intent (verbose form may be clearer)
                        fix: Some(Fix::unsafe_fix(
                            "Use nat instead of int{x >= 0} (CAUTION: changes type)",
                            vec![Edit {
                                file: file.to_path_buf(),
                                range: Range::new(line_num, start_col, line_num, end_col),
                                new_text: format!("{}:nat", var_name),
                            }],
                            FixConfidence::Low,
                            "Type change from int{...} to nat may affect type inference",
                        )
                        .with_safety_level(FixSafetyLevel::Caution)  // Type changes require review
                        .with_reversible(true)  // Can change back to int{x >= 0}
                        .with_requires_review(true)),  // Always review type changes
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for int{x > 0} that could be pos.
    fn check_int_to_pos(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            for caps in REFINEMENT.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }

                let var_name = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                let base_type = caps.get(2).map(|m| m.as_str()).unwrap_or("");
                let body = caps.get(3).map(|m| m.as_str()).unwrap_or("");

                if base_type == "int" && Self::is_gt_zero_refinement(var_name, body) {
                    let start_col = byte_to_char_col(line, full_match.start());
                    let end_col = byte_to_char_col(line, full_match.end());

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST012,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::new(line_num, start_col, line_num, end_col),
                        message: format!(
                            "Consider using `pos` instead of `int{{{} > 0}}`. \
                             The `pos` type is defined as `x:int{{x > 0}}` in Prims. \
                             NOTE: This changes the type, which may affect type inference. \
                             Keep the verbose form if it aids documentation or if dependent \
                             code expects the explicit refinement.",
                            var_name
                        ),
                        // UNSAFE: This CHANGES THE TYPE from int{...} to pos.
                        // While semantically equivalent, this can affect:
                        // - Type inference in dependent code
                        // - Code that pattern-matches on the type
                        // - Documentation intent (verbose form may be clearer)
                        fix: Some(Fix::unsafe_fix(
                            "Use pos instead of int{x > 0} (CAUTION: changes type)",
                            vec![Edit {
                                file: file.to_path_buf(),
                                range: Range::new(line_num, start_col, line_num, end_col),
                                new_text: format!("{}:pos", var_name),
                            }],
                            FixConfidence::Low,
                            "Type change from int{...} to pos may affect type inference",
                        )
                        .with_safety_level(FixSafetyLevel::Caution)  // Type changes require review
                        .with_reversible(true)  // Can change back to int{x > 0}
                        .with_requires_review(true)),  // Always review type changes
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for unsatisfiable refinements like x > 5 /\ x < 3.
    ///
    /// Only fires when the contradictory pattern is found inside a refinement
    /// brace `{...}`, preventing false positives on bare assertions or comments.
    /// Uses pre-compiled regexes from `lazy_static!`.
    fn check_unsatisfiable(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            // Only search inside refinement bodies to avoid false positives
            // on assertions like `assert (x > 5 /\ x < 3)`.
            for ref_caps in REFINEMENT.captures_iter(line) {
                let Some(ref_match) = ref_caps.get(0) else { continue };
                if is_inside_string_or_comment(line, ref_match.start()) {
                    continue;
                }
                let body = ref_caps.get(3).map(|m| m.as_str()).unwrap_or("");
                let Some(body_group) = ref_caps.get(3) else { continue };
                let body_start_byte = body_group.start();

                // Check "var > N /\ var < M" inside the refinement body
                for caps in UNSAT_GT_LT.captures_iter(body) {
                    let var1 = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                    let var2 = caps.get(3).map(|m| m.as_str()).unwrap_or("");
                    if var1 != var2 {
                        continue;
                    }
                    if let (Ok(lower), Ok(upper)) = (
                        caps.get(2).map_or("", |m| m.as_str()).parse::<i64>(),
                        caps.get(4).map_or("", |m| m.as_str()).parse::<i64>(),
                    ) {
                        if lower >= upper {
                            let inner = { let Some(m) = caps.get(0) else { continue }; m };
                            let start_col =
                                byte_to_char_col(line, body_start_byte + inner.start());
                            let end_col =
                                byte_to_char_col(line, body_start_byte + inner.end());

                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST012,
                                severity: DiagnosticSeverity::Error,
                                file: file.to_path_buf(),
                                range: Range::new(line_num, start_col, line_num, end_col),
                                message: format!(
                                    "UNSATISFIABLE REFINEMENT: No value can satisfy \
                                     `{} > {} /\\ {} < {}`. \
                                     This constraint is logically impossible.",
                                    var1, lower, var2, upper
                                ),
                                fix: None,
                            });
                        }
                    }
                }

                // Check "var < N /\ var > M" (reversed order) inside the body
                for caps in UNSAT_LT_GT.captures_iter(body) {
                    let var1 = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                    let var2 = caps.get(3).map(|m| m.as_str()).unwrap_or("");
                    if var1 != var2 {
                        continue;
                    }
                    if let (Ok(upper), Ok(lower)) = (
                        caps.get(2).map_or("", |m| m.as_str()).parse::<i64>(),
                        caps.get(4).map_or("", |m| m.as_str()).parse::<i64>(),
                    ) {
                        if lower >= upper {
                            let inner = { let Some(m) = caps.get(0) else { continue }; m };
                            let start_col =
                                byte_to_char_col(line, body_start_byte + inner.start());
                            let end_col =
                                byte_to_char_col(line, body_start_byte + inner.end());

                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST012,
                                severity: DiagnosticSeverity::Error,
                                file: file.to_path_buf(),
                                range: Range::new(line_num, start_col, line_num, end_col),
                                message: format!(
                                    "UNSATISFIABLE REFINEMENT: No value can satisfy \
                                     `{} < {} /\\ {} > {}`. \
                                     This constraint is logically impossible.",
                                    var1, upper, var2, lower
                                ),
                                fix: None,
                            });
                        }
                    }
                }
            }
        }

        diagnostics
    }

    /// Check for squash/erased simplification patterns.
    ///
    /// Detects:
    /// - `erased (erased t)` - double erasure is redundant
    /// - `reveal (hide x)` - round-trip that can be eliminated
    /// - `hide (reveal x)` - round-trip that can be eliminated
    fn check_ghost_erased_simplifications(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            // Check for double erased wrapping
            if DOUBLE_ERASED.is_match(line) {
                if let Some(m) = DOUBLE_ERASED.find(line) {
                    if !is_inside_string_or_comment(line, m.start()) {
                        let start_col = byte_to_char_col(line, m.start());
                        let end_col = byte_to_char_col(line, m.end());
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST012,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::new(line_num, start_col, line_num, end_col),
                            message: "Double erasure: `erased (erased t)` is redundant. \
                                     A single `erased t` suffices since erasure is idempotent."
                                .to_string(),
                            fix: None,
                        });
                    }
                }
            }

            // Check for reveal(hide x) round-trip
            for caps in REVEAL_HIDE.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }
                let var = caps.get(1).map(|m| m.as_str()).unwrap_or("x");
                let start_col = byte_to_char_col(line, full_match.start());
                let end_col = byte_to_char_col(line, full_match.end());
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST012,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::new(line_num, start_col, line_num, end_col),
                    message: format!(
                        "Round-trip: `reveal (hide {})` simplifies to `{}`. \
                         Use `Ghost.reveal_hide` lemma or eliminate directly.",
                        var, var
                    ),
                    fix: Some(Fix::safe(
                        "Eliminate reveal/hide round-trip (safe: identity)",
                        vec![Edit {
                            file: file.to_path_buf(),
                            range: Range::new(line_num, start_col, line_num, end_col),
                            new_text: var.to_string(),
                        }],
                    )
                    .with_safety_level(FixSafetyLevel::Caution)
                    .with_reversible(true)
                    .with_requires_review(true)),
                });
            }

            // Check for hide(reveal x) round-trip
            for caps in HIDE_REVEAL.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }
                let var = caps.get(1).map(|m| m.as_str()).unwrap_or("x");
                let start_col = byte_to_char_col(line, full_match.start());
                let end_col = byte_to_char_col(line, full_match.end());
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST012,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::new(line_num, start_col, line_num, end_col),
                    message: format!(
                        "Round-trip: `hide (reveal {})` simplifies to `{}`. \
                         Use `Ghost.hide_reveal` lemma or eliminate directly.",
                        var, var
                    ),
                    fix: Some(Fix::safe(
                        "Eliminate hide/reveal round-trip (safe: identity)",
                        vec![Edit {
                            file: file.to_path_buf(),
                            range: Range::new(line_num, start_col, line_num, end_col),
                            new_text: var.to_string(),
                        }],
                    )
                    .with_safety_level(FixSafetyLevel::Caution)
                    .with_reversible(true)
                    .with_requires_review(true)),
                });
            }

            // Check for squash equality pattern
            for caps in SQUASH_EQ.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }
                let var1 = caps.get(1).map(|m| m.as_str()).unwrap_or("a");
                let var2 = caps.get(2).map(|m| m.as_str()).unwrap_or("b");
                let start_col = byte_to_char_col(line, full_match.start());
                let end_col = byte_to_char_col(line, full_match.end());
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST012,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::new(line_num, start_col, line_num, end_col),
                    message: format!(
                        "Consider if `squash ({} == {})` can be replaced with \
                         a decidable equality check or a direct propositional proof. \
                         For eqtypes, `{} = {}` (single =) gives decidable equality.",
                        var1, var2, var1, var2
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for `{False}` refinement - always unsatisfiable (empty type).
    ///
    /// `x:T{False}` creates a type with no inhabitants. This is almost certainly
    /// a bug unless used intentionally as `void` / bottom type.
    ///
    /// Intentional patterns (demoted to Info):
    /// - `false_elim`, `absurd`, `diverge` — standard F* false-elimination functions
    /// - `{False}` used as a parameter type in `val` declarations (ex falso pattern)
    /// - `.fsti` files defining effect combinators that use bottom types
    fn check_false_refinement(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let file_name = file.file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("");

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            for caps in FALSE_REFINEMENT.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }

                let var_name = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                let type_name = caps.get(2).map(|m| m.as_str()).unwrap_or("");
                let start_col = byte_to_char_col(line, full_match.start());
                let end_col = byte_to_char_col(line, full_match.end());

                // Check if this is an intentional bottom-type pattern:
                // 1. val/let declaration with a known false-elimination name
                // 2. {False} used as a parameter (before `->`) in a val declaration
                let is_intentional = Self::is_intentional_false_refinement(
                    trimmed, line, full_match.end(), file_name,
                );

                let (severity, message) = if is_intentional {
                    (
                        DiagnosticSeverity::Info,
                        format!(
                            "Bottom type: `{}:{} {{False}}` has no inhabitants (intentional \
                             false-elimination / ex falso pattern).",
                            var_name, type_name
                        ),
                    )
                } else {
                    (
                        DiagnosticSeverity::Error,
                        format!(
                            "UNSATISFIABLE REFINEMENT: `{}:{} {{False}}` has no inhabitants. \
                             No value can satisfy the `False` predicate. This creates an \
                             empty type (bottom). If this is intentional (e.g., as a void type), \
                             consider using `empty` or `False -> void` instead.",
                            var_name, type_name
                        ),
                    )
                };

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST012,
                    severity,
                    file: file.to_path_buf(),
                    range: Range::new(line_num, start_col, line_num, end_col),
                    message,
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Determine if a `{False}` refinement is an intentional bottom-type pattern.
    ///
    /// Returns true for:
    /// - Known false-elimination function names (`false_elim`, `absurd`, `diverge`, etc.)
    /// - `{False}` appearing in parameter position (before `->`) in val declarations
    /// - Pervasives and other core module files that define effect combinators
    fn is_intentional_false_refinement(
        trimmed: &str,
        line: &str,
        match_end: usize,
        file_name: &str,
    ) -> bool {
        // Known false-elimination / bottom-type function names
        let bottom_names = [
            "false_elim", "absurd", "diverge", "empty_elim", "void_elim",
            "exfalso", "ex_falso", "bottom", "unreachable",
        ];

        let lower = trimmed.to_lowercase();
        for name in &bottom_names {
            if lower.contains(name) {
                return true;
            }
        }

        // Check if this is a val/assume val with {False} in parameter position
        // (i.e., there is a `->` after the match, meaning {False} is a parameter, not return type)
        if trimmed.starts_with("val ") || trimmed.starts_with("assume val ") {
            // If there's a `->` after the {False} match, it's a parameter
            let after_match = &line[match_end..];
            if after_match.contains("->") {
                return true;
            }
        }

        // Core F* modules that legitimately use bottom types in effect definitions
        if file_name.starts_with("FStar.Pervasives")
            || file_name.starts_with("Prims")
        {
            return true;
        }

        false
    }

    /// Check for additional unsatisfiable patterns: `x >= N /\ x < N` and `x > N /\ x <= N`.
    ///
    /// These are strict boundary contradictions that the simpler check_unsatisfiable
    /// does not catch.
    fn check_unsatisfiable_boundary(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            for ref_caps in REFINEMENT.captures_iter(line) {
                let Some(ref_match) = ref_caps.get(0) else { continue };
                if is_inside_string_or_comment(line, ref_match.start()) {
                    continue;
                }
                let body = ref_caps.get(3).map(|m| m.as_str()).unwrap_or("");
                let Some(body_group) = ref_caps.get(3) else { continue };
                let body_start_byte = body_group.start();

                // Check "var >= N /\ var < N" (lower bound equals strict upper bound)
                for caps in UNSAT_GTE_LT.captures_iter(body) {
                    let var1 = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                    let var2 = caps.get(3).map(|m| m.as_str()).unwrap_or("");
                    if var1 != var2 {
                        continue;
                    }
                    if let (Ok(lower), Ok(upper)) = (
                        caps.get(2).map_or("", |m| m.as_str()).parse::<i64>(),
                        caps.get(4).map_or("", |m| m.as_str()).parse::<i64>(),
                    ) {
                        if lower >= upper {
                            let inner = { let Some(m) = caps.get(0) else { continue }; m };
                            let start_col =
                                byte_to_char_col(line, body_start_byte + inner.start());
                            let end_col =
                                byte_to_char_col(line, body_start_byte + inner.end());

                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST012,
                                severity: DiagnosticSeverity::Error,
                                file: file.to_path_buf(),
                                range: Range::new(line_num, start_col, line_num, end_col),
                                message: format!(
                                    "UNSATISFIABLE REFINEMENT: No value can satisfy \
                                     `{} >= {} /\\ {} < {}`. \
                                     This constraint is logically impossible.",
                                    var1, lower, var2, upper
                                ),
                                fix: None,
                            });
                        }
                    }
                }

                // Check "var > N /\ var <= N" (strict lower bound equals upper bound)
                for caps in UNSAT_GT_LTE.captures_iter(body) {
                    let var1 = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                    let var2 = caps.get(3).map(|m| m.as_str()).unwrap_or("");
                    if var1 != var2 {
                        continue;
                    }
                    if let (Ok(lower), Ok(upper)) = (
                        caps.get(2).map_or("", |m| m.as_str()).parse::<i64>(),
                        caps.get(4).map_or("", |m| m.as_str()).parse::<i64>(),
                    ) {
                        if lower >= upper {
                            let inner = { let Some(m) = caps.get(0) else { continue }; m };
                            let start_col =
                                byte_to_char_col(line, body_start_byte + inner.start());
                            let end_col =
                                byte_to_char_col(line, body_start_byte + inner.end());

                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST012,
                                severity: DiagnosticSeverity::Error,
                                file: file.to_path_buf(),
                                range: Range::new(line_num, start_col, line_num, end_col),
                                message: format!(
                                    "UNSATISFIABLE REFINEMENT: No value can satisfy \
                                     `{} > {} /\\ {} <= {}`. \
                                     This constraint is logically impossible.",
                                    var1, lower, var2, upper
                                ),
                                fix: None,
                            });
                        }
                    }
                }

                // Check "var = N /\ var <> N" (equality contradicts disequality)
                for caps in UNSAT_EQ_NEQ.captures_iter(body) {
                    let var1 = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                    let var2 = caps.get(3).map(|m| m.as_str()).unwrap_or("");
                    let val1 = caps.get(2).map(|m| m.as_str()).unwrap_or("");
                    let val2 = caps.get(4).map(|m| m.as_str()).unwrap_or("");
                    if var1 != var2 || val1 != val2 {
                        continue;
                    }

                    let inner = { let Some(m) = caps.get(0) else { continue }; m };
                    let start_col =
                        byte_to_char_col(line, body_start_byte + inner.start());
                    let end_col =
                        byte_to_char_col(line, body_start_byte + inner.end());

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST012,
                        severity: DiagnosticSeverity::Error,
                        file: file.to_path_buf(),
                        range: Range::new(line_num, start_col, line_num, end_col),
                        message: format!(
                            "UNSATISFIABLE REFINEMENT: No value can satisfy \
                             `{} = {} /\\ {} <> {}`. \
                             Equality and disequality on the same value are contradictory.",
                            var1, val1, var2, val2
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for reversed comparison `0 <= x` in int refinement that could be nat.
    ///
    /// This is the reversed form of `x >= 0`. We provide a hint suggesting the
    /// canonical form. This is conservative - we only hint, not auto-fix.
    fn check_reversed_gte_zero(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            for caps in REVERSED_GTE_ZERO.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }

                let var_name = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                let ref_var = caps.get(2).map(|m| m.as_str()).unwrap_or("");

                // Only fire if the refinement variable matches the binding variable
                if var_name != ref_var {
                    continue;
                }

                let start_col = byte_to_char_col(line, full_match.start());
                let end_col = byte_to_char_col(line, full_match.end());

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST012,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::new(line_num, start_col, line_num, end_col),
                    message: format!(
                        "Consider using `nat` instead of `int{{0 <= {}}}`. \
                         The `nat` type is defined as `x:int{{x >= 0}}` in Prims, \
                         and `0 <= {}` is semantically equivalent to `{} >= 0`. \
                         NOTE: This changes the type, which may affect type inference.",
                        ref_var, ref_var, ref_var
                    ),
                    fix: Some(Fix::unsafe_fix(
                        "Use nat instead of int{0 <= x} (CAUTION: changes type)",
                        vec![Edit {
                            file: file.to_path_buf(),
                            range: Range::new(line_num, start_col, line_num, end_col),
                            new_text: format!("{}:nat", var_name),
                        }],
                        FixConfidence::Low,
                        "Type change from int{...} to nat may affect type inference",
                    )
                    .with_safety_level(FixSafetyLevel::Caution)
                    .with_reversible(true)
                    .with_requires_review(true)),
                });
            }
        }

        diagnostics
    }

    /// Check for `nat{x <> 0}` which is equivalent to `pos`.
    ///
    /// Since `nat` is `x:int{x >= 0}` and adding `x <> 0` gives `x:int{x >= 0 /\ x <> 0}`
    /// which is equivalent to `x:int{x > 0}` = `pos`.
    fn check_nat_neq_zero(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            for caps in NAT_NEQ_ZERO.captures_iter(line) {
                let full_match = { let Some(m) = caps.get(0) else { continue }; m };
                if is_inside_string_or_comment(line, full_match.start()) {
                    continue;
                }

                let var_name = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                let ref_var = caps.get(2).map(|m| m.as_str()).unwrap_or("");

                // Only fire if the refinement variable matches the binding variable
                if var_name != ref_var {
                    continue;
                }

                let start_col = byte_to_char_col(line, full_match.start());
                let end_col = byte_to_char_col(line, full_match.end());

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST012,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::new(line_num, start_col, line_num, end_col),
                    message: format!(
                        "Consider using `pos` instead of `nat{{{} <> 0}}`. \
                         Since `nat` is `x:int{{x >= 0}}`, adding `{} <> 0` gives \
                         `x:int{{x > 0}}` which is `pos`. \
                         NOTE: This changes the type, which may affect type inference.",
                        ref_var, ref_var
                    ),
                    fix: Some(Fix::unsafe_fix(
                        "Use pos instead of nat{x <> 0} (CAUTION: changes type)",
                        vec![Edit {
                            file: file.to_path_buf(),
                            range: Range::new(line_num, start_col, line_num, end_col),
                            new_text: format!("{}:pos", var_name),
                        }],
                        FixConfidence::Low,
                        "Type change from nat{...} to pos may affect type inference",
                    )
                    .with_safety_level(FixSafetyLevel::Caution)
                    .with_reversible(true)
                    .with_requires_review(true)),
                });
            }
        }

        diagnostics
    }
}

impl Default for RefinementSimplifierRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for RefinementSimplifierRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST012
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        diagnostics.extend(self.check_redundant_nat(file, content));
        diagnostics.extend(self.check_redundant_pos(file, content));
        diagnostics.extend(self.check_true_refinement(file, content));
        diagnostics.extend(self.check_int_to_nat(file, content));
        diagnostics.extend(self.check_int_to_pos(file, content));
        diagnostics.extend(self.check_unsatisfiable(file, content));
        diagnostics.extend(self.check_false_refinement(file, content));
        diagnostics.extend(self.check_unsatisfiable_boundary(file, content));
        diagnostics.extend(self.check_reversed_gte_zero(file, content));
        diagnostics.extend(self.check_nat_neq_zero(file, content));
        diagnostics.extend(self.check_ghost_erased_simplifications(file, content));

        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn make_path() -> PathBuf {
        PathBuf::from("test.fst")
    }

    #[test]
    fn test_redundant_nat_refinement() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x:nat{x >= 0}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("Redundant refinement"));
        assert!(diags[0].message.contains("nat"));
        assert!(diags[0].fix.is_some());
    }

    #[test]
    fn test_redundant_pos_refinement() {
        let rule = RefinementSimplifierRule::new();
        let content = "let bar (n:pos{n > 0}) = n";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("Redundant refinement"));
        assert!(diags[0].message.contains("pos"));
    }

    #[test]
    fn test_true_refinement() {
        let rule = RefinementSimplifierRule::new();
        let content = "let baz (x:int{True}) = x + 1";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("Useless refinement"));
    }

    #[test]
    fn test_int_to_nat() {
        let rule = RefinementSimplifierRule::new();
        let content = "let len (n:int{n >= 0}) = n";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("Consider using `nat`"));
        assert_eq!(diags[0].severity, DiagnosticSeverity::Info);
    }

    #[test]
    fn test_int_to_pos() {
        let rule = RefinementSimplifierRule::new();
        let content = "let positive (n:int{n > 0}) = n";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("Consider using `pos`"));
    }

    #[test]
    fn test_unsatisfiable_gt_lt() {
        let rule = RefinementSimplifierRule::new();
        let content = "let impossible (x:int{x > 5 /\\ x < 3}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("UNSATISFIABLE"));
        assert_eq!(diags[0].severity, DiagnosticSeverity::Error);
    }

    #[test]
    fn test_unsatisfiable_equal_bounds() {
        let rule = RefinementSimplifierRule::new();
        let content = "let also_impossible (x:int{x > 3 /\\ x < 3}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("UNSATISFIABLE"));
    }

    #[test]
    fn test_satisfiable_range() {
        let rule = RefinementSimplifierRule::new();
        // This is satisfiable (x could be 4)
        let content = "let valid_range (x:int{x > 3 /\\ x < 5}) = x";
        let diags = rule.check(&make_path(), content);
        // Should not produce unsatisfiable error
        assert!(!diags.iter().any(|d| d.message.contains("UNSATISFIABLE")));
    }

    #[test]
    fn test_valid_nat_refinement() {
        let rule = RefinementSimplifierRule::new();
        // nat with additional constraint (not just >= 0) is valid
        let content = "let bounded (x:nat{x < 100}) = x";
        let diags = rule.check(&make_path(), content);
        // Should not produce any diagnostics
        assert!(diags.is_empty());
    }

    #[test]
    fn test_comment_lines_skipped() {
        let rule = RefinementSimplifierRule::new();
        let content = "// let foo (x:nat{x >= 0}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    // ========== Autofix verification tests ==========

    #[test]
    fn test_nat_refinement_fix_content() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x:nat{x >= 0}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().unwrap();
        assert_eq!(fix.edits.len(), 1);
        assert_eq!(fix.edits[0].new_text, "x:nat");
        // Message now indicates safety
        assert!(fix.message.contains("Remove redundant refinement"));
        assert!(fix.message.contains("safe"));
    }

    #[test]
    fn test_pos_refinement_fix_content() {
        let rule = RefinementSimplifierRule::new();
        let content = "let bar (n:pos{n > 0}) = n";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().unwrap();
        assert_eq!(fix.edits[0].new_text, "n:pos");
    }

    #[test]
    fn test_true_refinement_fix_content() {
        let rule = RefinementSimplifierRule::new();
        let content = "let baz (x:int{True}) = x + 1";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().unwrap();
        assert_eq!(fix.edits[0].new_text, "x:int");
        // Message now indicates safety
        assert!(fix.message.contains("Remove useless {True} refinement"));
        assert!(fix.message.contains("safe"));
    }

    #[test]
    fn test_int_to_nat_fix_content() {
        let rule = RefinementSimplifierRule::new();
        let content = "let len (n:int{n >= 0}) = n";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().unwrap();
        assert_eq!(fix.edits[0].new_text, "n:nat");
    }

    #[test]
    fn test_int_to_pos_fix_content() {
        let rule = RefinementSimplifierRule::new();
        let content = "let positive (n:int{n > 0}) = n";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().unwrap();
        assert_eq!(fix.edits[0].new_text, "n:pos");
    }

    // ========== UInt suggestion REMOVED tests ==========
    // The old UInt32/UInt64 suggestions were false positives because
    // nat{x < pow2 32} and FStar.UInt32.t have fundamentally different
    // semantics (mathematical nat vs machine word with modular arithmetic).

    #[test]
    fn test_nat_pow2_32_no_longer_triggers() {
        let rule = RefinementSimplifierRule::new();
        let content = "let bounded32 (x:nat{x < pow2 32}) = x";
        let diags = rule.check(&make_path(), content);
        // Must produce ZERO diagnostics -- this is valid F* code.
        assert!(diags.is_empty());
    }

    #[test]
    fn test_nat_pow2_64_no_longer_triggers() {
        let rule = RefinementSimplifierRule::new();
        let content = "let bounded64 (n:nat{n < pow2 64}) = n";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    // ========== Column calculation tests ==========

    #[test]
    fn test_column_calculation_simple() {
        let rule = RefinementSimplifierRule::new();
        // "let foo " is 8 chars, x starts at column 9
        let content = "let foo (x:nat{x >= 0}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        // x:nat{x >= 0} starts at position 9
        assert_eq!(diags[0].range.start_col, 10);
    }

    #[test]
    fn test_column_calculation_with_leading_spaces() {
        let rule = RefinementSimplifierRule::new();
        let content = "    let foo (x:nat{x >= 0}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        // 4 spaces + "let foo " = 13 chars, x starts at column 14
        assert_eq!(diags[0].range.start_col, 14);
    }

    #[test]
    fn test_byte_to_char_col_ascii() {
        // Pure ASCII: byte offset == char offset
        let s = "hello world";
        assert_eq!(byte_to_char_col(s, 0), 1); // Column 1
        assert_eq!(byte_to_char_col(s, 5), 6); // Column 6
        assert_eq!(byte_to_char_col(s, 11), 12); // Column 12
    }

    #[test]
    fn test_byte_to_char_col_utf8() {
        // UTF-8 with multi-byte chars: byte offset != char offset
        let s = "hi there";
        assert_eq!(byte_to_char_col(s, 0), 1);
        assert_eq!(byte_to_char_col(s, 2), 3);
    }

    #[test]
    fn test_byte_to_char_col_edge_cases() {
        let s = "abc";
        // Beyond string length should clamp
        assert_eq!(byte_to_char_col(s, 100), 4);
        // Empty prefix
        assert_eq!(byte_to_char_col(s, 0), 1);
    }

    // ========== Whitespace variation tests ==========

    #[test]
    fn test_no_space_in_refinement() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x:nat{x>=0}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("Redundant refinement"));
    }

    #[test]
    fn test_extra_spaces_in_refinement() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x:nat{  x >= 0  }) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("Redundant refinement"));
    }

    #[test]
    fn test_multiline_not_detected() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x:nat{\nx >= 0\n}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    // ========== Multiple diagnostics tests ==========

    #[test]
    fn test_multiple_refinements_same_line() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x:nat{x >= 0}) (y:pos{y > 0}) = x + y";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 2);
    }

    #[test]
    fn test_multiple_refinements_different_lines() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x:nat{x >= 0}) = x\nlet bar (y:int{y >= 0}) = y";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 2);
        assert_eq!(diags[0].range.start_line, 1);
        assert_eq!(diags[1].range.start_line, 2);
    }

    // ========== Block comment tests ==========

    #[test]
    fn test_block_comment_skipped() {
        let rule = RefinementSimplifierRule::new();
        let content = "(* let foo (x:nat{x >= 0}) = x *)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    // ========== Unsatisfiable edge cases ==========

    #[test]
    fn test_unsatisfiable_reversed_order() {
        let rule = RefinementSimplifierRule::new();
        let content = "let impossible (x:int{x < 3 /\\ x > 5}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("UNSATISFIABLE"));
    }

    #[test]
    fn test_unsatisfiable_no_fix_provided() {
        let rule = RefinementSimplifierRule::new();
        let content = "let impossible (x:int{x > 5 /\\ x < 3}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].fix.is_none());
    }

    #[test]
    fn test_different_variables_not_unsatisfiable() {
        let rule = RefinementSimplifierRule::new();
        let content = "let valid (x:int{x > 5 /\\ y < 3}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("UNSATISFIABLE")));
    }

    // ========== No false positive tests ==========

    #[test]
    fn test_no_false_positive_nat_with_constraint() {
        let rule = RefinementSimplifierRule::new();
        let content = "let bounded (x:nat{x < 10}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    #[test]
    fn test_no_false_positive_pos_with_constraint() {
        let rule = RefinementSimplifierRule::new();
        let content = "let bounded (x:pos{x <= 100}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    #[test]
    fn test_no_false_positive_int_with_other_constraint() {
        let rule = RefinementSimplifierRule::new();
        let content = "let bounded (x:int{x < 100}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    // ========== NEW: False positive regression tests ==========

    #[test]
    fn test_no_false_positive_string_literal() {
        let rule = RefinementSimplifierRule::new();
        // Refinement pattern inside a string literal must NOT trigger
        let content = r#"let msg = "x:nat{x >= 0}" in msg"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Should not flag refinement patterns inside string literals"
        );
    }

    #[test]
    fn test_no_false_positive_inline_block_comment() {
        let rule = RefinementSimplifierRule::new();
        // Refinement inside inline (* ... *) comment must NOT trigger
        let content = "let f = (* x:nat{x >= 0} *) 42";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Should not flag refinement patterns inside inline block comments"
        );
    }

    #[test]
    fn test_no_false_positive_unsatisfiable_outside_refinement() {
        let rule = RefinementSimplifierRule::new();
        // Unsatisfiable pattern in a bare assert, NOT inside a refinement brace.
        // The old code would flag this; the new code should not.
        let content = "let _ = assert (x > 5 /\\ x < 3)";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("UNSATISFIABLE")),
            "Should not flag unsatisfiable patterns outside refinement braces"
        );
    }

    #[test]
    fn test_no_false_positive_compound_refinement_nat() {
        let rule = RefinementSimplifierRule::new();
        // int{x >= 0 /\ x < 256} should NOT suggest nat -- the refinement
        // has additional constraints beyond just >= 0.
        let content = r"let byte (x:int{x >= 0 /\ x < 256}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Should not suggest nat for compound refinements"
        );
    }

    #[test]
    fn test_no_false_positive_compound_refinement_pos() {
        let rule = RefinementSimplifierRule::new();
        // int{x > 0 /\ x <= 255} should NOT suggest pos.
        let content = r"let positive_byte (x:int{x > 0 /\ x <= 255}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Should not suggest pos for compound refinements"
        );
    }

    #[test]
    fn test_no_false_positive_string_literal_unsatisfiable() {
        let rule = RefinementSimplifierRule::new();
        let content = r#"let msg = "x:int{x > 5 /\ x < 3}" in msg"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Should not flag unsatisfiable patterns inside string literals"
        );
    }

    #[test]
    fn test_no_false_positive_true_in_string() {
        let rule = RefinementSimplifierRule::new();
        let content = r#"let msg = "x:int{True}" in msg"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Should not flag {{True}} inside string literals"
        );
    }

    #[test]
    fn test_is_inside_string_or_comment_basic() {
        // After opening quote, offset 5 is inside the string
        assert!(is_inside_string_or_comment(r#"foo "bar" baz"#, 5));
        // Before opening quote, offset 0 is outside
        assert!(!is_inside_string_or_comment(r#"foo "bar" baz"#, 0));
        // After closing quote, offset 10 is outside
        assert!(!is_inside_string_or_comment(r#"foo "bar" baz"#, 10));
    }

    #[test]
    fn test_is_inside_block_comment() {
        assert!(is_inside_string_or_comment("foo (* bar *) baz", 7));
        assert!(!is_inside_string_or_comment("foo (* bar *) baz", 0));
        assert!(!is_inside_string_or_comment("foo (* bar *) baz", 14));
    }

    #[test]
    fn test_is_inside_escaped_string() {
        // Escaped quote inside a string should not end the string
        let line = r#"let s = "x:nat{x >= 0}\"more" in s"#;
        // Position of the opening `"` is byte 8, so byte 10 is inside
        assert!(is_inside_string_or_comment(line, 10));
    }

    #[test]
    fn test_hacl_star_pattern_no_false_positive() {
        let rule = RefinementSimplifierRule::new();
        // Real pattern from hacl-star: d:int{r * d % n = 1}
        // Should NOT trigger any diagnostic (complex refinement, not >= 0 or > 0)
        let content = "val lemma_mont_one: n:pos -> r:pos -> d:int{r * d % n = 1} -> a:nat";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Should not flag complex refinements from real hacl-star code"
        );
    }

    // ========== Fix Safety Tests ==========
    // These tests verify the critical safety features for auto-fix.

    #[test]
    fn test_redundant_nat_fix_is_safe_and_auto_applicable() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x:nat{x >= 0}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);

        let fix = diags[0].fix.as_ref().expect("Should have a fix");
        assert!(fix.is_safe(), "Redundant nat removal should be marked safe");
        assert!(
            fix.can_auto_apply(),
            "Safe high-confidence fix should be auto-applicable"
        );
        assert!(
            fix.message.contains("safe"),
            "Fix message should indicate safety"
        );
    }

    #[test]
    fn test_redundant_pos_fix_is_safe_and_auto_applicable() {
        let rule = RefinementSimplifierRule::new();
        let content = "let bar (n:pos{n > 0}) = n";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);

        let fix = diags[0].fix.as_ref().expect("Should have a fix");
        assert!(fix.is_safe(), "Redundant pos removal should be marked safe");
        assert!(
            fix.can_auto_apply(),
            "Safe high-confidence fix should be auto-applicable"
        );
    }

    #[test]
    fn test_true_refinement_fix_is_safe_and_auto_applicable() {
        let rule = RefinementSimplifierRule::new();
        let content = "let baz (x:int{True}) = x + 1";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);

        let fix = diags[0].fix.as_ref().expect("Should have a fix");
        assert!(fix.is_safe(), "True refinement removal should be marked safe");
        assert!(
            fix.can_auto_apply(),
            "Safe high-confidence fix should be auto-applicable"
        );
    }

    #[test]
    fn test_int_to_nat_fix_is_unsafe_not_auto_applicable() {
        let rule = RefinementSimplifierRule::new();
        let content = "let len (n:int{n >= 0}) = n";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);

        let fix = diags[0].fix.as_ref().expect("Should have a fix");
        assert!(
            !fix.is_safe(),
            "int->nat type change should be marked UNSAFE"
        );
        assert!(
            !fix.can_auto_apply(),
            "Unsafe fix should NOT be auto-applicable"
        );
        assert!(
            fix.unsafe_reason.is_some(),
            "Unsafe fix should have a reason"
        );
        assert!(
            fix.message.contains("CAUTION"),
            "Fix message should warn about type change"
        );
    }

    #[test]
    fn test_int_to_pos_fix_is_unsafe_not_auto_applicable() {
        let rule = RefinementSimplifierRule::new();
        let content = "let positive (n:int{n > 0}) = n";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);

        let fix = diags[0].fix.as_ref().expect("Should have a fix");
        assert!(
            !fix.is_safe(),
            "int->pos type change should be marked UNSAFE"
        );
        assert!(
            !fix.can_auto_apply(),
            "Unsafe fix should NOT be auto-applicable"
        );
        assert!(
            fix.unsafe_reason.is_some(),
            "Unsafe fix should have a reason"
        );
    }

    #[test]
    fn test_int_to_nat_message_warns_about_type_change() {
        let rule = RefinementSimplifierRule::new();
        let content = "let len (n:int{n >= 0}) = n";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);

        // Message should warn about the implications
        assert!(
            diags[0].message.contains("NOTE"),
            "Message should have a NOTE about implications"
        );
        assert!(
            diags[0].message.contains("type inference"),
            "Message should mention type inference impact"
        );
    }

    #[test]
    fn test_unsatisfiable_has_no_fix() {
        let rule = RefinementSimplifierRule::new();
        let content = "let impossible (x:int{x > 5 /\\ x < 3}) = x";
        let diags = rule.check(&make_path(), content);
        assert_eq!(diags.len(), 1);

        assert!(
            diags[0].fix.is_none(),
            "Unsatisfiable refinement should have no fix"
        );
        assert_eq!(
            diags[0].severity,
            DiagnosticSeverity::Error,
            "Unsatisfiable should be an error"
        );
    }

    // ========== Additional Edge Case Tests ==========

    #[test]
    fn test_reversed_gte_now_hints_nat() {
        let rule = RefinementSimplifierRule::new();
        // "0 <= x" is semantically the same as "x >= 0".
        // We now detect this reversed form and suggest nat (Info severity).
        let content = "let foo (x:int{0 <= x}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("nat") && d.message.contains("0 <=")),
            "Reversed comparison form should now suggest nat"
        );
        assert!(
            diags.iter().any(|d| d.severity == DiagnosticSeverity::Info),
            "Reversed comparison hint should be Info severity"
        );
    }

    #[test]
    fn test_not_int_base_type_no_simplification() {
        let rule = RefinementSimplifierRule::new();
        // Base type is "integer" not "int" - should not trigger
        let content = "let foo (x:integer{x >= 0}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Only exact 'int' base type should trigger simplification"
        );
    }

    #[test]
    fn test_qualified_int_not_matched() {
        let rule = RefinementSimplifierRule::new();
        // FStar.Int.int is different from bare int - should not trigger
        // Note: Our regex only matches single-word types
        let content = "let foo (x:FStar.Int.int{x >= 0}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Qualified types should not trigger simplification"
        );
    }

    #[test]
    fn test_conjunction_with_gte_zero_not_nat() {
        let rule = RefinementSimplifierRule::new();
        // int{x >= 0 /\ x <> 5} has additional constraint - NOT equivalent to nat
        let content = r"let foo (x:int{x >= 0 /\ x <> 5}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "int{{x >= 0 /\\ extra}} should NOT suggest nat"
        );
    }

    #[test]
    fn test_disjunction_with_gte_zero_not_nat() {
        let rule = RefinementSimplifierRule::new();
        // int{x >= 0 \/ x < -10} is NOT equivalent to nat
        let content = r"let foo (x:int{x >= 0 \/ x < -10}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "int{{x >= 0 \\/ extra}} should NOT suggest nat"
        );
    }

    #[test]
    fn test_negation_with_gte_zero_not_nat() {
        let rule = RefinementSimplifierRule::new();
        // int{~(x >= 0)} is the opposite of nat
        let content = r"let foo (x:int{~(x >= 0)}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Negated constraint should NOT suggest nat"
        );
    }

    // ========== NEW: Ghost/erased simplification tests ==========

    #[test]
    fn test_double_erased_detected() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x: erased (erased nat)) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Double erasure")),
            "Should detect double erased wrapping"
        );
    }

    #[test]
    fn test_single_erased_no_warning() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x: erased nat) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Double erasure")),
            "Single erased should not trigger double erasure warning"
        );
    }

    #[test]
    fn test_reveal_hide_roundtrip_detected() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo x = reveal (hide x)";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Round-trip") && d.message.contains("reveal")),
            "Should detect reveal(hide x) round-trip"
        );
    }

    #[test]
    fn test_hide_reveal_roundtrip_detected() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo x = hide (reveal x)";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Round-trip") && d.message.contains("hide")),
            "Should detect hide(reveal x) round-trip"
        );
    }

    #[test]
    fn test_ghost_reveal_hide_qualified_detected() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo x = Ghost.reveal (Ghost.hide x)";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Round-trip")),
            "Should detect qualified Ghost.reveal(Ghost.hide x) round-trip"
        );
    }

    #[test]
    fn test_reveal_alone_no_warning() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo x = reveal x";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Round-trip")),
            "Standalone reveal should not trigger round-trip warning"
        );
    }

    #[test]
    fn test_squash_eq_detected() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (p: squash (a == b)) = ()";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("squash")),
            "Should detect squash equality pattern"
        );
    }

    #[test]
    fn test_reveal_hide_fix_content() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo x = reveal (hide x)";
        let diags = rule.check(&make_path(), content);
        let roundtrip_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Round-trip"))
            .collect();
        assert_eq!(roundtrip_diags.len(), 1);
        let fix = roundtrip_diags[0].fix.as_ref().expect("Should have a fix");
        assert_eq!(fix.edits[0].new_text, "x");
    }

    #[test]
    fn test_double_erased_in_comment_skipped() {
        let rule = RefinementSimplifierRule::new();
        let content = "// erased (erased nat) is bad";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Double erasure")),
            "Should skip double erased in comments"
        );
    }

    #[test]
    fn test_roundtrip_in_string_skipped() {
        let rule = RefinementSimplifierRule::new();
        let content = r#"let msg = "reveal (hide x)" in msg"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Round-trip")),
            "Should skip round-trip patterns inside string literals"
        );
    }

    // ========== NEW: False refinement tests ==========

    #[test]
    fn test_false_refinement_detected() {
        let rule = RefinementSimplifierRule::new();
        let content = "let void_type (x:int{False}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("UNSATISFIABLE") && d.message.contains("False")),
            "Should detect False refinement as unsatisfiable"
        );
        assert!(
            diags.iter().any(|d| d.severity == DiagnosticSeverity::Error),
            "False refinement should be Error severity"
        );
    }

    #[test]
    fn test_false_refinement_different_types() {
        let rule = RefinementSimplifierRule::new();
        let content = "let void_nat (x:nat{False}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("UNSATISFIABLE") && d.message.contains("False")),
            "Should detect False refinement on nat type"
        );
    }

    #[test]
    fn test_false_refinement_in_comment_skipped() {
        let rule = RefinementSimplifierRule::new();
        let content = "// x:int{False} is bottom type";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("UNSATISFIABLE") && d.message.contains("no inhabitants")),
            "Should skip False refinement in comments"
        );
    }

    #[test]
    fn test_false_refinement_in_string_skipped() {
        let rule = RefinementSimplifierRule::new();
        let content = r#"let msg = "x:int{False}" in msg"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("no inhabitants")),
            "Should skip False refinement in string literals"
        );
    }

    #[test]
    fn test_false_refinement_val_parameter_is_intentional() {
        let rule = RefinementSimplifierRule::new();
        // {False} in parameter position of val declaration is standard ex falso pattern
        let content = "val false_elim (#a: Type) (u: unit{False}) : Tot a";
        let diags = rule.check(&make_path(), content);
        let false_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("False"))
            .collect();
        assert_eq!(false_diags.len(), 1);
        assert_eq!(
            false_diags[0].severity,
            DiagnosticSeverity::Info,
            "false_elim with False parameter should be Info, not Error"
        );
        assert!(
            false_diags[0].message.contains("intentional"),
            "Message should indicate intentional pattern"
        );
    }

    #[test]
    fn test_false_refinement_val_param_arrow_after() {
        let rule = RefinementSimplifierRule::new();
        // {False} in param position (arrow after) for arbitrary function name
        let content = "val my_func : (u:unit{False}) -> Tot int";
        let diags = rule.check(&make_path(), content);
        let false_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("False"))
            .collect();
        assert_eq!(false_diags.len(), 1);
        assert_eq!(
            false_diags[0].severity,
            DiagnosticSeverity::Info,
            "False in val parameter position should be Info"
        );
    }

    #[test]
    fn test_false_refinement_pervasives_file() {
        let rule = RefinementSimplifierRule::new();
        let content = "val diverge_Dv_eff (u:unit{False}) : Tot a";
        let pervasives = PathBuf::from("FStar.Pervasives.fsti");
        let diags = rule.check(&pervasives, content);
        let false_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("False"))
            .collect();
        assert_eq!(false_diags.len(), 1);
        assert_eq!(
            false_diags[0].severity,
            DiagnosticSeverity::Info,
            "Pervasives file should get Info severity for False refinement"
        );
    }

    #[test]
    fn test_false_refinement_let_body_still_error() {
        let rule = RefinementSimplifierRule::new();
        // {False} in a let binding with unknown name -- still suspicious
        let content = "let bad_func (x:int{False}) = x";
        let diags = rule.check(&make_path(), content);
        let false_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("False"))
            .collect();
        assert_eq!(false_diags.len(), 1);
        assert_eq!(
            false_diags[0].severity,
            DiagnosticSeverity::Error,
            "False in let binding with unknown name should remain Error"
        );
    }

    // ========== NEW: Boundary unsatisfiable tests ==========

    #[test]
    fn test_unsatisfiable_gte_lt_same_bound() {
        let rule = RefinementSimplifierRule::new();
        let content = "let impossible (x:int{x >= 5 /\\ x < 5}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("UNSATISFIABLE")),
            "Should detect x >= 5 /\\ x < 5 as unsatisfiable"
        );
    }

    #[test]
    fn test_unsatisfiable_gt_lte_same_bound() {
        let rule = RefinementSimplifierRule::new();
        let content = "let impossible (x:int{x > 5 /\\ x <= 5}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("UNSATISFIABLE")),
            "Should detect x > 5 /\\ x <= 5 as unsatisfiable"
        );
    }

    #[test]
    fn test_unsatisfiable_eq_neq() {
        let rule = RefinementSimplifierRule::new();
        let content = "let impossible (x:int{x = 5 /\\ x <> 5}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("UNSATISFIABLE")),
            "Should detect x = 5 /\\ x <> 5 as unsatisfiable"
        );
    }

    #[test]
    fn test_satisfiable_gte_lt_different_bounds() {
        let rule = RefinementSimplifierRule::new();
        // x >= 3 /\ x < 5 is satisfiable (x could be 3 or 4)
        let content = "let valid (x:int{x >= 3 /\\ x < 5}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("UNSATISFIABLE")),
            "x >= 3 /\\ x < 5 should not be flagged as unsatisfiable"
        );
    }

    #[test]
    fn test_eq_neq_different_values_not_unsatisfiable() {
        let rule = RefinementSimplifierRule::new();
        // x = 5 /\ x <> 3 is satisfiable
        let content = "let valid (x:int{x = 5 /\\ x <> 3}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("UNSATISFIABLE") && d.message.contains("disequality")),
            "x = 5 /\\ x <> 3 should not be flagged as unsatisfiable"
        );
    }

    // ========== NEW: Reversed comparison tests ==========

    #[test]
    fn test_reversed_gte_zero_hint() {
        let rule = RefinementSimplifierRule::new();
        let content = "let foo (x:int{0 <= x}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("nat") && d.message.contains("0 <=")),
            "Should suggest nat for int{{0 <= x}}"
        );
    }

    #[test]
    fn test_reversed_gte_zero_different_vars_no_hint() {
        let rule = RefinementSimplifierRule::new();
        // Variable name doesn't match refinement variable
        let content = "let foo (x:int{0 <= y}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("0 <=")),
            "Should not suggest nat when binding var != refinement var"
        );
    }

    // ========== NEW: nat{x <> 0} -> pos tests ==========

    #[test]
    fn test_nat_neq_zero_to_pos() {
        let rule = RefinementSimplifierRule::new();
        let content = "let nonzero (x:nat{x <> 0}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("pos") && d.message.contains("<> 0")),
            "Should suggest pos for nat{{x <> 0}}"
        );
    }

    #[test]
    fn test_nat_neq_zero_different_vars_no_hint() {
        let rule = RefinementSimplifierRule::new();
        let content = "let nonzero (x:nat{y <> 0}) = x";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("pos") && d.message.contains("<> 0")),
            "Should not suggest pos when binding var != refinement var"
        );
    }

    #[test]
    fn test_nat_neq_zero_fix_content() {
        let rule = RefinementSimplifierRule::new();
        let content = "let nonzero (x:nat{x <> 0}) = x";
        let diags = rule.check(&make_path(), content);
        let pos_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("pos") && d.message.contains("<> 0"))
            .collect();
        assert_eq!(pos_diags.len(), 1);
        let fix = pos_diags[0].fix.as_ref().expect("Should have a fix");
        assert_eq!(fix.edits[0].new_text, "x:pos");
        assert!(!fix.is_safe(), "nat->pos change should be unsafe");
    }
}
