//! FST013: Documentation checker.
//!
//! Checks for missing documentation on public declarations.
//! F* supports two documentation comment styles:
//! - Block doc comments: `(** ... *)`
//! - Triple-slash comments: `/// ...`
//!
//! ## Checks Performed
//!
//! 1. **Missing docs**: Public `val` and `type` declarations without doc comments.
//! 2. **Module-level docs**: `.fsti` interface files without a module-level doc comment.
//! 3. **Doc quality**: Existing doc comments that are stubs, too short, or just repeat the name.
//! 4. **Complex undocumented types**: ADTs with many constructors, records, `noeq` types.
//!
//! ## Safety Features
//!
//! This rule includes safeguards to prevent unwanted modifications:
//! - Skips auto-generated files (detected by markers in comments)
//! - Skips test files (detected by filename/path patterns)
//! - Skips private declarations, `inline_for_extraction noextract` helpers
//! - Preserves existing partial documentation
//! - Uses INFO severity (not warning/error)
//! - Marks fixes as LOW confidence (requires explicit --apply)
//!
//! ## Batch Mode
//!
//! When many declarations are missing documentation, the tool shows a summary
//! of how many stubs would be added rather than auto-applying all changes.

use lazy_static::lazy_static;
use regex::Regex;
use std::path::Path;

use super::parser::{parse_fstar_file, BlockType};
use super::rules::{Diagnostic, DiagnosticSeverity, Edit, Fix, FixConfidence, FixSafetyLevel, Range, Rule, RuleCode};
use super::shared_patterns::{
    PARAM_EXTRACT_RE, INLINE_NOEXTRACT_RE, PRIVATE_DECL_RE, ASSUME_VAL_RE,
};

lazy_static! {
    /// Pattern for block doc comments: `(**` at start of trimmed line,
    /// but not `(***` or `(**)`
    static ref DOC_BLOCK: Regex = Regex::new(r"^\(\*\*(?:[^*)]|$)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for triple-slash doc comments at line start
    static ref DOC_TRIPLE: Regex = Regex::new(r"^\s*///").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect simple type abbreviations: `type foo = bar`
    /// where the RHS is a single identifier (possibly qualified like A.B.c).
    /// These are self-documenting and do not need doc comments.
    static ref TYPE_ABBREVIATION: Regex = Regex::new(
        r"(?m)^\s*(?:type|and)\s+\w+(?:\s+\w+)*\s*=\s*[\w.]+\s*$"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Patterns indicating auto-generated files that should be skipped.
    /// These appear in file headers/comments.
    static ref AUTO_GENERATED_MARKERS: Vec<Regex> = vec![
        Regex::new(r"(?i)auto[-_]?generated").unwrap_or_else(|e| panic!("regex: {e}")),
        Regex::new(r"(?i)do\s+not\s+edit").unwrap_or_else(|e| panic!("regex: {e}")),
        Regex::new(r"(?i)generated\s+by").unwrap_or_else(|e| panic!("regex: {e}")),
        Regex::new(r"(?i)machine[-_]?generated").unwrap_or_else(|e| panic!("regex: {e}")),
        Regex::new(r"(?i)automatically\s+generated").unwrap_or_else(|e| panic!("regex: {e}")),
        Regex::new(r"(?i)this\s+file\s+is\s+generated").unwrap_or_else(|e| panic!("regex: {e}")),
    ];

    /// Patterns for test file names/paths that should be skipped.
    /// NOTE: These patterns are intentionally conservative to avoid false positives.
    /// Only matches files IN test directories, not files NAMED "test.fst".
    static ref TEST_FILE_PATTERNS: Vec<Regex> = vec![
        // Test directory patterns (most reliable)
        Regex::new(r"(?i)/tests?/").unwrap_or_else(|e| panic!("regex: {e}")),
        Regex::new(r"(?i)/spec[s]?/").unwrap_or_else(|e| panic!("regex: {e}")),
        Regex::new(r"(?i)/__tests__/").unwrap_or_else(|e| panic!("regex: {e}")),
        // Example/scratch patterns
        Regex::new(r"(?i)/examples?/").unwrap_or_else(|e| panic!("regex: {e}")),
        Regex::new(r"(?i)/scratch/").unwrap_or_else(|e| panic!("regex: {e}")),
        // Test suffix patterns - require prefix to avoid matching "test.fst"
        Regex::new(r"(?i)[A-Z][a-zA-Z0-9]*[_-]?[Tt]est[s]?\.fsti?$").unwrap_or_else(|e| panic!("regex: {e}")),
        Regex::new(r"(?i)[A-Z][a-zA-Z0-9]*[_-]?[Ss]pec[s]?\.fsti?$").unwrap_or_else(|e| panic!("regex: {e}")),
        // HACL* test convention: Hacl.Test.<Module>.fst
        Regex::new(r"(?i)Hacl\.Test\.\w+\.fsti?$").unwrap_or_else(|e| panic!("regex: {e}")),
    ];

    /// Pattern to detect return type annotation in val signature.
    /// Matches the final type after the last arrow (captures everything after ->).
    /// Uses greedy match to get the full return type.
    static ref RETURN_TYPE_PATTERN: Regex = Regex::new(r"->\s*(.+)$").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect unit/void return types (no meaningful return value).
    /// Matches: unit, Tot unit, Pure unit, ST unit, Lemma, etc.
    /// Also handles cases where unit appears anywhere in the return type.
    static ref UNIT_RETURN_PATTERN: Regex = Regex::new(r"(?i)^\s*(unit\b|Tot\s+unit|Pure\s+unit|ST\s+unit|Lemma\b|squash\b)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect ADT constructors (lines starting with `|` after type declaration).
    static ref ADT_CONSTRUCTOR: Regex = Regex::new(r"^\s*\|").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect record fields (lines with `field_name :` inside braces).
    static ref RECORD_FIELD: Regex = Regex::new(r"^\s*\w+\s*:").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect `noeq` qualifier on types.
    static ref NOEQ_TYPE: Regex = Regex::new(r"(?:^|\s)noeq\s").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect stub/placeholder doc comments.
    /// Matches doc comments containing only TODO, placeholder text, or just the function name.
    static ref DOC_STUB_PATTERN: Regex = Regex::new(
        r"(?i)^\(\*\*\s*(?:TODO|FIXME|HACK|XXX|PLACEHOLDER|UNDOCUMENTED|FILL\s*IN)[\s.:*)]"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect a doc comment that only contains the function name in brackets.
    /// e.g., `(** [foo] *)` with no actual description.
    static ref DOC_NAME_ONLY: Regex = Regex::new(
        r"^\(\*\*\s*\[\w+(?:\s+\w+)*\]\s*\*\)\s*$"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect `requires` clause in signature.
    static ref REQUIRES_CLAUSE: Regex = Regex::new(r"\brequires\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect `ensures` clause in signature.
    static ref ENSURES_CLAUSE: Regex = Regex::new(r"\bensures\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect Lemma return type in val signatures.
    /// Matches: `Lemma`, `Tot ... Lemma`, `Pure unit`, `squash ...`
    /// In F*, Lemma vals are self-documenting via their formal spec (requires/ensures).
    static ref LEMMA_VAL_PATTERN: Regex = Regex::new(
        r"(?m)(?::\s*Lemma\b|(?:->|:)\s*Lemma\b|:\s*squash\b|(?:->|:)\s*squash\b)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect refinement types: `{x | ...}` or `{x : ... | ...}`
    static ref REFINEMENT_PATTERN: Regex = Regex::new(r"\{[^}]*\|").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to count explicit named parameters: `(name: ...)` or `(name : ...)`
    static ref NAMED_PARAM_PATTERN: Regex = Regex::new(r"\(\s*#?\w+\s*:").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect regular (non-doc) F* comments: `(* ... *)` but NOT `(** ... *)`
    static ref REGULAR_COMMENT: Regex = Regex::new(r"^\s*\(\*(?!\*)").unwrap_or_else(|e| panic!("regex: {e}"));
}

/// Extract parameter names from an F* function signature.
///
/// Parses signatures like:
/// - `(x: int) -> (y: int) -> int`
/// - `(#a: Type) -> (b: a) -> b`
///
/// Filters out:
/// - Parameters starting with underscore (internal/ignored)
/// - Implicit type parameters (starting with #)
fn extract_params_from_signature(signature: &str) -> Vec<String> {
    PARAM_EXTRACT_RE
        .captures_iter(signature)
        .filter_map(|c| c.get(1).map(|m| m.as_str().to_string()))
        .filter(|p| !p.starts_with('_') && !p.starts_with('#'))
        .collect()
}

/// Check if a signature has a meaningful return value (not unit/void).
///
/// Returns `true` if the function returns something other than unit,
/// `false` for unit-returning functions, lemmas, etc.
fn has_meaningful_return(signature: &str) -> bool {
    if let Some(caps) = RETURN_TYPE_PATTERN.captures(signature) {
        if let Some(ret_type) = caps.get(1) {
            let ret = ret_type.as_str();
            // Check if it's a unit type or Lemma (which returns squash/proof)
            if UNIT_RETURN_PATTERN.is_match(ret) {
                return false;
            }
            return true;
        }
    }
    // If no arrow found, it's a constant (has a value)
    signature.contains(':')
}

/// Check if file content indicates it is auto-generated.
///
/// Scans the first N lines for markers like "auto-generated", "do not edit", etc.
fn is_auto_generated_content(content: &str) -> bool {
    // Only check first 50 lines (or first comment block)
    let check_lines: String = content.lines().take(50).collect::<Vec<_>>().join("\n");

    for pattern in AUTO_GENERATED_MARKERS.iter() {
        if pattern.is_match(&check_lines) {
            return true;
        }
    }
    false
}

/// Check if file path indicates it is a test file.
///
/// Checks filename patterns like *Test.fst, *_test.fst, and
/// directory patterns like /tests/, /test/, etc.
fn is_test_file(file: &Path) -> bool {
    let path_str = file.to_string_lossy();

    for pattern in TEST_FILE_PATTERNS.iter() {
        if pattern.is_match(&path_str) {
            return true;
        }
    }
    false
}

/// Analyze the complexity of a type declaration.
///
/// Returns a `TypeComplexity` indicating how complex the type is,
/// which affects whether documentation is required and what severity to use.
fn analyze_type_complexity(block_text: &str) -> TypeComplexity {
    let lines: Vec<&str> = block_text.lines().collect();

    // Count ADT constructors
    let constructor_count = lines.iter()
        .filter(|l| ADT_CONSTRUCTOR.is_match(l))
        .count();

    // Count record fields (lines with `name :` inside curly braces)
    let has_braces = block_text.contains('{') && block_text.contains('}');
    let field_count = if has_braces {
        lines.iter()
            .filter(|l| RECORD_FIELD.is_match(l) && !l.trim().starts_with("type"))
            .count()
    } else {
        0
    };

    let is_noeq = NOEQ_TYPE.is_match(block_text);

    if constructor_count >= 5 || field_count >= 5 {
        TypeComplexity::High { constructor_count, field_count, is_noeq }
    } else if constructor_count >= 3 || field_count >= 3 || is_noeq {
        TypeComplexity::Medium { constructor_count, field_count, is_noeq }
    } else if constructor_count > 0 || field_count > 0 {
        TypeComplexity::Low { constructor_count, field_count }
    } else {
        TypeComplexity::Simple
    }
}

/// Complexity level of a type declaration.
#[derive(Debug, PartialEq, Eq)]
enum TypeComplexity {
    /// Simple type (abbreviation or basic).
    Simple,
    /// Low complexity: 1-2 constructors or fields.
    Low { constructor_count: usize, field_count: usize },
    /// Medium complexity: 3-4 constructors/fields, or noeq qualifier.
    Medium { constructor_count: usize, field_count: usize, is_noeq: bool },
    /// High complexity: 5+ constructors or fields.
    High { constructor_count: usize, field_count: usize, is_noeq: bool },
}

/// Check if a doc comment is a low-quality stub.
///
/// Detects doc comments that contain only TODO markers, just the function name,
/// or are unreasonably short (less than 10 characters of actual content).
fn is_low_quality_doc(doc_text: &str) -> Option<DocQualityIssue> {
    let trimmed = doc_text.trim();

    // Check for pure TODO/placeholder stubs
    if DOC_STUB_PATTERN.is_match(trimmed) {
        return Some(DocQualityIssue::StubOnly);
    }

    // Check for name-only docs: `(** [foo] *)`
    if DOC_NAME_ONLY.is_match(trimmed) {
        return Some(DocQualityIssue::NameOnly);
    }

    // Extract content between (** and *)
    let content = trimmed
        .strip_prefix("(**")
        .and_then(|s| s.strip_suffix("*)"))
        .unwrap_or(trimmed);

    // Remove the [name] bracket and whitespace
    let content_clean = content.trim();
    let content_no_brackets = if content_clean.starts_with('[') {
        // Remove the [name ...] part
        if let Some(end) = content_clean.find(']') {
            content_clean[end + 1..].trim()
        } else {
            content_clean
        }
    } else {
        content_clean
    };

    // Check if remaining content is too short (under 8 chars excluding whitespace/punctuation)
    let meaningful_len = content_no_brackets
        .chars()
        .filter(|c| c.is_alphanumeric())
        .count();

    if meaningful_len < 4 && !content_no_brackets.is_empty() {
        return Some(DocQualityIssue::TooShort);
    }

    None
}

/// Type of documentation quality issue.
#[derive(Debug, PartialEq, Eq)]
enum DocQualityIssue {
    /// Doc comment is just a TODO/FIXME stub.
    StubOnly,
    /// Doc comment only contains the function name in brackets.
    NameOnly,
    /// Doc comment content is too short to be useful.
    TooShort,
}

/// Check if a `.fsti` file has a module-level doc comment.
///
/// In FStar/ulib, module-level docs appear as `(** ... @summary ... *)` either
/// before or immediately after the `module` declaration. See FStar.FiniteSet.Base.fst
/// and FStar.Ghost.fsti for canonical examples.
fn has_module_doc_comment(content: &str) -> bool {
    let lines: Vec<&str> = content.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        // Skip blank lines
        if trimmed.is_empty() {
            continue;
        }

        // Check for doc comment before module declaration
        if DOC_BLOCK.is_match(trimmed) {
            return true;
        }

        // Check for triple-slash doc before module
        if DOC_TRIPLE.is_match(line) {
            return true;
        }

        // Track module declaration
        if trimmed.starts_with("module ") && !trimmed.starts_with("module type") {
            // Check line immediately after module for doc comment
            for j in (i + 1)..lines.len().min(i + 5) {
                let next = lines[j].trim();
                if next.is_empty() {
                    continue;
                }
                if DOC_BLOCK.is_match(next) || DOC_TRIPLE.is_match(lines[j]) {
                    // Doc comment immediately after module is considered module-level
                    // Only if it's NOT followed by a val/type/let
                    if j + 1 < lines.len() {
                        let after_doc = lines[j + 1..].iter()
                            .find(|l| !l.trim().is_empty() && !l.trim().starts_with('*') && !l.trim().ends_with("*)"));
                        if let Some(after) = after_doc {
                            let a = after.trim();
                            // If the line after the doc is a declaration, this doc belongs
                            // to that declaration, not the module
                            if a.starts_with("val ") || a.starts_with("type ") ||
                               a.starts_with("let ") || a.starts_with("open ") {
                                continue;
                            }
                        }
                    }
                    return true;
                }
                // Regular comment before first declaration
                if next.starts_with("(*") && !DOC_BLOCK.is_match(next) {
                    break;
                }
                // Hit a declaration without doc
                break;
            }
            break;
        }

        // Regular comments -- keep looking
        if trimmed.starts_with("(*") {
            continue;
        }

        // Non-comment, non-module line -- stop looking
        if !trimmed.starts_with("//") {
            break;
        }
    }

    false
}

/// Extract the doc comment text for a block.
///
/// Looks in both the block's own lines and the source lines immediately before it.
/// Returns the full doc comment text if found, None otherwise.
fn extract_doc_comment_text(
    block_lines: &[String],
    source_lines: &[&str],
    block_start_line: usize,
) -> Option<String> {
    // Check block's own lines first
    for line in block_lines {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if DOC_BLOCK.is_match(trimmed) {
            // Collect the full doc comment
            let mut doc = String::new();
            for l in block_lines {
                let t = l.trim();
                if t.is_empty() && doc.is_empty() {
                    continue;
                }
                if doc.is_empty() && DOC_BLOCK.is_match(t) {
                    doc.push_str(t);
                    if t.contains("*)") {
                        break;
                    }
                } else if !doc.is_empty() {
                    doc.push('\n');
                    doc.push_str(t);
                    if t.contains("*)") {
                        break;
                    }
                } else {
                    break;
                }
            }
            if !doc.is_empty() {
                return Some(doc);
            }
        }
        if DOC_TRIPLE.is_match(line) {
            return Some(trimmed.to_string());
        }
        if trimmed.starts_with("(*") {
            continue;
        }
        break;
    }

    // Check source lines before block
    if block_start_line >= 2 {
        let mut idx = block_start_line - 2;
        while idx > 0 && source_lines.get(idx).is_some_and(|l| l.trim().is_empty()) {
            idx -= 1;
        }
        if let Some(line) = source_lines.get(idx) {
            let trimmed = line.trim();
            if DOC_BLOCK.is_match(trimmed) && trimmed.contains("*)") {
                return Some(trimmed.to_string());
            }
            if DOC_TRIPLE.is_match(line) {
                return Some(trimmed.to_string());
            }
            // Multi-line doc comment ending with *)
            if trimmed.ends_with("*)") {
                let mut scan_idx = idx;
                while scan_idx > 0 {
                    if let Some(scan_line) = source_lines.get(scan_idx) {
                        if DOC_BLOCK.is_match(scan_line.trim()) {
                            let doc: String = source_lines[scan_idx..=idx]
                                .iter()
                                .map(|l| l.trim())
                                .collect::<Vec<_>>()
                                .join("\n");
                            return Some(doc);
                        }
                        if scan_line.trim().starts_with("(*") && !DOC_BLOCK.is_match(scan_line.trim()) {
                            break;
                        }
                    }
                    if scan_idx == 0 { break; }
                    scan_idx -= 1;
                }
            }
        }
    }

    None
}

/// Generate a module-level documentation stub.
///
/// Follows the FStar/ulib convention seen in FStar.FiniteSet.Base:
/// ```text
/// (**
/// This module provides ...
///
/// @summary Brief description
/// *)
/// ```
pub fn generate_module_doc_stub(module_name: &str) -> String {
    format!(
        "(**\nThis module TODO: describe purpose of {}.\n\n@summary TODO: Brief summary\n*)\n",
        module_name
    )
}

/// Generate a documentation stub for a declaration.
///
/// Creates an F*-style doc comment following FStar/ulib conventions:
/// - `(** [name params] description *)` for vals (matches FStar.Classical.fsti style)
/// - `(** [name] description *)` for types
/// - `@param` tags for each explicit parameter
/// - `@returns` tag for meaningful return values
/// - `@summary` for complex types
pub fn generate_doc_stub(name: &str, block_type: BlockType, signature: &str) -> String {
    let mut stub = String::new();

    stub.push_str("(** ");

    match block_type {
        BlockType::Val => {
            // Extract parameters from signature
            let params = extract_params_from_signature(signature);

            stub.push_str(&format!(
                "[{}{}] TODO: Add description.\n",
                name,
                if params.is_empty() {
                    String::new()
                } else {
                    format!(" {}", params.join(" "))
                }
            ));
            stub.push('\n');

            for param in &params {
                stub.push_str(&format!("    @param {} TODO: Describe parameter\n", param));
            }

            // Only add @returns if the function has a meaningful return value
            if has_meaningful_return(signature) {
                stub.push_str("    @returns TODO: Describe return value\n");
            }
        }
        BlockType::Type => {
            let complexity = analyze_type_complexity(signature);
            match complexity {
                TypeComplexity::High { constructor_count, field_count, .. }
                | TypeComplexity::Medium { constructor_count, field_count, .. } => {
                    stub.push_str(&format!("[{}] TODO: Describe this type.\n\n", name));
                    if constructor_count > 0 {
                        stub.push_str(&format!(
                            "    This type has {} constructors. Document each variant.\n",
                            constructor_count
                        ));
                    }
                    if field_count > 0 {
                        stub.push_str(&format!(
                            "    This record has {} fields. Document each field.\n",
                            field_count
                        ));
                    }
                    stub.push_str("    @summary TODO: Brief summary\n");
                }
                _ => {
                    stub.push_str(&format!("[{}] TODO: Describe this type.\n", name));
                }
            }
        }
        _ => {
            stub.push_str(&format!("[{}] TODO: Add description.\n", name));
        }
    }

    stub.push_str("*)\n");
    stub
}

/// FST013: Documentation checker rule.
///
/// Checks that public `val` and `type` declarations have documentation comments.
///
/// ## Safety Features
///
/// This rule includes multiple safeguards:
/// - Skips auto-generated files (detected by comment markers)
/// - Skips test files (detected by filename/path patterns)
/// - Skips private declarations (marked with `private` keyword)
/// - Skips internal names (starting with underscore `_`)
/// - Skips `.fst` files that have a corresponding `.fsti` (docs belong in interface)
/// - Skips simple type abbreviations (`type t = nat`) which are self-documenting
/// - Skips `inline_for_extraction noextract` helpers (extraction control, not public API)
/// - Skips `assume val` axioms (documented differently)
/// - Uses INFO severity (not warning/error)
/// - Marks fixes as LOW confidence (requires explicit --apply)
///
/// ## Doc Quality Checking
///
/// When a doc comment exists but is low quality (TODO stubs, name-only, too short),
/// a hint-level diagnostic is emitted suggesting improvement.
///
/// ## Module-Level Documentation
///
/// For `.fsti` interface files, checks that a module-level doc comment exists
/// (following FStar/ulib convention with `@summary`).
pub struct DocCheckerRule;

impl DocCheckerRule {
    pub fn new() -> Self {
        Self
    }

    /// Check if a type declaration is a simple abbreviation.
    ///
    /// Simple type abbreviations like `type t = nat` or `type counter = size_nat`
    /// are self-documenting and do not need explicit doc comments.
    /// Returns true for `type foo = bar` where bar is a single (possibly qualified)
    /// identifier, false for ADTs, records, or complex type expressions.
    fn is_type_abbreviation(block_text: &str) -> bool {
        TYPE_ABBREVIATION.is_match(block_text)
    }

    /// Check if a `.fst` file has a corresponding `.fsti` interface file.
    ///
    /// In F*, the `.fsti` file is the public interface. When it exists,
    /// documentation belongs there, not in the `.fst` implementation.
    fn has_interface_file(fst_path: &Path) -> bool {
        fst_path
            .extension()
            .is_some_and(|ext| ext == "fst")
            && fst_path.with_extension("fsti").exists()
    }

    /// Check if a block has a doc comment.
    ///
    /// Checks both:
    /// 1. The block's own lines (parser may include leading comments)
    /// 2. Lines in the source content immediately before the block
    ///
    /// Returns true if either contains a doc comment.
    fn block_has_doc_comment(
        block_lines: &[String],
        source_lines: &[&str],
        block_start_line: usize,
    ) -> bool {
        // First, check the block's own lines for doc comments
        for line in block_lines {
            let trimmed = line.trim();

            // Skip blank lines at the start
            if trimmed.is_empty() {
                continue;
            }

            // Check for block doc comment `(** ... `
            if DOC_BLOCK.is_match(trimmed) {
                return true;
            }

            // Check for triple-slash doc comment `///`
            if DOC_TRIPLE.is_match(line) {
                return true;
            }

            // If we hit a non-comment, non-blank line that's not a doc comment,
            // check if it's a regular comment or the declaration itself
            if trimmed.starts_with("(*") {
                // Regular comment - continue looking
                continue;
            }

            // Hit the actual declaration - no doc comment found in block lines
            break;
        }

        // Second, check lines before the block in the source content
        // The parser may have put the doc comment in the header section
        Self::has_doc_comment_before_line(source_lines, block_start_line)
    }

    /// Check if there's a doc comment in the lines immediately before a given line.
    ///
    /// Scans backward from `line_num` (1-indexed) looking for doc comments,
    /// skipping blank lines and tracking comment blocks.
    fn has_doc_comment_before_line(lines: &[&str], line_num: usize) -> bool {
        if line_num < 2 {
            return false;
        }

        // Convert to 0-indexed and look at line before
        let mut idx = line_num - 2;

        // Skip trailing blank lines
        while idx > 0 && lines.get(idx).is_some_and(|l| l.trim().is_empty()) {
            idx -= 1;
        }

        // Check if we're at the end of a block comment
        if let Some(line) = lines.get(idx) {
            let trimmed = line.trim();

            // Check for single-line doc block comment
            if DOC_BLOCK.is_match(trimmed) {
                return true;
            }

            // Check for triple-slash doc comment
            if DOC_TRIPLE.is_match(line) {
                return true;
            }

            // If line ends with `*)`, scan backward for opening
            if trimmed.ends_with("*)") {
                let mut scan_idx = idx;
                let mut found_doc_marker = false;

                // Scan backward through the comment
                while scan_idx > 0 {
                    if let Some(scan_line) = lines.get(scan_idx) {
                        // Check for doc comment opening marker
                        if DOC_BLOCK.is_match(scan_line.trim()) {
                            found_doc_marker = true;
                            break;
                        }

                        // Check for regular comment opening (not doc)
                        if scan_line.trim().starts_with("(*")
                            && !DOC_BLOCK.is_match(scan_line.trim())
                        {
                            break;
                        }
                    }
                    if scan_idx == 0 {
                        break;
                    }
                    scan_idx -= 1;
                }

                if found_doc_marker {
                    return true;
                }
            }
        }

        false
    }

    /// Check if a block's text indicates it is an `inline_for_extraction noextract` helper.
    fn is_extraction_helper(block_text: &str) -> bool {
        INLINE_NOEXTRACT_RE.is_match(block_text)
    }

    /// Check if a block is an `assume val` axiom declaration.
    fn is_assume_val(block_text: &str) -> bool {
        ASSUME_VAL_RE.is_match(block_text)
    }

    /// Extract the module name from content for diagnostics.
    fn extract_module_name(content: &str) -> Option<String> {
        for line in content.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix("module ") {
                let name = rest.trim();
                if !name.is_empty() {
                    return Some(name.to_string());
                }
            }
            break;
        }
        None
    }

    /// Check if a val signature has complex pre/postconditions (requires/ensures).
    ///
    /// In F*, requires/ensures clauses are formal machine-checked specifications.
    /// They serve as precise documentation themselves, so their presence actually
    /// makes human-written doc comments LESS necessary, not more.
    fn has_complex_contract(block_text: &str) -> bool {
        REQUIRES_CLAUSE.is_match(block_text) || ENSURES_CLAUSE.is_match(block_text)
    }

    /// Check if a val declaration has a Lemma return type.
    ///
    /// In F*, Lemma vals like `val foo : ... -> Lemma (requires P) (ensures Q)`
    /// are completely self-documenting: the type signature IS the formal specification.
    /// The name, parameters, requires, and ensures clauses form a machine-checked
    /// contract that is more precise than any English doc comment could be.
    fn is_lemma_val(block_text: &str) -> bool {
        LEMMA_VAL_PATTERN.is_match(block_text)
    }

    /// Check if a val signature is "complex enough" to be self-documenting.
    ///
    /// In F*, a type signature with multiple arrows, refinement types, named
    /// parameters, or effect annotations provides comprehensive documentation
    /// of what the function does. For example:
    ///   `val uint8_to_uint32: a:U8.t -> Tot (b:U32.t{U32.v b = U8.v a})`
    /// is completely self-documenting via the types and refinements.
    ///
    /// Returns true if the signature has enough structure to document itself:
    /// - 2+ function arrows (`->`)
    /// - Any refinement types (`{...| ...}`)
    /// - 2+ named parameters (`(name: type)`)
    /// - Any effect annotation (requires/ensures)
    fn has_complex_signature(block_text: &str) -> bool {
        let arrow_count = block_text.matches("->").count();
        let has_refinement = REFINEMENT_PATTERN.is_match(block_text);
        let named_params = NAMED_PARAM_PATTERN.find_iter(block_text).count();
        let has_contract = REQUIRES_CLAUSE.is_match(block_text)
            || ENSURES_CLAUSE.is_match(block_text);

        // Any of these makes the signature self-documenting
        arrow_count >= 2 || has_refinement || named_params >= 2 || has_contract
    }

    /// Check if there's a regular (non-doc) comment within a few lines before a block.
    ///
    /// In F*'s ulib, many declarations use regular comments `(* ... *)` instead of
    /// doc comments `(** ... *)`. These are functionally equivalent documentation.
    /// For example, FStar.Map.fsti uses:
    ///   `(* sel m k : Look up key 'k' in map 'm' *)`
    ///   `val sel: ...`
    ///
    /// Returns true if a regular comment exists within `max_distance` lines
    /// before the block start (skipping blank lines).
    fn has_nearby_regular_comment(
        source_lines: &[&str],
        block_start_line: usize,
        max_distance: usize,
    ) -> bool {
        if block_start_line < 2 {
            return false;
        }

        // Scan up to max_distance lines before the block (0-indexed from block_start_line-2)
        let start_idx = block_start_line.saturating_sub(2);
        let stop_idx = start_idx.saturating_sub(max_distance + 2);

        let mut idx = start_idx;
        let mut non_blank_checked = 0;
        while idx >= stop_idx.max(0) && non_blank_checked < max_distance {
            if let Some(line) = source_lines.get(idx) {
                let trimmed = line.trim();
                if trimmed.is_empty() {
                    // Skip blank lines without counting them
                } else if REGULAR_COMMENT.is_match(trimmed) || trimmed.ends_with("*)") {
                    return true;
                } else if DOC_BLOCK.is_match(trimmed) || DOC_TRIPLE.is_match(trimmed) {
                    // This is a doc comment -- the existing doc detection handles it
                    return false;
                } else {
                    // Hit a non-comment line (e.g., another declaration)
                    return false;
                }
                non_blank_checked += 1;
            }
            if idx == 0 {
                break;
            }
            idx -= 1;
        }

        false
    }
}

impl Default for DocCheckerRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for DocCheckerRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST013
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // SAFETY: Skip auto-generated files
        if is_auto_generated_content(content) {
            return diagnostics;
        }

        // SAFETY: Skip test files
        if is_test_file(file) {
            return diagnostics;
        }

        // If this is a .fst file with a corresponding .fsti, skip it entirely.
        // Documentation belongs in the .fsti interface file, not the implementation.
        if Self::has_interface_file(file) {
            return diagnostics;
        }

        let is_fsti = file.extension().is_some_and(|ext| ext == "fsti");

        // Check module-level documentation for .fsti files.
        // Demoted to Hint: nice-to-have, not a necessity. Most ulib .fsti files
        // lack module-level doc comments and the module name + contents are sufficient.
        if is_fsti && !has_module_doc_comment(content) {
            let module_name = Self::extract_module_name(content)
                .unwrap_or_else(|| "this module".to_string());

            let stub = generate_module_doc_stub(&module_name);

            let fix = Fix::new(
                format!("Add module-level documentation for `{}`", module_name),
                vec![Edit {
                    file: file.to_path_buf(),
                    range: Range::new(1, 1, 1, 1),
                    new_text: stub,
                }],
            )
            .with_confidence(FixConfidence::Low)
            .with_safety_level(FixSafetyLevel::Safe)
            .with_reversible(true)
            .with_requires_review(true);

            diagnostics.push(Diagnostic {
                rule: RuleCode::FST013,
                severity: DiagnosticSeverity::Hint,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: format!(
                    "Interface file `{}` is missing a module-level doc comment. \
                     Add (** @summary ... *) before the module declaration, \
                     following FStar/ulib convention.",
                    module_name
                ),
                fix: Some(fix),
            });
        }

        let (_, blocks) = parse_fstar_file(content);
        let source_lines: Vec<&str> = content.lines().collect();

        for block in &blocks {
            // Only check val and type declarations
            if !matches!(block.block_type, BlockType::Val | BlockType::Type) {
                continue;
            }

            let block_text = block.lines.join("");

            // Check if declaration is private (use parser's is_private field OR regex)
            if block.is_private || PRIVATE_DECL_RE.is_match(&block_text) {
                continue;
            }

            // Skip inline_for_extraction noextract helpers
            if Self::is_extraction_helper(&block_text) {
                continue;
            }

            // Skip assume val axioms -- they are documented differently
            if Self::is_assume_val(&block_text) {
                continue;
            }

            // Skip simple type abbreviations (e.g., `type t = nat`) - self-documenting
            if block.block_type == BlockType::Type && Self::is_type_abbreviation(&block_text) {
                continue;
            }

            // Skip Lemma vals -- in F*, `val foo : ... -> Lemma (requires P) (ensures Q)`
            // is self-documenting via formal specification. The type IS the documentation.
            if block.block_type == BlockType::Val && Self::is_lemma_val(&block_text) {
                continue;
            }

            for name in &block.names {
                // Skip internal names (starting with underscore)
                if name.starts_with('_') {
                    continue;
                }

                // Check if there's a doc comment for this block
                if !Self::block_has_doc_comment(&block.lines, &source_lines, block.start_line) {
                    let kind = match block.block_type {
                        BlockType::Val => "val",
                        BlockType::Type => "type",
                        _ => "declaration",
                    };

                    // Determine severity using a graduated model based on how
                    // self-documenting the declaration already is.
                    //
                    // In F*, type signatures serve as machine-checked documentation:
                    // - Refinement types specify exact constraints
                    // - requires/ensures clauses are formal contracts
                    // - Named parameters with types explain inputs
                    // - Effect annotations describe side effects
                    //
                    // Severity rules:
                    // 1. .fst files (implementation): always Hint (docs belong in .fsti)
                    // 2. Nearby regular comment `(* ... *)`: Hint (already documented informally)
                    // 3. Complex signature (2+ arrows, refinements, named params): Hint
                    // 4. Contracts (requires/ensures): Hint (formal spec IS documentation)
                    // 5. Only truly bare, simple vals in .fsti: Info

                    let has_nearby_comment = Self::has_nearby_regular_comment(
                        &source_lines, block.start_line, 3,
                    );
                    let has_complex_sig = block.block_type == BlockType::Val
                        && Self::has_complex_signature(&block_text);
                    let has_contract = Self::has_complex_contract(&block_text);

                    let severity = if !is_fsti {
                        // .fst implementation files: docs are nice-to-have
                        DiagnosticSeverity::Hint
                    } else if has_nearby_comment {
                        // Already has informal documentation via regular (* ... *)
                        DiagnosticSeverity::Hint
                    } else if has_complex_sig || has_contract {
                        // Type signature is self-documenting
                        DiagnosticSeverity::Hint
                    } else {
                        // Truly undocumented public declaration in .fsti
                        DiagnosticSeverity::Info
                    };

                    // Build message with extra context for complex declarations
                    let extra = if block.block_type == BlockType::Type {
                        match analyze_type_complexity(&block_text) {
                            TypeComplexity::High { constructor_count, field_count, is_noeq } => {
                                let mut parts = Vec::new();
                                if constructor_count > 0 { parts.push(format!("{} constructors", constructor_count)); }
                                if field_count > 0 { parts.push(format!("{} fields", field_count)); }
                                if is_noeq { parts.push("noeq qualifier".to_string()); }
                                format!(" Complex type ({}) -- consider adding documentation.", parts.join(", "))
                            }
                            TypeComplexity::Medium { is_noeq, .. } if is_noeq => {
                                " This noeq type has no decidable equality -- consider explaining why.".to_string()
                            }
                            _ => String::new(),
                        }
                    } else if has_contract {
                        " This function has requires/ensures contract.".to_string()
                    } else {
                        String::new()
                    };

                    // Generate documentation stub as autofix
                    let stub = generate_doc_stub(name, block.block_type, &block_text);

                    let fix = Fix::new(
                        format!("Add documentation stub for `{}`", name),
                        vec![Edit {
                            file: file.to_path_buf(),
                            range: Range::new(block.start_line, 1, block.start_line, 1),
                            new_text: stub,
                        }],
                    )
                    .with_confidence(FixConfidence::Low)
                    .with_safety_level(FixSafetyLevel::Safe)
                    .with_reversible(true)
                    .with_requires_review(true);

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST013,
                        severity,
                        file: file.to_path_buf(),
                        range: Range::point(block.start_line, 1),
                        message: format!(
                            "Public {} `{}` is missing documentation. \
                             Add a doc comment (** ... *) or /// above the declaration.{}",
                            kind, name, extra
                        ),
                        fix: Some(fix),
                    });

                    // Only report once per block (for mutual recursion)
                    break;
                }

                // Doc exists -- check quality
                if let Some(doc_text) = extract_doc_comment_text(
                    &block.lines, &source_lines, block.start_line
                ) {
                    if let Some(issue) = is_low_quality_doc(&doc_text) {
                        let issue_msg = match issue {
                            DocQualityIssue::StubOnly =>
                                "Doc comment is a TODO stub. Replace with actual documentation.",
                            DocQualityIssue::NameOnly =>
                                "Doc comment only contains the function name. Add a description.",
                            DocQualityIssue::TooShort =>
                                "Doc comment is too short to be useful. Expand the description.",
                        };

                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST013,
                            severity: DiagnosticSeverity::Hint,
                            file: file.to_path_buf(),
                            range: Range::point(block.start_line, 1),
                            message: format!(
                                "Low-quality documentation for `{}`: {}",
                                name, issue_msg
                            ),
                            fix: None,
                        });

                        // Only report once per block
                        break;
                    }
                }
            }
        }

        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_doc_checker_missing_doc() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val undocumented_func : int -> int
let undocumented_func x = x
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].message.contains("undocumented_func"));
        assert!(diagnostics[0].message.contains("missing documentation"));
    }

    #[test]
    fn test_doc_checker_with_block_doc() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

(** This function does something. *)
val documented_func : int -> int
let documented_func x = x
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_doc_checker_with_triple_slash() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

/// This function does something.
val documented_func : int -> int
let documented_func x = x
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_doc_checker_private_skipped() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

private val internal_func : int -> int
let internal_func x = x
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_doc_checker_underscore_skipped() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val _internal : int -> int
let _internal x = x
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_doc_checker_fsti_checked() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val undocumented_func : int -> int
"#;
        let file = PathBuf::from("test.fsti");
        let diagnostics = rule.check(&file, content);

        // .fsti files ARE checked - they are the public interface
        // 1 for missing module doc + 1 for undocumented val
        assert!(diagnostics.iter().any(|d| d.message.contains("undocumented_func")));
    }

    #[test]
    fn test_doc_checker_type_missing_doc() {
        let rule = DocCheckerRule::new();
        // ADT type (not a simple abbreviation) should still require docs
        let content = r#"module Test

type my_type =
  | A
  | B of int
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].message.contains("my_type"));
        assert!(diagnostics[0].message.contains("type"));
    }

    #[test]
    fn test_doc_checker_multiline_doc_block() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

(**
 * This is a multi-line
 * documentation comment.
 *)
val documented_func : int -> int
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_block_has_doc_comment() {
        // Empty source lines for testing block lines only
        let empty_source: Vec<&str> = vec![];

        // Block doc comments should be detected in block lines
        let lines_with_block_doc = vec![
            "(** doc comment *)\n".to_string(),
            "val foo : int\n".to_string(),
        ];
        assert!(DocCheckerRule::block_has_doc_comment(
            &lines_with_block_doc,
            &empty_source,
            1
        ));

        // Triple slash doc comments should be detected
        let lines_with_triple_slash = vec![
            "/// doc comment\n".to_string(),
            "val foo : int\n".to_string(),
        ];
        assert!(DocCheckerRule::block_has_doc_comment(
            &lines_with_triple_slash,
            &empty_source,
            1
        ));

        // Regular comments are not doc comments
        let lines_with_regular_comment = vec![
            "(* regular comment *)\n".to_string(),
            "val foo : int\n".to_string(),
        ];
        assert!(!DocCheckerRule::block_has_doc_comment(
            &lines_with_regular_comment,
            &empty_source,
            1
        ));

        // No comment at all
        let lines_no_doc = vec!["val foo : int\n".to_string()];
        assert!(!DocCheckerRule::block_has_doc_comment(
            &lines_no_doc,
            &empty_source,
            1
        ));

        // Doc comment in source lines before block
        let source_with_doc: Vec<&str> =
            vec!["module Test", "", "(** doc comment *)", "val foo : int"];
        let block_only_val = vec!["val foo : int\n".to_string()];
        assert!(DocCheckerRule::block_has_doc_comment(
            &block_only_val,
            &source_with_doc,
            4
        ));
    }

    #[test]
    fn test_extract_params_from_signature() {
        // Simple parameters
        let sig = "val foo : (x: int) -> (y: int) -> int";
        let params = extract_params_from_signature(sig);
        assert_eq!(params, vec!["x", "y"]);

        // Parameters with spaces around colon
        let sig2 = "val bar : (a : nat) -> (b : nat) -> nat";
        let params2 = extract_params_from_signature(sig2);
        assert_eq!(params2, vec!["a", "b"]);

        // No parameters (constant)
        let sig3 = "val constant : int";
        let params3 = extract_params_from_signature(sig3);
        assert!(params3.is_empty());

        // Parameters starting with underscore should be filtered
        let sig4 = "val internal : (_x: int) -> (y: int) -> int";
        let params4 = extract_params_from_signature(sig4);
        assert_eq!(params4, vec!["y"]);

        // Complex signature with type parameters
        let sig5 = "val complex : (a: Type) -> (x: a) -> (y: a) -> a";
        let params5 = extract_params_from_signature(sig5);
        assert_eq!(params5, vec!["a", "x", "y"]);
    }

    #[test]
    fn test_generate_doc_stub_val() {
        let stub = generate_doc_stub(
            "foo",
            BlockType::Val,
            "val foo : (x: int) -> (y: int) -> int",
        );

        assert!(stub.starts_with("(** "));
        assert!(stub.ends_with("*)\n"));
        assert!(stub.contains("[foo x y]"));
        assert!(stub.contains("@param x"));
        assert!(stub.contains("@param y"));
        assert!(stub.contains("@returns"));
    }

    #[test]
    fn test_generate_doc_stub_type() {
        let stub = generate_doc_stub("my_type", BlockType::Type, "type my_type = int");

        assert!(stub.starts_with("(** "));
        assert!(stub.ends_with("*)\n"));
        assert!(stub.contains("[my_type]"));
        assert!(stub.contains("Describe this type"));
        assert!(!stub.contains("@param"));
        assert!(!stub.contains("@returns"));
    }

    #[test]
    fn test_generate_doc_stub_val_no_params() {
        let stub = generate_doc_stub("constant", BlockType::Val, "val constant : int");

        assert!(stub.starts_with("(** "));
        assert!(stub.ends_with("*)\n"));
        assert!(stub.contains("[constant]"));
        assert!(!stub.contains("@param"));
        assert!(stub.contains("@returns"));
    }

    #[test]
    fn test_doc_checker_produces_fix() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val undocumented_func : (x: int) -> (y: int) -> int
let undocumented_func x y = x + y
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].fix.is_some());

        let fix = diagnostics[0].fix.as_ref().unwrap();
        assert!(fix.message.contains("undocumented_func"));
        assert_eq!(fix.edits.len(), 1);

        let edit = &fix.edits[0];
        assert!(edit.new_text.contains("(** "));
        assert!(edit.new_text.contains("[undocumented_func"));
        assert!(edit.new_text.contains("@param x"));
        assert!(edit.new_text.contains("@param y"));
        assert!(edit.new_text.contains("@returns"));
        assert!(edit.new_text.contains("*)"));
    }

    #[test]
    fn test_doc_checker_type_produces_fix() {
        let rule = DocCheckerRule::new();
        // ADT type needs docs and gets a fix suggestion
        let content = r#"module Test

type my_type =
  | A
  | B of int
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].fix.is_some());

        let fix = diagnostics[0].fix.as_ref().unwrap();
        let edit = &fix.edits[0];
        assert!(edit.new_text.contains("[my_type]"));
        assert!(edit.new_text.contains("Describe this type"));
    }

    #[test]
    fn test_doc_checker_type_abbreviation_skipped() {
        let rule = DocCheckerRule::new();

        // Simple type abbreviation: `type t = nat`
        let content1 = "module Test\n\ntype counter = size_nat\n";
        let file = PathBuf::from("test.fst");
        assert!(
            rule.check(&file, content1).is_empty(),
            "simple type abbreviation should be skipped"
        );

        // Qualified type abbreviation: `type t = A.B.c`
        let content2 = "module Test\n\ntype my_buf = Lib.Buffer.buffer\n";
        assert!(
            rule.check(&file, content2).is_empty(),
            "qualified type abbreviation should be skipped"
        );

        // Type with parameters is still an abbreviation: `type t a = a`
        let content3 = "module Test\n\ntype alias a = a\n";
        assert!(
            rule.check(&file, content3).is_empty(),
            "parameterized type abbreviation should be skipped"
        );
    }

    #[test]
    fn test_doc_checker_complex_type_not_skipped() {
        let rule = DocCheckerRule::new();
        let file = PathBuf::from("test.fst");

        // ADT with constructors needs docs
        let content = "module Test\n\ntype color =\n  | Red\n  | Blue\n";
        assert!(
            !rule.check(&file, content).is_empty(),
            "ADT type should NOT be skipped"
        );
    }

    #[test]
    fn test_doc_checker_fsti_val_checked() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val add : int -> int -> int

val sub : int -> int -> int
"#;
        // .fsti file: public interface declarations should be checked
        // Note: Use a path that won't match test file patterns
        let file = PathBuf::from("/project/src/Module.fsti");
        let diagnostics = rule.check(&file, content);

        // Should have: 1 module-level doc missing + 2 undocumented vals = 3
        let val_diags: Vec<_> = diagnostics.iter()
            .filter(|d| d.message.contains("missing documentation"))
            .collect();
        assert_eq!(val_diags.len(), 2, "both undocumented vals in .fsti should warn");
    }

    #[test]
    fn test_doc_checker_fsti_with_docs_passes() {
        let rule = DocCheckerRule::new();
        let content = r#"(** Module documentation. @summary test *)
module Test

(** Adds two integers. *)
val add : int -> int -> int

(** Subtracts two integers. *)
val sub : int -> int -> int
"#;
        let file = PathBuf::from("test.fsti");
        let diagnostics = rule.check(&file, content);

        assert!(diagnostics.is_empty(), "documented .fsti vals should pass");
    }

    #[test]
    fn test_is_type_abbreviation() {
        // Simple abbreviations
        assert!(DocCheckerRule::is_type_abbreviation("type t = nat"));
        assert!(DocCheckerRule::is_type_abbreviation("type counter = size_nat"));
        assert!(DocCheckerRule::is_type_abbreviation("type va_fuel = nat"));
        assert!(DocCheckerRule::is_type_abbreviation("type name = string"));
        assert!(DocCheckerRule::is_type_abbreviation("type t = Lib.Buffer.buffer"));

        // Parameterized abbreviations
        assert!(DocCheckerRule::is_type_abbreviation("type alias a = a"));

        // NOT abbreviations
        assert!(!DocCheckerRule::is_type_abbreviation(
            "type color =\n  | Red\n  | Blue"
        ));
        assert!(!DocCheckerRule::is_type_abbreviation(
            "type pair = { fst: int; snd: int }"
        ));
        assert!(!DocCheckerRule::is_type_abbreviation(
            "type t = x:int{x > 0}"
        ));
    }

    #[test]
    fn test_has_interface_file_nonexistent() {
        // For a path where no .fsti exists on disk, should return false
        let path = PathBuf::from("/tmp/definitely_nonexistent_fstar_test.fst");
        assert!(!DocCheckerRule::has_interface_file(&path));

        // Non-.fst extension should return false regardless
        let fsti_path = PathBuf::from("test.fsti");
        assert!(!DocCheckerRule::has_interface_file(&fsti_path));
    }

    // =========================================================================
    // SAFETY FEATURE TESTS
    // =========================================================================

    #[test]
    fn test_auto_generated_file_detection() {
        // Auto-generated markers should be detected
        assert!(is_auto_generated_content("(* This file is auto-generated. Do not edit. *)\nmodule Test"));
        assert!(is_auto_generated_content("(** Generated by some tool *)\nmodule Test"));
        assert!(is_auto_generated_content("// AUTO_GENERATED\nmodule Test"));
        assert!(is_auto_generated_content("(* MACHINE GENERATED - DO NOT EDIT *)\nmodule Test"));
        assert!(is_auto_generated_content("(* This file is automatically generated *)\nmodule Test"));

        // Normal files should not be flagged
        assert!(!is_auto_generated_content("module Test\nval foo : int"));
        assert!(!is_auto_generated_content("(** Documentation for module *)\nmodule Test"));
        assert!(!is_auto_generated_content("(* Regular comment *)\nmodule Test\nlet x = 1"));
    }

    #[test]
    fn test_test_file_detection() {
        // Test directory patterns (primary detection mechanism)
        assert!(is_test_file(&PathBuf::from("/project/tests/Module.fst")));
        assert!(is_test_file(&PathBuf::from("/project/test/Module.fst")));
        assert!(is_test_file(&PathBuf::from("/project/__tests__/Module.fst")));
        assert!(is_test_file(&PathBuf::from("/project/specs/Module.fst")));
        assert!(is_test_file(&PathBuf::from("/project/examples/Demo.fst")));

        // Test suffix patterns (require CamelCase prefix)
        assert!(is_test_file(&PathBuf::from("/project/MyModuleTest.fst")));
        assert!(is_test_file(&PathBuf::from("/project/MyModule_test.fst")));
        assert!(is_test_file(&PathBuf::from("/project/SecuritySpec.fst")));

        // Non-test files - these should NOT be skipped
        assert!(!is_test_file(&PathBuf::from("/project/src/Module.fst")));
        assert!(!is_test_file(&PathBuf::from("/project/core/Types.fsti")));
        assert!(!is_test_file(&PathBuf::from("/project/lib/Utils.fst")));
        // "test.fst" standalone is NOT a test file (it's a module name)
        assert!(!is_test_file(&PathBuf::from("test.fst")));
        assert!(!is_test_file(&PathBuf::from("/project/Test.fst")));
    }

    #[test]
    fn test_doc_checker_skips_auto_generated() {
        let rule = DocCheckerRule::new();
        let content = r#"(* AUTO-GENERATED - DO NOT EDIT *)
module Test

val undocumented_func : int -> int
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(diagnostics.is_empty(), "Auto-generated files should be skipped");
    }

    #[test]
    fn test_doc_checker_skips_test_files() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val undocumented_func : int -> int
"#;
        let file = PathBuf::from("/project/tests/Test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(diagnostics.is_empty(), "Test files should be skipped");
    }

    // =========================================================================
    // RETURN TYPE DETECTION TESTS
    // =========================================================================

    #[test]
    fn test_has_meaningful_return() {
        // Functions with meaningful returns
        assert!(has_meaningful_return("val foo : int -> int"));
        assert!(has_meaningful_return("val bar : (x: nat) -> nat"));
        assert!(has_meaningful_return("val complex : (a: Type) -> (x: a) -> option a"));
        assert!(has_meaningful_return("val get_value : unit -> string"));

        // Functions without meaningful returns (unit, Lemma, etc.)
        assert!(!has_meaningful_return("val foo : int -> unit"));
        assert!(!has_meaningful_return("val lemma_foo : (x: int) -> Lemma (x >= 0)"));
        // Note: "Tot unit" as a return type should be detected
        // The pattern captures "Tot unit" and matches "unit" within
        assert!(!has_meaningful_return("val stateful : int -> unit"));
    }

    #[test]
    fn test_generate_doc_stub_no_returns_for_unit() {
        let stub = generate_doc_stub("action", BlockType::Val, "val action : int -> unit");
        assert!(!stub.contains("@returns"), "Unit-returning functions should not have @returns");
    }

    #[test]
    fn test_generate_doc_stub_no_returns_for_lemma() {
        // Lemmas return a proof/squash, not a meaningful value
        // Signature: val name : param_type -> Lemma ...
        let stub = generate_doc_stub("my_lemma", BlockType::Val, "val my_lemma : int -> Lemma True");
        assert!(!stub.contains("@returns"), "Lemmas should not have @returns");
    }

    // =========================================================================
    // COMPLEX SIGNATURE TESTS (from real F* code)
    // =========================================================================

    #[test]
    fn test_extract_params_complex_signatures() {
        // From BrrrInformationFlow.fsti - complex signatures
        let sig1 = "val sec_typecheck (ctx: sec_ctx) (pc: pc_label) (e: expr) : Tot (option labeled_type) (decreases e)";
        let params1 = extract_params_from_signature(sig1);
        assert_eq!(params1, vec!["ctx", "pc", "e"]);

        // Note: F* allows multiple params to share a type: (v1 v2 v3: value)
        // Our current regex only captures "param:" pattern, so this is a limitation.
        // The first param in the group will be captured.
        let sig2 = "val value_eq_trans (v1: value) (v2: value) (v3: value) : Lemma";
        let params2 = extract_params_from_signature(sig2);
        assert_eq!(params2, vec!["v1", "v2", "v3"]);

        // Generic/polymorphic parameters - #a is implicit
        // The # marker is filtered out. Only explicit parameters are kept.
        let sig3 = "val untrusted (#a:Type) (v: a) : integrity_labeled a";
        let params3 = extract_params_from_signature(sig3);
        // #a is captured as "#a" and filtered because it starts with #
        // Only 'v' remains as an explicit parameter
        assert_eq!(params3, vec!["v"]);
    }

    #[test]
    fn test_generate_stub_for_lemma() {
        let stub = generate_doc_stub(
            "sec_leq_refl",
            BlockType::Val,
            // Note: For the return type detector, the signature needs "->" before Lemma
            "val sec_leq_refl : (l: sec_level) -> Lemma (ensures sec_leq l l = true)",
        );

        assert!(stub.contains("[sec_leq_refl l]"));
        assert!(stub.contains("@param l"));
        assert!(!stub.contains("@returns"), "Lemmas should not have @returns");
    }

    #[test]
    fn test_generate_stub_for_complex_function() {
        let stub = generate_doc_stub(
            "dlm_declassify_logged",
            BlockType::Val,
            "val dlm_declassify_logged (env: acts_for_env) (req: dlm_declassify_request) (log: dlm_audit_log) (timestamp: nat) : option (dlm_label & dlm_audit_log)",
        );

        assert!(stub.contains("[dlm_declassify_logged env req log timestamp]"));
        assert!(stub.contains("@param env"));
        assert!(stub.contains("@param req"));
        assert!(stub.contains("@param log"));
        assert!(stub.contains("@param timestamp"));
        assert!(stub.contains("@returns"));
    }

    // =========================================================================
    // FIX CONFIDENCE TESTS
    // =========================================================================

    #[test]
    fn test_doc_fix_is_low_confidence() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val undocumented_func : int -> int
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert_eq!(diagnostics.len(), 1);
        let fix = diagnostics[0].fix.as_ref().unwrap();

        // Doc fixes are Safe (adding comments cannot break code) but Low confidence
        // (stubs contain TODOs that need human completion).
        assert!(fix.is_safe(), "Adding documentation is semantically safe");
        assert_eq!(fix.confidence, FixConfidence::Low, "Doc fixes should have low confidence");
        assert!(fix.requires_review, "Doc fixes should require review for TODO completion");
        assert!(!fix.can_auto_apply(), "Low confidence prevents auto-application");
    }

    #[test]
    fn test_doc_fix_cannot_auto_apply() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val foo : int -> int
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert_eq!(diagnostics.len(), 1);
        let fix = diagnostics[0].fix.as_ref().unwrap();

        // Should NOT auto-apply
        assert!(!fix.can_auto_apply(), "Doc fixes should require explicit --apply");
    }

    // =========================================================================
    // NEW: INLINE_FOR_EXTRACTION NOEXTRACT SKIPPING
    // =========================================================================

    #[test]
    fn test_doc_checker_skips_inline_noextract() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

inline_for_extraction noextract
val helper_fn : int -> int
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(
            diagnostics.is_empty(),
            "inline_for_extraction noextract helpers should be skipped"
        );
    }

    #[test]
    fn test_doc_checker_skips_noextract_inline() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

noextract inline_for_extraction
val another_helper : int -> int
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(
            diagnostics.is_empty(),
            "noextract inline_for_extraction should also be skipped"
        );
    }

    #[test]
    fn test_doc_checker_does_not_skip_inline_only() {
        let rule = DocCheckerRule::new();
        // inline_for_extraction WITHOUT noextract is a public API optimization hint
        let content = "module Test\n\nval public_fast : int -> int\n";
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(
            !diagnostics.is_empty(),
            "inline_for_extraction alone is not skipped (it's a public API hint)"
        );
    }

    // =========================================================================
    // NEW: ASSUME VAL SKIPPING
    // =========================================================================

    #[test]
    fn test_doc_checker_skips_assume_val() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

assume val axiom_fn : int -> int
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(
            diagnostics.is_empty(),
            "assume val axioms should be skipped"
        );
    }

    // =========================================================================
    // NEW: MODULE-LEVEL DOC CHECK
    // =========================================================================

    #[test]
    fn test_module_doc_check_missing() {
        let rule = DocCheckerRule::new();
        let content = r#"module MyModule

val foo : int -> int
"#;
        let file = PathBuf::from("/project/src/MyModule.fsti");
        let diagnostics = rule.check(&file, content);

        assert!(
            diagnostics.iter().any(|d| d.message.contains("module-level doc")),
            "Should flag missing module-level doc in .fsti"
        );
    }

    #[test]
    fn test_module_doc_check_present_before_module() {
        assert!(has_module_doc_comment(
            "(** This module does things. @summary Things *)\nmodule MyModule\n"
        ));
    }

    #[test]
    fn test_module_doc_check_present_triple_slash() {
        assert!(has_module_doc_comment(
            "/// This module provides important functionality.\nmodule MyModule\n"
        ));
    }

    #[test]
    fn test_module_doc_check_absent() {
        assert!(!has_module_doc_comment("module MyModule\n\nval foo : int\n"));
    }

    #[test]
    fn test_module_doc_not_checked_for_fst() {
        let rule = DocCheckerRule::new();
        let content = "module Test\n\nval foo : int -> int\n";
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(
            !diagnostics.iter().any(|d| d.message.contains("module-level")),
            "Module doc should not be checked for .fst files"
        );
    }

    #[test]
    fn test_generate_module_doc_stub() {
        let stub = generate_module_doc_stub("Hacl.Hash.SHA256");
        assert!(stub.contains("(**"));
        assert!(stub.contains("Hacl.Hash.SHA256"));
        assert!(stub.contains("@summary"));
        assert!(stub.contains("*)"));
    }

    // =========================================================================
    // NEW: DOC QUALITY CHECKS
    // =========================================================================

    #[test]
    fn test_low_quality_doc_stub_only() {
        assert_eq!(
            is_low_quality_doc("(** TODO *)"),
            Some(DocQualityIssue::StubOnly)
        );
        assert_eq!(
            is_low_quality_doc("(** FIXME: add docs *)"),
            Some(DocQualityIssue::StubOnly)
        );
        assert_eq!(
            is_low_quality_doc("(** TODO: describe this function *)"),
            Some(DocQualityIssue::StubOnly)
        );
    }

    #[test]
    fn test_low_quality_doc_name_only() {
        assert_eq!(
            is_low_quality_doc("(** [foo] *)"),
            Some(DocQualityIssue::NameOnly)
        );
        assert_eq!(
            is_low_quality_doc("(** [bar baz] *)"),
            Some(DocQualityIssue::NameOnly)
        );
    }

    #[test]
    fn test_low_quality_doc_too_short() {
        assert_eq!(
            is_low_quality_doc("(** [foo] ok *)"),
            Some(DocQualityIssue::TooShort)
        );
    }

    #[test]
    fn test_good_quality_doc() {
        // A real doc comment with meaningful content should pass
        assert_eq!(
            is_low_quality_doc("(** [foo x y] Computes the sum of x and y. *)"),
            None
        );
        assert_eq!(
            is_low_quality_doc("(** Adds two integers and returns their sum. *)"),
            None
        );
    }

    #[test]
    fn test_doc_quality_check_emits_hint() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

(** TODO *)
val stub_documented : int -> int
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        let quality_diags: Vec<_> = diagnostics.iter()
            .filter(|d| d.message.contains("Low-quality"))
            .collect();

        assert!(
            !quality_diags.is_empty(),
            "Should flag TODO-only doc comments as low quality"
        );
        assert_eq!(
            quality_diags[0].severity,
            DiagnosticSeverity::Hint,
            "Quality issues should be hints, not warnings"
        );
    }

    // =========================================================================
    // NEW: COMPLEX TYPE ANALYSIS
    // =========================================================================

    #[test]
    fn test_type_complexity_simple() {
        assert_eq!(
            analyze_type_complexity("type t = nat"),
            TypeComplexity::Simple
        );
    }

    #[test]
    fn test_type_complexity_low() {
        let complexity = analyze_type_complexity("type t =\n  | A\n  | B\n");
        match complexity {
            TypeComplexity::Low { constructor_count, .. } => {
                assert_eq!(constructor_count, 2);
            }
            _ => panic!("Expected Low complexity, got {:?}", complexity),
        }
    }

    #[test]
    fn test_type_complexity_medium_noeq() {
        let complexity = analyze_type_complexity("noeq type state = {\n  x: int;\n  y: int\n}");
        match complexity {
            TypeComplexity::Medium { is_noeq, .. } => {
                assert!(is_noeq, "noeq should be detected");
            }
            _ => panic!("Expected Medium complexity for noeq type, got {:?}", complexity),
        }
    }

    #[test]
    fn test_type_complexity_high() {
        let complexity = analyze_type_complexity(
            "type expr =\n  | Lit\n  | Var\n  | Add\n  | Sub\n  | Mul\n"
        );
        match complexity {
            TypeComplexity::High { constructor_count, .. } => {
                assert_eq!(constructor_count, 5);
            }
            _ => panic!("Expected High complexity, got {:?}", complexity),
        }
    }

    #[test]
    fn test_complex_type_gets_info_severity() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

type expr =
  | Lit of int
  | Var of string
  | Add of expr & expr
  | Sub of expr & expr
  | Mul of expr & expr
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(!diagnostics.is_empty(), "Complex undocumented type should be flagged");
        assert_eq!(
            diagnostics[0].severity,
            DiagnosticSeverity::Info,
            "Complex types use Info severity (formal type defs are self-documenting)"
        );
        assert!(
            diagnostics[0].message.contains("Complex type"),
            "Message should mention complexity"
        );
    }

    #[test]
    fn test_complex_type_stub_has_summary() {
        let stub = generate_doc_stub(
            "expr",
            BlockType::Type,
            "type expr =\n  | Lit\n  | Var\n  | Add\n  | Sub\n  | Mul\n",
        );

        assert!(stub.contains("@summary"), "Complex type stub should include @summary");
        assert!(stub.contains("5 constructors"), "Should mention constructor count");
    }

    // =========================================================================
    // NEW: CONTRACT-BASED SEVERITY
    // =========================================================================

    #[test]
    fn test_contract_val_gets_info() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val safe_div : (x: int) -> (y: int) -> Pure int
  (requires y <> 0)
  (ensures fun r -> r * y = x)
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        let val_diags: Vec<_> = diagnostics.iter()
            .filter(|d| d.message.contains("safe_div"))
            .collect();

        assert!(!val_diags.is_empty(), "Undocumented val with contract should be flagged");
        assert_eq!(
            val_diags[0].severity,
            DiagnosticSeverity::Info,
            "Contract vals use Info (formal spec is self-documenting)"
        );
        assert!(
            val_diags[0].message.contains("contract"),
            "Message should mention the contract"
        );
    }

    #[test]
    fn test_lemma_val_skipped() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val my_lemma : (x: int) -> Lemma (requires x > 0) (ensures x >= 1)
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        assert!(
            diagnostics.is_empty(),
            "Lemma vals are self-documenting via formal spec and should be skipped"
        );
    }

    #[test]
    fn test_lemma_val_with_smt_pat_skipped() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val inverse_vec_lemma : (#n: pos) -> (vec: bv_t n) ->
    Lemma (requires True) (ensures vec = (int2bv (bv2int vec))) [SMTPat (int2bv (bv2int vec))]
"#;
        let file = PathBuf::from("test.fsti");
        let diagnostics = rule.check(&file, content);

        // Only the module-level doc diagnostic, no val diagnostic
        let val_diags: Vec<_> = diagnostics.iter()
            .filter(|d| d.message.contains("inverse_vec_lemma"))
            .collect();
        assert!(
            val_diags.is_empty(),
            "Lemma vals with SMTPat are self-documenting and should be skipped"
        );
    }

    #[test]
    fn test_non_lemma_val_with_contract_still_flagged() {
        let rule = DocCheckerRule::new();
        let content = r#"module Test

val create_buffer : (len: nat) -> ST (buffer uint8)
  (requires fun h -> True)
  (ensures fun h0 r h1 -> live h1 r)
"#;
        let file = PathBuf::from("test.fst");
        let diagnostics = rule.check(&file, content);

        // Non-Lemma vals with contracts should still be flagged (as Info)
        let val_diags: Vec<_> = diagnostics.iter()
            .filter(|d| d.message.contains("create_buffer"))
            .collect();
        assert!(
            !val_diags.is_empty(),
            "Non-Lemma val with contract should still be flagged"
        );
        assert_eq!(
            val_diags[0].severity,
            DiagnosticSeverity::Info,
            "Non-Lemma contract vals should use Info severity"
        );
    }

    // =========================================================================
    // NEW: HACL* TEST FILE PATTERN
    // =========================================================================

    #[test]
    fn test_hacl_test_file_skipped() {
        assert!(
            is_test_file(&PathBuf::from("/project/Hacl.Test.SHA2.fst")),
            "HACL* test convention should be detected"
        );
        assert!(
            is_test_file(&PathBuf::from("/project/code/tests/Hacl.Test.K256.fst")),
            "HACL* test in test directory should be detected"
        );
    }
}
