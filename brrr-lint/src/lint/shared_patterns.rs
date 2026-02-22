//! Shared regex patterns used across multiple lint modules.
//!
//! This module consolidates duplicate `lazy_static!` regex definitions that were
//! independently created by different lint rules. Each pattern here is used by
//! at least 2 modules. Module-specific patterns remain in their respective files.

use lazy_static::lazy_static;
use regex::Regex;

lazy_static! {
    // =========================================================================
    // Module / Import patterns
    // Used by: import_optimizer, unused_opens, module_deps
    // =========================================================================

    /// Matches `open Module.Path` and captures the module path.
    /// Used by import_optimizer, unused_opens, module_deps.
    pub(crate) static ref OPEN_MODULE_RE: Regex =
        Regex::new(r"^open\s+([A-Z][\w.]*)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches `include Module.Path` and captures the module path.
    /// Used by import_optimizer, unused_opens, module_deps.
    pub(crate) static ref INCLUDE_MODULE_RE: Regex =
        Regex::new(r"^include\s+([A-Z][\w.]*)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches qualified identifier usage `Module.Path.ident` and captures
    /// (1) the module path and (2) the identifier.
    /// Used by import_optimizer, unused_opens.
    pub(crate) static ref QUALIFIED_USE_RE: Regex =
        Regex::new(r"\b([A-Z][\w.]*)\.([\w']+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Top-level module declaration: `module Foo.Bar` (no `=`).
    /// Captures the module path. Only matches if the line ends after the path.
    /// Used by import_optimizer, module_deps, parser.
    pub(crate) static ref MODULE_DECL_RE: Regex =
        Regex::new(r"^module\s+([A-Z][\w.]*)\s*$").unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // F* keyword / declaration patterns
    // Used by: multiple checkers
    // =========================================================================

    /// Extracts parameter names from F* signatures: `(name : Type)`.
    /// Captures the parameter name.
    /// Used by dead_code (FUNC_PARAM), doc_checker (PARAM_RE).
    pub(crate) static ref PARAM_EXTRACT_RE: Regex =
        Regex::new(r"\((\w+)\s*:").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches `inline_for_extraction noextract` or `noextract inline_for_extraction`.
    /// Used by doc_checker, test_generator.
    pub(crate) static ref INLINE_NOEXTRACT_RE: Regex = Regex::new(
        r"(?:^|\s)(?:inline_for_extraction\s+noextract|noextract\s+inline_for_extraction)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches `private` declaration modifier.
    /// Used by doc_checker, test_generator.
    pub(crate) static ref PRIVATE_DECL_RE: Regex =
        Regex::new(r"(?:^|\s)private\s").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches the `inline_for_extraction` keyword (word boundary).
    /// Used by dead_code, effect_checker, lowstar.
    pub(crate) static ref INLINE_FOR_EXTRACTION_RE: Regex =
        Regex::new(r"\binline_for_extraction\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches the `noextract` keyword (word boundary).
    /// Used by dead_code, lowstar.
    pub(crate) static ref NOEXTRACT_RE: Regex =
        Regex::new(r"\bnoextract\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches the `Lemma` keyword (word boundary).
    /// Used by test_generator, security, proof_hints.
    pub(crate) static ref LEMMA_RE: Regex =
        Regex::new(r"\bLemma\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches `assume val` keyword pair.
    /// Used by effect_checker, doc_checker.
    pub(crate) static ref ASSUME_VAL_RE: Regex =
        Regex::new(r"\bassume\s+val\b").unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Proof / SMT patterns
    // Used by: dead_code, proof_hints, z3_complexity, effect_checker, lowstar
    // =========================================================================

    /// Matches `[SMTPat (` trigger annotation.
    /// Used by dead_code (SMTPAT_PATTERN), proof_hints (SMTPAT_SINGLE).
    pub(crate) static ref SMTPAT_OPEN_RE: Regex =
        Regex::new(r"\[SMTPat\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches `assert false` / `assert False` in various forms.
    /// Used by effect_checker (ASSERT_FALSE_PATTERN), proof_hints (ASSERT_FALSE).
    pub(crate) static ref ASSERT_FALSE_RE: Regex =
        Regex::new(r"\bassert\s*[\(]?\s*[Ff]alse\s*[\)]?").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches `assert_norm(` call.
    /// Used by lowstar (ASSERT_NORM), z3_complexity (ASSERT_NORM).
    pub(crate) static ref ASSERT_NORM_CALL_RE: Regex =
        Regex::new(r"\bassert_norm\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches `assert_by_tactic` keyword.
    /// Used by z3_complexity (ASSERT_BY_TACTIC), proof_hints (ASSERT_BY_TACTIC_HELPER).
    pub(crate) static ref ASSERT_BY_TACTIC_RE: Regex =
        Regex::new(r"\bassert_by_tactic\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Effect annotation in function signatures.
    /// Matches: `-> Tot`, `-> GTot`, `-> Pure`, `-> Ghost`, `: Stack`, etc.
    /// Used by parser, effect_checker.
    pub(crate) static ref EFFECT_ANNOTATION_RE: Regex = Regex::new(
        r"(?:->|:)\s*(Tot|GTot|PURE|GHOST|Pure|Ghost|Lemma|ST|Stack|STATE|State|St|GST|Heap|StackInline|Inline|STL|Unsafe|Exn|Ex|EXN|Div|Dv|DIV|EXT|All|ALL|ML|Tac|TAC|TacH|TacS|TacRO|TacF)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));
}
