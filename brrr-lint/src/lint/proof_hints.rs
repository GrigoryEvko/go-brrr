//! FST009: Proof hint suggester.
//!
//! Suggests helpful proof patterns based on code analysis.
//! Comprehensive database of F* proof lemmas and techniques.

use lazy_static::lazy_static;
use regex::Regex;
use std::path::Path;

use super::rules::{Diagnostic, DiagnosticSeverity, Range, Rule, RuleCode};
use super::shared_patterns::{ASSERT_FALSE_RE, ASSERT_BY_TACTIC_RE};

// =============================================================================
// Pattern Database
// =============================================================================

lazy_static! {
    // === LIST PATTERNS ===
    /// List.length (l1 @ l2) - needs append_length lemma
    static ref LIST_APPEND_LENGTH: Regex =
        Regex::new(r"List\.length\s*\(\s*(\w+)\s*@\s*(\w+)\s*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// List.rev (List.rev l) - can simplify with rev_involutive
    static ref LIST_REV_REV: Regex =
        Regex::new(r"List\.rev\s*\(\s*List\.rev\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// List.mem x (l1 @ l2) - needs append_mem lemma
    static ref LIST_MEM_APPEND: Regex =
        Regex::new(r"List\.mem\s+\w+\s+\(\s*\w+\s*@").unwrap_or_else(|e| panic!("regex: {e}"));

    /// List.index on appended list
    static ref LIST_INDEX_APPEND: Regex =
        Regex::new(r"List\.index\s+\(\s*\w+\s*@").unwrap_or_else(|e| panic!("regex: {e}"));

    /// List.nth or List.index bounds checking (reserved for future use)
    #[allow(dead_code)]
    static ref LIST_NTH: Regex =
        Regex::new(r"List\.(nth|index)\s+\w+\s+\d+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// List.map (fun x -> ...) l - length preservation
    static ref LIST_MAP: Regex =
        Regex::new(r"List\.length\s*\(\s*List\.map\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// List.filter - length relationship
    static ref LIST_FILTER_LENGTH: Regex =
        Regex::new(r"List\.length\s*\(\s*List\.filter\b").unwrap_or_else(|e| panic!("regex: {e}"));

    // === SEQUENCE PATTERNS ===
    /// Seq.length (Seq.append s1 s2)
    static ref SEQ_APPEND_LENGTH: Regex =
        Regex::new(r"Seq\.length\s*\(\s*Seq\.append\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Seq.slice (Seq.append ...) - complex slicing
    static ref SEQ_SLICE_APPEND: Regex =
        Regex::new(r"Seq\.slice\s*\(\s*Seq\.append\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Seq.create n v - length is n
    static ref SEQ_CREATE: Regex =
        Regex::new(r"Seq\.create\s+(\w+|\d+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Seq.index (Seq.upd s i v) j - index after update
    static ref SEQ_INDEX_UPD: Regex =
        Regex::new(r"Seq\.index\s*\(\s*Seq\.upd\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Seq.upd (Seq.upd s i v) - double update (reserved for future use)
    #[allow(dead_code)]
    static ref SEQ_UPD_UPD: Regex =
        Regex::new(r"Seq\.upd\s*\(\s*Seq\.upd\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Seq.slice s 0 (Seq.length s) - identity slice
    static ref SEQ_SLICE_FULL: Regex =
        Regex::new(r"Seq\.slice\s+\w+\s+0\s+\(\s*Seq\.length\s+\w+\s*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Seq.equal usage
    static ref SEQ_EQUAL: Regex =
        Regex::new(r"Seq\.equal\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Seq.length (Seq.slice ...)
    static ref SEQ_SLICE_LENGTH: Regex =
        Regex::new(r"Seq\.length\s*\(\s*Seq\.slice\b").unwrap_or_else(|e| panic!("regex: {e}"));

    // === MODULAR ARITHMETIC ===
    // Note: Rust regex doesn't support backreferences, so we use simpler patterns
    // that may match more broadly. The hints are still useful.

    /// (a + b * c) % d - general modular pattern
    static ref MOD_PLUS: Regex =
        Regex::new(r"\(\s*\w+\s*\+\s*\w+\s*\*\s*\w+\s*\)\s*%\s*\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// (a * b) % c - multiplication then modulo
    static ref MOD_MUL: Regex =
        Regex::new(r"\(\s*\w+\s*\*\s*\w+\s*\)\s*%\s*\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Simple x % y pattern (reserved for future use)
    #[allow(dead_code)]
    static ref MOD_SIMPLE: Regex =
        Regex::new(r"\w+\s*%\s*\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// (a * b) / c - multiplication then division
    static ref DIV_MUL: Regex =
        Regex::new(r"\(\s*\w+\s*\*\s*\w+\s*\)\s*/\s*\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// (a % b) % c - nested modulo
    static ref MOD_MOD: Regex =
        Regex::new(r"\(\s*\w+\s*%\s*\w+\s*\)\s*%\s*\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// a % n < n (when n > 0) (reserved for future use)
    #[allow(dead_code)]
    static ref MOD_BOUND: Regex =
        Regex::new(r"\w+\s*%\s*\w+\s*<\s*\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// a / b <= a (for positive integers) (reserved for future use)
    #[allow(dead_code)]
    static ref DIV_LE: Regex =
        Regex::new(r"\w+\s*/\s*\w+\s*<=\s*\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    // === POWER OF 2 ===
    /// pow2 x + pow2 y - addition of powers (may indicate doubling)
    static ref POW2_ADD: Regex =
        Regex::new(r"pow2\s+\w+\s*\+\s*pow2\s+\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// pow2 m * pow2 n == pow2 (m + n)
    static ref POW2_MUL: Regex =
        Regex::new(r"pow2\s+\w+\s*\*\s*pow2\s+\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// x / pow2 n (shift right semantically)
    static ref POW2_DIV: Regex =
        Regex::new(r"\w+\s*/\s*pow2\s+(\w+|\d+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// x % pow2 n (mask semantically)
    static ref POW2_MOD: Regex =
        Regex::new(r"\w+\s*%\s*pow2\s+(\w+|\d+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// pow2 without assert_norm
    static ref POW2_BARE: Regex =
        Regex::new(r"\bpow2\s+\d+\b").unwrap_or_else(|e| panic!("regex: {e}"));

    // === CLASSICAL LOGIC ===
    /// forall (x: t). P x
    static ref FORALL_INTRO: Regex =
        Regex::new(r"\bforall\s+\([^)]+\)\s*\.").unwrap_or_else(|e| panic!("regex: {e}"));

    /// exists (x: t). P x
    static ref EXISTS_INTRO: Regex =
        Regex::new(r"\bexists\s+\([^)]+\)\s*\.").unwrap_or_else(|e| panic!("regex: {e}"));

    // Note: The following patterns are defined for future use but not
    // actively checked in the current implementation.

    /// P ==> Q (implication)
    #[allow(dead_code)]
    static ref IMPLICATION: Regex =
        Regex::new(r"==>").unwrap_or_else(|e| panic!("regex: {e}"));

    /// ~P or not P (negation)
    #[allow(dead_code)]
    static ref NEGATION: Regex =
        Regex::new(r"\bnot\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Classical.move_requires (reserved for future use)
    #[allow(dead_code)]
    static ref MOVE_REQUIRES: Regex =
        Regex::new(r"Classical\.move_requires\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// forall x. ... ==> ... (often needs forall_intro + implication)
    static ref FORALL_IMPL: Regex =
        Regex::new(r"\bforall\s+\w+\s*\..*==>").unwrap_or_else(|e| panic!("regex: {e}"));

    // === BITVECTOR OPERATIONS ===
    /// logand operation
    static ref LOGAND: Regex =
        Regex::new(r"\blogand\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// logxor operation
    static ref LOGXOR: Regex =
        Regex::new(r"\blogxor\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// logor operation
    static ref LOGOR: Regex =
        Regex::new(r"\blogor\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// shift_left operation
    static ref SHIFT_LEFT: Regex =
        Regex::new(r"\bshift_left\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// shift_right operation
    static ref SHIFT_RIGHT: Regex =
        Regex::new(r"\bshift_right\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// lognot operation
    static ref LOGNOT: Regex =
        Regex::new(r"\blognot\b").unwrap_or_else(|e| panic!("regex: {e}"));

    // === INTEGER BOUNDS ===
    /// UInt8/16/32/64 bounds (reserved for future use)
    #[allow(dead_code)]
    static ref UINT_MAX: Regex =
        Regex::new(r"\b(max_int|max_uint|min_int)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Checking x < pow2 n (reserved for future use)
    #[allow(dead_code)]
    static ref UINT_BOUND_CHECK: Regex =
        Regex::new(r"\b\w+\s*<\s*pow2\s+\d+").unwrap_or_else(|e| panic!("regex: {e}"));

    // === LEMMA CALLS ===
    /// Already has a lemma call (reduce noise)
    static ref HAS_LEMMA_CALL: Regex =
        Regex::new(r"\b(lemma_|_lemma|Lemmas\.)\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// assert_norm usage
    static ref ASSERT_NORM: Regex =
        Regex::new(r"\bassert_norm\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// calc blocks for equational reasoning
    static ref CALC_BLOCK: Regex =
        Regex::new(r"\bcalc\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));

    // === PROOF CONSTRUCT PATTERNS ===

    /// SMTPatOr annotation (disjunctive patterns)
    static ref SMTPAT_OR: Regex =
        Regex::new(r"\[SMTPatOr\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// assert ... by (tactic) pattern
    static ref ASSERT_BY_TACTIC: Regex =
        Regex::new(r"\bassert\b[^;]*\bby\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));

    /// decreases clause
    static ref DECREASES_CLAUSE: Regex =
        Regex::new(r"\bdecreases\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Recursive function (let rec)
    static ref LET_REC: Regex =
        Regex::new(r"\blet\s+rec\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Val with Lemma in signature (for SMTPat checking)
    static ref VAL_LEMMA: Regex =
        Regex::new(r"\bval\b[^:]*:.*\bLemma\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Lemma with SMTPat already present
    static ref LEMMA_WITH_SMTPAT: Regex =
        Regex::new(r"\bLemma\b.*\[SMTPat").unwrap_or_else(|e| panic!("regex: {e}"));

    /// #push-options pragma
    static ref PUSH_OPTIONS: Regex =
        Regex::new(r"#push-options").unwrap_or_else(|e| panic!("regex: {e}"));

    /// #pop-options pragma
    static ref POP_OPTIONS: Regex =
        Regex::new(r"#pop-options").unwrap_or_else(|e| panic!("regex: {e}"));

    /// #set-options pragma
    static ref SET_OPTIONS: Regex =
        Regex::new(r"#set-options").unwrap_or_else(|e| panic!("regex: {e}"));

    /// #restart-solver pragma
    static ref RESTART_SOLVER: Regex =
        Regex::new(r"#restart-solver").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Fuel setting pattern
    static ref FUEL_PRAGMA: Regex =
        Regex::new(r"--fuel\s+(\d+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// IFuel setting pattern
    static ref IFUEL_PRAGMA: Regex =
        Regex::new(r"--ifuel\s+(\d+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// calc step count (== { ... } lines within a calc block)
    static ref CALC_STEP: Regex =
        Regex::new(r"^\s*==\s*\{").unwrap_or_else(|e| panic!("regex: {e}"));

    /// squash type pattern
    static ref SQUASH_TYPE: Regex =
        Regex::new(r"\bsquash\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Ghost.erased or erased type
    static ref ERASED_TYPE: Regex =
        Regex::new(r"\b(?:Ghost\.)?erased\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Ghost.reveal pattern
    static ref GHOST_REVEAL: Regex =
        Regex::new(r"\b(?:Ghost\.)?reveal\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Ghost.hide pattern
    static ref GHOST_HIDE: Regex =
        Regex::new(r"\b(?:Ghost\.)?hide\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// SMTPat on a bare variable (overly broad trigger, matching loop risk)
    /// E.g. [SMTPat x] instead of [SMTPat (f x)]
    static ref SMTPAT_BARE_VAR: Regex =
        Regex::new(r"\[SMTPat\s+([a-z_]\w*)\s*\]").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Chained lemma calls pattern: `lemma1 x; lemma2 x; lemma3 x`
    /// which could be refactored into a single combined lemma
    static ref CHAINED_LEMMA_CALLS: Regex =
        Regex::new(r"\b(lemma_\w+|_lemma\w*)\s+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// calc block with inequality relation (<=, <, >=, >)
    static ref CALC_INEQUALITY: Regex =
        Regex::new(r"\bcalc\s*\(\s*(<=|<|>=|>)\s*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    // === REFINEMENT TYPES (reserved for future use) ===
    /// nat refinement
    #[allow(dead_code)]
    static ref NAT_REFINEMENT: Regex =
        Regex::new(r"\bnat\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// pos refinement
    #[allow(dead_code)]
    static ref POS_REFINEMENT: Regex =
        Regex::new(r"\bpos\b").unwrap_or_else(|e| panic!("regex: {e}"));

    // === EFFECT PATTERNS (reserved for future use) ===
    /// Pure vs Tot distinction
    #[allow(dead_code)]
    static ref PURE_EFFECT: Regex =
        Regex::new(r"\bPure\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Ghost effect usage
    #[allow(dead_code)]
    static ref GHOST_EFFECT: Regex =
        Regex::new(r"\bGhost\b").unwrap_or_else(|e| panic!("regex: {e}"));
}

// =============================================================================
// Hint Database
// =============================================================================

/// A proof hint with associated metadata.
#[derive(Debug, Clone, Copy)]
pub struct ProofHint {
    /// Short identifier for the pattern
    pub pattern_name: &'static str,
    /// The lemma or tactic to use
    pub lemma: &'static str,
    /// Human-readable description of what the lemma proves
    pub description: &'static str,
    /// Category for grouping related hints
    pub category: HintCategory,
}

/// Categories for organizing hints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HintCategory {
    List,
    Sequence,
    ModularArithmetic,
    PowerOfTwo,
    ClassicalLogic,
    Bitvector,
    IntegerBounds,
    ProofTechnique,
    SmtPattern,
    GhostErased,
    DecreasesClause,
}

impl HintCategory {
    pub fn as_str(&self) -> &'static str {
        match self {
            HintCategory::List => "List",
            HintCategory::Sequence => "Sequence",
            HintCategory::ModularArithmetic => "Modular Arithmetic",
            HintCategory::PowerOfTwo => "Power of 2",
            HintCategory::ClassicalLogic => "Classical Logic",
            HintCategory::Bitvector => "Bitvector",
            HintCategory::IntegerBounds => "Integer Bounds",
            HintCategory::ProofTechnique => "Proof Technique",
            HintCategory::SmtPattern => "SMT Pattern",
            HintCategory::GhostErased => "Ghost/Erased",
            HintCategory::DecreasesClause => "Decreases",
        }
    }
}

/// Comprehensive database of proof hints organized by pattern.
pub const HINT_DATABASE: &[ProofHint] = &[
    // === LIST HINTS ===
    ProofHint {
        pattern_name: "list_append_length",
        lemma: "FStar.List.Tot.Properties.append_length l1 l2",
        description: "length (l1 @ l2) == length l1 + length l2",
        category: HintCategory::List,
    },
    ProofHint {
        pattern_name: "list_rev_involutive",
        lemma: "FStar.List.Tot.Properties.rev_involutive l",
        description: "rev (rev l) == l",
        category: HintCategory::List,
    },
    ProofHint {
        pattern_name: "list_mem_append",
        lemma: "FStar.List.Tot.Properties.append_mem l1 l2 x",
        description: "mem x (l1 @ l2) <==> mem x l1 || mem x l2",
        category: HintCategory::List,
    },
    ProofHint {
        pattern_name: "list_index_append_left",
        lemma: "FStar.List.Tot.Properties.append_index_l l1 l2 i",
        description: "i < length l1 ==> index (l1 @ l2) i == index l1 i",
        category: HintCategory::List,
    },
    ProofHint {
        pattern_name: "list_index_append_right",
        lemma: "FStar.List.Tot.Properties.append_index_r l1 l2 i",
        description: "i >= length l1 ==> index (l1 @ l2) i == index l2 (i - length l1)",
        category: HintCategory::List,
    },
    ProofHint {
        pattern_name: "list_map_length",
        lemma: "FStar.List.Tot.Properties.map_length f l",
        description: "length (map f l) == length l",
        category: HintCategory::List,
    },
    ProofHint {
        pattern_name: "list_filter_length",
        lemma: "FStar.List.Tot.Properties.filter_length f l",
        description: "length (filter f l) <= length l",
        category: HintCategory::List,
    },
    ProofHint {
        pattern_name: "list_rev_length",
        lemma: "FStar.List.Tot.Properties.rev_length l",
        description: "length (rev l) == length l",
        category: HintCategory::List,
    },
    // === SEQUENCE HINTS ===
    ProofHint {
        pattern_name: "seq_append_length",
        lemma: "FStar.Seq.Properties.lemma_len_append s1 s2",
        description: "Seq.length (Seq.append s1 s2) == Seq.length s1 + Seq.length s2",
        category: HintCategory::Sequence,
    },
    ProofHint {
        pattern_name: "seq_slice_length",
        lemma: "FStar.Seq.Properties.lemma_len_slice s i j",
        description: "Seq.length (Seq.slice s i j) == j - i",
        category: HintCategory::Sequence,
    },
    ProofHint {
        pattern_name: "seq_create_length",
        lemma: "FStar.Seq.Base.lemma_create_len n v",
        description: "Seq.length (Seq.create n v) == n",
        category: HintCategory::Sequence,
    },
    ProofHint {
        pattern_name: "seq_upd_index_same",
        lemma: "FStar.Seq.Properties.lemma_index_upd1 s i v",
        description: "Seq.index (Seq.upd s i v) i == v",
        category: HintCategory::Sequence,
    },
    ProofHint {
        pattern_name: "seq_upd_index_other",
        lemma: "FStar.Seq.Properties.lemma_index_upd2 s i v j",
        description: "i <> j ==> Seq.index (Seq.upd s i v) j == Seq.index s j",
        category: HintCategory::Sequence,
    },
    ProofHint {
        pattern_name: "seq_equal_intro",
        lemma: "FStar.Seq.Properties.lemma_eq_intro s1 s2",
        description: "Prove Seq.equal by showing same length and same elements",
        category: HintCategory::Sequence,
    },
    ProofHint {
        pattern_name: "seq_equal_elim",
        lemma: "FStar.Seq.Properties.lemma_eq_elim s1 s2",
        description: "Seq.equal s1 s2 ==> s1 == s2",
        category: HintCategory::Sequence,
    },
    ProofHint {
        pattern_name: "seq_slice_slice",
        lemma: "FStar.Seq.Properties.lemma_slice_slice s i j k l",
        description: "Seq.slice (Seq.slice s i j) k l == Seq.slice s (i+k) (i+l)",
        category: HintCategory::Sequence,
    },
    ProofHint {
        pattern_name: "seq_append_assoc",
        lemma: "FStar.Seq.Properties.lemma_append_assoc s1 s2 s3",
        description: "Seq.append s1 (Seq.append s2 s3) == Seq.append (Seq.append s1 s2) s3",
        category: HintCategory::Sequence,
    },
    ProofHint {
        pattern_name: "seq_slice_full",
        lemma: "FStar.Seq.Properties.lemma_slice_full s",
        description: "Seq.slice s 0 (Seq.length s) == s",
        category: HintCategory::Sequence,
    },
    // === MODULAR ARITHMETIC HINTS ===
    ProofHint {
        pattern_name: "mod_plus",
        lemma: "FStar.Math.Lemmas.lemma_mod_plus a k n",
        description: "(a + k * n) % n == a % n",
        category: HintCategory::ModularArithmetic,
    },
    ProofHint {
        pattern_name: "mod_mul_cancel",
        lemma: "FStar.Math.Lemmas.cancel_mul_mod a n",
        description: "(a * n) % n == 0",
        category: HintCategory::ModularArithmetic,
    },
    ProofHint {
        pattern_name: "mod_self",
        lemma: "FStar.Math.Lemmas.small_mod 0 n",
        description: "n % n == 0 (or use small_mod for 0 % n)",
        category: HintCategory::ModularArithmetic,
    },
    ProofHint {
        pattern_name: "div_mul_cancel",
        lemma: "FStar.Math.Lemmas.cancel_mul_div a n",
        description: "(a * n) / n == a",
        category: HintCategory::ModularArithmetic,
    },
    ProofHint {
        pattern_name: "mod_mod",
        lemma: "FStar.Math.Lemmas.lemma_mod_mod a n",
        description: "(a % n) % n == a % n",
        category: HintCategory::ModularArithmetic,
    },
    ProofHint {
        pattern_name: "mod_bound",
        lemma: "FStar.Math.Lemmas.lemma_mod_lt a n",
        description: "n > 0 ==> a % n < n",
        category: HintCategory::ModularArithmetic,
    },
    ProofHint {
        pattern_name: "mod_add",
        lemma: "FStar.Math.Lemmas.lemma_mod_add_distr a b n",
        description: "(a + b) % n == ((a % n) + (b % n)) % n",
        category: HintCategory::ModularArithmetic,
    },
    ProofHint {
        pattern_name: "mod_sub",
        lemma: "FStar.Math.Lemmas.lemma_mod_sub_distr a b n",
        description: "(a - b) % n == ((a % n) - (b % n)) % n (when a >= b)",
        category: HintCategory::ModularArithmetic,
    },
    ProofHint {
        pattern_name: "div_le",
        lemma: "FStar.Math.Lemmas.lemma_div_le a b n",
        description: "a <= b ==> a / n <= b / n",
        category: HintCategory::ModularArithmetic,
    },
    ProofHint {
        pattern_name: "euclidean_division",
        lemma: "FStar.Math.Lemmas.euclidean_division_definition a n",
        description: "a == (a / n) * n + a % n",
        category: HintCategory::ModularArithmetic,
    },
    // === POWER OF 2 HINTS ===
    ProofHint {
        pattern_name: "pow2_double",
        lemma: "FStar.Math.Lemmas.pow2_double_sum n",
        description: "pow2 n + pow2 n == pow2 (n + 1)",
        category: HintCategory::PowerOfTwo,
    },
    ProofHint {
        pattern_name: "pow2_plus",
        lemma: "FStar.Math.Lemmas.pow2_plus m n",
        description: "pow2 m * pow2 n == pow2 (m + n)",
        category: HintCategory::PowerOfTwo,
    },
    ProofHint {
        pattern_name: "pow2_lt_compat",
        lemma: "FStar.Math.Lemmas.pow2_lt_compat m n",
        description: "m < n ==> pow2 m < pow2 n",
        category: HintCategory::PowerOfTwo,
    },
    ProofHint {
        pattern_name: "pow2_le_compat",
        lemma: "FStar.Math.Lemmas.pow2_le_compat m n",
        description: "m <= n ==> pow2 m <= pow2 n",
        category: HintCategory::PowerOfTwo,
    },
    ProofHint {
        pattern_name: "pow2_modulo_modulo",
        lemma: "FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 a m n",
        description: "m <= n ==> (a % pow2 n) % pow2 m == a % pow2 m",
        category: HintCategory::PowerOfTwo,
    },
    ProofHint {
        pattern_name: "pow2_div_lemma",
        lemma: "FStar.Math.Lemmas.pow2_div_lemma a n",
        description: "(a * pow2 n) / pow2 n == a",
        category: HintCategory::PowerOfTwo,
    },
    ProofHint {
        pattern_name: "pow2_assert_norm",
        lemma: "assert_norm (pow2 N == <value>)",
        description: "Use assert_norm to normalize pow2 with concrete exponent",
        category: HintCategory::PowerOfTwo,
    },
    // === CLASSICAL LOGIC HINTS ===
    ProofHint {
        pattern_name: "forall_intro",
        lemma: "Classical.forall_intro (fun x -> <proof>)",
        description: "Prove forall by introducing arbitrary x",
        category: HintCategory::ClassicalLogic,
    },
    ProofHint {
        pattern_name: "exists_intro",
        lemma: "Classical.exists_intro p witness",
        description: "Prove exists by providing a witness",
        category: HintCategory::ClassicalLogic,
    },
    ProofHint {
        pattern_name: "move_requires",
        lemma: "Classical.move_requires lemma arg",
        description: "Convert (requires P ==> ensures Q) to (P ==> Q)",
        category: HintCategory::ClassicalLogic,
    },
    ProofHint {
        pattern_name: "forall_intro_2",
        lemma: "Classical.forall_intro_2 (fun x y -> <proof>)",
        description: "Prove forall over two variables",
        category: HintCategory::ClassicalLogic,
    },
    ProofHint {
        pattern_name: "forall_intro_3",
        lemma: "Classical.forall_intro_3 (fun x y z -> <proof>)",
        description: "Prove forall over three variables",
        category: HintCategory::ClassicalLogic,
    },
    ProofHint {
        pattern_name: "impl_intro",
        lemma: "introduce (P ==> Q) with <assumption>. <proof>",
        description: "Prove implication by assuming antecedent",
        category: HintCategory::ClassicalLogic,
    },
    ProofHint {
        pattern_name: "and_intro",
        lemma: "introduce P /\\ Q with <proof_P> and <proof_Q>",
        description: "Prove conjunction by proving both parts",
        category: HintCategory::ClassicalLogic,
    },
    ProofHint {
        pattern_name: "or_intro_l",
        lemma: "introduce (P \\/ Q) with Left <proof_P>",
        description: "Prove disjunction via left disjunct",
        category: HintCategory::ClassicalLogic,
    },
    ProofHint {
        pattern_name: "or_intro_r",
        lemma: "introduce (P \\/ Q) with Right <proof_Q>",
        description: "Prove disjunction via right disjunct",
        category: HintCategory::ClassicalLogic,
    },
    ProofHint {
        pattern_name: "excluded_middle",
        lemma: "Classical.excluded_middle P",
        description: "P \\/ ~P (law of excluded middle)",
        category: HintCategory::ClassicalLogic,
    },
    // === BITVECTOR HINTS ===
    ProofHint {
        pattern_name: "logand_mask",
        lemma: "FStar.UInt.logand_mask x n",
        description: "logand x (pow2 n - 1) == x % pow2 n",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "logand_self",
        lemma: "FStar.UInt.logand_self x",
        description: "logand x x == x",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "logand_zero",
        lemma: "FStar.UInt.logand_zero x",
        description: "logand x 0 == 0",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "logxor_self",
        lemma: "FStar.UInt.logxor_self x",
        description: "logxor x x == 0",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "logxor_zero",
        lemma: "FStar.UInt.logxor_zero x",
        description: "logxor x 0 == x",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "logor_zero",
        lemma: "FStar.UInt.logor_zero x",
        description: "logor x 0 == x",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "logor_self",
        lemma: "FStar.UInt.logor_self x",
        description: "logor x x == x",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "shift_left_value",
        lemma: "FStar.UInt.shift_left_value x n",
        description: "shift_left x n == x * pow2 n",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "shift_right_value",
        lemma: "FStar.UInt.shift_right_value x n",
        description: "shift_right x n == x / pow2 n",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "lognot_involutive",
        lemma: "FStar.UInt.lognot_involutive x",
        description: "lognot (lognot x) == x",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "logand_commutative",
        lemma: "FStar.UInt.logand_commutative x y",
        description: "logand x y == logand y x",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "logxor_commutative",
        lemma: "FStar.UInt.logxor_commutative x y",
        description: "logxor x y == logxor y x",
        category: HintCategory::Bitvector,
    },
    ProofHint {
        pattern_name: "bitvector_assert_norm",
        lemma: "assert_norm (logand x y == <value>)",
        description: "Use assert_norm to normalize bitvector operations with concrete values",
        category: HintCategory::Bitvector,
    },
    // === PROOF TECHNIQUE HINTS ===
    ProofHint {
        pattern_name: "calc_block",
        lemma: "calc (==) { a; == { <proof> } b; == { <proof> } c; }",
        description: "Use calc for equational reasoning chains",
        category: HintCategory::ProofTechnique,
    },
    ProofHint {
        pattern_name: "assert_by",
        lemma: "assert P by (tactic)",
        description: "Prove assertion using specific tactic",
        category: HintCategory::ProofTechnique,
    },
    ProofHint {
        pattern_name: "admit_for_debugging",
        lemma: "admit() (* REMOVE BEFORE COMMIT *)",
        description: "Temporarily admit to debug other parts",
        category: HintCategory::ProofTechnique,
    },
    ProofHint {
        pattern_name: "cut_lemma",
        lemma: "let _ = lemma_name args in",
        description: "Call lemma to establish intermediate fact",
        category: HintCategory::ProofTechnique,
    },
    // === SMT PATTERN HINTS ===
    ProofHint {
        pattern_name: "smtpat_trigger",
        lemma: "[SMTPat (f x)]",
        description: "Add SMTPat trigger to lemma for automatic instantiation by Z3",
        category: HintCategory::SmtPattern,
    },
    ProofHint {
        pattern_name: "smtpat_or",
        lemma: "[SMTPatOr [[SMTPat (f x)]; [SMTPat (g x)]]]",
        description: "Use SMTPatOr for disjunctive pattern triggers",
        category: HintCategory::SmtPattern,
    },
    ProofHint {
        pattern_name: "smtpat_multiple",
        lemma: "[SMTPat (f x); SMTPat (g y)]",
        description: "Use multiple SMTPat for conjunctive triggers",
        category: HintCategory::SmtPattern,
    },
    // === GHOST/ERASED HINTS ===
    ProofHint {
        pattern_name: "ghost_reveal_hide",
        lemma: "Ghost.hide (Ghost.reveal x) == x",
        description: "hide/reveal are inverses - round-trip can be eliminated",
        category: HintCategory::GhostErased,
    },
    ProofHint {
        pattern_name: "erased_bind",
        lemma: "let@ x = erased_val in ...",
        description: "Use monadic bind (let@) for erased computations",
        category: HintCategory::GhostErased,
    },
    ProofHint {
        pattern_name: "squash_return",
        lemma: "return_squash (proof_term)",
        description: "Convert proof term to squash type",
        category: HintCategory::GhostErased,
    },
    // === DECREASES CLAUSE HINTS ===
    ProofHint {
        pattern_name: "decreases_lex",
        lemma: "(decreases (lex_t ...))",
        description: "Use lexicographic ordering for complex termination proofs",
        category: HintCategory::DecreasesClause,
    },
    ProofHint {
        pattern_name: "decreases_nat",
        lemma: "(decreases n)",
        description: "Decrease on natural number argument for recursive functions",
        category: HintCategory::DecreasesClause,
    },
];

// =============================================================================
// Pattern Matcher
// =============================================================================

/// FST009: Proof Hint Suggester
///
/// Analyzes code patterns and suggests helpful proof lemmas and techniques.
/// Only fires hints when there is evidence the user is trying to prove something
/// about the pattern (assertion context) or is struggling with a proof (nearby admit).
pub struct ProofHintsRule;

impl ProofHintsRule {
    pub fn new() -> Self {
        Self
    }

    /// Check if line should be skipped (comments, already has lemmas).
    fn should_skip_line(&self, line: &str) -> bool {
        let trimmed = line.trim();
        if trimmed.starts_with("(*") || trimmed.starts_with("//") {
            return true;
        }
        // Skip lines that already have lemma calls
        if HAS_LEMMA_CALL.is_match(line) {
            return true;
        }
        false
    }

    /// Check if the line is in a proof/assertion context where hints are useful.
    /// Returns true if the line contains assert, requires, ensures, or similar
    /// proof obligation keywords. Bare usage of operations (e.g. `logand x y`
    /// in a computation) does NOT need a hint.
    fn is_proof_context(line: &str) -> bool {
        let trimmed = line.trim();
        trimmed.contains("assert")
            || trimmed.starts_with("requires")
            || trimmed.starts_with("ensures")
            || trimmed.contains("requires (")
            || trimmed.contains("ensures (")
            || trimmed.contains("calc (")
            || trimmed.contains("calc(")
    }

    /// Check if there is an `admit()` within `window` lines of the given index,
    /// indicating the user is struggling with a proof nearby.
    fn has_nearby_admit(lines: &[&str], line_idx: usize, window: usize) -> bool {
        let start = line_idx.saturating_sub(window);
        let end = (line_idx + window + 1).min(lines.len());
        for line in &lines[start..end] {
            if line.contains("admit()") || line.contains("admit ()") {
                return true;
            }
        }
        false
    }

    /// Check for list patterns and return matching hints.
    fn check_list_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            // List.length (l1 @ l2)
            if LIST_APPEND_LENGTH.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[0], // list_append_length
                ));
            }

            // List.rev (List.rev ...)
            if LIST_REV_REV.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[1], // list_rev_involutive
                ));
            }

            // List.mem x (l1 @ l2)
            if LIST_MEM_APPEND.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[2], // list_mem_append
                ));
            }

            // List.index (l1 @ l2) i
            if LIST_INDEX_APPEND.is_match(line) {
                // Suggest both left and right index lemmas
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: For indexing into appended list, use:\n  - `{}` for indices in left part\n  - `{}` for indices in right part",
                        HINT_DATABASE[3].category.as_str(),
                        HINT_DATABASE[3].lemma,
                        HINT_DATABASE[4].lemma,
                    ),
                    fix: None,
                });
            }

            // List.length (List.map f l)
            if LIST_MAP.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[5], // list_map_length
                ));
            }

            // List.length (List.filter f l)
            if LIST_FILTER_LENGTH.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[6], // list_filter_length
                ));
            }
        }

        diagnostics
    }

    /// Check for sequence patterns and return matching hints.
    /// Composite patterns (Seq.length(Seq.append ...) etc.) are specific enough
    /// to always fire. Bare Seq.equal is gated on proof context.
    fn check_seq_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            // Seq.length (Seq.append ...) - specific composite, always useful
            if SEQ_APPEND_LENGTH.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[8], // seq_append_length
                ));
            }

            // Seq.slice (Seq.append ...) - specific composite, always useful
            if SEQ_SLICE_APPEND.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: Slicing an appended sequence is complex. Consider using `lemma_len_append` and `lemma_slice_slice`",
                        HintCategory::Sequence.as_str(),
                    ),
                    fix: None,
                });
            }

            // Seq.length (Seq.slice ...) - specific composite, always useful
            if SEQ_SLICE_LENGTH.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[9], // seq_slice_length
                ));
            }

            // Seq.create n v - only when combined with Seq.length (already specific)
            if SEQ_CREATE.is_match(line) && line.contains("Seq.length") {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[10], // seq_create_length
                ));
            }

            // Seq.index (Seq.upd ...) - specific composite, always useful
            if SEQ_INDEX_UPD.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: For indexing after update:\n  - `{}` (same index)\n  - `{}` (different index)",
                        HintCategory::Sequence.as_str(),
                        HINT_DATABASE[11].lemma,
                        HINT_DATABASE[12].lemma,
                    ),
                    fix: None,
                });
            }

            // Seq.equal - only in proof context or near admit.
            // Bare Seq.equal in specs/ensures is normal, not hint-worthy.
            if SEQ_EQUAL.is_match(line) {
                let in_proof = Self::is_proof_context(line)
                    || Self::has_nearby_admit(&lines, line_idx, 5);
                if in_proof {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST009,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "[{}] Hint: For sequence equality:\n  - `{}` (prove equal)\n  - `{}` (use equality)",
                            HintCategory::Sequence.as_str(),
                            HINT_DATABASE[13].lemma,
                            HINT_DATABASE[14].lemma,
                        ),
                        fix: None,
                    });
                }
            }

            // Seq.slice s 0 (Seq.length s) - specific composite, always useful
            if SEQ_SLICE_FULL.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[17], // seq_slice_full
                ));
            }
        }

        diagnostics
    }

    /// Check for modular arithmetic patterns.
    /// MOD_MOD is always specific enough to fire.
    /// MOD_PLUS, MOD_MUL, DIV_MUL are gated on proof context since they match
    /// very common arithmetic in type signatures and computations.
    fn check_mod_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            let in_proof = Self::is_proof_context(line)
                || Self::has_nearby_admit(&lines, line_idx, 5);

            // (a + b * c) % d - suggests lemma_mod_plus (only in proof context)
            if MOD_PLUS.is_match(line) && in_proof {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[18], // mod_plus
                ));
            }

            // (a * b) % c - suggests cancel_mul_mod (only in proof context)
            if MOD_MUL.is_match(line) && !MOD_PLUS.is_match(line) && in_proof {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[19], // mod_mul_cancel
                ));
            }

            // (a * b) / c - suggests cancel_mul_div (only in proof context)
            if DIV_MUL.is_match(line) && in_proof {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[21], // div_mul_cancel
                ));
            }

            // (a % b) % c - nested modulo, specific enough to always fire
            if MOD_MOD.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[22], // mod_mod
                ));
            }
        }

        diagnostics
    }

    /// Check for power of 2 patterns.
    /// Composite patterns (pow2 + pow2, pow2 * pow2) are specific enough to keep.
    /// The bare `pow2 N` pattern is gated on proof context to avoid noise
    /// in crypto code where pow2 appears in type signatures and computations.
    fn check_pow2_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            // pow2 x + pow2 y - specific composite pattern, always useful
            if POW2_ADD.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[28], // pow2_double
                ));
            }

            // pow2 m * pow2 n - specific composite pattern, always useful
            if POW2_MUL.is_match(line) {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[29], // pow2_plus
                ));
            }

            // x / pow2 n - only in proof context (avoid noise on type sigs)
            if POW2_DIV.is_match(line) && Self::is_proof_context(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: Division by pow2 may need `{}` or consider using shift_right semantically",
                        HintCategory::PowerOfTwo.as_str(),
                        HINT_DATABASE[33].lemma,
                    ),
                    fix: None,
                });
            }

            // x % pow2 n - only in proof context (avoid noise on type sigs)
            if POW2_MOD.is_match(line) && Self::is_proof_context(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: Modulo pow2 may need `pow2_modulo_modulo_lemma` or consider equivalence to logand mask",
                        HintCategory::PowerOfTwo.as_str(),
                    ),
                    fix: None,
                });
            }

            // Bare pow2 with numeric argument (suggest assert_norm)
            // Only in proof context or near admit - avoids massive noise on
            // type signatures like `x:int{x < pow2 64}`.
            if POW2_BARE.is_match(line) && !ASSERT_NORM.is_match(line) {
                if line.contains("pow2_") || line.contains("lemma_pow2") {
                    continue;
                }
                let in_proof = Self::is_proof_context(line)
                    || Self::has_nearby_admit(&lines, line_idx, 5);
                if !in_proof {
                    continue;
                }
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[34], // pow2_assert_norm
                ));
            }
        }

        diagnostics
    }

    /// Check for classical logic patterns.
    /// Only fires when quantifiers appear inside assertions or near proof
    /// struggles. Quantifiers in type signatures and specs are normal usage
    /// and do not need hints.
    fn check_logic_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            // Only suggest logic hints when user is trying to prove a quantifier,
            // not when quantifiers appear in type signatures or specs.
            let in_proof = Self::is_proof_context(line)
                || Self::has_nearby_admit(&lines, line_idx, 5);
            if !in_proof {
                continue;
            }

            // forall (x: t). P
            if FORALL_INTRO.is_match(line) && !line.contains("forall_intro") {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[35], // forall_intro
                ));
            }

            // exists (x: t). P
            if EXISTS_INTRO.is_match(line) && !line.contains("exists_intro") {
                diagnostics.push(self.create_hint(
                    file,
                    line_num,
                    &HINT_DATABASE[36], // exists_intro
                ));
            }

            // forall x. P x ==> Q x
            if FORALL_IMPL.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: For `forall x. P x ==> Q x`, use `Classical.forall_intro` combined with `Classical.move_requires` if needed",
                        HintCategory::ClassicalLogic.as_str(),
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for bitvector patterns.
    /// Only fires when the bitvector operation appears in a proof context
    /// (assert, requires, ensures) or near an admit(), to avoid noise on
    /// every computational use of logand/logxor/etc. in crypto code.
    fn check_bitvector_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            // Only suggest bitvector hints when the user is proving something
            // about the operation, not on every computational use.
            let in_proof = Self::is_proof_context(line)
                || Self::has_nearby_admit(&lines, line_idx, 5);
            if !in_proof {
                continue;
            }

            let has_assert_norm = ASSERT_NORM.is_match(line);

            // logand
            if LOGAND.is_match(line) && !has_assert_norm {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: logand lemmas available:\n  - `logand_self x` (x & x == x)\n  - `logand_zero x` (x & 0 == 0)\n  - `logand_mask x n` (x & (pow2 n - 1) == x % pow2 n)\n  Consider `assert_norm` for concrete values",
                        HintCategory::Bitvector.as_str(),
                    ),
                    fix: None,
                });
            }

            // logxor
            if LOGXOR.is_match(line) && !has_assert_norm {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: logxor lemmas available:\n  - `logxor_self x` (x ^ x == 0)\n  - `logxor_zero x` (x ^ 0 == x)\n  Consider `assert_norm` for concrete values",
                        HintCategory::Bitvector.as_str(),
                    ),
                    fix: None,
                });
            }

            // logor
            if LOGOR.is_match(line) && !has_assert_norm {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: logor lemmas available:\n  - `logor_self x` (x | x == x)\n  - `logor_zero x` (x | 0 == x)\n  Consider `assert_norm` for concrete values",
                        HintCategory::Bitvector.as_str(),
                    ),
                    fix: None,
                });
            }

            // shift_left
            if SHIFT_LEFT.is_match(line) && !has_assert_norm {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: `shift_left x n == x * pow2 n` - use `FStar.UInt.shift_left_value` lemma",
                        HintCategory::Bitvector.as_str(),
                    ),
                    fix: None,
                });
            }

            // shift_right
            if SHIFT_RIGHT.is_match(line) && !has_assert_norm {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: `shift_right x n == x / pow2 n` - use `FStar.UInt.shift_right_value` lemma",
                        HintCategory::Bitvector.as_str(),
                    ),
                    fix: None,
                });
            }

            // lognot
            if LOGNOT.is_match(line) && !has_assert_norm {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: `lognot_involutive x` - lognot (lognot x) == x",
                        HintCategory::Bitvector.as_str(),
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for proof technique patterns (calc blocks, assert-by-tactic, etc.).
    fn check_proof_technique_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        let lines: Vec<&str> = content.lines().collect();
        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            // Count equality assertions - if many in sequence, suggest calc
            if line.contains("assert") && line.contains("==") && !CALC_BLOCK.is_match(line) {
                let mut consecutive_asserts = 1;
                for next_line in lines.iter().skip(line_idx + 1).take(3) {
                    if next_line.contains("assert") && next_line.contains("==") {
                        consecutive_asserts += 1;
                    } else if !next_line.trim().is_empty() {
                        break;
                    }
                }

                if consecutive_asserts >= 2 {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST009,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "[{}] Hint: Multiple equality assertions could be combined into a `calc` block for clearer equational reasoning",
                            HintCategory::ProofTechnique.as_str(),
                        ),
                        fix: None,
                    });
                }
            }

            // Detect assert ... by (tactic) and suggest common tactics
            if ASSERT_BY_TACTIC.is_match(line) || ASSERT_BY_TACTIC_RE.is_match(line) {
                // Check if the tactic body is empty or uses admit
                let has_tadmit = line.contains("tadmit") || line.contains("admit");
                if has_tadmit {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST009,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "[{}] Hint: `assert ... by (tadmit())` bypasses tactic proof. \
                             Consider using `norm`, `trefl`, `smt`, or `compute` tactics instead",
                            HintCategory::ProofTechnique.as_str(),
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for SMTPat-related patterns: missing triggers on lemmas,
    /// SMTPatOr usage, and SMTPat selectivity.
    fn check_smt_pattern_hints(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            // Detect val declarations with Lemma effect but no SMTPat.
            // Only fire when there is a nearby admit indicating a proof struggle,
            // or the lemma is short (< 5 lines ahead before next val/let).
            if VAL_LEMMA.is_match(line) && !LEMMA_WITH_SMTPAT.is_match(line) {
                // Check if the lemma body (next few lines) has admit
                let has_nearby_struggle = Self::has_nearby_admit(&lines, line_idx, 10);
                if has_nearby_struggle {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST009,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "[{}] Hint: Lemma without `[SMTPat ...]` trigger. \
                             Adding an SMTPat allows Z3 to use this lemma automatically. \
                             Example: `[SMTPat (f x)]` triggers when Z3 sees `f x`",
                            HintCategory::SmtPattern.as_str(),
                        ),
                        fix: None,
                    });
                }
            }

            // Detect SMTPatOr usage and provide guidance
            if SMTPAT_OR.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: `SMTPatOr` creates disjunctive triggers (OR). \
                         Each inner list is an alternative pattern set. \
                         Ensure each alternative is selective enough to avoid quantifier explosion",
                        HintCategory::SmtPattern.as_str(),
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for calc block complexity: long calc chains that may
    /// benefit from splitting or intermediate lemma extraction.
    fn check_calc_block_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut in_calc = false;
        let mut calc_start_line = 0;
        let mut calc_step_count = 0;
        let mut brace_depth: i32 = 0;

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if CALC_BLOCK.is_match(line) && !in_calc {
                in_calc = true;
                calc_start_line = line_num;
                calc_step_count = 0;
                brace_depth = 0;
                // Count opening braces on the calc line
                for ch in line.chars() {
                    if ch == '{' { brace_depth += 1; }
                    if ch == '}' { brace_depth -= 1; }
                }
                continue;
            }

            if in_calc {
                for ch in line.chars() {
                    if ch == '{' { brace_depth += 1; }
                    if ch == '}' { brace_depth -= 1; }
                }

                if CALC_STEP.is_match(line) {
                    calc_step_count += 1;
                }

                // End of calc block when braces balance
                if brace_depth <= 0 {
                    in_calc = false;
                    if calc_step_count > 8 {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST009,
                            severity: DiagnosticSeverity::Hint,
                            file: file.to_path_buf(),
                            range: Range::point(calc_start_line, 1),
                            message: format!(
                                "[{}] Hint: Long calc block ({} steps). \
                                 Consider extracting intermediate lemmas to \
                                 improve readability and verification performance",
                                HintCategory::ProofTechnique.as_str(),
                                calc_step_count,
                            ),
                            fix: None,
                        });
                    }
                }
            }
        }

        diagnostics
    }

    /// Check for decreases clause patterns: recursive functions without
    /// explicit decreases annotations, and common decreases patterns.
    fn check_decreases_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            // Detect `let rec` without `decreases` within next ~10 lines
            if LET_REC.is_match(line) {
                let mut has_decreases = false;
                // Check current line and next 15 lines for decreases clause
                let check_end = (line_idx + 16).min(lines.len());
                for check_line in &lines[line_idx..check_end] {
                    if DECREASES_CLAUSE.is_match(check_line) {
                        has_decreases = true;
                        break;
                    }
                    // Stop at next top-level binding
                    let trimmed = check_line.trim();
                    if trimmed.starts_with("let ") && !trimmed.starts_with("let rec")
                        && trimmed != line.trim()
                    {
                        break;
                    }
                }

                // Only hint if near an admit (proof struggle)
                if !has_decreases && Self::has_nearby_admit(&lines, line_idx, 15) {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST009,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "[{}] Hint: Recursive function without explicit `decreases` clause. \
                             Adding `(decreases arg)` can help F* prove termination. \
                             For complex cases, use `(decreases %[a; b])` for lexicographic order",
                            HintCategory::DecreasesClause.as_str(),
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for ghost/erased type patterns and suggest simplifications.
    fn check_ghost_erased_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            let in_proof = Self::is_proof_context(line)
                || Self::has_nearby_admit(&lines, line_idx, 5);

            // Detect Ghost.reveal (Ghost.hide x) round-trip
            if GHOST_REVEAL.is_match(line) && GHOST_HIDE.is_match(line) && in_proof {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: `reveal (hide x) == x` and `hide (reveal x) == x`. \
                         These are inverses - the round-trip can be eliminated. \
                         Use `Ghost.hide_reveal` or `Ghost.reveal_hide` SMTPat lemmas",
                        HintCategory::GhostErased.as_str(),
                    ),
                    fix: None,
                });
            }

            // Detect squash patterns in proof context
            if SQUASH_TYPE.is_match(line) && in_proof
                && line.contains("squash (") && !line.contains("return_squash")
            {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: `squash p` is equivalent to `unit -> Lemma p`. \
                         Use `return_squash` to create a squash, and `get_proof` to extract. \
                         Consider if `Lemma` effect would be clearer",
                        HintCategory::GhostErased.as_str(),
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for fuel/ifuel pragma patterns and suggest optimizations.
    fn check_fuel_pragma_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut push_count: i32 = 0;
        let mut pop_count: i32 = 0;

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            if PUSH_OPTIONS.is_match(line) {
                push_count += 1;
            }
            if POP_OPTIONS.is_match(line) {
                pop_count += 1;
            }

            // Detect fuel 0 --ifuel 0 pattern (good practice, suggest as positive)
            if let Some(caps) = FUEL_PRAGMA.captures(line) {
                if let Ok(fuel) = caps.get(1).map_or("", |m| m.as_str()).parse::<u32>() {
                    if fuel == 0 && line.contains("--ifuel 0") {
                        // This is the recommended pattern, no hint needed
                        continue;
                    }
                }
            }

            // Detect #restart-solver usage
            if RESTART_SOLVER.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: `#restart-solver` resets Z3 state. \
                         Useful after complex proofs to avoid context pollution. \
                         If needed frequently, consider splitting the module",
                        HintCategory::ProofTechnique.as_str(),
                    ),
                    fix: None,
                });
            }
        }

        // Check for unbalanced push/pop (file-level)
        if push_count > pop_count + 1 {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST009,
                severity: DiagnosticSeverity::Warning,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: format!(
                    "[{}] Warning: {} `#push-options` but only {} `#pop-options`. \
                     Unbalanced push/pop may leak solver settings to subsequent definitions",
                    HintCategory::ProofTechnique.as_str(),
                    push_count, pop_count,
                ),
                fix: None,
            });
        }

        diagnostics
    }

    /// Check for `assert false` / `assert False` patterns.
    ///
    /// `assert false` in F* derives anything via False elimination. If this is
    /// in a proof, it means the proof state is contradictory (which may be
    /// intentional for reductio proofs, but is often a logic error).
    fn check_assert_false_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            if ASSERT_FALSE_RE.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Warning: `assert false` derives anything via False elimination. \
                         This means the proof state is contradictory. If intentional \
                         (reductio ad absurdum), document the reasoning. Otherwise, this \
                         may indicate a logic error in your proof.",
                        HintCategory::ProofTechnique.as_str(),
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for SMTPat on bare variables (overly broad triggers).
    ///
    /// `[SMTPat x]` where x is a plain variable (not an application like `f x`)
    /// creates an overly broad trigger that can cause matching loops in Z3.
    /// SMTPat should trigger on function applications to be selective.
    fn check_smtpat_selectivity(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            if SMTPAT_BARE_VAR.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Warning: SMTPat on bare variable is overly broad and can \
                         cause Z3 matching loops. Use `[SMTPat (f x)]` to trigger on a \
                         specific function application instead of `[SMTPat x]`.",
                        HintCategory::SmtPattern.as_str(),
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for calc blocks with inequality relations and provide guidance.
    ///
    /// Calc blocks with `<=`, `<`, `>=`, `>` are less common than `==` and
    /// require careful attention to transitivity. Provide a helpful hint about
    /// mixing relations in calc blocks.
    fn check_calc_inequality_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            if self.should_skip_line(line) {
                continue;
            }

            if CALC_INEQUALITY.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST009,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "[{}] Hint: Calc block with inequality relation. In F*, calc blocks \
                         support mixed relations (==, <=, <) where each step must compose. \
                         For example, `a == b` then `b <= c` gives `a <= c`. \
                         Ensure each step's justification is sufficient for the relation used.",
                        HintCategory::ProofTechnique.as_str(),
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Create a standard hint diagnostic from a ProofHint.
    fn create_hint(&self, file: &Path, line_num: usize, hint: &ProofHint) -> Diagnostic {
        Diagnostic {
            rule: RuleCode::FST009,
            severity: DiagnosticSeverity::Hint,
            file: file.to_path_buf(),
            range: Range::point(line_num, 1),
            message: format!(
                "[{}] Hint: `{}` - {}",
                hint.category.as_str(),
                hint.lemma,
                hint.description,
            ),
            fix: None,
        }
    }

    /// Get all hints for a specific category.
    pub fn get_hints_by_category(category: HintCategory) -> Vec<&'static ProofHint> {
        HINT_DATABASE
            .iter()
            .filter(|h| h.category == category)
            .collect()
    }

    /// Search hints by keyword.
    pub fn search_hints(keyword: &str) -> Vec<&'static ProofHint> {
        let keyword_lower = keyword.to_lowercase();
        HINT_DATABASE
            .iter()
            .filter(|h| {
                h.pattern_name.to_lowercase().contains(&keyword_lower)
                    || h.lemma.to_lowercase().contains(&keyword_lower)
                    || h.description.to_lowercase().contains(&keyword_lower)
            })
            .collect()
    }
}

impl Default for ProofHintsRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for ProofHintsRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST009
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        diagnostics.extend(self.check_list_patterns(file, content));
        diagnostics.extend(self.check_seq_patterns(file, content));
        diagnostics.extend(self.check_mod_patterns(file, content));
        diagnostics.extend(self.check_pow2_patterns(file, content));
        diagnostics.extend(self.check_logic_patterns(file, content));
        diagnostics.extend(self.check_bitvector_patterns(file, content));
        diagnostics.extend(self.check_proof_technique_patterns(file, content));
        diagnostics.extend(self.check_smt_pattern_hints(file, content));
        diagnostics.extend(self.check_calc_block_patterns(file, content));
        diagnostics.extend(self.check_decreases_patterns(file, content));
        diagnostics.extend(self.check_ghost_erased_patterns(file, content));
        diagnostics.extend(self.check_fuel_pragma_patterns(file, content));
        diagnostics.extend(self.check_assert_false_patterns(file, content));
        diagnostics.extend(self.check_smtpat_selectivity(file, content));
        diagnostics.extend(self.check_calc_inequality_patterns(file, content));

        diagnostics
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn make_path() -> PathBuf {
        PathBuf::from("test.fst")
    }

    // === List Pattern Tests ===

    #[test]
    fn test_list_append_length_hint() {
        let rule = ProofHintsRule::new();
        let content = "let len = List.length (xs @ ys)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("append_length")));
    }

    #[test]
    fn test_list_rev_rev_hint() {
        let rule = ProofHintsRule::new();
        let content = "let xs' = List.rev (List.rev xs)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("rev_involutive")));
    }

    #[test]
    fn test_list_mem_append_hint() {
        let rule = ProofHintsRule::new();
        let content = "let b = List.mem x (xs @ ys)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("append_mem")));
    }

    #[test]
    fn test_list_index_append_hint() {
        let rule = ProofHintsRule::new();
        let content = "let v = List.index (xs @ ys) i";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("append_index")));
    }

    #[test]
    fn test_list_map_length_hint() {
        let rule = ProofHintsRule::new();
        let content = "let n = List.length (List.map f xs)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("map_length")));
    }

    #[test]
    fn test_list_filter_length_hint() {
        let rule = ProofHintsRule::new();
        let content = "let n = List.length (List.filter f xs)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("filter_length")));
    }

    // === Sequence Pattern Tests ===

    #[test]
    fn test_seq_append_length_hint() {
        let rule = ProofHintsRule::new();
        let content = "let n = Seq.length (Seq.append s1 s2)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("lemma_len_append")));
    }

    #[test]
    fn test_seq_slice_append_hint() {
        let rule = ProofHintsRule::new();
        let content = "let s = Seq.slice (Seq.append s1 s2) i j";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("slice") || d.message.contains("append")));
    }

    #[test]
    fn test_seq_slice_length_hint() {
        let rule = ProofHintsRule::new();
        let content = "let n = Seq.length (Seq.slice s i j)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("lemma_len_slice")));
    }

    #[test]
    fn test_seq_index_upd_hint() {
        let rule = ProofHintsRule::new();
        let content = "let v = Seq.index (Seq.upd s i x) j";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("lemma_index_upd")));
    }

    #[test]
    fn test_seq_equal_hint_in_assert_context() {
        let rule = ProofHintsRule::new();
        let content = "assert (Seq.equal s1 s2)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("lemma_eq")));
    }

    #[test]
    fn test_seq_slice_full_hint() {
        let rule = ProofHintsRule::new();
        let content = "let s' = Seq.slice s 0 (Seq.length s)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("lemma_slice_full")));
    }

    // === Modular Arithmetic Tests ===

    #[test]
    fn test_mod_plus_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert ((a + b * n) % n == a % n)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("lemma_mod_plus")));
    }

    #[test]
    fn test_mod_plus_no_hint_bare_usage() {
        let rule = ProofHintsRule::new();
        let content = "let r = (a + b * n) % n";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("lemma_mod_plus")));
    }

    #[test]
    fn test_mod_mul_cancel_hint() {
        let rule = ProofHintsRule::new();
        let content = "assert ((a * n) % n == 0)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("cancel_mul_mod")));
    }

    #[test]
    fn test_div_mul_cancel_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert ((a * n) / n == a)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("cancel_mul_div")));
    }

    #[test]
    fn test_div_mul_no_hint_bare() {
        let rule = ProofHintsRule::new();
        let content = "let r = (a * n) / n";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("cancel_mul_div")));
    }

    #[test]
    fn test_mod_mod_hint() {
        let rule = ProofHintsRule::new();
        // MOD_MOD is specific enough to always fire
        let content = "let r = (a % n) % n";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("lemma_mod_mod")));
    }

    // === Power of 2 Tests ===

    #[test]
    fn test_pow2_double_hint() {
        let rule = ProofHintsRule::new();
        let content = "assert (pow2 n + pow2 n == pow2 (n + 1))";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("pow2_double_sum")));
    }

    #[test]
    fn test_pow2_mul_hint() {
        let rule = ProofHintsRule::new();
        let content = "let x = pow2 m * pow2 n";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("pow2_plus")));
    }

    #[test]
    fn test_pow2_div_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (y / pow2 8 == z)";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("pow2") && d.message.contains("div")));
    }

    #[test]
    fn test_pow2_div_no_hint_bare() {
        let rule = ProofHintsRule::new();
        let content = "let x = y / pow2 8";
        let diags = rule.check(&make_path(), content);
        assert!(!diags
            .iter()
            .any(|d| d.message.contains("Division by pow2")));
    }

    #[test]
    fn test_pow2_mod_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (y % pow2 8 == z)";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("pow2") && d.message.contains("modulo")));
    }

    #[test]
    fn test_pow2_mod_no_hint_bare() {
        let rule = ProofHintsRule::new();
        let content = "let x = y % pow2 8";
        let diags = rule.check(&make_path(), content);
        assert!(!diags
            .iter()
            .any(|d| d.message.contains("Modulo pow2")));
    }

    #[test]
    fn test_pow2_bare_in_assert_suggests_assert_norm() {
        let rule = ProofHintsRule::new();
        let content = "assert (x < pow2 32)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("assert_norm")));
    }

    #[test]
    fn test_pow2_bare_no_hint_in_type_sig() {
        let rule = ProofHintsRule::new();
        // Bare pow2 in a type signature should NOT fire
        let content = "val f: x:int{x < pow2 64} -> y:int";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("assert_norm")
            && d.message.contains("Use assert_norm to normalize pow2")));
    }

    #[test]
    fn test_pow2_bare_near_admit_fires() {
        let rule = ProofHintsRule::new();
        let content = "let x = pow2 32 in\nadmit()";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("assert_norm")));
    }

    #[test]
    fn test_pow2_with_assert_norm_no_extra_hint() {
        let rule = ProofHintsRule::new();
        let content = "let _ = assert_norm (pow2 32 == 4294967296)";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| {
            d.message.contains("assert_norm")
                && d.message.contains("Use assert_norm to normalize pow2")
        }));
    }

    // === Classical Logic Tests ===

    #[test]
    fn test_forall_intro_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (forall (x: nat). x >= 0)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("forall_intro")));
    }

    #[test]
    fn test_forall_no_hint_in_spec() {
        let rule = ProofHintsRule::new();
        // forall in a type signature / spec should NOT fire
        let content = "val f: squash (forall (x: nat). x >= 0)";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("forall_intro")));
    }

    #[test]
    fn test_forall_hint_near_admit() {
        let rule = ProofHintsRule::new();
        let content = "let _ = forall (x: nat). x >= 0 in\nlet y = 1 in\nadmit()";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("forall_intro")));
    }

    #[test]
    fn test_exists_intro_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (exists (x: nat). x > 10)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("exists_intro")));
    }

    #[test]
    fn test_exists_no_hint_in_spec() {
        let rule = ProofHintsRule::new();
        let content = "val f: squash (exists (x: nat). x > 10)";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("exists_intro")));
    }

    #[test]
    fn test_forall_impl_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (forall x. P x ==> Q x)";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("forall_intro") || d.message.contains("move_requires")));
    }

    // === Bitvector Tests ===

    #[test]
    fn test_logand_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (logand x 0xff == x % 256)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("logand")));
    }

    #[test]
    fn test_logand_no_hint_bare_usage() {
        let rule = ProofHintsRule::new();
        // Bare computational use should NOT fire
        let content = "let masked = logand x 0xff";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("logand")));
    }

    #[test]
    fn test_logxor_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (logxor a a == 0)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("logxor")));
    }

    #[test]
    fn test_logxor_no_hint_bare_usage() {
        let rule = ProofHintsRule::new();
        let content = "let result = logxor a b";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("logxor")));
    }

    #[test]
    fn test_logor_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (logor a 0 == a)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("logor")));
    }

    #[test]
    fn test_logor_no_hint_bare_usage() {
        let rule = ProofHintsRule::new();
        let content = "let combined = logor a b";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("logor")));
    }

    #[test]
    fn test_shift_left_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (shift_left x n == x * pow2 n)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("shift_left")));
    }

    #[test]
    fn test_shift_left_no_hint_bare_usage() {
        let rule = ProofHintsRule::new();
        let content = "let shifted = shift_left x n";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("shift_left")));
    }

    #[test]
    fn test_shift_right_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (shift_right x n == x / pow2 n)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("shift_right")));
    }

    #[test]
    fn test_shift_right_no_hint_bare_usage() {
        let rule = ProofHintsRule::new();
        let content = "let shifted = shift_right x n";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("shift_right")));
    }

    #[test]
    fn test_lognot_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (lognot (lognot x) == x)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("lognot")));
    }

    #[test]
    fn test_lognot_no_hint_bare_usage() {
        let rule = ProofHintsRule::new();
        let content = "let inverted = lognot x";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("lognot")));
    }

    #[test]
    fn test_bitvector_near_admit_fires() {
        let rule = ProofHintsRule::new();
        let content = "let result = logand x 0xff in\nadmit()";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("logand")));
    }

    #[test]
    fn test_bitvector_with_assert_norm_no_hint() {
        let rule = ProofHintsRule::new();
        let content = "let _ = assert_norm (logand x 0xff == 0)";
        let diags = rule.check(&make_path(), content);
        // Should not suggest when assert_norm is present
        assert!(!diags
            .iter()
            .any(|d| d.message.contains("logand") && d.message.contains("lemmas")));
    }

    // === Seq.equal context gating ===

    #[test]
    fn test_seq_equal_hint_in_assert() {
        let rule = ProofHintsRule::new();
        let content = "assert (Seq.equal s1 s2)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("lemma_eq")));
    }

    #[test]
    fn test_seq_equal_no_hint_in_ensures() {
        let rule = ProofHintsRule::new();
        // Seq.equal in ensures is a spec, not a proof struggle
        // Note: ensures starts the line (trimmed) so it IS proof context,
        // but regular usage in a let binding is not.
        let content = "let b = Seq.equal s1 s2";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("lemma_eq")));
    }

    // === Proof Technique Tests ===

    #[test]
    fn test_multiple_asserts_suggest_calc() {
        let rule = ProofHintsRule::new();
        let content = r#"
assert (a == b);
assert (b == c);
assert (c == d);
"#;
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("calc")));
    }

    // === Skip Tests ===

    #[test]
    fn test_comment_lines_skipped() {
        let rule = ProofHintsRule::new();
        let content = "(* List.length (xs @ ys) *)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    #[test]
    fn test_lines_with_lemma_calls_skipped() {
        let rule = ProofHintsRule::new();
        let content = "let _ = lemma_len_append s1 s2 in Seq.length (Seq.append s1 s2)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    // === Proof context helper tests ===

    #[test]
    fn test_is_proof_context_assert() {
        assert!(ProofHintsRule::is_proof_context("  assert (x == y)"));
    }

    #[test]
    fn test_is_proof_context_requires() {
        assert!(ProofHintsRule::is_proof_context("  requires (x > 0)"));
    }

    #[test]
    fn test_is_proof_context_ensures() {
        assert!(ProofHintsRule::is_proof_context("  ensures (result > 0)"));
    }

    #[test]
    fn test_is_proof_context_bare_let() {
        assert!(!ProofHintsRule::is_proof_context("  let x = logand a b"));
    }

    #[test]
    fn test_has_nearby_admit() {
        let lines = vec!["let x = 1", "let y = 2", "admit()", "let z = 3"];
        assert!(ProofHintsRule::has_nearby_admit(&lines, 0, 5));
        assert!(ProofHintsRule::has_nearby_admit(&lines, 3, 5));
        assert!(!ProofHintsRule::has_nearby_admit(&lines, 0, 1));
    }

    // === Utility Function Tests ===

    #[test]
    fn test_get_hints_by_category() {
        let list_hints = ProofHintsRule::get_hints_by_category(HintCategory::List);
        assert!(list_hints.len() >= 4);
        assert!(list_hints.iter().all(|h| h.category == HintCategory::List));
    }

    #[test]
    fn test_search_hints() {
        let results = ProofHintsRule::search_hints("append");
        assert!(!results.is_empty());
        assert!(results.iter().any(|h| h.pattern_name.contains("append")));
    }

    #[test]
    fn test_search_hints_case_insensitive() {
        let results = ProofHintsRule::search_hints("APPEND");
        assert!(!results.is_empty());
    }

    #[test]
    fn test_hint_database_has_all_categories() {
        let categories = [
            HintCategory::List,
            HintCategory::Sequence,
            HintCategory::ModularArithmetic,
            HintCategory::PowerOfTwo,
            HintCategory::ClassicalLogic,
            HintCategory::Bitvector,
            HintCategory::ProofTechnique,
        ];

        for cat in categories {
            let hints = ProofHintsRule::get_hints_by_category(cat);
            assert!(!hints.is_empty(), "Category {:?} should have hints", cat);
        }
    }

    #[test]
    fn test_hint_database_entries_valid() {
        for hint in HINT_DATABASE {
            assert!(
                !hint.pattern_name.is_empty(),
                "Pattern name should not be empty"
            );
            assert!(!hint.lemma.is_empty(), "Lemma should not be empty");
            assert!(
                !hint.description.is_empty(),
                "Description should not be empty"
            );
        }
    }

    // ========== NEW: SMTPat pattern tests ==========

    #[test]
    fn test_smtpat_or_detected() {
        let rule = ProofHintsRule::new();
        let content = r#"val lemma1 : x:nat -> Lemma (P x) [SMTPatOr [[SMTPat (f x)]; [SMTPat (g x)]]]"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("SMTPatOr")),
            "Should detect SMTPatOr usage"
        );
    }

    #[test]
    fn test_lemma_without_smtpat_with_nearby_admit() {
        let rule = ProofHintsRule::new();
        let content = r#"
val my_lemma : x:nat -> Lemma (x + 0 == x)
let my_lemma x = admit ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("SMTPat")),
            "Should suggest SMTPat for lemma near admit"
        );
    }

    #[test]
    fn test_lemma_with_smtpat_no_warning() {
        let rule = ProofHintsRule::new();
        let content = r#"val my_lemma : x:nat -> Lemma (x + 0 == x) [SMTPat (x + 0)]"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("without") && d.message.contains("SMTPat")),
            "Should not warn when SMTPat is present"
        );
    }

    // ========== NEW: Calc block tests ==========

    #[test]
    fn test_long_calc_block_detected() {
        let rule = ProofHintsRule::new();
        // Build a calc block with > 8 steps
        let mut content = String::from("let proof x =\n  calc (==) {\n    step0;\n");
        for i in 1..=10 {
            content.push_str(&format!("    == {{ lemma{} () }}\n    step{};\n", i, i));
        }
        content.push_str("  }\n");
        let diags = rule.check(&make_path(), &content);
        assert!(
            diags.iter().any(|d| d.message.contains("Long calc block")),
            "Should detect long calc block"
        );
    }

    #[test]
    fn test_short_calc_block_no_warning() {
        let rule = ProofHintsRule::new();
        let content = r#"
let proof x =
  calc (==) {
    step0;
    == { lemma1 () }
    step1;
    == { lemma2 () }
    step2;
  }
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Long calc block")),
            "Short calc block should not trigger warning"
        );
    }

    // ========== NEW: Assert-by-tactic tests ==========

    #[test]
    fn test_assert_by_tadmit_detected() {
        let rule = ProofHintsRule::new();
        let content = r#"let proof x = assert (P x) by (tadmit())"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("tadmit")),
            "Should detect tadmit in assert-by-tactic"
        );
    }

    #[test]
    fn test_assert_by_smt_no_warning() {
        let rule = ProofHintsRule::new();
        let content = r#"let proof x = assert (P x) by (smt())"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("tadmit")),
            "assert by (smt()) should not trigger tadmit warning"
        );
    }

    // ========== NEW: Decreases clause tests ==========

    #[test]
    fn test_let_rec_without_decreases_near_admit() {
        let rule = ProofHintsRule::new();
        let content = r#"
let rec factorial (n:nat) : nat =
  if n = 0 then 1
  else n * factorial (n - 1)
let _ = admit ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("decreases")),
            "Should suggest decreases clause near admit"
        );
    }

    #[test]
    fn test_let_rec_with_decreases_no_warning() {
        let rule = ProofHintsRule::new();
        let content = r#"
let rec factorial (n:nat) : Tot nat (decreases n) =
  if n = 0 then 1
  else n * factorial (n - 1)
let _ = admit ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Recursive function without")),
            "Should not warn when decreases is present"
        );
    }

    // ========== NEW: Ghost/erased pattern tests ==========

    #[test]
    fn test_reveal_hide_roundtrip_in_proof() {
        let rule = ProofHintsRule::new();
        let content = r#"
let proof x =
  assert (reveal (hide x) == x);
  admit ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("reveal") && d.message.contains("hide")),
            "Should detect reveal/hide round-trip"
        );
    }

    #[test]
    fn test_squash_in_proof_context() {
        let rule = ProofHintsRule::new();
        let content = r#"
let proof x =
  assert (squash (x == 0));
  admit ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("squash")),
            "Should detect squash in proof context"
        );
    }

    // ========== NEW: Fuel pragma / push-pop tests ==========

    #[test]
    fn test_unbalanced_push_pop_detected() {
        let rule = ProofHintsRule::new();
        let content = r#"
#push-options "--fuel 2"
let foo x = x + 1
#push-options "--fuel 4"
let bar x = x + 2
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("push-options") && d.message.contains("pop-options")),
            "Should detect unbalanced push/pop-options"
        );
    }

    #[test]
    fn test_balanced_push_pop_no_warning() {
        let rule = ProofHintsRule::new();
        let content = r#"
#push-options "--fuel 2"
let foo x = x + 1
#pop-options
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Unbalanced") || (d.message.contains("push-options") && d.message.contains("pop-options"))),
            "Balanced push/pop should not trigger warning"
        );
    }

    #[test]
    fn test_restart_solver_hint() {
        let rule = ProofHintsRule::new();
        let content = r#"
#restart-solver
let proof x = admit ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("restart-solver")),
            "Should hint about restart-solver usage"
        );
    }

    // ========== NEW: Category tests ==========

    #[test]
    fn test_hint_categories_complete() {
        // Verify all new categories have at least one hint
        let smt_hints = ProofHintsRule::get_hints_by_category(HintCategory::SmtPattern);
        assert!(!smt_hints.is_empty(), "SmtPattern category should have hints");

        let ghost_hints = ProofHintsRule::get_hints_by_category(HintCategory::GhostErased);
        assert!(!ghost_hints.is_empty(), "GhostErased category should have hints");

        let dec_hints = ProofHintsRule::get_hints_by_category(HintCategory::DecreasesClause);
        assert!(!dec_hints.is_empty(), "DecreasesClause category should have hints");
    }

    #[test]
    fn test_search_hints_smtpat() {
        let results = ProofHintsRule::search_hints("SMTPat");
        assert!(!results.is_empty(), "Should find hints about SMTPat");
    }

    #[test]
    fn test_search_hints_decreases() {
        let results = ProofHintsRule::search_hints("decreases");
        assert!(!results.is_empty(), "Should find hints about decreases");
    }

    // ========== NEW: Assert false tests ==========

    #[test]
    fn test_assert_false_detected() {
        let rule = ProofHintsRule::new();
        let content = "let proof x = assert false";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("assert false") || d.message.contains("False elimination")),
            "Should detect assert false"
        );
    }

    #[test]
    fn test_assert_false_with_parens_detected() {
        let rule = ProofHintsRule::new();
        let content = "let proof x = assert (False)";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("False elimination")),
            "Should detect assert (False)"
        );
    }

    #[test]
    fn test_assert_false_in_comment_skipped() {
        let rule = ProofHintsRule::new();
        let content = "// assert false is used for reductio";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("False elimination")),
            "Should skip assert false in comments"
        );
    }

    // ========== NEW: SMTPat selectivity tests ==========

    #[test]
    fn test_smtpat_bare_var_warning() {
        let rule = ProofHintsRule::new();
        let content = "val lemma1 : x:nat -> Lemma (P x) [SMTPat x]";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("bare variable") && d.message.contains("matching loops")),
            "Should warn about SMTPat on bare variable"
        );
    }

    #[test]
    fn test_smtpat_application_no_warning() {
        let rule = ProofHintsRule::new();
        let content = "val lemma1 : x:nat -> Lemma (P x) [SMTPat (f x)]";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("bare variable")),
            "Should not warn about SMTPat on function application"
        );
    }

    // ========== NEW: Calc inequality tests ==========

    #[test]
    fn test_calc_inequality_hint() {
        let rule = ProofHintsRule::new();
        let content = "  calc (<=) {";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("inequality relation")),
            "Should provide hint for calc with inequality"
        );
    }

    #[test]
    fn test_calc_equality_no_inequality_hint() {
        let rule = ProofHintsRule::new();
        let content = "  calc (==) {";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("inequality relation")),
            "Should not fire inequality hint for equality calc"
        );
    }

    #[test]
    fn test_calc_less_than_hint() {
        let rule = ProofHintsRule::new();
        let content = "  calc (<) {";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("inequality relation")),
            "Should provide hint for calc with < relation"
        );
    }
}
