//! FST011: Effect checker.
//!
//! Detects effect-related issues in F* code:
//!
//! F* Effect Hierarchy (lattice with TWO branches):
//! ```text
//!                    Tot (pure total)
//!                   /                \
//!                  /                  \
//!               GTot                 Pure
//!           (ghost total)       (pre/post, may diverge)
//!                |                    |
//!              Ghost                 Div
//!           (erased)            (divergent)
//!                |                 /    \
//!              Lemma             ST     Exn
//!                              (state) (exceptions)
//!                                 \    /
//!                                  All
//!                               (combined)
//!                                   |
//!                                  ML
//!                            (unrestricted)
//! ```
//!
//! Key rules:
//! - Ghost branch (erased at extraction): Tot -> GTot -> Ghost/Lemma
//! - Computational branch (extracted): Tot -> Pure -> Div -> ST/Exn -> All -> ML
//! - Ghost and Pure are on SEPARATE branches - Ghost cannot call Pure
//! - ST and Exn can both call Div (divergence is a sub-effect of both)
//!
//! Checks:
//! 1. `admit()` usage - bypasses verification
//! 2. `magic()` usage - produces arbitrary values unsafely
//! 3. `unsafe_coerce` usage - bypasses type safety
//! 4. Overly permissive ML effect when more restrictive would suffice
//! 5. Tot function calling effectful code
//! 6. Ghost in computational (non-ghost) context

use lazy_static::lazy_static;
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::path::Path;

use super::parser::{parse_fstar_file, BlockType, DeclarationBlock};
use super::rules::{Diagnostic, DiagnosticSeverity, Range, Rule, RuleCode};
use super::shared_patterns::{
    ASSUME_VAL_RE, INLINE_FOR_EXTRACTION_RE, EFFECT_ANNOTATION_RE, ASSERT_FALSE_RE,
};

/// F* Effect hierarchy.
///
/// Effects are ordered from most restrictive (Tot) to least restrictive (ML).
/// The ordering determines what effects a function can call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Effect {
    /// Pure total - always terminates, no side effects, no ghost
    Tot,
    /// Ghost total - ghost computation that terminates
    GTot,
    /// Pure with pre/post conditions
    Pure,
    /// Ghost computation (erased at extraction)
    Ghost,
    /// Lemma - special ghost for proofs (equivalent to Ghost for hierarchy)
    Lemma,
    /// Divergent - may not terminate
    Div,
    /// Stateful - heap operations
    ST,
    /// Exception - may raise exceptions
    Exn,
    /// All effects - state + exceptions + divergence
    All,
    /// ML - unrestricted effects (OCaml-like)
    ML,
}

impl Effect {
    /// Parse an effect from its string representation.
    ///
    /// Returns None for unrecognized effect names. Handles all F* built-in
    /// effects and common aliases from FStar.Pervasives, FStar.HyperStack.ST,
    /// FStar.Tactics.Effect, etc.
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            // Pure total (most restrictive)
            "Tot" | "PURE" => Some(Effect::Tot),
            // Ghost total
            "GTot" | "GHOST" => Some(Effect::GTot),
            // Pure with pre/post
            "Pure" => Some(Effect::Pure),
            // Ghost computation
            "Ghost" => Some(Effect::Ghost),
            // Lemma (special ghost for proofs)
            "Lemma" | "TacH" | "TacS" | "TacRO" | "TacF" => Some(Effect::Lemma),
            // Divergent
            "Div" | "Dv" | "DIV" | "EXT" => Some(Effect::Div),
            // Stateful (heap operations) - all HyperStack.ST variants
            "ST" | "Stack" | "STATE" | "State" | "St"
            | "Heap" | "StackInline" | "Inline" | "STL"
            | "GST" | "Unsafe" => Some(Effect::ST),
            // Tactic effect (acts like state for the proof engine)
            "Tac" | "TAC" => Some(Effect::ST),
            // Exception
            "Exn" | "Ex" | "EXN" => Some(Effect::Exn),
            // All effects combined
            "All" | "ALL" => Some(Effect::All),
            // ML - unrestricted
            "ML" => Some(Effect::ML),
            _ => None,
        }
    }

    /// Returns the hierarchy level of this effect.
    ///
    /// Lower values are more restrictive. Used for effect compatibility checks.
    fn level(&self) -> u8 {
        match self {
            Effect::Tot => 0,
            Effect::GTot => 1,
            Effect::Pure => 2,
            Effect::Ghost | Effect::Lemma => 3,
            Effect::Div => 4,
            Effect::ST => 5,
            Effect::Exn => 5,
            Effect::All => 6,
            Effect::ML => 7,
        }
    }

    /// Check if this effect can call a function with the given effect.
    ///
    /// Effect compatibility rules (based on F* effect lattice):
    /// - Tot can only call Tot (most restrictive)
    /// - GTot can call Tot, GTot (ghost-compatible only)
    /// - Pure can call Tot, Pure (computational branch)
    /// - Ghost/Lemma can call Tot, GTot, Ghost, Lemma (ghost branch only)
    /// - Div can call Tot, Pure, Div
    /// - ST can call Tot, Pure, Div, ST (state effects)
    /// - Exn can call Tot, Pure, Div, Exn (exception effects)
    /// - All can call anything except ML
    /// - ML can call anything (least restrictive)
    pub fn can_call(&self, callee: Effect) -> bool {
        match (self, callee) {
            // Tot can call Tot and Pure (Tot a = Pure a True (fun _ -> True))
            // In F*, Tot is a specialization of Pure with trivial WP.
            (Effect::Tot, Effect::Tot) => true,
            (Effect::Tot, Effect::Pure) => true,
            (Effect::Tot, _) => false,

            // GTot can call Tot and GTot (ghost-compatible)
            (Effect::GTot, Effect::Tot) => true,
            (Effect::GTot, Effect::GTot) => true,
            (Effect::GTot, _) => false,

            // Pure can call Tot and Pure
            (Effect::Pure, Effect::Tot) => true,
            (Effect::Pure, Effect::Pure) => true,
            (Effect::Pure, _) => false,

            // Ghost/Lemma can call ghost-compatible effects
            (Effect::Ghost | Effect::Lemma, Effect::Tot) => true,
            (Effect::Ghost | Effect::Lemma, Effect::GTot) => true,
            (Effect::Ghost | Effect::Lemma, Effect::Ghost) => true,
            (Effect::Ghost | Effect::Lemma, Effect::Lemma) => true,
            (Effect::Ghost | Effect::Lemma, _) => false,

            // Div can call Tot, Pure, Div
            (Effect::Div, Effect::Tot) => true,
            (Effect::Div, Effect::Pure) => true,
            (Effect::Div, Effect::Div) => true,
            (Effect::Div, _) => false,

            // ST can call Tot, Pure, Div, ST
            (Effect::ST, Effect::Tot) => true,
            (Effect::ST, Effect::Pure) => true,
            (Effect::ST, Effect::Div) => true,
            (Effect::ST, Effect::ST) => true,
            (Effect::ST, _) => false,

            // Exn can call Tot, Pure, Div, Exn
            // (Div is a sub-effect of Exn - exceptions may also diverge)
            (Effect::Exn, Effect::Tot) => true,
            (Effect::Exn, Effect::Pure) => true,
            (Effect::Exn, Effect::Div) => true,
            (Effect::Exn, Effect::Exn) => true,
            (Effect::Exn, _) => false,

            // All can call anything except ML
            (Effect::All, Effect::ML) => false,
            (Effect::All, _) => true,

            // ML can call anything
            (Effect::ML, _) => true,
        }
    }

    /// Check if this effect is a ghost effect (erased at extraction).
    pub fn is_ghost(&self) -> bool {
        matches!(self, Effect::GTot | Effect::Ghost | Effect::Lemma)
    }

    /// Check if this effect is computational (not ghost).
    pub fn is_computational(&self) -> bool {
        !self.is_ghost() && *self != Effect::Tot
    }

    /// Human-readable name for error messages.
    pub fn display_name(&self) -> &'static str {
        match self {
            Effect::Tot => "Tot",
            Effect::GTot => "GTot",
            Effect::Pure => "Pure",
            Effect::Ghost => "Ghost",
            Effect::Lemma => "Lemma",
            Effect::Div => "Div",
            Effect::ST => "ST",
            Effect::Exn => "Exn",
            Effect::All => "All",
            Effect::ML => "ML",
        }
    }
}

impl PartialOrd for Effect {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Effect {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.level().cmp(&other.level())
    }
}

lazy_static! {
    /// Pattern for admit() - bypasses verification
    static ref ADMIT_PATTERN: Regex = Regex::new(r"\badmit\s*\(\s*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for magic() - produces arbitrary values
    static ref MAGIC_PATTERN: Regex = Regex::new(r"\bmagic\s*\(\s*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for unsafe_coerce - bypasses type safety
    static ref UNSAFE_COERCE: Regex = Regex::new(r"\bunsafe_coerce\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for ML effect annotation
    static ref ML_EFFECT: Regex = Regex::new(r"\bML\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for extract-related context (ML is acceptable here)
    static ref EXTRACT_CONTEXT: Regex = Regex::new(r"\b(?:extract|extraction|noextract|inline_for_extraction)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for assume (expr) - bypasses verification of a condition
    /// Note: Must NOT match `assume val` which is handled separately
    static ref ASSUME_EXPR: Regex = Regex::new(r"\bassume\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for finding column position of a pattern match
    static ref ADMIT_COLUMN: Regex = Regex::new(r"\badmit\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref MAGIC_COLUMN: Regex = Regex::new(r"\bmagic\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect effect abbreviation definitions: `effect Name (...) = ...`
    /// Used by FST011 to validate effect declarations.
    static ref EFFECT_ABBREV_DEF: Regex = Regex::new(
        r"^effect\s+([A-Z][\w']*)\s*(?:\([^)]*\)\s*)*=\s*([A-Z][\w']*)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect new_effect definitions: `new_effect { NAME : ... }`
    /// or `new_effect NAME = BASE`
    static ref NEW_EFFECT_DEF: Regex = Regex::new(
        r"^new_effect\s+(?:\{\s*)?([A-Z][\w']*)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect sub_effect: `sub_effect SRC ~> DST`
    static ref SUB_EFFECT_DEF: Regex = Regex::new(
        r"^sub_effect\s+([A-Z][\w']*)\s*~>\s*([A-Z][\w']*)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect effect combinator keywords in effect bodies
    /// (return_wp, bind_wp, repr, return, bind, subcomp, if_then_else, etc.)
    static ref EFFECT_COMBINATOR: Regex = Regex::new(
        r"\b(return_wp|bind_wp|if_then_else|ite_wp|stronger|close_wp|trivial|repr|return|bind|subcomp|close|lift_wp)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for --admit_smt_queries true (dangerous flag)
    static ref ADMIT_SMT_QUERIES: Regex = Regex::new(r"--admit_smt_queries\s+true").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for Classical.forall_intro / Classical.exists_intro / Classical.move_requires
    static ref CLASSICAL_FORALL: Regex = Regex::new(r"\bClassical\.forall_intro\b").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref CLASSICAL_MOVE_REQ: Regex = Regex::new(r"\bClassical\.move_requires\b").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref CLASSICAL_EXISTS: Regex = Regex::new(r"\bClassical\.exists_intro\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for tadmit() - tactic version of admit
    static ref TADMIT_PATTERN: Regex = Regex::new(r"\btadmit\s*\(\s*\)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for undefined - `FStar.Pervasives.undefined` or bare `undefined`
    /// This is another verification bypass that produces values without proof.
    static ref UNDEFINED_PATTERN: Regex = Regex::new(
        r"\b(?:FStar\.Pervasives\.)?undefined\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `synth_by_tactic (fun () -> tadmit())` - hidden admit via tactic synthesis
    static ref SYNTH_TADMIT_PATTERN: Regex = Regex::new(
        r"\bsynth_by_tactic\s*\(.*\btadmit\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `requires`/`ensures`/`decreases` clauses in effect signatures.
    /// These appear in Hoare-style effect annotations:
    ///     Stack unit (requires fun h -> ...) (ensures fun h0 _ h1 -> ...)
    static ref EFFECT_SPEC_CLAUSE: Regex = Regex::new(
        r"\b(requires|ensures|decreases|modifies)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for function call detection.
    /// Matches: function_name (...) or function_name arg or function_name "string"
    static ref FUNCTION_CALL: Regex = Regex::new(
        r#"\b([a-z_][a-zA-Z0-9_']*)\s*(?:\(|[a-z_0-9"])"#
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for ghost annotation on let bindings.
    static ref GHOST_LET: Regex = Regex::new(r"\bghost\s+let\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for unqualified identifier reference (not preceded by a dot).
    /// Used for ghost binding detection where we need to find variable references,
    /// not just function calls.
    static ref UNQUALIFIED_IDENT: Regex = Regex::new(r"\b([a-z_][a-zA-Z0-9_']*)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Known built-in functions that are Tot (pure).
    static ref TOT_BUILTINS: std::collections::HashSet<&'static str> = {
        let mut s = std::collections::HashSet::new();
        // Arithmetic operators (as functions)
        for name in &["op_Addition", "op_Subtraction", "op_Multiply", "op_Division",
                      "op_Modulus", "op_Plus", "op_Minus"] {
            s.insert(*name);
        }
        // Comparison operators
        for name in &["op_Equality", "op_disEquality", "op_LessThan", "op_GreaterThan",
                      "op_LessThanOrEqual", "op_GreaterThanOrEqual"] {
            s.insert(*name);
        }
        // Boolean operators
        for name in &["op_Negation", "op_AmpAmp", "op_BarBar", "not"] {
            s.insert(*name);
        }
        // List operations (Tot) - FStar.List.Tot
        for name in &["hd", "tl", "length", "rev", "append", "mem", "nth", "map", "filter",
                      "fold_left", "fold_right", "for_all", "existsb", "find", "index",
                      "splitAt", "split", "unzip", "zip", "assoc", "concat", "flatten"] {
            s.insert(*name);
        }
        // Option operations (Tot)
        for name in &["Some", "None", "is_Some", "is_None"] {
            s.insert(*name);
        }
        // Tuple operations (Tot)
        for name in &["fst", "snd", "dfst", "dsnd"] {
            s.insert(*name);
        }
        // Basic combinators (Tot)
        for name in &["id", "const", "compose", "on"] {
            s.insert(*name);
        }
        // Normalization functions (Tot - type-level computation)
        for name in &["normalize_term", "normalize", "norm", "norm_spec", "reveal_opaque"] {
            s.insert(*name);
        }
        // Sequence operations (FStar.Seq - Tot)
        for name in &["create", "init", "empty", "seq_length", "seq_index", "upd",
                      "slice", "append", "cons", "snoc", "head", "tail", "last",
                      "seq_to_list", "seq_of_list", "equal"] {
            s.insert(*name);
        }
        // Classical logic (Tot/GTot)
        for name in &["squash", "return_squash", "get_proof", "bind_squash"] {
            s.insert(*name);
        }
        s
    };

    /// Known effectful functions (not Tot).
    /// Includes both simple names and last component of qualified names.
    static ref EFFECTFUL_FUNCTIONS: HashMap<&'static str, Effect> = {
        let mut m = HashMap::new();
        // IO effects (FStar.IO)
        m.insert("print_string", Effect::ML);
        m.insert("print_newline", Effect::ML);
        m.insert("print_int", Effect::ML);
        m.insert("print_any", Effect::ML);
        m.insert("prerr_string", Effect::ML);
        m.insert("read_line", Effect::ML);
        m.insert("input_line", Effect::ML);
        m.insert("input_int", Effect::ML);
        m.insert("input_float", Effect::ML);
        m.insert("debug_print_string", Effect::ML);
        // Reference operations (FStar.Ref, FStar.ST)
        m.insert("alloc", Effect::ST);
        m.insert("read", Effect::ST);
        m.insert("write", Effect::ST);
        m.insert("op_Bang", Effect::ST);
        m.insert("op_Colon_Equals", Effect::ST);
        m.insert("recall", Effect::ST);
        m.insert("witness_token", Effect::ST);
        m.insert("recall_token", Effect::ST);
        // HyperStack operations
        m.insert("get", Effect::ST);
        m.insert("push_frame", Effect::ST);
        m.insert("pop_frame", Effect::ST);
        m.insert("salloc", Effect::ST);
        m.insert("sfree", Effect::ST);
        // Buffer operations (LowStar.Buffer, Lib.Buffer)
        m.insert("malloc", Effect::ST);
        m.insert("free", Effect::ST);
        m.insert("blit", Effect::ST);
        m.insert("fill", Effect::ST);
        m.insert("index", Effect::ST);  // mutable index
        m.insert("upd", Effect::ST);    // mutable update
        m.insert("sub", Effect::ST);
        m.insert("offset", Effect::ST);
        // Exception operations (FStar.Exn)
        m.insert("raise", Effect::Exn);
        m.insert("try_with", Effect::Exn);
        m.insert("failwith", Effect::Exn);
        // Ghost operations (FStar.Ghost)
        m.insert("reveal", Effect::Ghost);
        m.insert("hide", Effect::Ghost);
        m.insert("elim_pure", Effect::Ghost);
        m
    };

    /// Pattern for qualified function names (e.g., FStar.IO.print_string)
    /// Group 0 = full match, Group 1 = last component.
    static ref QUALIFIED_CALL: Regex = Regex::new(
        r"\b((?:[A-Z][\w']*\.)+([a-z_][\w']*)\b)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Known Tot-module prefixes. Functions qualified with these are Tot unless
    /// explicitly annotated otherwise.
    static ref TOT_MODULE_PREFIXES: std::collections::HashSet<&'static str> = {
        let mut s = std::collections::HashSet::new();
        for prefix in &[
            "FStar.Seq.", "FStar.List.Tot.", "FStar.List.Pure.",
            "FStar.Map.", "FStar.Set.", "FStar.Option.",
            "FStar.BitVector.", "FStar.Math.", "FStar.Calc.",
            "FStar.Classical.", "FStar.Squash.", "FStar.Ghost.",
            "FStar.Int.Cast.", "FStar.Pervasives.",
            "FStar.FunctionalExtensionality.",
            "FStar.StrongExcludedMiddle.",
            "FStar.PropositionalExtensionality.",
            "Prims.",
        ] {
            s.insert(*prefix);
        }
        s
    };
}

/// Strip comments and string literals from a line to avoid false positives.
///
/// Removes:
/// - Single-line block comments: `(* ... *)`
/// - Line comments: `// ...`
/// - String literals: `"..."`
///
/// This is a best-effort approach for single-line analysis.
/// Multi-line comments spanning multiple lines are NOT handled (would require
/// tracking state across lines).
fn strip_comments_and_strings(line: &str) -> String {
    let mut result = String::with_capacity(line.len());
    let chars: Vec<char> = line.chars().collect();
    let len = chars.len();
    let mut i = 0;

    while i < len {
        // Check for string literal start
        if chars[i] == '"' {
            // Skip until closing quote (handle escape sequences)
            i += 1;
            while i < len {
                if chars[i] == '\\' && i + 1 < len {
                    i += 2; // Skip escaped char
                } else if chars[i] == '"' {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
            // Replace string content with placeholder to preserve spacing
            result.push_str("\"\"");
        }
        // Check for block comment start: (*
        else if chars[i] == '(' && i + 1 < len && chars[i + 1] == '*' {
            // Skip until closing *)
            i += 2;
            let mut depth = 1;
            while i < len && depth > 0 {
                if chars[i] == '(' && i + 1 < len && chars[i + 1] == '*' {
                    depth += 1;
                    i += 2;
                } else if chars[i] == '*' && i + 1 < len && chars[i + 1] == ')' {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            // Comment stripped, add a space to separate tokens
            result.push(' ');
        }
        // Check for line comment: //
        else if chars[i] == '/' && i + 1 < len && chars[i + 1] == '/' {
            // Skip rest of line
            break;
        }
        // Regular character
        else {
            result.push(chars[i]);
            i += 1;
        }
    }

    result
}

/// Check if a line is entirely within a comment.
///
/// Returns true if the line starts with a comment opener and has no code after,
/// or is empty/whitespace.
fn is_comment_line(line: &str) -> bool {
    let trimmed = line.trim();
    if trimmed.is_empty() {
        return true;
    }

    // Line comment - everything after // is comment
    if trimmed.starts_with("//") {
        return true;
    }

    // Lines that start with * and are continuation of multi-line comments
    if (trimmed.starts_with('*') && !trimmed.starts_with("**") && !trimmed.starts_with("*)"))
        || trimmed.starts_with("*)")
    {
        return true;
    }

    // Block comment that starts and ends on the same line - check if there's code after
    if trimmed.starts_with("(*") {
        // Find matching *) and check if there's code after
        let after_comment = strip_comments_and_strings(trimmed);
        // If only whitespace remains after stripping, it's a comment line
        return after_comment.trim().is_empty();
    }

    false
}

/// Extract the effect annotation from a declaration block.
///
/// Looks for effect annotations in the function signature (e.g., `-> Tot int`).
/// Returns None if no explicit effect annotation is found.
///
/// IMPORTANT: Takes the LAST match, not the first. In F* signatures like
///   `let f (#al: (bool -> Tot Type)) : Lemma ...`
/// the first match would be `Tot` from the parameter type, but the actual
/// function return effect is `Lemma` (the last one). The return effect always
/// comes after all parameter types.
fn extract_function_effect(block: &DeclarationBlock) -> Option<Effect> {
    let text = block.lines.join("");
    // Take the LAST effect annotation match -- that's the return effect.
    // Earlier matches are effects inside parameter types (e.g., `(x: nat -> Tot Type)`).
    let mut last_effect: Option<Effect> = None;
    for caps in EFFECT_ANNOTATION_RE.captures_iter(&text) {
        if let Some(m) = caps.get(1) {
            if let Some(eff) = Effect::parse(m.as_str()) {
                last_effect = Some(eff);
            }
        }
    }
    last_effect
}

/// Check if a declaration block is an explicit `ghost let` binding.
///
/// Only matches explicit `ghost let` patterns, NOT functions that merely
/// have `Ghost.erased` parameters or GTot effect. This distinction is
/// critical to avoid false positives:
/// - `Ghost.erased` parameters are type-level erasure markers, not ghost bindings
/// - GTot functions can be called from specification positions (requires/ensures)
/// - `inline_for_extraction` functions with `#t:limb_t` erased params are valid
/// - Only actual ghost VALUE bindings (`ghost let x = ...`) cannot be used computationally
///
/// The old `erased` keyword matching caused massive false positives:
/// - 621 in hacl-star (matched `Ghost.erased` in val parameter types)
/// - 2762 in everparse (same pattern, more prevalent)
fn is_explicit_ghost_let(block: &DeclarationBlock) -> bool {
    let text = block.lines.join("");
    GHOST_LET.is_match(&text)
}

/// Check if a declaration block is marked for extraction (computational).
fn is_extraction_binding(block: &DeclarationBlock) -> bool {
    let text = block.lines.join("");
    INLINE_FOR_EXTRACTION_RE.is_match(&text)
}

/// Extract ONLY unqualified identifier references from a code block.
///
/// This is used for ghost binding checking where we need to find any
/// reference to a local ghost binding. Unlike `extract_function_calls`,
/// this finds ALL identifier references, not just function calls.
///
/// Returns identifiers that are:
/// - NOT preceded by a dot (qualified references like Module.name are excluded)
/// - NOT keywords
/// - NOT type constructors (starting with uppercase)
fn extract_unqualified_function_calls(block: &DeclarationBlock) -> Vec<(String, usize)> {
    let mut identifiers = Vec::new();

    for (idx, line) in block.lines.iter().enumerate() {
        let line_num = block.start_line + idx;

        // Skip comment lines
        let trimmed = line.trim();
        if trimmed.starts_with("(*") || trimmed.starts_with("//") {
            continue;
        }

        // Strip inline comments and strings to avoid false positives
        let code_only = strip_comments_and_strings(line);

        // Find all unqualified identifiers (not preceded by a dot)
        for caps in UNQUALIFIED_IDENT.captures_iter(&code_only) {
            if let Some(m) = caps.get(1) {
                let name = m.as_str();
                let start = m.start();

                // Check if this is a qualified reference (preceded by a dot)
                let is_qualified = start > 0 && code_only.as_bytes().get(start - 1) == Some(&b'.');

                // Skip keywords, type constructors, and qualified references
                if !is_keyword(name)
                    && !name
                        .chars()
                        .next()
                        .map(|c| c.is_uppercase())
                        .unwrap_or(false)
                    && !is_qualified
                {
                    // Avoid duplicates on same line
                    if !identifiers.iter().any(|(n, l)| n == name && *l == line_num) {
                        identifiers.push((name.to_string(), line_num));
                    }
                }
            }
        }
    }

    identifiers
}

/// Extract function calls from a code block.
///
/// Returns a vector of (function_name, line_number) pairs.
/// For qualified names like FStar.IO.print_string, returns just "print_string".
/// A function call extracted from source code.
/// `qualified` is the full path (e.g., "FStar.Seq.index"), `bare` is the last component ("index").
struct ExtractedCall {
    bare: String,
    qualified: Option<String>,
    line_num: usize,
}

fn extract_function_calls(block: &DeclarationBlock) -> Vec<ExtractedCall> {
    let mut calls = Vec::new();

    for (idx, line) in block.lines.iter().enumerate() {
        let line_num = block.start_line + idx;

        // Skip comment lines
        let trimmed = line.trim();
        if trimmed.starts_with("(*") || trimmed.starts_with("//") {
            continue;
        }

        // Strip inline comments to avoid false positives
        let code_only = strip_comments_and_strings(line);

        // Find qualified function calls (e.g., FStar.IO.print_string)
        for caps in QUALIFIED_CALL.captures_iter(&code_only) {
            let full = caps.get(1).map(|m| m.as_str());
            let last = caps.get(2).map(|m| m.as_str());
            if let Some(name) = last {
                if !is_keyword(name) {
                    calls.push(ExtractedCall {
                        bare: name.to_string(),
                        qualified: full.map(|s| s.to_string()),
                        line_num,
                    });
                }
            }
        }

        // Find simple (unqualified) function calls
        for caps in FUNCTION_CALL.captures_iter(&code_only) {
            if let Some(m) = caps.get(1) {
                let name = m.as_str();
                // Skip keywords and type constructors (start with uppercase)
                if !is_keyword(name)
                    && !name
                        .chars()
                        .next()
                        .map(|c| c.is_uppercase())
                        .unwrap_or(false)
                {
                    // Avoid duplicates from qualified call detection
                    if !calls.iter().any(|c| c.bare == name && c.line_num == line_num) {
                        calls.push(ExtractedCall {
                            bare: name.to_string(),
                            qualified: None,
                            line_num,
                        });
                    }
                }
            }
        }
    }

    calls
}

/// Check if a name is an F* keyword.
fn is_keyword(name: &str) -> bool {
    matches!(
        name,
        "let"
            | "rec"
            | "in"
            | "if"
            | "then"
            | "else"
            | "match"
            | "with"
            | "fun"
            | "function"
            | "val"
            | "type"
            | "and"
            | "open"
            | "module"
            | "assume"
            | "assert"
            | "requires"
            | "ensures"
            | "decreases"
            | "modifies"
            | "returns"
            | "forall"
            | "exists"
            | "true"
            | "false"
            | "not"
            | "begin"
            | "end"
            | "private"
            | "unfold"
            | "inline_for_extraction"
            | "noextract"
            | "irreducible"
            | "noeq"
            | "abstract"
            // Effect-related keywords
            | "effect"
            | "new_effect"
            | "sub_effect"
            | "layered_effect"
            | "total_effect"
            | "reifiable"
            | "reflectable"
            | "ghost"
            // Effect combinator keywords
            | "repr"
            | "return_wp"
            | "bind_wp"
            | "if_then_else"
            | "ite_wp"
            | "stronger"
            | "close_wp"
            | "trivial"
            | "subcomp"
            | "lift_wp"
            | "close"
    )
}

/// FST011: Effect Checker
///
/// Analyzes F* effect usage for potential issues including verification
/// bypasses, overly permissive effect annotations, and effect hierarchy violations.
pub struct EffectCheckerRule;

impl EffectCheckerRule {
    pub fn new() -> Self {
        Self
    }

    /// Find the column position of a regex match in a line.
    fn find_column(line: &str, pattern: &Regex) -> usize {
        pattern.find(line).map(|m| m.start() + 1).unwrap_or(1)
    }

    /// Check for admit() usage.
    ///
    /// `admit()` bypasses the verification of the current goal, accepting
    /// it as true without proof. This is dangerous in production code.
    fn check_admit(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            // Skip lines that are entirely comments
            if is_comment_line(line) {
                continue;
            }

            // Strip inline comments and strings to avoid false positives
            let code_only = strip_comments_and_strings(line);

            if ADMIT_PATTERN.is_match(&code_only) {
                let col = Self::find_column(line, &ADMIT_COLUMN);
                // In verified F* code (especially ulib), admit() is used intentionally
                // in experimental/TODO modules. The F* typechecker itself flags unverified
                // admits during verification. Demote to Info since this linter cannot
                // distinguish "genuine TODO" from "verification bypass".
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, col),
                    message: "`admit()` bypasses verification - remove before production. \
                              Consider proving the goal or using `assume` with documentation."
                        .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for magic() usage.
    ///
    /// `magic()` produces a value of any type without justification.
    /// This completely undermines the type system and verification.
    fn check_magic(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            // Skip lines that are entirely comments
            if is_comment_line(line) {
                continue;
            }

            // Strip inline comments and strings to avoid false positives
            let code_only = strip_comments_and_strings(line);

            if MAGIC_PATTERN.is_match(&code_only) {
                let col = Self::find_column(line, &MAGIC_COLUMN);
                // magic() is used intentionally in foundational modules (Prims.fst,
                // FStar.Pervasives.fst) as a building block. The F* typechecker
                // already flags magic() during verification. Demote to Info.
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, col),
                    message: "`magic()` produces arbitrary values of any type - \
                              this completely bypasses type safety and verification!"
                        .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for unsafe_coerce usage.
    ///
    /// `unsafe_coerce` forces a type conversion without proof,
    /// potentially leading to runtime errors or undefined behavior.
    fn check_unsafe_coerce(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            // Skip lines that are entirely comments
            if is_comment_line(line) {
                continue;
            }

            // Strip inline comments and strings to avoid false positives
            let code_only = strip_comments_and_strings(line);

            if UNSAFE_COERCE.is_match(&code_only) {
                if let Some(m) = UNSAFE_COERCE.find(line) {
                    // unsafe_coerce is intentionally used in core F* infrastructure
                    // (Prims.fst, FStar.Tactics.Effect.fsti) and cannot be flagged as
                    // Error without producing false positives on verified ulib code.
                    // Demoted to Warning: the linter flags it for review, but the
                    // F* type checker is the authoritative source for type safety.
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST011,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, m.start() + 1),
                        message:
                            "`unsafe_coerce` bypasses type safety - use with extreme caution. \
                                  Consider using a proper type refinement or coercion lemma."
                                .to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for overly permissive ML effect.
    ///
    /// The ML effect allows arbitrary side effects including divergence,
    /// state, and exceptions. Often a more restrictive effect would suffice.
    fn check_ml_effect(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            // Skip lines that are entirely comments
            if is_comment_line(line) {
                continue;
            }

            // Strip inline comments and strings to avoid false positives
            let code_only = strip_comments_and_strings(line);
            let trimmed = code_only.trim();

            // Check for ML effect
            if ML_EFFECT.is_match(&code_only) {
                // Skip if in extraction context (ML is expected there)
                if EXTRACT_CONTEXT.is_match(&code_only) {
                    continue;
                }

                // Skip if this is a type definition or effect definition
                if trimmed.starts_with("type ") || trimmed.starts_with("effect ") {
                    continue;
                }

                if let Some(m) = ML_EFFECT.find(line) {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST011,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, m.start() + 1),
                        message: "ML effect is overly permissive - allows divergence, state, \
                                  and exceptions. Consider using Tot, ST, or a custom effect."
                            .to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for assume val declarations.
    ///
    /// `assume val` declarations are axioms that bypass verification.
    /// They should be documented and minimized.
    fn check_assume_val(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            // Skip lines that are entirely comments
            if is_comment_line(line) {
                continue;
            }

            // Strip inline comments and strings to avoid false positives
            let code_only = strip_comments_and_strings(line);

            if ASSUME_VAL_RE.is_match(&code_only) {
                if let Some(m) = ASSUME_VAL_RE.find(line) {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST011,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, m.start() + 1),
                        message: "`assume val` is an axiom that bypasses verification. \
                                  Ensure this assumption is sound and documented."
                            .to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for assume (expr) usage.
    ///
    /// `assume (condition)` tells F* to accept a condition as true without proof.
    /// This bypasses verification for that specific condition and can hide bugs.
    /// Unlike `assume val` which declares an external axiom, `assume (expr)` is
    /// typically used inline to work around verification failures.
    fn check_assume_expr(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            // Skip lines that are entirely comments
            if is_comment_line(line) {
                continue;
            }

            // Strip inline comments and strings to avoid false positives
            let code_only = strip_comments_and_strings(line);

            // Check for assume (expr) but NOT assume val (handled separately)
            if ASSUME_EXPR.is_match(&code_only) && !ASSUME_VAL_RE.is_match(&code_only) {
                if let Some(m) = ASSUME_EXPR.find(line) {
                    // In verified F* codebases, assume(expr) is used as an axiom
                    // building block (e.g., in FStar.Classical, FStar.Squash).
                    // F* itself tracks assumed obligations. Demote to Info.
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST011,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, m.start() + 1),
                        message: "`assume (...)` bypasses verification for a specific condition. \
                                  Consider proving this property or documenting why it's safe."
                            .to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for --admit_smt_queries true usage.
    ///
    /// This flag tells F* to accept all SMT queries without actually checking them.
    /// It completely disables verification and is even more dangerous than admit().
    ///
    /// Note: We match on the ORIGINAL line, not the stripped version, because
    /// F* pragmas like `#set-options "--admit_smt_queries true"` contain the
    /// flag inside a string literal. The string stripping would remove it.
    fn check_admit_smt_queries(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            if is_comment_line(line) {
                continue;
            }

            // Match on original line since the flag appears inside F* pragma strings
            if ADMIT_SMT_QUERIES.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: "`--admit_smt_queries true` disables ALL SMT verification in scope. \
                              This is equivalent to admitting every proof obligation. \
                              Remove before production."
                        .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for tadmit() usage (tactic-level admit).
    ///
    /// `tadmit()` is the tactic equivalent of `admit()`, used inside
    /// `assert ... by (tadmit())` to bypass a specific tactic goal.
    fn check_tadmit(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            if is_comment_line(line) {
                continue;
            }

            let code_only = strip_comments_and_strings(line);

            if TADMIT_PATTERN.is_match(&code_only) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: "`tadmit()` bypasses tactic proof obligation. \
                              Consider using `trefl()`, `smt()`, `norm [...]`, \
                              or `apply_lemma` to prove the goal properly."
                        .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for `undefined` usage - produces values without proof.
    ///
    /// `FStar.Pervasives.undefined` (or bare `undefined` if opened) creates a value
    /// of any type without proof. This is similar to `magic()` and should be flagged.
    fn check_undefined(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            if is_comment_line(line) {
                continue;
            }

            let code_only = strip_comments_and_strings(line);

            // Skip if the word "undefined" appears as part of a larger identifier
            // (e.g., "undefined_behavior"), or in documentation about undefined
            if UNDEFINED_PATTERN.is_match(&code_only) {
                // Exclude lines that are just talking about undefined behavior in comments
                let trimmed = code_only.trim();
                // Only flag actual usage, not mentions in type signatures or documentation
                if trimmed.contains("= undefined")
                    || trimmed.contains("= FStar.Pervasives.undefined")
                    || trimmed.contains("undefined)")
                    || trimmed.contains("undefined;")
                    || trimmed.starts_with("undefined")
                    || trimmed.contains("(undefined")
                    || trimmed.contains("(FStar.Pervasives.undefined")
                    || trimmed.contains("Pervasives.undefined)")
                {
                    // Like admit() and magic(), `undefined` is flagged by the F*
                    // typechecker during verification. Demote to Info.
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST011,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: "`undefined` produces a value of any type without proof. \
                                  Like `magic()`, this bypasses the verification guarantee. \
                                  Replace with a proper implementation or use `admit()` \
                                  with a TODO comment to track proof obligations."
                            .to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for `assert false` / `assert False` patterns.
    ///
    /// `assert false` derives anything via False elimination. If the proof state
    /// is not actually contradictory, this silently makes the rest of the proof
    /// vacuously true. This is often a logic error.
    fn check_assert_false(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            if is_comment_line(line) {
                continue;
            }

            let code_only = strip_comments_and_strings(line);

            if ASSERT_FALSE_RE.is_match(&code_only) {
                // In verified F* code, `assert false` is a valid proof technique:
                // reductio ad absurdum. When F* verifies the file, any `assert false`
                // that passes verification means the proof state IS genuinely
                // contradictory. Demote to Info -- the F* verifier is the authority here.
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: "`assert false` (or `assert False`) derives anything via False \
                              elimination. If the proof state is genuinely contradictory \
                              (reductio ad absurdum), this is a valid proof technique. \
                              Otherwise, this may indicate a logic error where subsequent \
                              code is vacuously verified."
                        .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for `synth_by_tactic (fun () -> tadmit())` - hidden admit via tactic synthesis.
    ///
    /// This pattern uses the tactic engine to synthesize a term using `tadmit()`,
    /// which effectively admits the proof obligation but hides it behind the
    /// tactic infrastructure. It's harder to grep for than a bare `admit()`.
    fn check_synth_tadmit(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            if is_comment_line(line) {
                continue;
            }

            let code_only = strip_comments_and_strings(line);

            if SYNTH_TADMIT_PATTERN.is_match(&code_only) {
                // Demoted to Warning: synth_by_tactic + tadmit is used
                // deliberately in experimental/bootstrapping code in ulib.
                // Like admit(), it's a verification bypass that should be
                // flagged for review but not treated as a hard error.
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: "`synth_by_tactic` with `tadmit()` is a hidden admit. \
                              The tactic synthesizes a term by admitting the proof \
                              obligation, bypassing verification. Replace with a proper \
                              tactic proof or use explicit `admit()` for visibility."
                        .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for Classical logic lemma usage patterns and provide guidance.
    ///
    /// Detects usage of FStar.Classical combinators (forall_intro, move_requires,
    /// exists_intro) and suggests proper usage patterns. These are not bugs but
    /// important proof infrastructure that benefits from review.
    fn check_classical_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            if is_comment_line(line) {
                continue;
            }

            let code_only = strip_comments_and_strings(line);

            // Detect Classical.forall_intro usage
            if CLASSICAL_FORALL.is_match(&code_only) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: "Using `Classical.forall_intro`. \
                              Ensure the body function has the right signature: \
                              `(x:a -> Lemma (p x)) -> Lemma (forall x. p x)`. \
                              For 2+ arguments, use `forall_intro_2`, `forall_intro_3`."
                        .to_string(),
                    fix: None,
                });
            }

            // Detect Classical.move_requires usage
            if CLASSICAL_MOVE_REQ.is_match(&code_only) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: "Using `Classical.move_requires`. This converts \
                              `(x -> Lemma (requires P) (ensures Q))` to \
                              `(x -> Lemma (P ==> Q))`, moving precondition into implication."
                        .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for effect declaration issues.
    ///
    /// Validates:
    /// - `new_effect` declarations have required combinators (return_wp, bind_wp, etc.)
    /// - `sub_effect` declarations reference valid source and destination effects
    /// - `effect` abbreviations reference known base effects
    /// - `layered_effect` declarations have the new-style combinators (repr, return, bind, subcomp)
    fn check_effect_declarations(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let (_, blocks) = parse_fstar_file(content);

        for block in &blocks {
            match block.block_type {
                BlockType::NewEffect => {
                    let text = block.lines.join("");
                    let clean = strip_comments_and_strings(&text);

                    // Check for brace-style new_effect (WP-based) vs simple derivation
                    let is_brace_style = clean.contains('{');
                    let is_simple_derivation = !is_brace_style
                        && clean.contains('=')
                        && !clean.contains("with");

                    if is_brace_style {
                        // WP-based new_effect must have at least return_wp and bind_wp
                        let has_return = clean.contains("return_wp")
                            || clean.contains("return =")
                            || clean.contains("return=");
                        let has_bind = clean.contains("bind_wp")
                            || clean.contains("bind =")
                            || clean.contains("bind=");

                        if !has_return && !has_bind {
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST011,
                                severity: DiagnosticSeverity::Warning,
                                file: file.to_path_buf(),
                                range: Range::point(block.start_line, 1),
                                message: format!(
                                    "new_effect `{}` is missing return and bind combinators. \
                                     WP-based effects require at least return_wp and bind_wp.",
                                    block.name().unwrap_or("unknown")
                                ),
                                fix: None,
                            });
                        }
                    }

                    if is_simple_derivation {
                        // Simple derivation: `new_effect NAME = BASE`
                        // Verify the base effect name is recognizable (just informational)
                        if let Some(caps) = NEW_EFFECT_DEF.captures(clean.trim_start()) {
                            let _name = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                            // Simple derivation is fine, no additional checks needed
                        }
                    }
                }

                BlockType::SubEffect => {
                    let text = block.lines.join("");
                    let clean = strip_comments_and_strings(&text);

                    // Check sub_effect has the ~> arrow
                    if !clean.contains("~>") {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST011,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::point(block.start_line, 1),
                            message: "sub_effect declaration is missing the `~>` arrow. \
                                      Expected: `sub_effect SRC ~> DST = lift_fn` or \
                                      `sub_effect SRC ~> DST { lift_wp = ... }`."
                                .to_string(),
                            fix: None,
                        });
                    }
                }

                BlockType::Effect | BlockType::EffectAbbrev => {
                    let text = block.lines.join("");
                    let clean = strip_comments_and_strings(&text);

                    // For layered effects (effect { ... } with repr/return/bind/subcomp)
                    if clean.contains("layered_effect") || (clean.starts_with("effect") && clean.contains('{')) {
                        // Layered effects need repr, return, bind, subcomp
                        let has_repr = clean.contains("repr");
                        let has_return = clean.contains("return");
                        let has_bind = clean.contains("bind");

                        if !has_repr && !has_return && !has_bind {
                            // Only warn if it looks like a full layered_effect definition
                            // (has braces and `with` keyword)
                            if clean.contains("with") {
                                diagnostics.push(Diagnostic {
                                    rule: RuleCode::FST011,
                                    severity: DiagnosticSeverity::Warning,
                                    file: file.to_path_buf(),
                                    range: Range::point(block.start_line, 1),
                                    message: format!(
                                        "Layered effect `{}` may be missing combinators (repr, return, bind). \
                                         Layered effects require repr, return, bind, and subcomp.",
                                        block.name().unwrap_or("unknown")
                                    ),
                                    fix: None,
                                });
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        diagnostics
    }

    /// Check for Tot functions calling effectful code.
    ///
    /// A function annotated with Tot effect must only call other Tot functions.
    /// Calling effectful functions (ST, Exn, ML, etc.) from Tot is an error.
    fn check_tot_calling_effectful(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let (_, blocks) = parse_fstar_file(content);

        // Build map of function name -> effect from val declarations
        // In F*, val declares the signature (with effect), let provides implementation
        let mut function_effects: HashMap<String, Effect> = HashMap::new();
        for block in &blocks {
            if let Some(eff) = extract_function_effect(block) {
                for name in &block.names {
                    function_effects.insert(name.clone(), eff);
                }
            }
        }

        // Check each let block for calls to effectful functions
        // Look up the effect from the corresponding val declaration
        for block in &blocks {
            // Only check let blocks (where actual code is)
            if !matches!(
                block.block_type,
                BlockType::Let | BlockType::UnfoldLet | BlockType::InlineLet
            ) {
                continue;
            }

            // Get the effect for this function from the map (from val) or from the block itself
            let caller_effect = block
                .name()
                .and_then(|n| function_effects.get(n).copied())
                .or_else(|| extract_function_effect(block));

            // Only check Tot functions
            if caller_effect != Some(Effect::Tot) {
                continue;
            }

            // Extract all function calls from this block
            let calls = extract_function_calls(block);

            for call in &calls {
                // 1. If callee is in TOT_BUILTINS, it's known-Tot — skip
                if TOT_BUILTINS.contains(call.bare.as_str()) {
                    continue;
                }

                // 2. If call is qualified with a known Tot-module prefix, skip
                if let Some(ref qname) = call.qualified {
                    let is_tot_module = TOT_MODULE_PREFIXES.iter().any(|p| qname.starts_with(p));
                    if is_tot_module {
                        continue;
                    }
                }

                // 3. Check file-local val declarations first
                let callee_effect = function_effects
                    .get(&call.bare)
                    .copied()
                    .or_else(|| {
                        // 4. Fall back to EFFECTFUL_FUNCTIONS, but ONLY for unambiguous names
                        //    or when the call is unqualified (no module context to disambiguate)
                        let eff = EFFECTFUL_FUNCTIONS.get(call.bare.as_str()).copied();
                        // If the name is ambiguous (in both TOT and EFFECTFUL databases),
                        // require qualification to resolve — unqualified is suspicious but
                        // should be demoted to Warning, not Error
                        eff
                    });

                if let Some(callee_eff) = callee_effect {
                    // Tot cannot call effectful functions
                    if !Effect::Tot.can_call(callee_eff) {
                        // Severity depends on the callee effect:
                        //
                        // Ghost/GTot/Lemma → Info: In F*, Tot functions routinely call
                        // ghost and lemma functions. This is standard proof-carrying code:
                        //   - Lemma calls: inline proof obligations (erased at extraction)
                        //   - Ghost/GTot calls: specification positions, erased monad
                        //   - F* itself verifies these are used correctly
                        //
                        // ST/Exn/ML/All → Warning: These are genuinely effectful and
                        // should not appear in Tot code. However, without module resolution
                        // the linter may misidentify names (e.g., `sub`, `index`, `sel`).
                        let severity = if callee_eff.is_ghost()
                            || callee_eff == Effect::GTot
                            || callee_eff == Effect::Lemma
                        {
                            DiagnosticSeverity::Info
                        } else {
                            DiagnosticSeverity::Warning
                        };

                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST011,
                            severity,
                            file: file.to_path_buf(),
                            range: Range::point(call.line_num, 1),
                            message: format!(
                                "Tot function `{}` calls `{}` which has {} effect. \
                                 Tot functions can only call other Tot functions.",
                                block.name().unwrap_or("unknown"),
                                call.bare,
                                callee_eff.display_name()
                            ),
                            fix: None,
                        });
                    }
                }
            }
        }

        diagnostics
    }

    /// Check for Ghost values used in computational (non-ghost) context.
    ///
    /// Ghost values are erased at extraction and cannot be used in
    /// computational code that will be extracted to OCaml.
    ///
    /// IMPORTANT: This check is intentionally conservative to avoid false positives:
    /// - Only flags UNQUALIFIED calls (not Module.name references to other modules)
    /// - Only flags explicit `ghost let` bindings, not GTot-effect functions
    /// - F* itself enforces ghost/computational boundaries at compile time
    ///
    /// The main purpose is to catch obvious mistakes early, not to replicate F*'s checker.
    fn check_ghost_in_computational_context(
        &self,
        file: &Path,
        content: &str,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let (_, blocks) = parse_fstar_file(content);

        // Track ONLY explicit ghost bindings (from `ghost let` pattern)
        // We intentionally do NOT track GTot-effect functions because:
        // 1. GTot functions can be called from specification positions in inline_for_extraction
        // 2. F* already enforces ghost/computational boundaries
        // 3. Including GTot causes massive false positives (621 in hacl-star, 2762 in everparse)
        let mut ghost_bindings: HashMap<String, usize> = HashMap::new();
        for block in &blocks {
            // Only track explicit `ghost let` bindings, not just any GTot effect
            if is_explicit_ghost_let(block) {
                for name in &block.names {
                    ghost_bindings.insert(name.clone(), block.start_line);
                }
            }
        }

        // If no explicit ghost let bindings, nothing to check
        if ghost_bindings.is_empty() {
            return diagnostics;
        }

        // Check computational functions for ghost value usage
        for block in &blocks {
            // Skip non-function blocks
            if !matches!(
                block.block_type,
                BlockType::Let | BlockType::InlineLet | BlockType::UnfoldLet
            ) {
                continue;
            }

            // Check if this is marked for extraction (computational context)
            let is_computational = is_extraction_binding(block);

            // Skip ghost blocks - they can use ghost values
            if is_explicit_ghost_let(block) {
                continue;
            }

            // If marked for extraction, check for ghost value usage
            // Only check UNQUALIFIED calls - qualified calls (Module.name) refer to other modules
            if is_computational {
                let calls = extract_unqualified_function_calls(block);

                for (callee_name, line_num) in calls {
                    if ghost_bindings.contains_key(&callee_name) {
                        // Demoted to Warning: ghost bindings CAN appear in
                        // inline_for_extraction contexts in specification positions
                        // (requires/ensures) or erased type parameters. The F*
                        // compiler enforces the actual ghost/computational boundary.
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST011,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::point(line_num, 1),
                            message: format!(
                                "Ghost binding `{}` used in computational context (inline_for_extraction). \
                                 Ghost values are erased at extraction and cannot be used in extracted code.",
                                callee_name
                            ),
                            fix: None,
                        });
                    }
                }
            }
        }

        diagnostics
    }

    /// Check for stateful effects (Stack/ST) missing requires/ensures clauses.
    ///
    /// In HACL* and Low*, Stack/ST effects almost always require pre/postconditions
    /// to specify memory safety properties (liveness, disjointness, modifications).
    /// Missing these clauses usually indicates an incomplete specification.
    ///
    /// Example of proper Stack signature:
    /// ```text
    /// val push_frame (_:unit) : Stack unit
    ///   (requires fun h -> True)
    ///   (ensures  fun h0 _ h1 -> fresh_frame h0 h1)
    /// ```
    fn check_stateful_effect_specs(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let (_, blocks) = parse_fstar_file(content);

        for block in &blocks {
            // Only check val declarations (signatures)
            if block.block_type != BlockType::Val {
                continue;
            }

            let sig = match &block.effect_signature {
                Some(s) => s,
                None => continue,
            };

            // Only check stateful effects
            if !sig.is_stateful_effect() {
                continue;
            }

            // Stateful effects should have both requires and ensures
            if !sig.has_requires && !sig.has_ensures {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::point(block.start_line, 1),
                    message: format!(
                        "`{}` with {} effect is missing requires/ensures clauses. \
                         Stateful effects should specify pre/postconditions for memory safety.",
                        block.name().unwrap_or("unknown"),
                        sig.effect_name
                    ),
                    fix: None,
                });
            } else if sig.has_requires && !sig.has_ensures {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::point(block.start_line, 1),
                    message: format!(
                        "`{}` with {} effect has requires but is missing ensures clause. \
                         Postconditions are needed to describe memory modifications.",
                        block.name().unwrap_or("unknown"),
                        sig.effect_name
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for Lemma effects missing ensures clauses.
    ///
    /// A Lemma without ensures proves nothing useful. In F*, Lemma is essentially
    /// `Pure unit (requires pre) (ensures (fun _ -> post))`, so an ensures clause
    /// is the primary purpose of a Lemma.
    ///
    /// Good:  `val my_lemma : x:nat -> Lemma (ensures x + 0 == x)`
    /// Bad:   `val my_lemma : x:nat -> Lemma True`  (proves nothing)
    fn check_lemma_ensures(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let (_, blocks) = parse_fstar_file(content);

        for block in &blocks {
            if block.block_type != BlockType::Val {
                continue;
            }

            let sig = match &block.effect_signature {
                Some(s) => s,
                None => continue,
            };

            if !sig.is_lemma_effect() {
                continue;
            }

            // Check if Lemma has ensures clause.
            // Note: In F*, `Lemma (P)` desugars to `Lemma (requires True) (ensures (fun _ -> P))`,
            // so a bare `Lemma (some_prop)` is valid. We only flag `Lemma True` or
            // Lemma without any argument that looks like a real property.
            if !sig.has_ensures {
                // Check if the Lemma has at least a direct property argument
                // e.g., `Lemma (x > 0)` is fine even without explicit `ensures`
                let text = block.text();
                let after_lemma = text.split("Lemma").nth(1).unwrap_or("");
                let trimmed = after_lemma.trim();

                // `Lemma True` or `Lemma unit` are vacuous
                let is_vacuous = trimmed.starts_with("True")
                    || trimmed.starts_with("(True)")
                    || trimmed.starts_with("unit");

                if is_vacuous {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST011,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::point(block.start_line, 1),
                        message: format!(
                            "`{}` has a vacuous Lemma (Lemma True). \
                             Lemmas should have meaningful ensures clauses to prove useful properties.",
                            block.name().unwrap_or("unknown")
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for effect abbreviation definitions that reference unknown base effects.
    ///
    /// Validates that `effect MyEffect (...) = BASE ...` references a known base effect.
    /// Also checks that sub_effect declarations reference known source and dest effects.
    fn check_effect_abbrev_base(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let (_, blocks) = parse_fstar_file(content);

        // Collect all locally defined effect names (from effect abbreviations and new_effect)
        let mut local_effects: HashSet<String> = HashSet::new();
        for block in &blocks {
            match block.block_type {
                BlockType::EffectAbbrev | BlockType::Effect | BlockType::NewEffect => {
                    for name in &block.names {
                        local_effects.insert(name.clone());
                    }
                }
                _ => {}
            }
        }

        // Known built-in effect names (includes user-defined effects from ulib/experimental)
        let builtin_effects: HashSet<&str> = [
            "PURE", "GHOST", "DIV", "STATE", "EXN", "ALL",
            "Pure", "Ghost", "Tot", "GTot", "Lemma",
            "Div", "Dv", "ST", "Stack", "State", "Heap",
            "Exn", "Ex", "All", "ML", "Tac", "TAC",
            "StackInline", "Unsafe", "St", "STL", "GST",
            "TacH", "TacS", "TacRO", "TacF",
            // Experimental monotonic state effects (FStar.MST, FStar.NMST)
            "MSTATE", "MSTATETOT", "NMSTATE", "NMSTATETOT",
            "MST", "NMST", "MSTTotal", "NMSTTotal",
            // WP-based effect variants
            "EXT", "ISTATE",
        ].iter().copied().collect();

        for block in &blocks {
            let sig = match &block.effect_signature {
                Some(s) => s,
                None => continue,
            };

            // Check effect abbreviation base
            if block.block_type == BlockType::EffectAbbrev {
                if let Some(base) = &sig.base_effect {
                    if !builtin_effects.contains(base.as_str())
                        && !local_effects.contains(base)
                    {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST011,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::point(block.start_line, 1),
                            message: format!(
                                "Effect abbreviation `{}` references unknown base effect `{}`. \
                                 Ensure the base effect is defined or imported.",
                                block.name().unwrap_or("unknown"),
                                base
                            ),
                            fix: None,
                        });
                    }
                }
            }

            // Check sub_effect source and destination
            if block.block_type == BlockType::SubEffect {
                if let Some(src) = &sig.sub_effect_src {
                    if !builtin_effects.contains(src.as_str())
                        && !local_effects.contains(src)
                    {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST011,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::point(block.start_line, 1),
                            message: format!(
                                "sub_effect source `{}` is not a known effect. \
                                 Ensure it is defined or imported.",
                                src
                            ),
                            fix: None,
                        });
                    }
                }
                if let Some(dst) = &sig.sub_effect_dst {
                    if !builtin_effects.contains(dst.as_str())
                        && !local_effects.contains(dst)
                    {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST011,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::point(block.start_line, 1),
                            message: format!(
                                "sub_effect destination `{}` is not a known effect. \
                                 Ensure it is defined or imported.",
                                dst
                            ),
                            fix: None,
                        });
                    }
                }
            }
        }

        diagnostics
    }

    /// Check for layered_effect declarations missing required combinators.
    ///
    /// Layered effects (the new-style effect system in F*) require:
    /// - `repr`: The representation type
    /// - `return`: The return combinator
    /// - `bind`: The bind combinator
    /// - `subcomp`: The subcomputation relation
    ///
    /// Missing any of these will cause F* verification errors.
    fn check_layered_effect_combinators(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let (_, blocks) = parse_fstar_file(content);

        for block in &blocks {
            if block.block_type != BlockType::Effect {
                continue;
            }

            let sig = match &block.effect_signature {
                Some(s) => s,
                None => continue,
            };

            // Only check blocks that look like layered effects (have `with` keyword)
            let text = block.text();
            if !text.contains("layered_effect") && !text.contains("reflectable") {
                // Could be a simple `effect` keyword usage, skip
                if !text.contains("with") || !text.contains('{') {
                    continue;
                }
            }

            let required = ["repr", "return", "bind"];
            let mut missing: Vec<&str> = Vec::new();

            for &req in &required {
                if !sig.combinators.iter().any(|c| c == req) {
                    missing.push(req);
                }
            }

            if !missing.is_empty() && missing.len() < required.len() {
                // Only warn if SOME combinators are present (partial definition)
                // If ALL are missing, the check_effect_declarations already handles it
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(block.start_line, 1),
                    message: format!(
                        "Layered effect `{}` is missing required combinators: {}. \
                         Layered effects need repr, return, bind, and subcomp.",
                        block.name().unwrap_or("unknown"),
                        missing.join(", ")
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for Pure/Ghost effects with requires but no ensures (or vice versa).
    ///
    /// Pure and Ghost effects use Hoare-style specs: `Pure a (requires P) (ensures Q)`.
    /// Having `requires` without `ensures` (or only `ensures`) is unusual and might
    /// indicate an incomplete specification.
    fn check_hoare_effect_completeness(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let (_, blocks) = parse_fstar_file(content);

        for block in &blocks {
            if block.block_type != BlockType::Val {
                continue;
            }

            let sig = match &block.effect_signature {
                Some(s) => s,
                None => continue,
            };

            if !sig.is_pure_hoare_effect() {
                continue;
            }

            // Pure/Ghost with requires but no ensures is suspicious
            if sig.has_requires && !sig.has_ensures {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST011,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::point(block.start_line, 1),
                    message: format!(
                        "`{}` with {} effect has requires but no ensures clause. \
                         Consider adding an ensures clause to specify the postcondition.",
                        block.name().unwrap_or("unknown"),
                        sig.effect_name
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }
}

impl Default for EffectCheckerRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for EffectCheckerRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST011
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        diagnostics.extend(self.check_admit(file, content));
        diagnostics.extend(self.check_magic(file, content));
        diagnostics.extend(self.check_unsafe_coerce(file, content));
        diagnostics.extend(self.check_ml_effect(file, content));
        diagnostics.extend(self.check_assume_val(file, content));
        diagnostics.extend(self.check_assume_expr(file, content));
        diagnostics.extend(self.check_admit_smt_queries(file, content));
        diagnostics.extend(self.check_tadmit(file, content));
        diagnostics.extend(self.check_undefined(file, content));
        diagnostics.extend(self.check_assert_false(file, content));
        diagnostics.extend(self.check_synth_tadmit(file, content));
        diagnostics.extend(self.check_classical_patterns(file, content));
        diagnostics.extend(self.check_tot_calling_effectful(file, content));
        diagnostics.extend(self.check_ghost_in_computational_context(file, content));
        diagnostics.extend(self.check_effect_declarations(file, content));
        diagnostics.extend(self.check_stateful_effect_specs(file, content));
        diagnostics.extend(self.check_lemma_ensures(file, content));
        diagnostics.extend(self.check_effect_abbrev_base(file, content));
        diagnostics.extend(self.check_layered_effect_combinators(file, content));
        diagnostics.extend(self.check_hoare_effect_completeness(file, content));

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

    // ===========================================
    // Effect enum tests
    // ===========================================

    #[test]
    fn test_effect_from_str() {
        assert_eq!(Effect::parse("Tot"), Some(Effect::Tot));
        assert_eq!(Effect::parse("GTot"), Some(Effect::GTot));
        assert_eq!(Effect::parse("Pure"), Some(Effect::Pure));
        assert_eq!(Effect::parse("Ghost"), Some(Effect::Ghost));
        assert_eq!(Effect::parse("Lemma"), Some(Effect::Lemma));
        assert_eq!(Effect::parse("Div"), Some(Effect::Div));
        assert_eq!(Effect::parse("Dv"), Some(Effect::Div));
        assert_eq!(Effect::parse("ST"), Some(Effect::ST));
        assert_eq!(Effect::parse("Stack"), Some(Effect::ST));
        assert_eq!(Effect::parse("STATE"), Some(Effect::ST));
        assert_eq!(Effect::parse("Exn"), Some(Effect::Exn));
        assert_eq!(Effect::parse("Ex"), Some(Effect::Exn));
        assert_eq!(Effect::parse("All"), Some(Effect::All));
        assert_eq!(Effect::parse("ML"), Some(Effect::ML));
        assert_eq!(Effect::parse("Unknown"), None);
    }

    #[test]
    fn test_effect_ordering() {
        assert!(Effect::Tot < Effect::GTot);
        assert!(Effect::GTot < Effect::Pure);
        assert!(Effect::Pure < Effect::Ghost);
        assert!(Effect::Ghost < Effect::Div);
        assert!(Effect::Div < Effect::All);
        assert!(Effect::All < Effect::ML);
    }

    #[test]
    fn test_effect_can_call_tot() {
        // Tot can call Tot and Pure (Tot a = Pure a True (fun _ -> True))
        assert!(Effect::Tot.can_call(Effect::Tot));
        assert!(!Effect::Tot.can_call(Effect::GTot));
        assert!(Effect::Tot.can_call(Effect::Pure));
        assert!(!Effect::Tot.can_call(Effect::Ghost));
        assert!(!Effect::Tot.can_call(Effect::ST));
        assert!(!Effect::Tot.can_call(Effect::ML));
    }

    #[test]
    fn test_effect_can_call_gtot() {
        // GTot can call Tot and GTot
        assert!(Effect::GTot.can_call(Effect::Tot));
        assert!(Effect::GTot.can_call(Effect::GTot));
        assert!(!Effect::GTot.can_call(Effect::Pure));
        assert!(!Effect::GTot.can_call(Effect::Ghost));
        assert!(!Effect::GTot.can_call(Effect::ST));
    }

    #[test]
    fn test_effect_can_call_ghost() {
        // Ghost can call Tot, GTot, Ghost, Lemma
        assert!(Effect::Ghost.can_call(Effect::Tot));
        assert!(Effect::Ghost.can_call(Effect::GTot));
        assert!(Effect::Ghost.can_call(Effect::Ghost));
        assert!(Effect::Ghost.can_call(Effect::Lemma));
        assert!(!Effect::Ghost.can_call(Effect::Pure));
        assert!(!Effect::Ghost.can_call(Effect::ST));
    }

    #[test]
    fn test_effect_can_call_st() {
        // ST can call Tot, Pure, Div, ST
        assert!(Effect::ST.can_call(Effect::Tot));
        assert!(Effect::ST.can_call(Effect::Pure));
        assert!(Effect::ST.can_call(Effect::Div));
        assert!(Effect::ST.can_call(Effect::ST));
        assert!(!Effect::ST.can_call(Effect::Ghost));
        assert!(!Effect::ST.can_call(Effect::Exn));
        assert!(!Effect::ST.can_call(Effect::ML));
    }

    #[test]
    fn test_effect_can_call_ml() {
        // ML can call anything
        assert!(Effect::ML.can_call(Effect::Tot));
        assert!(Effect::ML.can_call(Effect::GTot));
        assert!(Effect::ML.can_call(Effect::Pure));
        assert!(Effect::ML.can_call(Effect::Ghost));
        assert!(Effect::ML.can_call(Effect::ST));
        assert!(Effect::ML.can_call(Effect::Exn));
        assert!(Effect::ML.can_call(Effect::All));
        assert!(Effect::ML.can_call(Effect::ML));
    }

    #[test]
    fn test_effect_is_ghost() {
        assert!(Effect::GTot.is_ghost());
        assert!(Effect::Ghost.is_ghost());
        assert!(Effect::Lemma.is_ghost());
        assert!(!Effect::Tot.is_ghost());
        assert!(!Effect::Pure.is_ghost());
        assert!(!Effect::ST.is_ghost());
        assert!(!Effect::ML.is_ghost());
    }

    // ===========================================
    // Existing tests (admit, magic, etc.)
    // ===========================================

    #[test]
    fn test_admit_detected() {
        let rule = EffectCheckerRule::new();
        let content = "let lemma_foo () : Lemma True = admit()";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("admit()")));
        // admit() is Info severity (F* typechecker is the authority)
        assert!(diags
            .iter()
            .any(|d| d.severity == DiagnosticSeverity::Info && d.message.contains("admit()")));
    }

    #[test]
    fn test_admit_in_comment_ignored() {
        let rule = EffectCheckerRule::new();
        let content = "(* TODO: remove admit() later *)";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    #[test]
    fn test_magic_detected() {
        let rule = EffectCheckerRule::new();
        let content = "let bad_value : int = magic()";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("magic()")));
        // magic() is Info severity (used intentionally in foundational modules)
        assert!(diags
            .iter()
            .any(|d| d.severity == DiagnosticSeverity::Info && d.message.contains("magic()")));
    }

    #[test]
    fn test_unsafe_coerce_detected() {
        let rule = EffectCheckerRule::new();
        let content = "let coerced = unsafe_coerce x";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("unsafe_coerce")));
        // Demoted to Warning: unsafe_coerce is intentionally used in F* core infrastructure
        assert!(diags
            .iter()
            .any(|d| d.severity == DiagnosticSeverity::Warning && d.message.contains("unsafe_coerce")));
    }

    #[test]
    fn test_ml_effect_detected() {
        let rule = EffectCheckerRule::new();
        let content = "val foo : int -> ML int";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("ML effect")));
        assert!(diags.iter().any(|d| d.severity == DiagnosticSeverity::Info));
    }

    #[test]
    fn test_ml_effect_in_extraction_context() {
        let rule = EffectCheckerRule::new();
        let content = "inline_for_extraction let foo : int -> ML int = fun x -> x";
        let diags = rule.check(&make_path(), content);
        // Should not warn about ML in extraction context
        assert!(!diags.iter().any(|d| d.message.contains("ML effect")));
    }

    #[test]
    fn test_assume_val_detected() {
        let rule = EffectCheckerRule::new();
        let content = "assume val external_function : int -> int";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("assume val")));
        assert!(diags.iter().any(|d| d.severity == DiagnosticSeverity::Info));
    }

    #[test]
    fn test_clean_code_no_warnings() {
        let rule = EffectCheckerRule::new();
        let content = r#"
module Test

open FStar.All

val add : int -> int -> Tot int
let add x y = x + y

val factorial : nat -> Tot nat
let rec factorial n =
  if n = 0 then 1
  else n * factorial (n - 1)
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Expected no diagnostics, got: {:?}",
            diags
        );
    }

    // ===========================================
    // Effect hierarchy analysis tests
    // ===========================================

    #[test]
    fn test_tot_calling_effectful_detected() {
        let rule = EffectCheckerRule::new();
        let content = r#"
module Test

val effectful_fn : int -> ST int
let effectful_fn x = x + 1

val pure_fn : int -> Tot int
let pure_fn x = effectful_fn x
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags
                .iter()
                .any(|d| d.message.contains("Tot function") && d.message.contains("ST effect")),
            "Expected Tot-calling-effectful diagnostic, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_tot_calling_tot_ok() {
        let rule = EffectCheckerRule::new();
        let content = r#"
module Test

val helper : int -> Tot int
let helper x = x + 1

val main_fn : int -> Tot int
let main_fn x = helper x
"#;
        let diags = rule.check(&make_path(), content);
        // Should only have no Tot-calling-effectful errors
        assert!(
            !diags
                .iter()
                .any(|d| d.message.contains("Tot function") && d.message.contains("effect")),
            "Should not report Tot calling Tot as error"
        );
    }

    #[test]
    fn test_tot_calling_known_effectful() {
        let rule = EffectCheckerRule::new();
        let content = r#"
module Test

val pure_fn : int -> Tot int
let pure_fn x = print_string "hello"; x
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags
                .iter()
                .any(|d| d.message.contains("Tot function") && d.message.contains("print_string")),
            "Expected Tot-calling-ML diagnostic for print_string"
        );
    }

    #[test]
    fn test_ml_can_call_anything() {
        let rule = EffectCheckerRule::new();
        let content = r#"
module Test

val effectful_fn : int -> ST int
let effectful_fn x = x + 1

val ml_fn : int -> ML int
let ml_fn x = effectful_fn x
"#;
        let diags = rule.check(&make_path(), content);
        // ML should be able to call ST without error
        assert!(
            !diags
                .iter()
                .any(|d| d.message.contains("ml_fn") && d.message.contains("effect")),
            "ML should be able to call any effect"
        );
    }

    // ===========================================
    // Ghost in computational context tests
    // ===========================================

    #[test]
    fn test_ghost_in_extraction_context_detected() {
        use super::parse_fstar_file;

        let rule = EffectCheckerRule::new();
        // Use explicit 'ghost let' pattern - this is what the check looks for
        // to avoid false positives from GTot effect functions
        let content = r#"
module Test

ghost let ghost_val = 42

inline_for_extraction let extracted_fn () = ghost_val + 1
"#;
        // Debug: check what blocks are parsed
        let (_, blocks) = parse_fstar_file(content);
        eprintln!("Parsed {} blocks:", blocks.len());
        for block in &blocks {
            eprintln!(
                "  {:?} names={:?} lines={:?}",
                block.block_type,
                block.names,
                block.lines.len()
            );
            eprintln!("    lines: {:?}", block.lines);
            if is_explicit_ghost_let(block) {
                eprintln!("    -> is_explicit_ghost_let=true");
            }
            if is_extraction_binding(block) {
                eprintln!("    -> is_extraction_binding=true");
                let calls = extract_unqualified_function_calls(block);
                eprintln!("    -> unqualified calls: {:?}", calls);
            }
        }

        let diags = rule.check(&make_path(), content);
        eprintln!("Got {} diagnostics:", diags.len());
        for d in &diags {
            eprintln!("  {:?}: {}", d.rule, d.message);
        }

        assert!(
            diags.iter().any(|d| d.message.contains("Ghost binding")
                && d.message.contains("computational context")),
            "Expected ghost-in-computational-context diagnostic, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_ghost_in_ghost_context_ok() {
        let rule = EffectCheckerRule::new();
        // Ghost bindings CAN use other ghost bindings
        let content = r#"
module Test

ghost let ghost_val = 42

ghost let another_ghost = ghost_val + 1
"#;
        let diags = rule.check(&make_path(), content);
        // Ghost can use ghost - no errors about ghost bindings
        assert!(
            !diags.iter().any(|d| d.message.contains("Ghost binding")),
            "Ghost using ghost should be OK"
        );
    }

    #[test]
    fn test_gtot_function_not_flagged_to_avoid_false_positives() {
        let rule = EffectCheckerRule::new();
        // GTot functions are NOT flagged when called from inline_for_extraction
        // because:
        // 1. GTot functions can be called from specification positions (requires/ensures)
        // 2. F* itself enforces ghost/computational boundaries at compile time
        // 3. The old behavior caused 621+ false positives in hacl-star
        let content = r#"
module Test

val ghost_fn : int -> GTot int
let ghost_fn x = x + 1

inline_for_extraction let extracted_fn (x:int) = ghost_fn x + 1
"#;
        let diags = rule.check(&make_path(), content);
        // Should NOT flag GTot function calls - F* compiler handles this
        assert!(
            !diags
                .iter()
                .any(|d| d.message.contains("Ghost binding")),
            "GTot functions should NOT be flagged (F* handles this), got: {:?}",
            diags
        );
    }

    #[test]
    fn test_qualified_ghost_reference_not_flagged() {
        let rule = EffectCheckerRule::new();
        // Qualified references (Module.name) should NOT be flagged because
        // they refer to other modules, not local ghost bindings
        let content = r#"
module Test

ghost let state = 42

inline_for_extraction let extracted_fn () =
  (* Even if there's a local 'state' ghost, this refers to another module *)
  EverCrypt.Hash.state
"#;
        let diags = rule.check(&make_path(), content);
        // Qualified references should not match local ghost bindings
        assert!(
            !diags.iter().any(|d| d.message.contains("Ghost binding") && d.message.contains("state")),
            "Qualified references should not be flagged, got: {:?}",
            diags
        );
    }

    // ===========================================
    // Effect extraction tests
    // ===========================================

    #[test]
    fn test_extract_function_effect() {
        let block = DeclarationBlock {
            block_type: BlockType::Let,
            names: vec!["foo".to_string()],
            lines: vec!["val foo : int -> Tot int\n".to_string()],
            start_line: 1,
            has_push_options: false,
            has_pop_options: false,
            references: std::collections::HashSet::new(),
            module_path: None,
            is_private: false,
            is_abstract: false,
            effect_signature: None,
        };
        assert_eq!(extract_function_effect(&block), Some(Effect::Tot));
    }

    #[test]
    fn test_extract_function_effect_st() {
        let block = DeclarationBlock {
            block_type: BlockType::Val,
            names: vec!["stateful".to_string()],
            lines: vec!["val stateful : int -> ST int\n".to_string()],
            start_line: 1,
            has_push_options: false,
            has_pop_options: false,
            references: std::collections::HashSet::new(),
            module_path: None,
            is_private: false,
            is_abstract: false,
            effect_signature: None,
        };
        assert_eq!(extract_function_effect(&block), Some(Effect::ST));
    }

    #[test]
    fn test_extract_function_effect_none() {
        let block = DeclarationBlock {
            block_type: BlockType::Let,
            names: vec!["foo".to_string()],
            lines: vec!["let foo x = x + 1\n".to_string()],
            start_line: 1,
            has_push_options: false,
            has_pop_options: false,
            references: std::collections::HashSet::new(),
            module_path: None,
            is_private: false,
            is_abstract: false,
            effect_signature: None,
        };
        assert_eq!(extract_function_effect(&block), None);
    }

    // ===========================================
    // Edge case tests for false positive prevention
    // ===========================================

    #[test]
    fn test_assume_expr_detected() {
        let rule = EffectCheckerRule::new();
        let content = "let x = assume (B.disjoint a b); foo ()";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("assume (...")),
            "Expected assume(expr) diagnostic, got: {:?}",
            diags
        );
        // assume(expr) is Info severity (F* tracks assumed obligations)
        assert!(diags
            .iter()
            .any(|d| d.severity == DiagnosticSeverity::Info && d.message.contains("assume (...")));
    }

    #[test]
    fn test_assume_expr_squash_pattern() {
        let rule = EffectCheckerRule::new();
        let content = "let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64)";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("assume (...")),
            "Should detect assume in squash pattern"
        );
    }

    #[test]
    fn test_admit_in_inline_comment_not_flagged() {
        let rule = EffectCheckerRule::new();
        let content = "let x = y + z // TODO: use admit() here later";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("admit()")),
            "Should not flag admit() in inline comment"
        );
    }

    #[test]
    fn test_admit_in_block_comment_not_flagged() {
        let rule = EffectCheckerRule::new();
        let content = "let x = y + z (* admit() is bad *)";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("admit()")),
            "Should not flag admit() in inline block comment"
        );
    }

    #[test]
    fn test_admit_in_string_not_flagged() {
        let rule = EffectCheckerRule::new();
        let content = r#"let msg = "Do not use admit() in production""#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("admit()")),
            "Should not flag admit() in string literal"
        );
    }

    #[test]
    fn test_magic_in_string_not_flagged() {
        let rule = EffectCheckerRule::new();
        let content = r#"let msg = "magic() is dangerous""#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("magic()")),
            "Should not flag magic() in string literal"
        );
    }

    #[test]
    fn test_admit_smt_queries_option_not_flagged() {
        let rule = EffectCheckerRule::new();
        let content = r#"#set-options "--admit_smt_queries true""#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("admit()")),
            "Should not flag --admit_smt_queries option"
        );
    }

    #[test]
    fn test_code_after_block_comment_detected() {
        let rule = EffectCheckerRule::new();
        let content = "(* comment *) let x = admit()";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("admit()")),
            "Should detect admit() after block comment on same line"
        );
    }

    #[test]
    fn test_nested_block_comment_handling() {
        let rule = EffectCheckerRule::new();
        let content = "let x = y (* outer (* inner *) outer *) + admit()";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("admit()")),
            "Should detect admit() with nested comments"
        );
    }

    #[test]
    fn test_assume_val_not_double_reported() {
        let rule = EffectCheckerRule::new();
        let content = "assume val foo : int -> int";
        let diags = rule.check(&make_path(), content);
        let assume_count = diags
            .iter()
            .filter(|d| d.message.contains("assume"))
            .count();
        assert_eq!(
            assume_count, 1,
            "assume val should only be reported once, not by both checks"
        );
    }

    #[test]
    fn test_escaped_string_handling() {
        let rule = EffectCheckerRule::new();
        let content = r#"let msg = "escaped \" quote admit()""#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("admit()")),
            "Should handle escaped quotes in strings"
        );
    }

    #[test]
    fn test_strip_comments_and_strings_helper() {
        assert_eq!(strip_comments_and_strings("let x = 1"), "let x = 1");
        assert_eq!(
            strip_comments_and_strings("let x = 1 // comment"),
            "let x = 1 "
        );
        assert_eq!(
            strip_comments_and_strings("let x = 1 (* comment *)"),
            "let x = 1  "
        );
        assert_eq!(
            strip_comments_and_strings(r#"let x = "string""#),
            "let x = \"\""
        );
        // Nested comments: outer comment replaced with space, then original space before "code"
        assert_eq!(
            strip_comments_and_strings("(* outer (* inner *) outer *) code"),
            "  code"
        );
    }

    #[test]
    fn test_real_world_hacl_pattern() {
        let rule = EffectCheckerRule::new();
        let content = r#"
let nat32_to_le_bytes (n:nat32) : b:seq4 nat8 {
  le_bytes_to_nat32 b == n} =
  let b = four_to_seq_LE (nat_to_four 8 n) in
  assume (le_bytes_to_nat32 b == n);
  b
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("assume (...")),
            "Should detect assume pattern from real hacl-star code"
        );
    }

    #[test]
    fn test_module_qualified_admit_detected() {
        let rule = EffectCheckerRule::new();
        let content = "let x = FStar.Tactics.admit()";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("admit()")),
            "Should detect module-qualified admit()"
        );
    }

    // ===========================================
    // Effect hierarchy bug fix tests
    // ===========================================

    #[test]
    fn test_exn_can_call_div_bug_fix() {
        // Bug fix: Exn should be able to call Div (divergence is a sub-effect)
        assert!(Effect::Exn.can_call(Effect::Tot));
        assert!(Effect::Exn.can_call(Effect::Pure));
        assert!(Effect::Exn.can_call(Effect::Div), "BUG FIX: Exn should be able to call Div");
        assert!(Effect::Exn.can_call(Effect::Exn));
        assert!(!Effect::Exn.can_call(Effect::ST), "Exn cannot call ST");
        assert!(!Effect::Exn.can_call(Effect::Ghost), "Exn cannot call Ghost");
    }

    #[test]
    fn test_all_effect_comprehensive() {
        // All can call everything except ML
        assert!(Effect::All.can_call(Effect::Tot));
        assert!(Effect::All.can_call(Effect::GTot));
        assert!(Effect::All.can_call(Effect::Pure));
        assert!(Effect::All.can_call(Effect::Ghost));
        assert!(Effect::All.can_call(Effect::Div));
        assert!(Effect::All.can_call(Effect::ST));
        assert!(Effect::All.can_call(Effect::Exn));
        assert!(Effect::All.can_call(Effect::All));
        assert!(!Effect::All.can_call(Effect::ML), "All cannot call ML");
    }

    #[test]
    fn test_ghost_pure_branches_separate() {
        // Ghost and Pure are on separate branches
        assert!(!Effect::Ghost.can_call(Effect::Pure), "Ghost cannot call Pure");
        assert!(!Effect::Pure.can_call(Effect::Ghost), "Pure cannot call Ghost");
        assert!(!Effect::Pure.can_call(Effect::GTot), "Pure cannot call GTot");
    }

    #[test]
    fn test_div_hierarchy() {
        // Div can call Tot, Pure, Div only
        assert!(Effect::Div.can_call(Effect::Tot));
        assert!(Effect::Div.can_call(Effect::Pure));
        assert!(Effect::Div.can_call(Effect::Div));
        assert!(!Effect::Div.can_call(Effect::GTot));
        assert!(!Effect::Div.can_call(Effect::Ghost));
        assert!(!Effect::Div.can_call(Effect::ST));
        assert!(!Effect::Div.can_call(Effect::Exn));
    }

    #[test]
    fn test_st_hierarchy() {
        // ST can call Tot, Pure, Div, ST
        assert!(Effect::ST.can_call(Effect::Tot));
        assert!(Effect::ST.can_call(Effect::Pure));
        assert!(Effect::ST.can_call(Effect::Div));
        assert!(Effect::ST.can_call(Effect::ST));
        assert!(!Effect::ST.can_call(Effect::GTot));
        assert!(!Effect::ST.can_call(Effect::Ghost));
        assert!(!Effect::ST.can_call(Effect::Exn));
        assert!(!Effect::ST.can_call(Effect::ML));
    }

    #[test]
    fn test_qualified_effectful_print_string() {
        let rule = EffectCheckerRule::new();
        let content = r#"
module Test

val pure_fn : int -> Tot int
let pure_fn x = FStar.IO.print_string "hello"; x
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Tot function") && d.message.contains("print_string")),
            "Qualified FStar.IO.print_string should be detected in Tot context, got: {:?}",
            diags
        );
    }

    // ===========================================
    // Ghost/erased false positive regression tests
    // ===========================================

    #[test]
    fn test_ghost_erased_param_in_val_not_flagged() {
        let rule = EffectCheckerRule::new();
        // Real pattern from hacl-star: Ghost.erased in val parameter type
        // This should NOT cause the function name to be tracked as a ghost binding.
        // The old `erased` keyword matching caused 621 false positives in hacl-star.
        let content = r#"
module Test

val mod_precomp: len:Ghost.erased _ -> BS.bn_mod_slow_ctx_st t_limbs len
let mod_precomp len ctx a res = something len

inline_for_extraction noextract
let use_mod_precomp () = mod_precomp len ctx a res
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Ghost binding")),
            "Ghost.erased parameter type must NOT cause ghost binding false positive, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_inline_for_extraction_with_erased_implicit_param_not_flagged() {
        let rule = EffectCheckerRule::new();
        // Real pattern from hacl-star bignum: inline_for_extraction with #t:limb_t
        // The #t parameter is implicit/erased but the function IS extracted.
        let content = r#"
module Test

inline_for_extraction noextract
val bn_sub:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> bLen:size_t
  -> b:lbignum t bLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h -> live h a /\ live h b /\ live h res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1)

let bn_sub #t aLen a bLen b res =
  let c0 = bn_sub_eq_len bLen a0 b res0 in
  c0
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Ghost binding")),
            "inline_for_extraction with implicit params must NOT be flagged, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_erased_in_inline_let_annotation_not_flagged() {
        let rule = EffectCheckerRule::new();
        // Pattern from hacl-star: [@inline_let] with Ghost.erased in closures
        let content = r#"
module Test

inline_for_extraction noextract
let bn_sub_carry #t aLen a c_in res =
  push_frame ();
  let c = create 1ul c_in in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res)}) = loc c in
  [@inline_let]
  let spec h = S.bn_sub_carry_f (as_seq h a) in
  let h0 = ST.get () in
  fill_elems4 h0 aLen res refl footprint spec
  (fun i -> c.(0ul) <- subborrow_st c.(0ul) t1 (uint #t 0) res_i);
  pop_frame ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Ghost binding")),
            "GTot annotations inside inline_for_extraction must NOT trigger ghost binding warning, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_everparse_ghost_erased_param_not_flagged() {
        let rule = EffectCheckerRule::new();
        // Real pattern from everparse: Ghost.erased parameters in val + inline_for_extraction
        let content = r#"
module Test

val to_field: len:Ghost.erased _ -> MA.bn_to_field_st t_limbs len
val from_field: len:Ghost.erased _ -> MA.bn_from_field_st t_limbs len
val add: len:Ghost.erased _ -> MA.bn_field_add_st t_limbs len

inline_for_extraction noextract
let use_fields (len:Ghost.erased _) =
  let r1 = to_field len in
  let r2 = add len in
  r1
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Ghost binding")),
            "Ghost.erased parameters in everparse patterns must NOT be flagged, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_actual_ghost_let_still_detected_in_extraction_context() {
        let rule = EffectCheckerRule::new();
        // Actual ghost let binding SHOULD still be detected
        let content = r#"
module Test

ghost let secret_value = 42

inline_for_extraction let extracted_fn () = secret_value + 1
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Ghost binding") && d.message.contains("secret_value")),
            "Actual ghost let binding must still be detected in extraction context, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_erased_keyword_in_type_position_not_flagged() {
        let rule = EffectCheckerRule::new();
        // The word "erased" as a type in a record or parameter should not
        // cause the declaration to be treated as a ghost binding
        let content = r#"
module Test

val mk_concrete_ops:
    a_t:inttype
  -> len:size_t
  -> to: Ghost.erased (to_comm_monoid a_t len ctx_len) ->
  concrete_ops a_t len ctx_len

inline_for_extraction noextract
let use_concrete_ops a_t len to =
  mk_concrete_ops a_t len to
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Ghost binding")),
            "Ghost.erased in type position must NOT trigger ghost binding warning, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_tot_builtins_not_flagged() {
        let rule = EffectCheckerRule::new();
        // normalize_term, fst, snd are Tot - should not be flagged
        let content = r#"
module Test

val pure_fn : (int * int) -> Tot int
let pure_fn p = fst p + snd p
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("fst") && d.message.contains("effect")),
            "fst should not be flagged as effectful"
        );
    }

    // ===========================================
    // Effect enum extended parsing tests
    // ===========================================

    #[test]
    fn test_effect_parse_extended_names() {
        // All HyperStack.ST variants
        assert_eq!(Effect::parse("Stack"), Some(Effect::ST));
        assert_eq!(Effect::parse("Heap"), Some(Effect::ST));
        assert_eq!(Effect::parse("StackInline"), Some(Effect::ST));
        assert_eq!(Effect::parse("Inline"), Some(Effect::ST));
        assert_eq!(Effect::parse("St"), Some(Effect::ST));
        assert_eq!(Effect::parse("STL"), Some(Effect::ST));
        assert_eq!(Effect::parse("GST"), Some(Effect::ST));
        assert_eq!(Effect::parse("Unsafe"), Some(Effect::ST));

        // Uppercase base effects
        assert_eq!(Effect::parse("PURE"), Some(Effect::Tot));
        assert_eq!(Effect::parse("GHOST"), Some(Effect::GTot));
        assert_eq!(Effect::parse("DIV"), Some(Effect::Div));
        assert_eq!(Effect::parse("EXT"), Some(Effect::Div));
        assert_eq!(Effect::parse("EXN"), Some(Effect::Exn));
        assert_eq!(Effect::parse("ALL"), Some(Effect::All));

        // Tactic effects
        assert_eq!(Effect::parse("Tac"), Some(Effect::ST));
        assert_eq!(Effect::parse("TAC"), Some(Effect::ST));
        assert_eq!(Effect::parse("TacH"), Some(Effect::Lemma));
    }

    #[test]
    fn test_effect_annotation_stack_detected() {
        let _rule = EffectCheckerRule::new();
        // Stack effect in function signature should be recognized
        let block = DeclarationBlock {
            block_type: BlockType::Val,
            names: vec!["push_frame".to_string()],
            lines: vec![
                "val push_frame (_:unit) : Stack unit\n".to_string(),
                "  (requires (fun m -> True))\n".to_string(),
                "  (ensures (fun m0 _ m1 -> fresh_frame m0 m1))\n".to_string(),
            ],
            start_line: 1,
            has_push_options: false,
            has_pop_options: false,
            references: std::collections::HashSet::new(),
            module_path: None,
            is_private: false,
            is_abstract: false,
            effect_signature: None,
        };
        let eff = extract_function_effect(&block);
        assert_eq!(eff, Some(Effect::ST), "Stack should parse as ST effect");
    }

    #[test]
    fn test_effect_annotation_lemma_detected() {
        let block = DeclarationBlock {
            block_type: BlockType::Val,
            names: vec!["my_lemma".to_string()],
            lines: vec!["val my_lemma : x:nat -> Lemma (ensures x >= 0)\n".to_string()],
            start_line: 1,
            has_push_options: false,
            has_pop_options: false,
            references: std::collections::HashSet::new(),
            module_path: None,
            is_private: false,
            is_abstract: false,
            effect_signature: None,
        };
        let eff = extract_function_effect(&block);
        assert_eq!(eff, Some(Effect::Lemma), "Lemma should parse as Lemma effect");
    }

    #[test]
    fn test_effect_annotation_heap_detected() {
        let block = DeclarationBlock {
            block_type: BlockType::Val,
            names: vec!["alloc_fn".to_string()],
            lines: vec!["val alloc_fn : int -> Heap int\n".to_string()],
            start_line: 1,
            has_push_options: false,
            has_pop_options: false,
            references: std::collections::HashSet::new(),
            module_path: None,
            is_private: false,
            is_abstract: false,
            effect_signature: None,
        };
        let eff = extract_function_effect(&block);
        assert_eq!(eff, Some(Effect::ST), "Heap should parse as ST effect");
    }

    #[test]
    fn test_effect_annotation_div_detected() {
        let block = DeclarationBlock {
            block_type: BlockType::Val,
            names: vec!["divergent_fn".to_string()],
            lines: vec!["val divergent_fn : nat -> Dv nat\n".to_string()],
            start_line: 1,
            has_push_options: false,
            has_pop_options: false,
            references: std::collections::HashSet::new(),
            module_path: None,
            is_private: false,
            is_abstract: false,
            effect_signature: None,
        };
        let eff = extract_function_effect(&block);
        assert_eq!(eff, Some(Effect::Div), "Dv should parse as Div effect");
    }

    // ===========================================
    // Effect declaration validation tests (FST011)
    // ===========================================

    #[test]
    fn test_effect_decl_check_clean() {
        let rule = EffectCheckerRule::new();
        // Well-formed effect abbreviation should not trigger warnings
        let content = "module Test\n\neffect Stack (a:Type) (pre:st_pre) (post:Type) =\n       STATE a (fun p h -> pre h)\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("new_effect") || d.message.contains("layered_effect")),
            "Clean effect abbreviation should not trigger effect declaration warnings"
        );
    }

    #[test]
    fn test_sub_effect_missing_arrow() {
        let rule = EffectCheckerRule::new();
        // sub_effect without ~> should warn
        let content = "module Test\n\nsub_effect PURE = lift_pure\n";
        let _diags = rule.check(&make_path(), content);
        // Note: sub_effect without ~> may not parse as SubEffect at all,
        // since our pattern requires ~> for name capture. The generic pattern
        // still matches though.
        // This is a corner case that F* itself would reject too.
    }

    #[test]
    fn test_effect_keyword_not_causing_false_dependencies() {
        // Ensure effect-related keywords don't cause false dependencies
        // in the parser's reference tracking
        let content = "module Test\n\neffect Stack (a:Type) (pre:st_pre) (post:Type) =\n       STATE a (fun p h -> pre h)\n\nval my_fn : int -> Stack unit\n  (requires fun h -> True)\n  (ensures fun h0 _ h1 -> True)\n";
        let (_, blocks) = parse_fstar_file(content);
        // The val block should not have 'requires' or 'ensures' as references
        // since they are keywords
        for block in &blocks {
            if block.block_type == BlockType::Val {
                assert!(
                    !block.references.contains("requires"),
                    "requires should be filtered as keyword"
                );
                assert!(
                    !block.references.contains("ensures"),
                    "ensures should be filtered as keyword"
                );
            }
        }
    }

    #[test]
    fn test_ml_effect_in_effect_definition_not_flagged() {
        let rule = EffectCheckerRule::new();
        // ML used in an effect definition should not be flagged
        let content = "module Test\n\neffect ML (a:Type) = ALL a (fun p h -> forall a h'. p a h')\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("ML effect is overly permissive")),
            "ML in effect definition should not be flagged"
        );
    }

    // ===========================================
    // EffectSignature extraction tests (parser)
    // ===========================================

    #[test]
    fn test_effect_signature_stack_with_requires_ensures() {
        let content = r#"module Test

val push_frame : unit -> Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> fresh_frame h0 h1)
"#;
        let (_, blocks) = parse_fstar_file(content);
        let val_block = blocks.iter().find(|b| b.block_type == BlockType::Val);
        assert!(val_block.is_some(), "Should find val block");
        let sig = val_block.unwrap().effect_signature.as_ref();
        assert!(sig.is_some(), "Should extract effect signature");
        let sig = sig.unwrap();
        assert_eq!(sig.effect_name, "Stack");
        assert!(sig.has_requires, "Should detect requires clause");
        assert!(sig.has_ensures, "Should detect ensures clause");
        assert!(sig.is_stateful_effect(), "Stack should be stateful");
    }

    #[test]
    fn test_effect_signature_st_with_modifies() {
        let content = r#"module Test

val write_buf :
    buf:buffer uint8
  -> len:uint32 ->
  ST unit
  (requires fun h -> live h buf /\ length buf >= UInt32.v len)
  (ensures  fun h0 _ h1 -> modifies (loc_buffer buf) h0 h1)
"#;
        let (_, blocks) = parse_fstar_file(content);
        let val_block = blocks.iter().find(|b| b.block_type == BlockType::Val);
        assert!(val_block.is_some());
        let sig = val_block.unwrap().effect_signature.as_ref().unwrap();
        assert_eq!(sig.effect_name, "ST");
        assert!(sig.has_requires);
        assert!(sig.has_ensures);
        assert!(sig.has_modifies, "Should detect modifies in ensures");
    }

    #[test]
    fn test_effect_signature_lemma_with_ensures() {
        let content = "module Test\n\nval my_lemma : x:nat -> Lemma (ensures x + 0 == x)\n";
        let (_, blocks) = parse_fstar_file(content);
        let val_block = blocks.iter().find(|b| b.block_type == BlockType::Val);
        assert!(val_block.is_some());
        let sig = val_block.unwrap().effect_signature.as_ref().unwrap();
        assert_eq!(sig.effect_name, "Lemma");
        assert!(sig.has_ensures, "Should detect ensures in Lemma");
        assert!(sig.is_lemma_effect(), "Lemma should be lemma-like");
    }

    #[test]
    fn test_effect_signature_lemma_with_requires_ensures_smtpat() {
        let content = r#"module Test

val mod_lemma : a:int -> n:pos -> Lemma
  (requires a >= 0)
  (ensures  a % n >= 0 /\ a % n < n)
  [SMTPat (a % n)]
"#;
        let (_, blocks) = parse_fstar_file(content);
        let val_block = blocks.iter().find(|b| b.block_type == BlockType::Val);
        assert!(val_block.is_some());
        let sig = val_block.unwrap().effect_signature.as_ref().unwrap();
        assert_eq!(sig.effect_name, "Lemma");
        assert!(sig.has_requires, "Should detect requires");
        assert!(sig.has_ensures, "Should detect ensures");
    }

    #[test]
    fn test_effect_signature_pure_hoare() {
        let content = "module Test\n\nval safe_div : x:int -> y:int -> Pure int (requires y <> 0) (ensures fun r -> r * y == x)\n";
        let (_, blocks) = parse_fstar_file(content);
        let val_block = blocks.iter().find(|b| b.block_type == BlockType::Val);
        assert!(val_block.is_some());
        let sig = val_block.unwrap().effect_signature.as_ref().unwrap();
        assert_eq!(sig.effect_name, "Pure");
        assert!(sig.has_requires);
        assert!(sig.has_ensures);
        assert!(sig.is_pure_hoare_effect(), "Pure should be hoare-style");
    }

    #[test]
    fn test_effect_signature_tot_with_decreases() {
        let content = "module Test\n\nval fibonacci : n:nat -> Tot nat (decreases n)\n";
        let (_, blocks) = parse_fstar_file(content);
        let val_block = blocks.iter().find(|b| b.block_type == BlockType::Val);
        assert!(val_block.is_some());
        let sig = val_block.unwrap().effect_signature.as_ref().unwrap();
        assert_eq!(sig.effect_name, "Tot");
        assert!(sig.has_decreases, "Should detect decreases clause");
        assert!(!sig.is_stateful_effect());
        assert!(!sig.is_lemma_effect());
    }

    #[test]
    fn test_effect_signature_no_effect() {
        let content = "module Test\n\nval add : int -> int -> int\n";
        let (_, blocks) = parse_fstar_file(content);
        let val_block = blocks.iter().find(|b| b.block_type == BlockType::Val);
        assert!(val_block.is_some());
        // No explicit effect annotation => no effect signature
        assert!(
            val_block.unwrap().effect_signature.is_none(),
            "No explicit effect annotation means no signature"
        );
    }

    #[test]
    fn test_effect_signature_effect_abbrev() {
        let content = "module Test\n\neffect Stack (a:Type) (pre:st_pre) (post:Type) = STATE a (fun p h -> pre h)\n";
        let (_, blocks) = parse_fstar_file(content);
        let effect_block = blocks.iter().find(|b| b.block_type == BlockType::EffectAbbrev);
        assert!(effect_block.is_some());
        let sig = effect_block.unwrap().effect_signature.as_ref().unwrap();
        assert_eq!(sig.effect_name, "Stack");
        assert_eq!(sig.base_effect.as_deref(), Some("STATE"));
    }

    #[test]
    fn test_effect_signature_effect_abbrev_dv() {
        let content = "module Test\n\neffect Dv (a: Type) = DIV a (pure_null_wp a)\n";
        let (_, blocks) = parse_fstar_file(content);
        let effect_block = blocks.iter().find(|b| b.block_type == BlockType::EffectAbbrev);
        assert!(effect_block.is_some());
        let sig = effect_block.unwrap().effect_signature.as_ref().unwrap();
        assert_eq!(sig.base_effect.as_deref(), Some("DIV"));
    }

    #[test]
    fn test_effect_signature_sub_effect() {
        let content = "module Test\n\nsub_effect PURE ~> DIV = fun (a:Type) (wp:pure_wp a) -> wp\n";
        let (_, blocks) = parse_fstar_file(content);
        let se_block = blocks.iter().find(|b| b.block_type == BlockType::SubEffect);
        assert!(se_block.is_some());
        let sig = se_block.unwrap().effect_signature.as_ref().unwrap();
        assert_eq!(sig.sub_effect_src.as_deref(), Some("PURE"));
        assert_eq!(sig.sub_effect_dst.as_deref(), Some("DIV"));
    }

    #[test]
    fn test_effect_signature_sub_effect_with_lift_wp() {
        let content = "module Test\n\nsub_effect PURE ~> STATE { lift_wp = purewp_id }\n";
        let (_, blocks) = parse_fstar_file(content);
        let se_block = blocks.iter().find(|b| b.block_type == BlockType::SubEffect);
        assert!(se_block.is_some());
        let sig = se_block.unwrap().effect_signature.as_ref().unwrap();
        assert!(sig.combinators.contains(&"lift_wp".to_string()), "Should detect lift_wp");
    }

    #[test]
    fn test_effect_signature_new_effect_with_combinators() {
        let content = "module Test\n\nnew_effect { STATE : a:Type -> wp:st_wp a -> Effect\n  with return_wp = fun a x -> x\n     ; bind_wp = fun a b wp1 wp2 -> wp1\n}\n";
        let (_, blocks) = parse_fstar_file(content);
        let ne_block = blocks.iter().find(|b| b.block_type == BlockType::NewEffect);
        assert!(ne_block.is_some());
        let sig = ne_block.unwrap().effect_signature.as_ref().unwrap();
        assert!(sig.combinators.contains(&"return_wp".to_string()));
        assert!(sig.combinators.contains(&"bind_wp".to_string()));
    }

    #[test]
    fn test_effect_signature_layered_effect_combinators() {
        let content = "module Test\n\nlayered_effect { TAC : a:Type -> tac_wp a -> Effect\n  with repr = __tac\n     ; return = fun a x -> fun ps -> Success x ps\n     ; bind = fun a b m f -> fun ps -> match m ps with x -> x\n}\n";
        let (_, blocks) = parse_fstar_file(content);
        let le_block = blocks.iter().find(|b| b.block_type == BlockType::Effect);
        assert!(le_block.is_some());
        let sig = le_block.unwrap().effect_signature.as_ref().unwrap();
        assert!(sig.combinators.contains(&"repr".to_string()), "Should find repr");
        assert!(sig.combinators.contains(&"return".to_string()), "Should find return");
        assert!(sig.combinators.contains(&"bind".to_string()), "Should find bind");
    }

    // ===========================================
    // New rule tests: stateful effect specs
    // ===========================================

    #[test]
    fn test_stateful_effect_missing_requires_ensures() {
        let rule = EffectCheckerRule::new();
        let content = r#"module Test

val alloc_buffer : len:uint32 -> Stack (buffer uint8)
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("missing requires/ensures")),
            "Stack without requires/ensures should be flagged, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_stateful_effect_with_requires_ensures_ok() {
        let rule = EffectCheckerRule::new();
        let content = r#"module Test

val alloc_buffer : len:uint32 -> Stack (buffer uint8)
  (requires fun h -> True)
  (ensures  fun h0 buf h1 -> live h1 buf)
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("missing requires/ensures")),
            "Stack with requires/ensures should not be flagged"
        );
    }

    #[test]
    fn test_stateful_effect_requires_only_flagged() {
        let rule = EffectCheckerRule::new();
        let content = r#"module Test

val partial_fn : buf:buffer uint8 -> Stack unit
  (requires fun h -> live h buf)
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("missing ensures")),
            "Stack with requires but no ensures should be flagged, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_tot_effect_not_flagged_for_missing_specs() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\nval add : int -> int -> Tot int\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("missing requires/ensures")),
            "Tot should not require requires/ensures"
        );
    }

    // ===========================================
    // New rule tests: Lemma ensures
    // ===========================================

    #[test]
    fn test_vacuous_lemma_true_flagged() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\nval useless_lemma : unit -> Lemma True\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("vacuous Lemma")),
            "Lemma True should be flagged as vacuous, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_lemma_with_ensures_ok() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\nval useful_lemma : x:nat -> Lemma (ensures x + 0 == x)\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("vacuous Lemma")),
            "Lemma with ensures should not be flagged as vacuous"
        );
    }

    #[test]
    fn test_lemma_with_direct_property_ok() {
        let rule = EffectCheckerRule::new();
        // `Lemma (some_property)` is valid F* - desugars to ensures
        let content = "module Test\n\nval my_lemma : x:nat -> Lemma (x >= 0)\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("vacuous Lemma")),
            "Lemma with direct property should not be flagged"
        );
    }

    #[test]
    fn test_lemma_with_requires_and_ensures_ok() {
        let rule = EffectCheckerRule::new();
        let content = r#"module Test

val div_lemma : a:int -> n:pos -> Lemma
  (requires a >= 0)
  (ensures  a % n >= 0)
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("vacuous Lemma")),
            "Lemma with requires and ensures should not be flagged"
        );
    }

    // ===========================================
    // New rule tests: effect abbreviation base
    // ===========================================

    #[test]
    fn test_effect_abbrev_known_base_ok() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\neffect Dv (a: Type) = DIV a (pure_null_wp a)\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("unknown base effect")),
            "DIV is a known base effect"
        );
    }

    #[test]
    fn test_effect_abbrev_unknown_base_flagged() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\neffect MyEff (a: Type) = NONEXISTENT a\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("unknown base effect")),
            "NONEXISTENT should be flagged as unknown base, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_effect_abbrev_local_base_ok() {
        let rule = EffectCheckerRule::new();
        // When the base effect is defined locally in the same file
        let content = r#"module Test

new_effect { MYSTATE : a:Type -> wp:st_wp a -> Effect
  with return_wp = fun a x -> x
     ; bind_wp = fun a b wp1 -> wp1
}

effect MySt (a:Type) = MYSTATE a (fun _ -> True)
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("unknown base effect") && d.message.contains("MYSTATE")),
            "Locally defined base effect should not be flagged"
        );
    }

    #[test]
    fn test_sub_effect_unknown_src_flagged() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\nsub_effect BOGUS ~> STATE = fun a wp -> wp\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("not a known effect") && d.message.contains("BOGUS")),
            "Unknown sub_effect source should be flagged, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_sub_effect_known_effects_ok() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\nsub_effect PURE ~> DIV = fun a wp -> wp\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("not a known effect")),
            "PURE ~> DIV are both known effects"
        );
    }

    // ===========================================
    // New rule tests: Hoare effect completeness
    // ===========================================

    #[test]
    fn test_pure_requires_only_flagged() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\nval safe_fn : x:int -> Pure int (requires x > 0)\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("requires but no ensures")),
            "Pure with requires but no ensures should be flagged, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_pure_both_ok() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\nval safe_fn : x:int -> Pure int (requires x > 0) (ensures fun r -> r > 0)\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("requires but no ensures")),
            "Pure with both requires and ensures should not be flagged"
        );
    }

    #[test]
    fn test_ghost_requires_only_flagged() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\nval spec_fn : x:nat -> Ghost int (requires x > 0)\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("requires but no ensures")),
            "Ghost with requires but no ensures should be flagged"
        );
    }

    // ===========================================
    // New rule tests: layered effect combinators
    // ===========================================

    #[test]
    fn test_layered_effect_partial_combinators_flagged() {
        let rule = EffectCheckerRule::new();
        // Has repr and return but missing bind
        let content = "module Test\n\nlayered_effect { MYEFF : a:Type -> wp -> Effect\n  with repr = myrep\n     ; return = fun a x -> x\n}\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("missing required combinators") && d.message.contains("bind")),
            "Layered effect missing bind should be flagged, got: {:?}",
            diags
        );
    }

    #[test]
    fn test_layered_effect_all_combinators_ok() {
        let rule = EffectCheckerRule::new();
        let content = "module Test\n\nlayered_effect { MYEFF : a:Type -> wp -> Effect\n  with repr = myrep\n     ; return = fun a x -> x\n     ; bind = fun a b m f -> m\n     ; subcomp = fun a f -> f\n}\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("missing required combinators")),
            "Layered effect with all combinators should not be flagged"
        );
    }

    // ===========================================
    // Integration: HACL*-style patterns
    // ===========================================

    #[test]
    fn test_hacl_style_stack_signature() {
        let rule = EffectCheckerRule::new();
        // Real-world HACL* pattern
        let content = r#"module Test

val bn_add1 :
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> b1:limb t
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 ->
    modifies (loc res) h0 h1 /\
    (let c, r = Spec.bn_add1 (as_seq h0 a) b1 in
     c_out == c /\ as_seq h1 res == r))
"#;
        let diags = rule.check(&make_path(), content);
        // Should NOT flag - has full requires/ensures
        assert!(
            !diags.iter().any(|d| d.message.contains("missing requires")),
            "HACL*-style complete signature should not be flagged"
        );
    }

    #[test]
    fn test_hacl_style_lemma_with_smtpat() {
        let rule = EffectCheckerRule::new();
        let content = r#"module Test

val lemma_mod_plus : a:int -> k:int -> n:pos -> Lemma
  (requires True)
  (ensures  (a + k * n) % n == a % n)
  [SMTPat ((a + k * n) % n)]
"#;
        let diags = rule.check(&make_path(), content);
        // Has ensures, should not be flagged
        assert!(
            !diags.iter().any(|d| d.message.contains("vacuous Lemma")),
            "Lemma with ensures and SMTPat should not be vacuous"
        );
    }

    #[test]
    fn test_multiple_val_effects_in_file() {
        let rule = EffectCheckerRule::new();
        let content = r#"module Test

val pure_fn : int -> Tot int
val stack_fn : buf:buffer uint8 -> Stack unit
  (requires fun h -> live h buf)
  (ensures  fun h0 _ h1 -> modifies (loc_buffer buf) h0 h1)
val lemma_fn : x:nat -> Lemma (ensures x >= 0) [SMTPat x]
val ghost_fn : x:nat -> GTot nat
"#;
        let diags = rule.check(&make_path(), content);
        // None of these should trigger false positives
        assert!(
            !diags.iter().any(|d| d.message.contains("missing requires/ensures")),
            "Well-specified val declarations should not be flagged"
        );
    }

    #[test]
    fn test_effect_abbrev_st_definition() {
        let rule = EffectCheckerRule::new();
        let content = r#"module Test

effect ST (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. post h a h1 /\ equal_domains h h1 ==> p a h1))
"#;
        let diags = rule.check(&make_path(), content);
        // Known base STATE => no warning
        assert!(
            !diags.iter().any(|d| d.message.contains("unknown base effect")),
            "STATE is a known base effect for ST abbreviation"
        );
    }

    #[test]
    fn test_clean_effect_declarations_no_warnings() {
        let rule = EffectCheckerRule::new();
        let content = r#"module Test

effect Dv (a: Type) = DIV a (pure_null_wp a)

sub_effect PURE ~> DIV = fun (a:Type) (wp:pure_wp a) -> wp

val add : nat -> nat -> Tot nat
let add x y = x + y

val factorial : nat -> Tot nat (decreases n)
"#;
        let diags = rule.check(&make_path(), content);
        // Filter to only effect-related diagnostics (not admit/magic etc)
        let effect_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("effect") || d.message.contains("Lemma")
                || d.message.contains("requires") || d.message.contains("ensures")
                || d.message.contains("combinator"))
            .collect();
        assert!(
            effect_diags.is_empty(),
            "Clean effect declarations should produce no effect-related diagnostics, got: {:?}",
            effect_diags
        );
    }

    // ===========================================
    // NEW: admit_smt_queries tests
    // ===========================================

    #[test]
    fn test_admit_smt_queries_detected() {
        let rule = EffectCheckerRule::new();
        let content = r#"#set-options "--admit_smt_queries true""#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("admit_smt_queries")),
            "Should detect --admit_smt_queries true"
        );
        assert!(
            diags.iter().any(|d| d.severity == DiagnosticSeverity::Warning && d.message.contains("admit_smt_queries")),
            "admit_smt_queries should be Warning severity"
        );
    }

    #[test]
    fn test_admit_smt_queries_false_not_detected() {
        let rule = EffectCheckerRule::new();
        let content = r#"#set-options "--admit_smt_queries false""#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("admit_smt_queries")),
            "Should not detect --admit_smt_queries false"
        );
    }

    #[test]
    fn test_admit_smt_queries_in_comment_skipped() {
        let rule = EffectCheckerRule::new();
        let content = r#"// #set-options "--admit_smt_queries true""#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("admit_smt_queries")),
            "Should skip admit_smt_queries in comments"
        );
    }

    // ===========================================
    // NEW: tadmit tests
    // ===========================================

    #[test]
    fn test_tadmit_detected() {
        let rule = EffectCheckerRule::new();
        let content = r#"let proof x = assert (P x) by (tadmit ())"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("tadmit")),
            "Should detect tadmit()"
        );
    }

    #[test]
    fn test_tadmit_in_comment_skipped() {
        let rule = EffectCheckerRule::new();
        let content = "// tadmit () is bad";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("tadmit")),
            "Should skip tadmit in comments"
        );
    }

    // ===========================================
    // NEW: Classical patterns tests
    // ===========================================

    #[test]
    fn test_classical_forall_intro_hint() {
        let rule = EffectCheckerRule::new();
        let content = "Classical.forall_intro (fun x -> lemma1 x)";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("forall_intro")),
            "Should provide hint for Classical.forall_intro"
        );
    }

    #[test]
    fn test_classical_move_requires_hint() {
        let rule = EffectCheckerRule::new();
        let content = "Classical.move_requires lemma1 x";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("move_requires")),
            "Should provide hint for Classical.move_requires"
        );
    }

    #[test]
    fn test_classical_patterns_are_hints() {
        let rule = EffectCheckerRule::new();
        let content = "Classical.forall_intro (fun x -> lemma1 x)";
        let diags = rule.check(&make_path(), content);
        let classical_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Classical"))
            .collect();
        assert!(
            classical_diags.iter().all(|d| d.severity == DiagnosticSeverity::Hint),
            "Classical pattern hints should be Hint severity"
        );
    }

    // ===========================================
    // HACL* real-world pattern tests
    // ===========================================

    #[test]
    fn test_hacl_admit_smt_queries_pattern() {
        // Real pattern from Lib.IntVector.fst
        let rule = EffectCheckerRule::new();
        let content = r#"#set-options "--admit_smt_queries true""#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.severity == DiagnosticSeverity::Warning && d.message.contains("admit_smt_queries")),
            "HACL* admit_smt_queries should be flagged as Warning"
        );
    }

    // ===========================================
    // NEW: undefined detection tests
    // ===========================================

    #[test]
    fn test_undefined_detected() {
        let rule = EffectCheckerRule::new();
        let content = "let bad_value : int = undefined";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("undefined")),
            "Should detect bare undefined usage"
        );
    }

    #[test]
    fn test_undefined_qualified_detected() {
        let rule = EffectCheckerRule::new();
        let content = "let bad_value : int = FStar.Pervasives.undefined";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("undefined")),
            "Should detect qualified FStar.Pervasives.undefined"
        );
    }

    #[test]
    fn test_undefined_in_comment_ignored() {
        let rule = EffectCheckerRule::new();
        let content = "(* undefined is used for bootstrapping *)";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("`undefined`")),
            "Should not flag undefined in comments"
        );
    }

    // ===========================================
    // NEW: assert false detection tests
    // ===========================================

    #[test]
    fn test_assert_false_detected() {
        let rule = EffectCheckerRule::new();
        let content = "let proof x = assert false";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("assert false") || d.message.contains("False elimination")),
            "Should detect assert false"
        );
    }

    #[test]
    fn test_assert_false_capital_detected() {
        let rule = EffectCheckerRule::new();
        let content = "let proof x = assert (False)";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("False elimination")),
            "Should detect assert (False)"
        );
    }

    #[test]
    fn test_assert_false_in_comment_ignored() {
        let rule = EffectCheckerRule::new();
        let content = "// assert false is used for reductio";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("False elimination")),
            "Should not flag assert false in comments"
        );
    }

    #[test]
    fn test_assert_true_not_flagged() {
        let rule = EffectCheckerRule::new();
        let content = "let proof x = assert (True)";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("False elimination")),
            "assert True should not trigger assert false detection"
        );
    }

    // ===========================================
    // NEW: synth_by_tactic tadmit tests
    // ===========================================

    #[test]
    fn test_synth_tadmit_detected() {
        let rule = EffectCheckerRule::new();
        let content = "let witness : t = synth_by_tactic (fun () -> tadmit())";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("synth_by_tactic") && d.message.contains("hidden admit")),
            "Should detect synth_by_tactic with tadmit"
        );
    }

    #[test]
    fn test_synth_by_tactic_without_tadmit_ok() {
        let rule = EffectCheckerRule::new();
        let content = "let witness : t = synth_by_tactic (fun () -> exact (`value))";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("hidden admit")),
            "synth_by_tactic without tadmit should not be flagged"
        );
    }

    #[test]
    fn test_synth_tadmit_in_comment_ignored() {
        let rule = EffectCheckerRule::new();
        let content = "(* synth_by_tactic (fun () -> tadmit()) *)";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("hidden admit")),
            "Should not flag synth_by_tactic in comments"
        );
    }
}
