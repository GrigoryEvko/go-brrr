//! F* source file parser for lint rules.
//!
//! Port of reorder_fsti.py's FStarParser class.
//! Parses F* files into logical blocks for analysis and reordering.
//!
//! Supports F* tactics/metaprogramming constructs:
//! - Tactic expressions: `_ by (tactic)`, `assert ... by (...)`, `synth_by_tactic (...)`
//! - Quotation syntax: backtick forms `` `name ``, `` `%name ``, `` `#name ``, `` `(expr) ``
//! - Pragmas: `#set-options`, `#push-options`, `#pop-options`, `#reset-options`, `#restart-solver`
//! - Attributes: `[@ attr]`, `[@@ attr]`, `[@@@ attr]`
//! - SMT patterns: `[SMTPat ...]`, `[SMTPatOr [...]]`

use lazy_static::lazy_static;
use regex::Regex;
use std::collections::{HashMap, HashSet};

use super::shared_patterns::{EFFECT_ANNOTATION_RE, MODULE_DECL_RE};

/// Efficiently append a newline to a line slice, avoiding `format!` overhead.
/// `format!("{}\n", s)` goes through the full `std::fmt` Display machinery;
/// this direct construction is ~3-5x faster for this trivial case.
#[inline(always)]
fn line_newline(line: &str) -> String {
    let mut s = String::with_capacity(line.len() + 1);
    s.push_str(line);
    s.push('\n');
    s
}

/// Parsed effect signature information from val/let declarations.
///
/// Captures details about how an effect is used in a function signature,
/// including the effect name, return type position, and whether
/// requires/ensures/decreases clauses are present.
///
/// Examples of signatures this captures:
/// ```text
/// val foo : int -> Stack unit
///   (requires fun h -> live h buf)
///   (ensures  fun h0 _ h1 -> modifies (loc buf) h0 h1)
///
/// val bar : x:nat -> Pure int (requires (x > 0)) (ensures (fun r -> r > x))
///
/// val baz : unit -> Lemma (ensures (P /\ Q)) [SMTPat ...]
///
/// val qux : nat -> Tot nat (decreases n)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectSignature {
    /// The effect name (e.g., "Stack", "ST", "Pure", "Lemma", "Tot").
    pub effect_name: String,
    /// Whether a `requires` clause is present.
    pub has_requires: bool,
    /// Whether an `ensures` clause is present.
    pub has_ensures: bool,
    /// Whether a `decreases` clause is present.
    pub has_decreases: bool,
    /// Whether a `modifies` clause is present (in ensures or standalone).
    pub has_modifies: bool,
    /// The line number (1-indexed) where the effect annotation appears.
    pub effect_line: usize,
    /// For sub_effect: source effect name.
    pub sub_effect_src: Option<String>,
    /// For sub_effect: destination effect name.
    pub sub_effect_dst: Option<String>,
    /// For effect abbreviations: the base effect name being aliased.
    pub base_effect: Option<String>,
    /// For new_effect/layered_effect: which combinators are present.
    pub combinators: Vec<String>,
}

impl EffectSignature {
    /// Whether this is a stateful effect that typically needs requires/ensures.
    pub fn is_stateful_effect(&self) -> bool {
        matches!(
            self.effect_name.as_str(),
            "Stack" | "ST" | "STATE" | "State" | "Heap" | "StackInline"
            | "Inline" | "STL" | "GST" | "Unsafe"
        )
    }

    /// Whether this is a Low*/LowStar stack effect requiring frame discipline.
    ///
    /// Stack and StackInline effects in Low* require push_frame/pop_frame
    /// pairs and buffer liveness predicates. ST effects need modifies clauses.
    pub fn is_lowstar_stack_effect(&self) -> bool {
        matches!(
            self.effect_name.as_str(),
            "Stack" | "StackInline"
        )
    }

    /// Whether this is any Low* stateful effect (Stack, ST, or HyperStack-based).
    ///
    /// These effects deal with mutable heap memory and require:
    /// - `live` predicates for buffers in requires
    /// - `modifies` clauses in ensures
    /// - `disjoint` predicates for separate buffers
    pub fn is_lowstar_effect(&self) -> bool {
        matches!(
            self.effect_name.as_str(),
            "Stack" | "StackInline" | "ST" | "STATE" | "State"
        )
    }

    /// Whether this is a Lemma-like effect that should have ensures.
    pub fn is_lemma_effect(&self) -> bool {
        matches!(
            self.effect_name.as_str(),
            "Lemma" | "TacH" | "TacS" | "TacRO" | "TacF"
        )
    }

    /// Whether this is a Pure-like effect that can have pre/post conditions.
    pub fn is_pure_hoare_effect(&self) -> bool {
        matches!(self.effect_name.as_str(), "Pure" | "Ghost" | "Div")
    }
}

/// Machine integer type information for Low* code.
///
/// Represents F* machine integer types used in Low* for C extraction:
/// `FStar.UInt8.t`, `FStar.UInt32.t`, `FStar.UInt64.t`, etc.
/// Also covers `Lib.IntTypes` types: `uint8`, `uint16`, `uint32`, `uint64`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MachineIntType {
    /// 8-bit unsigned integer (uint8, UInt8.t, u8)
    U8,
    /// 16-bit unsigned integer (uint16, UInt16.t, u16)
    U16,
    /// 32-bit unsigned integer (uint32, UInt32.t, u32)
    U32,
    /// 64-bit unsigned integer (uint64, UInt64.t, u64)
    U64,
    /// 128-bit unsigned integer (uint128, UInt128.t)
    U128,
    /// Size type (size_t, size_nat) - always public
    SizeT,
}

impl MachineIntType {
    /// Parse a machine integer type from a string token.
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "uint8" | "UInt8.t" | "U8" | "u8" => Some(Self::U8),
            "uint16" | "UInt16.t" | "U16" | "u16" => Some(Self::U16),
            "uint32" | "UInt32.t" | "U32" | "u32" => Some(Self::U32),
            "uint64" | "UInt64.t" | "U64" | "u64" => Some(Self::U64),
            "uint128" | "UInt128.t" => Some(Self::U128),
            "size_t" | "size_nat" | "size_pos" => Some(Self::SizeT),
            _ => None,
        }
    }

    /// The bit width of this type.
    pub fn bit_width(&self) -> u32 {
        match self {
            Self::U8 => 8,
            Self::U16 => 16,
            Self::U32 => 32,
            Self::U64 => 64,
            Self::U128 => 128,
            Self::SizeT => 32, // platform-dependent but 32 for analysis
        }
    }

    /// Whether this type is always public (safe for branches/division).
    pub fn is_public(&self) -> bool {
        matches!(self, Self::SizeT)
    }
}

/// Low*/LowStar buffer type information.
///
/// Represents the various buffer types used in Low* code:
/// - `LowStar.Buffer.buffer t` - basic buffer
/// - `lbuffer t len` - length-indexed buffer (Lib.Buffer)
/// - `lbignum t len` - bignum buffer (HACL*)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LowStarBufferType {
    /// The element type of the buffer.
    pub element_type: String,
    /// The length (if statically known from type-level).
    pub length: Option<String>,
    /// Whether this is a bignum buffer.
    pub is_bignum: bool,
}

/// Check if a file appears to be a Low*/LowStar module based on its imports.
///
/// Scans the first 50 lines for characteristic Low* imports:
/// - `open FStar.HyperStack` or `open FStar.HyperStack.ST`
/// - `open LowStar.Buffer` or `open Lib.Buffer`
/// - `open Lib.IntTypes`
/// - `module ST = FStar.HyperStack.ST`
pub fn is_lowstar_module(content: &str) -> bool {
    // Scan first 50 lines without allocating a Vec or joining.
    // Find the byte offset of the 50th newline (or end of content).
    let header_end = content.as_bytes().iter()
        .enumerate()
        .filter(|(_, &b)| b == b'\n')
        .nth(49)
        .map(|(i, _)| i + 1)
        .unwrap_or(content.len());
    let header = &content[..header_end];
    header.contains("FStar.HyperStack")
        || header.contains("LowStar.Buffer")
        || header.contains("Lib.Buffer")
        || header.contains("Lib.IntTypes")
}

/// Extract module aliases from a file's header.
///
/// Returns a map of alias -> full module path for patterns like:
/// ```text
/// module ST = FStar.HyperStack.ST
/// module LSeq = Lib.Sequence
/// module BSeq = Lib.ByteSequence
/// ```
pub fn extract_module_aliases(content: &str) -> HashMap<String, String> {
    lazy_static! {
        static ref MODULE_ALIAS: Regex = Regex::new(
            r"module\s+(\w+)\s*=\s*([\w.]+)"
        ).unwrap_or_else(|e| panic!("regex: {e}"));
    }

    let mut aliases = HashMap::new();
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.starts_with("(*") {
            continue;
        }
        if let Some(caps) = MODULE_ALIAS.captures(trimmed) {
            if let (Some(alias), Some(path)) = (caps.get(1), caps.get(2)) {
                aliases.insert(alias.as_str().to_string(), path.as_str().to_string());
            }
        }
    }
    aliases
}

// =========================================================================
// Pragma, Attribute, SMT pattern, Tactic, Quotation types
// =========================================================================

/// Parsed F* pragma directive (compiler option control).
///
/// These appear at the top level and control verification parameters:
/// ```text
/// #set-options "--z3rlimit 50 --fuel 0 --ifuel 0"
/// #push-options "--fuel 2"
/// #pop-options
/// #reset-options "--z3rlimit 5"
/// #restart-solver
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pragma {
    /// `#set-options "..."` -- set options for the rest of the file.
    SetOptions(String),
    /// `#push-options "..."` -- push options onto the stack.
    PushOptions(String),
    /// `#pop-options` -- restore previous options.
    PopOptions,
    /// `#reset-options` or `#reset-options "..."` -- reset to defaults, optionally with new values.
    ResetOptions(Option<String>),
    /// `#restart-solver` -- restart the Z3 solver with a fresh state.
    RestartSolver,
}

/// Attribute style distinguishing old-style from new-style annotations.
///
/// F* has three attribute bracket forms:
/// - `[@ attr]`   -- old-style single attribute (F* 1.x)
/// - `[@@ attr]`  -- declaration attribute (F* 2.x)
/// - `[@@@ attr]` -- binder attribute (on parameters)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttributeStyle {
    /// `[@ attr]` -- old-style attribute.
    OldStyle,
    /// `[@@ attr]` -- declaration attribute.
    Declaration,
    /// `[@@@ attr]` -- binder attribute.
    Binder,
}

/// A parsed F* attribute annotation.
///
/// Examples from real code:
/// ```text
/// [@@"opaque_to_smt"]
/// [@@ CInline ]
/// [@@@ strict_on_arguments [1;2]]
/// [@@ Comment "Write the HMAC-MD5 MAC of a message"]
/// [@ no_auto_projectors]
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FStarAttribute {
    /// Bracket style: `@`, `@@`, or `@@@`.
    pub style: AttributeStyle,
    /// Attribute name (e.g., "CInline", "Comment", "opaque_to_smt").
    pub name: String,
    /// Optional argument text after the attribute name.
    pub args: Option<String>,
}

/// Comprehensive list of all known F* attributes.
///
/// These are used with bracket syntax `[@@attr]` or `[@@"attr"]` on declarations.
/// Gathered from FStar compiler source, HACL*, EverParse, and Vale codebases.
///
/// Categories:
/// - **Extraction control**: inline_for_extraction, noextract, CInline, CMacro,
///   CPrologue, CEpilogue, CAbstractStruct, CConst, CNoInline, specialize,
///   noextract_to, substitute
/// - **SMT/verification**: opaque_to_smt, unfold, irreducible, strict_on_arguments,
///   resolve_implicits, override_resolve_implicits_handler
/// - **Equality**: noeq, unopteq
/// - **Erasure**: erasable
/// - **Deprecation/diagnostics**: deprecated, expect_failure, expect_lax_failure
/// - **Plugin**: plugin
/// - **Positivity**: strictly_positive, unused, effect_param
/// - **Projectors**: no_auto_projectors
/// - **Documentation**: Comment
/// - **Tactic hints**: va_qattr, qmodattr, postprocess_with, preprocess_with
/// - **Type class**: tcnorm, no_method
/// - **Other**: normalize_term, norm, admit_termination, must_erase_for_extraction,
///   unifier_hint_injective, default_effect
pub const KNOWN_FSTAR_ATTRIBUTES: &[&str] = &[
    // Extraction control (Karamel/C backend)
    "inline_for_extraction",
    "noextract",
    "CInline",
    "CMacro",
    "CPrologue",
    "CEpilogue",
    "CAbstractStruct",
    "CConst",
    "CNoInline",
    "specialize",
    "noextract_to",
    "substitute",
    // SMT and verification control
    "opaque_to_smt",
    "unfold",
    "irreducible",
    "strict_on_arguments",
    "resolve_implicits",
    "override_resolve_implicits_handler",
    // Equality modifiers (also usable as attributes)
    "noeq",
    "unopteq",
    // Erasure
    "erasable",
    // Deprecation and diagnostics
    "deprecated",
    "expect_failure",
    "expect_lax_failure",
    // Plugin system
    "plugin",
    // Positivity and effect parameters
    "strictly_positive",
    "unused",
    "effect_param",
    // Projectors
    "no_auto_projectors",
    // Documentation (Karamel generates C comments)
    "Comment",
    // Tactic and metaprogramming hints (Vale/HACL*)
    "va_qattr",
    "qmodattr",
    "postprocess_with",
    "preprocess_with",
    // Type class
    "tcnorm",
    "no_method",
    // Normalization and misc
    "normalize_term",
    "norm",
    "admit_termination",
    "must_erase_for_extraction",
    "unifier_hint_injective",
    "default_effect",
    // Reduction control (used in Vale)
    "va_qattr",
];

lazy_static! {
    /// HashSet for O(1) attribute lookup instead of O(n) linear scan.
    static ref KNOWN_FSTAR_ATTRIBUTES_SET: HashSet<&'static str> = {
        KNOWN_FSTAR_ATTRIBUTES.iter().copied().collect()
    };
}

/// Check if a name is a known F* attribute.
///
/// Uses O(1) HashSet lookup instead of linear scan.
pub fn is_known_fstar_attribute(name: &str) -> bool {
    KNOWN_FSTAR_ATTRIBUTES_SET.contains(name)
}

impl FStarAttribute {
    /// Whether this attribute is a known F* attribute.
    pub fn is_known(&self) -> bool {
        is_known_fstar_attribute(&self.name)
    }

    /// Whether this attribute controls extraction behavior (C code generation).
    pub fn is_extraction_attribute(&self) -> bool {
        matches!(
            self.name.as_str(),
            "inline_for_extraction"
                | "noextract"
                | "CInline"
                | "CMacro"
                | "CPrologue"
                | "CEpilogue"
                | "CAbstractStruct"
                | "CConst"
                | "CNoInline"
                | "specialize"
                | "noextract_to"
                | "substitute"
                | "must_erase_for_extraction"
        )
    }

    /// Whether this attribute controls SMT/verification behavior.
    pub fn is_verification_attribute(&self) -> bool {
        matches!(
            self.name.as_str(),
            "opaque_to_smt"
                | "unfold"
                | "irreducible"
                | "strict_on_arguments"
                | "resolve_implicits"
                | "override_resolve_implicits_handler"
                | "erasable"
        )
    }
}

/// SMT pattern used in lemma signatures to guide Z3 instantiation.
///
/// Examples from FStar/ulib:
/// ```text
/// [SMTPat (f x)]
/// [SMTPat (f x); SMTPat (g y)]
/// [SMTPatOr [[SMTPat (f x)]; [SMTPat (g x)]]]
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtPattern {
    /// `SMTPat (expr)` -- single trigger pattern.
    Pat(String),
    /// `SMTPatOr [[pats]; [pats]]` -- disjunctive pattern (multiple alternatives).
    PatOr(Vec<Vec<SmtPattern>>),
}

/// Tactic expression form found in F* code.
///
/// Tactics are used for proof automation and metaprogramming.
/// Real-world examples from FStar/ulib and HACL*:
/// ```text
/// _ by (FStar.Tactics.Canon.canon())
/// assert (big_and' f [] == True) by (T.compute())
/// synth_by_tactic (specialize (foo [1; 2]) [`%foo])
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TacticExpr {
    /// `assert <prop> by (<tactic>)` -- assert with tactic proof.
    AssertBy {
        assertion: String,
        tactic_body: String,
    },
    /// `_ by (<tactic>)` -- wildcard with tactic proof (in calc blocks or definitions).
    WildcardBy {
        tactic_body: String,
    },
    /// `synth_by_tactic (<tactic>)` -- synthesize a witness using a tactic.
    SynthByTactic {
        tactic_body: String,
    },
}

/// Backtick quotation form used in F* metaprogramming.
///
/// F* supports several quotation syntaxes for reflecting terms:
/// ```text
/// `name         -- quote an identifier (resolve to fv)
/// `%name        -- quote a top-level name (fully qualified)
/// `#expr        -- antiquotation (splice)
/// `(expr)       -- quote an expression
/// ```
///
/// Real examples from FStar/ulib:
/// ```text
/// delta_only [`%calc_chain_related]
/// norm [delta_only [`%on_domain]]
/// apply_lemma (`other_lemma)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Quotation {
    /// `` `name `` -- quote an identifier.
    Name(String),
    /// `` `%name `` -- quote a fully qualified name.
    QualifiedName(String),
    /// `` `#expr `` -- antiquotation (splice into quoted term).
    Antiquote(String),
    /// `` `(expr) `` -- quote an expression.
    Expr(String),
}

/// Types of top-level blocks in F* files.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BlockType {
    Module,
    Open,
    Friend,
    /// `include ModuleName` -- re-exports all definitions from the module.
    Include,
    /// `module M = Long.Module.Name` -- module abbreviation (alias).
    ModuleAbbrev,
    SetOptions,
    Val,
    Type,
    Let,
    Assume,
    /// Generic effect declaration: `effect`, `layered_effect`, `new_effect`.
    Effect,
    /// `new_effect { NAME : ... with ... }` -- WP-based effect with combinators.
    NewEffect,
    /// `sub_effect SRC ~> DST` -- effect lifting declaration.
    SubEffect,
    /// `effect Name (a:Type) ... = BASE a ...` -- effect abbreviation/synonym.
    EffectAbbrev,
    Class,
    Instance,
    Exception,
    UnfoldLet,
    InlineLet,
    Directive,
    Comment,
    Unknown,
}

/// A logical block in an F* file representing a single declaration
/// with its associated comments, options, and continuations.
#[derive(Debug, Clone)]
pub struct DeclarationBlock {
    pub block_type: BlockType,
    /// All names in this block (for mutual recursion).
    pub names: Vec<String>,
    /// All lines including leading comments, options.
    pub lines: Vec<String>,
    /// 1-indexed line number.
    pub start_line: usize,
    pub has_push_options: bool,
    pub has_pop_options: bool,
    /// Names this block references (potential dependencies).
    pub references: HashSet<String>,
    /// For module abbreviations: the target module path (e.g., "FStar.UInt32").
    /// For open/include/friend: the module being opened/included/friended.
    pub module_path: Option<String>,
    /// Whether this declaration has the `private` modifier.
    pub is_private: bool,
    /// Whether this declaration has the (deprecated) `abstract` modifier.
    pub is_abstract: bool,
    /// Parsed effect signature information (for val/let with effects, effect decls).
    pub effect_signature: Option<EffectSignature>,
}

impl DeclarationBlock {
    /// Create a new DeclarationBlock with default values for the module metadata fields.
    pub fn new(
        block_type: BlockType,
        names: Vec<String>,
        lines: Vec<String>,
        start_line: usize,
    ) -> Self {
        Self {
            block_type,
            names,
            lines,
            start_line,
            has_push_options: false,
            has_pop_options: false,
            references: HashSet::new(),
            module_path: None,
            is_private: false,
            is_abstract: false,
            effect_signature: None,
        }
    }

    /// Create a new DeclarationBlock with explicit references (for testing).
    pub fn new_with_refs(
        block_type: BlockType,
        names: Vec<String>,
        lines: Vec<String>,
        start_line: usize,
        references: HashSet<String>,
    ) -> Self {
        Self {
            block_type,
            names,
            lines,
            start_line,
            has_push_options: false,
            has_pop_options: false,
            references,
            module_path: None,
            is_private: false,
            is_abstract: false,
            effect_signature: None,
        }
    }
}

impl DeclarationBlock {
    /// Primary name (first in list) for compatibility.
    pub fn name(&self) -> Option<&str> {
        self.names.first().map(|s| s.as_str())
    }

    /// Return the full text of this block.
    pub fn text(&self) -> String {
        self.lines.concat()
    }
}

lazy_static! {
    // F* identifier pattern - identifiers can contain apostrophes (primes)
    // Examples: expr', pattern', expr'_size, type_name
    static ref FSTAR_IDENT: &'static str = r"[a-zA-Z_][\w']*";

    // Declaration patterns - order matters: more specific patterns first
    // CRITICAL: Top-level F* declarations ALWAYS start at column 0
    static ref VAL_PATTERN: Regex = Regex::new(
        &format!(r"^(?:private\s+)?val\s+(?:\(([^)]+)\)|({}))", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    static ref ASSUME_VAL_PATTERN: Regex = Regex::new(
        &format!(r"^assume\s+val\s+(?:\(([^)]+)\)|({}))", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    static ref ASSUME_TYPE_PATTERN: Regex = Regex::new(
        &format!(r"^assume\s+type\s+({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    static ref TYPE_PATTERN: Regex = Regex::new(
        &format!(r"^(?:private\s+)?(?:(?:noeq|unopteq)\s+)?(?:abstract\s+)?type\s+({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    static ref UNFOLD_LET_PATTERN: Regex = Regex::new(
        &format!(r"^(?:\[@[^\]]*\]\s*)*(?:private\s+)?unfold\s+(?:inline_for_extraction\s+)?let\s+({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    static ref INLINE_LET_PATTERN: Regex = Regex::new(
        &format!(r"^(?:\[@[^\]]*\]\s*)*(?:private\s+)?inline_for_extraction\s+(?:noextract\s+)?(?:unfold\s+)?let\s+({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    static ref LET_REC_PATTERN: Regex = Regex::new(
        &format!(r"^(?:\[@[^\]]*\]\s*)*(?:private\s+)?let\s+rec\s+({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Match regular let bindings, including ghost let
    // The ghost modifier makes the binding erased at extraction
    static ref LET_PATTERN: Regex = Regex::new(
        &format!(r"^(?:\[@[^\]]*\]\s*)*(?:private\s+)?(?:ghost\s+)?let\s+({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Effect abbreviation: `effect Name (a:Type) ... = BASE a ...`
    // e.g., `effect Stack (a:Type) (pre:st_pre) (post:...) = STATE a ...`
    // Also matches: `effect Dv (a: Type) = DIV a (pure_null_wp a)`
    // Must come BEFORE the generic effect pattern to capture the name.
    static ref EFFECT_ABBREV_PATTERN: Regex = Regex::new(
        &format!(r"^effect\s+({})\s", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Layered effect: `layered_effect { NAME : ... }`
    static ref LAYERED_EFFECT_PATTERN: Regex = Regex::new(
        &format!(r"^layered_effect\s+\{{\s*({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Generic effect pattern (covers `effect {{ NAME ... }}` for layered effects
    // without the `layered_effect` keyword, e.g., `reflectable\neffect {{ ... }}`)
    // Also covers old-style `effect NAME ...` when followed by braces
    static ref EFFECT_PATTERN: Regex = Regex::new(
        &format!(r"^(?:layered_)?effect\s+({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Reflectable/reifiable effect: `reflectable\neffect {{ ... }}`
    // The modifier may appear on its own line or on the same line as `effect`.
    static ref REFLECTABLE_EFFECT_PATTERN: Regex = Regex::new(
        r"^reflectable\s*$"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    static ref REIFIABLE_EFFECT_PATTERN: Regex = Regex::new(
        r"^reifiable\s*$"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // `new_effect { NAME : ... with ... }` -- WP-based effect definition
    // Also matches `new_effect NAME = BASE` (simple derivation)
    static ref NEW_EFFECT_PATTERN: Regex = Regex::new(
        &format!(r"^new_effect\s+\{{?\s*({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // `total_effect { NAME : ... }` (rare, used in Prims.fst)
    static ref TOTAL_EFFECT_PATTERN: Regex = Regex::new(
        &format!(r"^total_effect\s+\{{?\s*({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // `sub_effect SRC ~> DST = ...` or `sub_effect SRC ~> DST { lift_wp = ... }`
    // Captures source and destination effect names
    static ref SUB_EFFECT_PATTERN: Regex = Regex::new(
        r"^sub_effect\s+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // More detailed sub_effect pattern to capture source and destination names
    static ref SUB_EFFECT_DETAIL_PATTERN: Regex = Regex::new(
        &format!(r"^sub_effect\s+({})\s*~>\s*({})", *FSTAR_IDENT, *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    static ref CLASS_PATTERN: Regex = Regex::new(
        &format!(r"^class\s+({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    static ref INSTANCE_PATTERN: Regex = Regex::new(
        &format!(r"^instance\s+({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    static ref EXCEPTION_PATTERN: Regex = Regex::new(
        &format!(r"^exception\s+({})", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern for 'and' continuation in mutual recursion
    static ref AND_PATTERN: Regex = Regex::new(
        &format!(r"^and\s+(?:\(([^)]+)\)|({}))", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Pattern for inline 'and' within a single line (e.g., "type A = ... and B = ...")
    // Used to extract additional names from mutual recursion on a single line
    static ref INLINE_AND_PATTERN: Regex = Regex::new(
        &format!(r"\band\s+(?:\(([^)]+)\)|({}))\s*=", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Header patterns (kept at top, not reordered)
    static ref MODULE_PATTERN: Regex = Regex::new(r"^module\s+").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref OPEN_PATTERN: Regex = Regex::new(r"^open\s+").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref FRIEND_PATTERN: Regex = Regex::new(r"^friend\s+").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref INCLUDE_PATTERN: Regex = Regex::new(r"^include\s+").unwrap_or_else(|e| panic!("regex: {e}"));

    // Module abbreviation: `module M = Long.Module.Name`
    // Captures: (1) alias name, (2) target qualified path
    static ref MODULE_ABBREV_PATTERN: Regex = Regex::new(
        &format!(r"^module\s+({})\s*=\s*([\w.]+)", *FSTAR_IDENT)
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Qualified module path: captures a dotted identifier like `FStar.Seq.Base`
    static ref QUALIFIED_MODULE_PATH: Regex = Regex::new(
        r"^([\w.]+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Open with module path: `open FStar.HyperStack.ST`
    static ref OPEN_MODULE_PATTERN: Regex = Regex::new(
        r"^open\s+([\w.]+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Friend with module path: `friend Hacl.Spec.Bignum.ModInvLimb`
    static ref FRIEND_MODULE_PATTERN: Regex = Regex::new(
        r"^friend\s+([\w.]+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Include with module path: `include Hacl.Hash.Core.SHA1`
    static ref INCLUDE_MODULE_PATTERN: Regex = Regex::new(
        r"^include\s+([\w.]+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Option directive patterns
    static ref PUSH_OPTIONS: Regex = Regex::new(r"^#push-options\s").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref POP_OPTIONS: Regex = Regex::new(r"^#pop-options").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref SET_OPTIONS: Regex = Regex::new(r"^#set-options\s").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref RESET_OPTIONS: Regex = Regex::new(r"^#reset-options").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref RESTART_SOLVER: Regex = Regex::new(r"^#restart-solver").unwrap_or_else(|e| panic!("regex: {e}"));

    // Debug command patterns: `#check`, `#normalize`
    // These are F* compiler debug commands that appear at the top level.
    static ref CHECK_COMMAND: Regex = Regex::new(r"^#check\b").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref NORMALIZE_COMMAND: Regex = Regex::new(r"^#normalize\b").unwrap_or_else(|e| panic!("regex: {e}"));

    // Attribute patterns for declarations:
    //   [@ attr]        -- old-style single attribute
    //   [@@ attr]       -- declaration attribute (F* 2.x)
    //   [@@@ attr]      -- binder attribute (on parameters)
    //   [@@ attr1; attr2] -- multiple attributes
    //   [@@(strict_on_arguments [1;2])] -- nested brackets in args
    // These appear on their own line before a val/let/type declaration.
    // Uses .* to allow nested brackets inside the attribute body.
    static ref STANDALONE_ATTRIBUTE: Regex = Regex::new(
        r"^\[@@?@?.*\]\s*$"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Multi-line attribute start: `[@@ Comment` or `[@@ attr` without closing `]`.
    // Real-world example from HACL*:
    //   [@@ Comment "Write the HMAC-MD5 MAC ..."
    //   "continues on next line."]
    static ref MULTILINE_ATTRIBUTE_START: Regex = Regex::new(
        r"^\[@@?@?\s"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // Type reference pattern for dependency extraction
    // CRITICAL: F* identifiers can contain apostrophes (e.g., expr', pattern')
    // Uses fancy-regex for lookahead/lookbehind support
    // CRITICAL: The '.' in the negative lookbehind prevents matching qualified name
    // components (e.g., in `S.bn_add`, only `S` matches, not `bn_add`).
    // Without this, qualified references like `Module.name` would create false
    // dependencies on locally declared `name`, causing spurious forward-reference
    // warnings in FST002.
    static ref TYPE_REF_PATTERN: fancy_regex::Regex = fancy_regex::Regex::new(
        r"(?<![a-zA-Z0-9_'.])([A-Z][\w']*|[a-z_][\w']*)(?![a-zA-Z0-9_'])"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // F* keywords to exclude from dependency analysis
    // CRITICAL: This list must be comprehensive to avoid false positive dependencies
    static ref FSTAR_KEYWORDS: HashSet<&'static str> = {
        let mut s = HashSet::new();
        // Declaration keywords
        for kw in &["val", "let", "rec", "type", "noeq", "and", "with", "match",
                    "module", "open", "friend", "include",
                    "effect", "layered_effect", "new_effect", "sub_effect", "total_effect",
                    "class", "instance", "exception",
                    "assume", "private", "abstract", "unfold", "irreducible",
                    "inline_for_extraction", "noextract", "opaque_to_smt",
                    "reifiable", "reflectable", "ghost"] {
            s.insert(*kw);
        }
        // Control flow keywords
        for kw in &["if", "then", "else", "begin", "end",
                    "fun", "function", "return", "yield",
                    "in", "of", "when", "as", "try"] {
            s.insert(*kw);
        }
        // Logic/quantifier keywords
        for kw in &["forall", "exists", "True", "False", "true", "false",
                    "not", "mod", "div", "land", "lor", "lxor"] {
            s.insert(*kw);
        }
        // Type-related keywords and built-in effect names
        for kw in &["prop", "Type", "Type0", "Type1", "eqtype", "squash",
                    // Effect names (F* built-in effect hierarchy)
                    "Tot", "GTot", "Lemma", "Pure", "Ghost",
                    "ST", "Stack", "STATE", "State", "Heap",
                    "Dv", "Div", "DIV",
                    "Exn", "Ex", "EXN",
                    "All", "ALL", "ML",
                    "PURE", "GHOST",
                    "Tac", "TAC", "TacH",
                    "StackInline", "Inline", "Unsafe", "St", "STL",
                    // Effect combinators (used in new_effect/layered_effect bodies)
                    "repr", "return_wp", "bind_wp",
                    "if_then_else", "ite_wp", "stronger",
                    "close_wp", "trivial",
                    "subcomp", "close",
                    "lift_wp",
                    // Effect specification keywords
                    "requires", "ensures", "returns", "decreases", "modifies",
                    "assert", "admit", "calc",
                    // Refinement/logic keywords
                    "Effect", "wp"] {
            s.insert(*kw);
        }
        // Tactic and metaprogramming keywords
        // These appear inside `_ by (...)`, `assert ... by (...)`,
        // `synth_by_tactic (...)`, and tactic definitions.
        for kw in &["by", "synth_by_tactic",
                    // Core tactic combinators (FStar.Tactics.V2.Builtins / Derived)
                    "dump", "smt", "trefl", "compute",
                    "tadmit", "exact", "apply", "apply_lemma",
                    "intro", "intros", "rewrite", "mapply",
                    "norm", "norm_term", "normalize",
                    "or_else", "try_with", "repeat", "first",
                    "cur_env", "cur_goal", "cur_witness",
                    "l_to_r", "pointwise", "topdown",
                    "assumption", "dismiss", "flip", "qed",
                    "split", "left", "right",
                    "implies_intro", "squash_intro",
                    "grewrite", "rename_to",
                    // Reflection / quotation keywords
                    "quote", "unquote", "pack", "inspect",
                    // Normalization steps (used inside norm [...])
                    "delta", "delta_only", "delta_attr",
                    "delta_qualifier", "delta_namespace",
                    "zeta", "zeta_full", "iota", "primops", "simplify",
                    // SMT pattern keywords
                    "SMTPat", "SMTPatOr",
                    // Attribute identifiers commonly used with [@@...]
                    "CInline", "CMacro", "CPrologue", "CEpilogue",
                    "CNoInline", "specialize", "erasable",
                    "no_prelude", "admitted", "do_not_unrefine",
                    "strict_on_arguments", "resolve_implicits",
                    "override_resolve_implicits_handler",
                    "strictly_positive", "unused", "effect_param",
                    "deprecated", "noextract_to"] {
            s.insert(*kw);
        }
        // F* built-in primitive types
        for kw in &["unit", "bool", "int", "nat", "pos", "string", "char"] {
            s.insert(*kw);
        }
        // Standard library types
        for kw in &["option", "list", "either", "ref", "seq", "set", "map"] {
            s.insert(*kw);
        }
        // Module prefixes
        for kw in &["FStar", "Prims"] {
            s.insert(*kw);
        }
        // Common constructors
        for kw in &["Some", "None", "Cons", "Nil", "Inl", "Inr"] {
            s.insert(*kw);
        }
        s
    };

    // F* operator character to function name component mapping
    // In F*, operator `@%.` resolves to function `op_At_Percent_Dot`
    static ref FSTAR_OP_CHARS: HashMap<char, &'static str> = {
        let mut m = HashMap::new();
        m.insert('@', "At");
        m.insert('%', "Percent");
        m.insert('.', "Dot");
        m.insert('+', "Plus");
        m.insert('-', "Minus");
        m.insert('*', "Star");
        m.insert('/', "Slash");
        m.insert('<', "Less");
        m.insert('>', "Greater");
        m.insert('=', "Equals");
        m.insert('!', "Bang");
        m.insert('|', "Bar");
        m.insert('&', "Amp");
        m.insert('^', "Hat");
        m.insert('~', "Tilde");
        m.insert('?', "Qmark");
        m.insert(':', "Colon");
        m.insert('$', "Dollar");
        m
    };

    // Pattern to match F* custom operators (sequences of operator chars)
    // These appear in expressions like `(a + b) @%. it` or `x |> f`
    // Uses fancy_regex for lookbehind support
    static ref FSTAR_OP_PATTERN: fancy_regex::Regex = fancy_regex::Regex::new(
        r"(?<![a-zA-Z0-9_])\s([!@#$%^&*+\-/|<>=~?:.]+)\s"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Pragma parsing patterns
    // =========================================================================

    /// Extracts the quoted option string from `#set-options "..."`.
    static ref SET_OPTIONS_VALUE: Regex = Regex::new(
        r#"^#set-options\s+"([^"]*)""#
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Extracts the quoted option string from `#push-options "..."`.
    static ref PUSH_OPTIONS_VALUE: Regex = Regex::new(
        r#"^#push-options\s+"([^"]*)""#
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Extracts the optional quoted option string from `#reset-options` or `#reset-options "..."`.
    static ref RESET_OPTIONS_VALUE: Regex = Regex::new(
        r#"^#reset-options(?:\s+"([^"]*)")?"#
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Attribute parsing patterns
    // =========================================================================

    /// Parse attribute content from `[@ content]`, `[@@ content]`, or `[@@@ content]`.
    /// Captures: (1) the @-prefix, (2) the attribute body.
    static ref ATTRIBUTE_CONTENT: Regex = Regex::new(
        r"^\[(@{1,3})\s*(.*)\]\s*$"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Parse a single attribute name and optional args from attribute body.
    /// Handles both quoted (`"opaque_to_smt"`) and unquoted (`CInline`) names.
    /// Captures: (1) quoted name or (2) unquoted name, (3) rest as args.
    static ref ATTRIBUTE_NAME: Regex = Regex::new(
        r#"^(?:"([^"]+)"|([A-Za-z_][\w']*))\s*(.*)?$"#
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // SMT pattern parsing patterns
    // =========================================================================

    /// Matches `SMTPat (expr)` -- captures the expression inside parens.
    /// Uses balanced-paren tracking externally; this just finds the start.
    static ref SMTPAT_START: Regex = Regex::new(
        r"\bSMTPat\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches `SMTPatOr` keyword.
    static ref SMTPATOR_START: Regex = Regex::new(
        r"\bSMTPatOr\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Finds the outermost SMT pattern list: `[SMTPat (...); SMTPat (...)]` or `[SMTPatOr [...]]`.
    /// This captures the bracketed suffix of a val/lemma signature.
    static ref SMT_PATTERN_BRACKET: Regex = Regex::new(
        r"\[\s*SMT(?:Pat|PatOr)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Tactic expression parsing patterns
    // =========================================================================

    /// Matches `assert <stuff> by (` -- the start of an assert-by-tactic.
    /// Captures: (1) the assertion expression between assert and by.
    static ref ASSERT_BY_PATTERN: Regex = Regex::new(
        r"\bassert\b\s*((?:\([^)]*\)|[^;])*?)\s*\bby\b\s*\("
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches `_ by (` -- wildcard-by-tactic (in calc blocks or definitions).
    static ref WILDCARD_BY_PATTERN: Regex = Regex::new(
        r"\b_\s+by\s*\("
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches `synth_by_tactic (` -- synthesize via tactic.
    static ref SYNTH_BY_TACTIC_PATTERN: Regex = Regex::new(
        r"\bsynth_by_tactic\s*\("
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Quotation parsing patterns
    // =========================================================================

    /// Matches backtick quotation forms in F* metaprogramming:
    ///   `%name  -- quote fully qualified name (e.g., `%calc_chain_related)
    ///   `#expr  -- antiquotation
    ///   `(expr) -- quote expression
    ///   `name   -- quote identifier
    ///
    /// Uses fancy_regex for lookbehind to avoid matching backticks inside strings
    /// or after other identifier characters.
    static ref QUOTATION_PATTERN: fancy_regex::Regex = fancy_regex::Regex::new(
        r"(?<![a-zA-Z0-9_'])`(%[A-Za-z_][\w'.]*|#[A-Za-z_][\w'.]*|\([^)]*\)|[A-Za-z_][\w'.]*)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));
}

/// Check if a trimmed string starts with a keyword followed by whitespace.
/// Byte-level check avoids regex overhead for simple `^keyword\s+` patterns.
#[inline(always)]
fn starts_with_keyword(s: &str, keyword: &str) -> bool {
    if s.len() <= keyword.len() {
        return false;
    }
    let bytes = s.as_bytes();
    bytes[..keyword.len()] == *keyword.as_bytes()
        && (bytes[keyword.len()] == b' ' || bytes[keyword.len()] == b'\t')
}

/// Check if a trimmed string starts with a keyword and the rest is
/// either empty or starts with whitespace (for `^keyword\b`-style patterns).
///
/// Uses `str::starts_with` instead of byte slicing to avoid panics on
/// multi-byte UTF-8 characters (e.g., `λ`, `≡` in comments).
#[inline(always)]
fn starts_with_keyword_boundary(s: &str, keyword: &str) -> bool {
    if !s.starts_with(keyword) {
        return false;
    }
    if s.len() == keyword.len() {
        return true;
    }
    // keyword is always ASCII, so byte indexing at keyword.len() is safe:
    // starts_with succeeded, meaning the first keyword.len() bytes are valid
    // ASCII (matching keyword), so the byte at keyword.len() is a valid char
    // boundary.
    let next = s.as_bytes()[keyword.len()];
    // Not an identifier continuation character
    !next.is_ascii_alphanumeric() && next != b'_'
}

/// Check if line is a header-like construct (module/open/friend/include/module-abbrev).
/// Returns BlockType or None.
/// Header lines must start at column 0 (no leading whitespace).
pub fn is_header_line(line: &str) -> Option<BlockType> {
    // Header lines must not have leading whitespace
    if line.starts_with(' ') || line.starts_with('\t') {
        return None;
    }
    let stripped = line.trim();
    // Module abbreviation must be checked BEFORE generic module pattern.
    // MODULE_ABBREV_PATTERN is `^module\s+IDENT\s*=\s*[\w.]+` -- needs regex for `=` check.
    if starts_with_keyword(stripped, "module") {
        if MODULE_ABBREV_PATTERN.is_match(stripped) {
            return Some(BlockType::ModuleAbbrev);
        }
        return Some(BlockType::Module);
    }
    if starts_with_keyword(stripped, "open") {
        return Some(BlockType::Open);
    }
    if starts_with_keyword(stripped, "include") {
        return Some(BlockType::Include);
    }
    if starts_with_keyword(stripped, "friend") {
        return Some(BlockType::Friend);
    }
    None
}

/// Extract module system info from a header-like line.
///
/// Returns (block_type, primary_name, module_path) for:
/// - `module M = FStar.UInt32`     -> (ModuleAbbrev, "M", Some("FStar.UInt32"))
/// - `module Hacl.Streaming.MD`    -> (Module, "Hacl.Streaming.MD", None)
/// - `open FStar.HyperStack.ST`    -> (Open, "FStar.HyperStack.ST", Some("FStar.HyperStack.ST"))
/// - `friend Hacl.Spec.Bignum`     -> (Friend, "Hacl.Spec.Bignum", Some("Hacl.Spec.Bignum"))
/// - `include Hacl.Hash.Core.SHA1` -> (Include, "Hacl.Hash.Core.SHA1", Some("Hacl.Hash.Core.SHA1"))
pub fn extract_module_construct_info(line: &str) -> Option<(BlockType, String, Option<String>)> {
    if line.starts_with(' ') || line.starts_with('\t') {
        return None;
    }
    let stripped = line.trim();

    // Early exit by first character to avoid running all regex patterns
    let first = stripped.as_bytes().first().copied()?;
    match first {
        b'm' if starts_with_keyword(stripped, "module") => {
            // Module abbreviation: `module M = Long.Module.Name`
            if let Some(caps) = MODULE_ABBREV_PATTERN.captures(stripped) {
                let alias = caps.get(1).map(|m| m.as_str().to_string()).unwrap_or_default();
                let target = caps.get(2).map(|m| m.as_str().to_string());
                return Some((BlockType::ModuleAbbrev, alias, target));
            }
            // Module declaration: `module Long.Module.Name`
            if let Some(caps) = MODULE_DECL_RE.captures(stripped) {
                let name = caps.get(1).map(|m| m.as_str().to_string()).unwrap_or_default();
                return Some((BlockType::Module, name, None));
            }
        }
        b'o' if starts_with_keyword(stripped, "open") => {
            if let Some(caps) = OPEN_MODULE_PATTERN.captures(stripped) {
                let path = caps.get(1).map(|m| m.as_str()).unwrap_or_default();
                return Some((BlockType::Open, path.to_string(), Some(path.to_string())));
            }
        }
        b'i' if starts_with_keyword(stripped, "include") => {
            if let Some(caps) = INCLUDE_MODULE_PATTERN.captures(stripped) {
                let path = caps.get(1).map(|m| m.as_str()).unwrap_or_default();
                return Some((BlockType::Include, path.to_string(), Some(path.to_string())));
            }
        }
        b'f' if starts_with_keyword(stripped, "friend") => {
            if let Some(caps) = FRIEND_MODULE_PATTERN.captures(stripped) {
                let path = caps.get(1).map(|m| m.as_str()).unwrap_or_default();
                return Some((BlockType::Friend, path.to_string(), Some(path.to_string())));
            }
        }
        _ => {}
    }
    None
}

/// Check if line is a standalone #set-options at file level.
///
/// Also recognizes `#check` and `#normalize` debug commands, which are
/// F* compiler directives that appear at the top level alongside options.
pub fn is_standalone_options(line: &str) -> bool {
    let stripped = line.trim();
    starts_with_keyword(stripped, "#set-options")
        || starts_with_keyword_boundary(stripped, "#reset-options")
        || starts_with_keyword_boundary(stripped, "#restart-solver")
        || starts_with_keyword_boundary(stripped, "#check")
        || starts_with_keyword_boundary(stripped, "#normalize")
}

/// Check if line is #push-options.
pub fn is_push_options(line: &str) -> bool {
    starts_with_keyword(line.trim(), "#push-options")
}

/// Check if line is #pop-options.
pub fn is_pop_options(line: &str) -> bool {
    starts_with_keyword_boundary(line.trim(), "#pop-options")
}

/// Check if line is a standalone attribute on its own line.
///
/// In F*, attributes can appear on their own line before a declaration:
/// ```text
/// [@@"opaque_to_smt"]
/// val foo : int -> int
///
/// [@@ __reduce__]
/// let helper x = x + 1
///
/// [@ CNoInline ]
/// val expensive_fn : int -> int
/// ```
///
/// These should be accumulated as pending lines and attached to the
/// subsequent declaration, just like standalone modifiers.
pub fn is_standalone_attribute(line: &str) -> bool {
    if line.starts_with(' ') || line.starts_with('\t') {
        return false;
    }
    let s = line.trim();
    // Manual match for `^\[@@?@?.*\]\s*$`: starts with `[@`, ends with `]`
    // after trimming. The `@?@?` means 1-3 `@` chars after `[`.
    // Minimum is `[@]` (3 chars).
    let bytes = s.as_bytes();
    if bytes.len() < 3 {
        return false;
    }
    bytes[0] == b'[' && bytes[1] == b'@' && bytes[bytes.len() - 1] == b']'
}

/// Check if a line starts a multi-line attribute (opening `[@@` without closing `]`).
///
/// Real-world example from HACL* (`Hacl.Streaming.SHA2.fst`):
/// ```text
/// [@@ Comment "Write the HMAC-MD5 MAC of a message (`data`)
/// by using a key (`key`) into `dst`.
/// `dst` must point to 16 bytes of memory."]
/// val compute_md5 : ...
/// ```
pub fn is_multiline_attribute_start(line: &str) -> bool {
    if line.starts_with(' ') || line.starts_with('\t') {
        return false;
    }
    let stripped = line.trim();
    let bytes = stripped.as_bytes();
    // Must start with `[@` followed by optional `@`s then whitespace, and NOT end with `]`
    if bytes.len() < 4 || bytes[0] != b'[' || bytes[1] != b'@' {
        return false;
    }
    // Skip additional `@` chars
    let mut pos = 2;
    while pos < bytes.len() && bytes[pos] == b'@' {
        pos += 1;
    }
    // Must be followed by whitespace
    pos < bytes.len() && bytes[pos].is_ascii_whitespace() && bytes[bytes.len() - 1] != b']'
}

/// Check if a line is a `//` single-line comment at column 0.
///
/// F* supports `//` line comments (in addition to `(* ... *)` block comments).
/// These appear frequently in HACL* test files as section dividers.
pub fn is_line_comment(line: &str) -> bool {
    let bytes = line.as_bytes();
    // Skip leading whitespace at byte level
    let mut i = 0;
    while i < bytes.len() && (bytes[i] == b' ' || bytes[i] == b'\t') {
        i += 1;
    }
    i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/'
}

/// Extract declaration name from regex captures.
fn extract_name_from_captures(caps: &regex::Captures) -> Option<String> {
    for i in 1..=caps.len() {
        if let Some(m) = caps.get(i) {
            let name = m.as_str().trim();
            // Clean up name - remove type annotations
            let name = name.split(':').next().unwrap_or(name);
            let name = name.split('(').next().unwrap_or(name).trim();
            // Handle special cases like 'unfold' appearing as name
            if matches!(
                name,
                "unfold" | "inline_for_extraction" | "noextract" | "rec"
            ) {
                continue;
            }
            if !name.is_empty() {
                return Some(name.to_string());
            }
        }
    }
    None
}

/// Extract declaration info from a line.
///
/// CRITICAL: Top-level F* declarations ALWAYS start at column 0.
/// Lines with leading whitespace are CONTINUATION lines, not new declarations.
///
/// Returns `(name, block_type)` for recognized declarations.
/// Also handles mid-file module system constructs: `open`, `friend`, `include`,
/// `module M = Path` which can appear anywhere in an F* file.
pub fn get_declaration_info(line: &str) -> Option<(String, BlockType)> {
    // CRITICAL FIX: Top-level declarations never have leading whitespace.
    let first = line.as_bytes().first().copied()?;
    if first == b' ' || first == b'\t' {
        return None;
    }

    let stripped = line.trim();
    let bytes = stripped.as_bytes();
    if bytes.is_empty() {
        return None;
    }

    // Skip if line is a comment or directive -- byte-level first-char check
    match bytes[0] {
        b'(' if bytes.len() > 1 && bytes[1] == b'*' => return None,
        b'#' => return None,
        b'/' if bytes.len() > 1 && bytes[1] == b'/' => return None,
        _ => {}
    }

    // Route by first character to avoid trying all 16+ regex patterns.
    // F* declarations start with: val, let, type, assume, unfold, inline_for_extraction,
    // effect, layered_effect, new_effect, sub_effect, class, instance, exception,
    // module, open, friend, include, private, abstract, ghost, noeq, unopteq, [@@...
    match bytes[0] {
        b'm' if starts_with_keyword(stripped, "module") => {
            // Module abbreviation: `module M = Long.Module.Name`
            if let Some(caps) = MODULE_ABBREV_PATTERN.captures(stripped) {
                if let Some(m) = caps.get(1) {
                    return Some((m.as_str().to_string(), BlockType::ModuleAbbrev));
                }
            }
            return None; // Bare module decl is handled in header
        }
        b'i' if starts_with_keyword(stripped, "include") => {
            if let Some(caps) = INCLUDE_MODULE_PATTERN.captures(stripped) {
                let path = caps.get(1).map(|m| m.as_str()).unwrap_or("include");
                return Some((path.to_string(), BlockType::Include));
            }
            return Some(("include".to_string(), BlockType::Include));
        }
        b'i' if starts_with_keyword(stripped, "instance") => {
            if let Some(caps) = INSTANCE_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Instance));
            }
        }
        b'a' if starts_with_keyword(stripped, "assume") => {
            // assume val or assume type
            if let Some(caps) = ASSUME_VAL_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Assume));
            }
            if let Some(caps) = ASSUME_TYPE_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Assume));
            }
        }
        b'v' if starts_with_keyword(stripped, "val") => {
            if let Some(caps) = VAL_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Val));
            }
        }
        b't' if starts_with_keyword(stripped, "type") => {
            if let Some(caps) = TYPE_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Type));
            }
        }
        b'l' if starts_with_keyword(stripped, "let") => {
            // let rec before let
            if let Some(caps) = LET_REC_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Let));
            }
            if let Some(caps) = LET_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Let));
            }
        }
        b'l' if starts_with_keyword(stripped, "layered_effect") => {
            if let Some(caps) = LAYERED_EFFECT_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Effect));
            }
        }
        b'e' if starts_with_keyword(stripped, "effect") => {
            if let Some(caps) = EFFECT_ABBREV_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::EffectAbbrev));
            }
            if let Some(caps) = EFFECT_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Effect));
            }
        }
        b'e' if starts_with_keyword(stripped, "exception") => {
            if let Some(caps) = EXCEPTION_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Exception));
            }
        }
        b'n' if starts_with_keyword(stripped, "new_effect") => {
            if let Some(caps) = NEW_EFFECT_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::NewEffect));
            }
            return Some(("new_effect".to_string(), BlockType::NewEffect));
        }
        b't' if starts_with_keyword(stripped, "total_effect") => {
            if let Some(caps) = TOTAL_EFFECT_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::NewEffect));
            }
        }
        b's' if starts_with_keyword(stripped, "sub_effect") || stripped == "sub_effect" => {
            if let Some(caps) = SUB_EFFECT_DETAIL_PATTERN.captures(stripped) {
                let src = caps.get(1).map(|m| m.as_str()).unwrap_or("?");
                let dst = caps.get(2).map(|m| m.as_str()).unwrap_or("?");
                let mut name = String::with_capacity(src.len() + 3 + dst.len());
                name.push_str(src);
                name.push_str("~>");
                name.push_str(dst);
                return Some((name, BlockType::SubEffect));
            }
            return Some(("sub_effect".to_string(), BlockType::SubEffect));
        }
        b'c' if starts_with_keyword(stripped, "class") => {
            if let Some(caps) = CLASS_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Class));
            }
        }
        b'u' if starts_with_keyword(stripped, "unfold") => {
            if let Some(caps) = UNFOLD_LET_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::UnfoldLet));
            }
        }
        b'i' if starts_with_keyword(stripped, "inline_for_extraction") => {
            if let Some(caps) = INLINE_LET_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::InlineLet));
            }
        }
        b'p' if starts_with_keyword(stripped, "private") => {
            // private val / private let / private type / private unfold let ...
            // Strip "private " and recurse on the remainder
            let rest = stripped["private".len()..].trim_start();
            // Try all private-prefixed patterns
            for (pattern, bt) in &[
                (&*VAL_PATTERN, BlockType::Val),
                (&*TYPE_PATTERN, BlockType::Type),
                (&*UNFOLD_LET_PATTERN, BlockType::UnfoldLet),
                (&*INLINE_LET_PATTERN, BlockType::InlineLet),
                (&*LET_REC_PATTERN, BlockType::Let),
                (&*LET_PATTERN, BlockType::Let),
            ] {
                if let Some(caps) = pattern.captures(stripped) {
                    return extract_name_from_captures(&caps).map(|n| (n, *bt));
                }
            }
            // Try the rest as a keyword
            if starts_with_keyword(rest, "val")
                || starts_with_keyword(rest, "let")
                || starts_with_keyword(rest, "type")
            {
                // Fallthrough to regex
            }
        }
        b'g' if starts_with_keyword(stripped, "ghost") => {
            // ghost let ...
            if let Some(caps) = LET_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Let));
            }
        }
        b'n' if starts_with_keyword(stripped, "noeq") || starts_with_keyword(stripped, "noextract") => {
            // noeq type ... or noextract let ...
            if let Some(caps) = TYPE_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Type));
            }
            if let Some(caps) = INLINE_LET_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::InlineLet));
            }
        }
        b'r' if stripped == "reflectable" || stripped == "reifiable" => {
            // These are standalone modifiers, not declarations
            return None;
        }
        b'[' if bytes.len() > 1 && bytes[1] == b'@' => {
            // Attribute-prefixed declaration: [@@...] let/val/type ...
            // Try attribute-prefixed patterns
            for (pattern, bt) in &[
                (&*UNFOLD_LET_PATTERN, BlockType::UnfoldLet),
                (&*INLINE_LET_PATTERN, BlockType::InlineLet),
                (&*LET_REC_PATTERN, BlockType::Let),
                (&*LET_PATTERN, BlockType::Let),
            ] {
                if let Some(caps) = pattern.captures(stripped) {
                    return extract_name_from_captures(&caps).map(|n| (n, *bt));
                }
            }
        }
        b'u' if starts_with_keyword(stripped, "unopteq") => {
            if let Some(caps) = TYPE_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Type));
            }
        }
        b'a' if starts_with_keyword(stripped, "abstract") => {
            if let Some(caps) = TYPE_PATTERN.captures(stripped) {
                return extract_name_from_captures(&caps).map(|n| (n, BlockType::Type));
            }
        }
        _ => {}
    }

    None
}

/// Check if a line is a standalone modifier prefix that precedes a declaration
/// on the next line.
///
/// In real F* code, modifiers like `inline_for_extraction noextract` or
/// `private` often appear on their own line before the actual `let`/`val`/`type`.
/// Standalone attribute lines like `[@@"opaque_to_smt"]` or `[@ CNoInline ]`
/// also qualify as modifiers.
///
/// Examples:
/// ```text
/// inline_for_extraction noextract
/// let uint8 = Lib.IntTypes.uint8
///
/// private unfold
/// let helper x = x + 1
///
/// noextract
/// val internal_fn : int -> int
///
/// [@@"opaque_to_smt"]
/// val foo : int -> int
///
/// [@ CNoInline ]
/// val bar : int -> int
/// ```
pub fn is_standalone_modifier(line: &str) -> bool {
    if line.starts_with(' ') || line.starts_with('\t') {
        return false;
    }
    let stripped = line.trim();

    // Check for standalone attribute lines: [@@...], [@...], [@@@...]
    if is_standalone_attribute(line) {
        return true;
    }

    // Check against known standalone modifier strings.
    // Also handles multi-word combos like `private noextract inline_for_extraction`.
    // Strategy: split the line into whitespace-separated tokens and verify ALL
    // tokens are valid modifier keywords (no stray identifiers).
    static MODIFIER_TOKENS: &[&str] = &[
        "inline_for_extraction",
        "noextract",
        "private",
        "abstract",
        "irreducible",
        "opaque_to_smt",
        "unfold",
        "noeq",
        "reflectable",
        "reifiable",
        "ghost",
        "total",
    ];

    let tokens: Vec<&str> = stripped.split_whitespace().collect();
    if tokens.is_empty() {
        return false;
    }
    tokens.iter().all(|t| MODIFIER_TOKENS.contains(t))
}

/// Detect `private` and `abstract` modifiers on a declaration line.
///
/// Handles both inline modifiers (`private let ...`) and standalone modifiers
/// where `private` or `abstract` appears on its own line before the declaration.
///
/// Returns `(is_private, is_abstract)`.
pub fn detect_visibility_modifiers(line: &str) -> (bool, bool) {
    let stripped = line.trim();
    // Single pass: check for both keywords by scanning whitespace-separated tokens.
    // Avoids double iteration from two separate `split_whitespace().any()` calls.
    let mut is_private = false;
    let mut is_abstract = false;
    for token in stripped.split_whitespace() {
        match token {
            "private" => is_private = true,
            "abstract" => is_abstract = true,
            _ => {}
        }
        if is_private && is_abstract {
            break;
        }
    }
    (is_private, is_abstract)
}

/// Extract name from 'and' continuation line.
/// 'and' in mutual recursion must start at column 0.
pub fn get_and_name(line: &str) -> Option<String> {
    // 'and' continuations must not have leading whitespace
    if line.starts_with(' ') || line.starts_with('\t') {
        return None;
    }
    let stripped = line.trim();
    AND_PATTERN
        .captures(stripped)
        .and_then(|caps| extract_name_from_captures(&caps))
}

/// Extract additional names from inline 'and' in mutual recursion.
///
/// F* allows mutual recursion on a single line:
///     type expr = ELit of int and stmt = SExpr of expr
///
/// This function finds all 'and NAME =' patterns in a line.
pub fn extract_inline_and_names(line: &str) -> Vec<String> {
    let mut names = Vec::new();
    for caps in INLINE_AND_PATTERN.captures_iter(line) {
        if let Some(name) = extract_name_from_captures(&caps) {
            names.push(name);
        }
    }
    names
}

/// Convert F* operator syntax to its op_* function name.
///
/// F* maps operator characters to names:
///     @%. -> op_At_Percent_Dot
///     |> -> op_Bar_Greater
///
/// Returns None if not all characters are valid F* operator chars.
pub fn operator_to_function_name(op: &str) -> Option<String> {
    let mut parts = Vec::new();
    for ch in op.chars() {
        if let Some(name) = FSTAR_OP_CHARS.get(&ch) {
            parts.push(*name);
        } else {
            return None;
        }
    }
    if parts.is_empty() {
        None
    } else {
        Some(format!("op_{}", parts.join("_")))
    }
}

/// Check if line is blank.
/// Count `(*` and `*)` comment delimiters in a line, ignoring those inside
/// string literals and `//` line comments.
///
/// State machine: Normal -> InString -> InLineComment
/// - Tracks `in_string` state, toggling on unescaped `"` characters
/// - Handles escaped backslashes: consecutive `\` before `"` are paired,
///   so `\\` + `"` means the quote is real (even count of `\`), while
///   `\"` means the quote is escaped (odd count)
/// - `//` outside strings stops scanning (rest of line is a comment)
/// - Only counts `(*` and `*)` when NOT inside a string or line comment
/// - Handles overlapping `(*)`: the left-to-right scan consumes `(*` first,
///   so the `*` cannot also be part of `*)`
pub fn count_comment_opens_closes(line: &str) -> (usize, usize) {
    let bytes = line.as_bytes();
    let len = bytes.len();
    let mut opens = 0usize;
    let mut closes = 0usize;
    let mut in_string = false;
    let mut i = 0;

    while i < len {
        if in_string {
            if bytes[i] == b'\\' && i + 1 < len {
                // Skip escaped character (handles \\, \", \n, etc.)
                // Pair-consumption: each \ consumes itself + next char
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
                // Line comment: rest of line is a comment, stop scanning.
                // Any (* or *) after // are just comment text, not delimiters.
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

/// Remove F* comments and string literals from text to avoid false dependencies.
///
/// Handles F*/OCaml comment conventions:
/// - Nested block comments: `(* outer (* inner *) outer *)`
/// - Line comments: `// text until end of line`
/// - String literals inside comments prevent premature closing:
///   `(* "*)" *)` is one comment, the `*)` inside the string is ignored
/// - Escaped characters in strings: `\"`, `\\`, etc. are properly consumed
///   using pair-consumption (each `\` + next char consumed together)
///
/// State machine: Normal -> InBlockComment(depth) -> InString -> InLineComment
/// - `//` in Normal state transitions to InLineComment (skip to newline)
/// - `(*` in Normal state transitions to InBlockComment(1)
/// - `"` in Normal state transitions to InString
/// - In block comments, `//` is just text (F*/OCaml convention)
///
/// Operates at byte level since F* source is ASCII-compatible. Non-ASCII
/// bytes in identifiers/comments are preserved correctly because we only
/// match single-byte delimiters (`(`, `*`, `)`, `"`, `\`, `/`).
pub fn strip_comments_and_strings(text: &str) -> String {
    let bytes = text.as_bytes();
    let n = bytes.len();
    // Pre-allocate result at full size (most code is not comments)
    let mut result = Vec::with_capacity(n);
    let mut i = 0;
    let mut comment_depth: u32 = 0;
    let mut in_comment_string = false;
    let mut in_line_comment = false;

    while i < n {
        // InLineComment state: skip until newline
        if in_line_comment {
            if bytes[i] == b'\n' {
                in_line_comment = false;
                result.push(bytes[i]);
            }
            i += 1;
            continue;
        }

        // InBlockComment state: track nesting and strings within comments
        if comment_depth > 0 {
            if in_comment_string {
                if bytes[i] == b'\\' && i + 1 < n {
                    i += 2;
                } else if bytes[i] == b'"' {
                    in_comment_string = false;
                    i += 1;
                } else {
                    i += 1;
                }
            } else {
                if bytes[i] == b'"' {
                    in_comment_string = true;
                    i += 1;
                } else if i + 1 < n && bytes[i] == b'(' && bytes[i + 1] == b'*' {
                    comment_depth += 1;
                    i += 2;
                } else if i + 1 < n && bytes[i] == b'*' && bytes[i + 1] == b')' {
                    comment_depth -= 1;
                    if comment_depth == 0 {
                        in_comment_string = false;
                    }
                    i += 2;
                } else {
                    i += 1;
                }
            }
            continue;
        }

        // Normal state: check for strings, line comments, block comments

        // InString: skip string literals
        if bytes[i] == b'"' {
            i += 1;
            while i < n && bytes[i] != b'"' {
                if bytes[i] == b'\\' && i + 1 < n {
                    i += 2;
                } else {
                    i += 1;
                }
            }
            if i < n {
                i += 1;
            }
            continue;
        }

        // Line comment: // starts a comment until end of line
        // In F* (like OCaml), // inside (* *) is just text, so only
        // recognize at depth 0
        if i + 1 < n && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            in_line_comment = true;
            i += 2;
            continue;
        }

        // Block comment open: (*
        if i + 1 < n && bytes[i] == b'(' && bytes[i + 1] == b'*' {
            comment_depth += 1;
            in_comment_string = false;
            i += 2;
            continue;
        }

        result.push(bytes[i]);
        i += 1;
    }

    // SAFETY: We only pushed bytes from the original valid UTF-8 string,
    // skipping complete comment/string sequences. All skipped delimiters
    // are single ASCII bytes, so remaining bytes form valid UTF-8.
    unsafe { String::from_utf8_unchecked(result) }
}

/// Extract effect signature information from a declaration block.
///
/// Parses the block text to find effect annotations and their associated
/// requires/ensures/decreases/modifies clauses.
///
/// For val/let blocks, looks for patterns like:
///   `-> Stack unit (requires fun h -> ...) (ensures fun h0 _ h1 -> ...)`
///   `-> Lemma (ensures P) [SMTPat ...]`
///   `-> Pure int (requires ...) (ensures ...)`
///
/// For effect declarations (new_effect, layered_effect, sub_effect, effect abbrev),
/// extracts combinator info, base effect, and source/dest for sub_effect.
pub fn extract_effect_signature(block: &DeclarationBlock) -> Option<EffectSignature> {
    let text = block.lines.concat();
    let clean = strip_comments_and_strings(&text);

    match block.block_type {
        BlockType::Val | BlockType::Let | BlockType::UnfoldLet | BlockType::InlineLet => {
            extract_val_effect_signature(&clean, block.start_line)
        }
        BlockType::EffectAbbrev => {
            extract_effect_abbrev_signature(&clean, block)
        }
        BlockType::NewEffect => {
            extract_new_effect_signature(&clean, block)
        }
        BlockType::SubEffect => {
            extract_sub_effect_signature(&clean, block)
        }
        BlockType::Effect => {
            // Layered effect or reflectable effect { ... }
            extract_layered_effect_signature(&clean, block)
        }
        _ => None,
    }
}

/// Extract effect signature from a val/let declaration.
fn extract_val_effect_signature(clean: &str, start_line: usize) -> Option<EffectSignature> {
    // Find effect name in the signature.
    // Look for patterns: `-> Effect`, `: Effect`, or standalone `Effect type` at return position.
    // The EFFECT_ANNOTATION_RE regex already captures this.
    let effect_name = EFFECT_ANNOTATION_RE
        .captures(clean)
        .and_then(|c| c.get(1))
        .map(|m| m.as_str().to_string())?;

    // Determine the line where the effect appears
    let effect_line = start_line; // Approximate; actual line depends on multi-line layout

    let has_requires = clean.contains("requires");
    let has_ensures = clean.contains("ensures");
    let has_decreases = clean.contains("decreases");
    let has_modifies = clean.contains("modifies");

    Some(EffectSignature {
        effect_name,
        has_requires,
        has_ensures,
        has_decreases,
        has_modifies,
        effect_line,
        sub_effect_src: None,
        sub_effect_dst: None,
        base_effect: None,
        combinators: Vec::new(),
    })
}

/// Extract signature from an effect abbreviation: `effect Name (...) = BASE ...`
fn extract_effect_abbrev_signature(clean: &str, block: &DeclarationBlock) -> Option<EffectSignature> {
    lazy_static! {
        static ref ABBREV_BASE: Regex = Regex::new(
            r"^effect\s+[A-Z][\w']*\s*(?:\([^)]*\)\s*)*=\s*([A-Z][\w']*)"
        ).unwrap_or_else(|e| panic!("regex: {e}"));
    }

    let trimmed = clean.trim_start();
    let base_effect = ABBREV_BASE
        .captures(trimmed)
        .and_then(|c| c.get(1))
        .map(|m| m.as_str().to_string());

    Some(EffectSignature {
        effect_name: block.name().unwrap_or("unknown").to_string(),
        has_requires: clean.contains("requires"),
        has_ensures: clean.contains("ensures"),
        has_decreases: clean.contains("decreases"),
        has_modifies: clean.contains("modifies"),
        effect_line: block.start_line,
        sub_effect_src: None,
        sub_effect_dst: None,
        base_effect,
        combinators: Vec::new(),
    })
}

/// Check if `text` contains `\bword\s*=` without compiling a regex.
/// Word boundary means the char before `word` (if any) is not alphanumeric/underscore,
/// and the char after `word` is either `=` or whitespace followed by `=`.
#[inline]
fn contains_combinator_assignment(text: &str, word: &str) -> bool {
    let tb = text.as_bytes();
    let wb = word.as_bytes();
    let wlen = wb.len();
    if tb.len() < wlen {
        return false;
    }
    let mut pos = 0;
    while pos + wlen <= tb.len() {
        if let Some(idx) = text[pos..].find(word) {
            let abs = pos + idx;
            // Check word boundary before
            let boundary_before = abs == 0 || {
                let prev = tb[abs - 1];
                !prev.is_ascii_alphanumeric() && prev != b'_' && prev != b'\''
            };
            if boundary_before {
                // Check `\s*=` after
                let mut after = abs + wlen;
                while after < tb.len() && tb[after].is_ascii_whitespace() {
                    after += 1;
                }
                if after < tb.len() && tb[after] == b'=' {
                    return true;
                }
            }
            pos = abs + 1;
        } else {
            break;
        }
    }
    false
}

/// Extract signature from a new_effect declaration.
fn extract_new_effect_signature(clean: &str, block: &DeclarationBlock) -> Option<EffectSignature> {
    let combinator_names = [
        "return_wp", "bind_wp", "if_then_else", "ite_wp",
        "stronger", "close_wp", "trivial",
        "repr", "return", "bind", "subcomp", "close", "lift_wp",
    ];

    let mut combinators = Vec::new();
    for name in &combinator_names {
        if contains_combinator_assignment(clean, name) {
            combinators.push(name.to_string());
        }
    }

    // For simple derivation `new_effect NAME = BASE`, extract base
    let base_effect = if !clean.contains('{') && clean.contains('=') {
        lazy_static! {
            static ref NEW_EFFECT_BASE: Regex = Regex::new(
                r"new_effect\s+[A-Z][\w']*\s*=\s*([A-Z][\w']*)"
            ).unwrap_or_else(|e| panic!("regex: {e}"));
        }
        NEW_EFFECT_BASE
            .captures(clean)
            .and_then(|c| c.get(1))
            .map(|m| m.as_str().to_string())
    } else {
        None
    };

    Some(EffectSignature {
        effect_name: block.name().unwrap_or("unknown").to_string(),
        has_requires: false,
        has_ensures: false,
        has_decreases: false,
        has_modifies: false,
        effect_line: block.start_line,
        sub_effect_src: None,
        sub_effect_dst: None,
        base_effect,
        combinators,
    })
}

/// Extract signature from a sub_effect declaration.
fn extract_sub_effect_signature(clean: &str, block: &DeclarationBlock) -> Option<EffectSignature> {
    lazy_static! {
        static ref SUB_EFFECT_RE: Regex = Regex::new(
            r"sub_effect\s+([A-Z][\w']*)\s*~>\s*([A-Z][\w']*)"
        ).unwrap_or_else(|e| panic!("regex: {e}"));
    }

    let (src, dst) = if let Some(caps) = SUB_EFFECT_RE.captures(clean) {
        (
            caps.get(1).map(|m| m.as_str().to_string()),
            caps.get(2).map(|m| m.as_str().to_string()),
        )
    } else {
        (None, None)
    };

    let has_lift_wp = clean.contains("lift_wp");
    let mut combinators = Vec::new();
    if has_lift_wp {
        combinators.push("lift_wp".to_string());
    }

    Some(EffectSignature {
        effect_name: "sub_effect".to_string(),
        has_requires: false,
        has_ensures: false,
        has_decreases: false,
        has_modifies: false,
        effect_line: block.start_line,
        sub_effect_src: src,
        sub_effect_dst: dst,
        base_effect: None,
        combinators,
    })
}

/// Extract signature from a layered_effect or reflectable effect.
fn extract_layered_effect_signature(clean: &str, block: &DeclarationBlock) -> Option<EffectSignature> {
    let combinator_names = [
        "repr", "return", "bind", "subcomp", "if_then_else", "close",
    ];

    let mut combinators = Vec::new();
    for name in &combinator_names {
        if contains_combinator_assignment(clean, name) {
            combinators.push(name.to_string());
        }
    }

    Some(EffectSignature {
        effect_name: block.name().unwrap_or("unknown").to_string(),
        has_requires: false,
        has_ensures: false,
        has_decreases: false,
        has_modifies: false,
        effect_line: block.start_line,
        sub_effect_src: None,
        sub_effect_dst: None,
        base_effect: None,
        combinators,
    })
}

// =========================================================================
// F* Type System: Type expressions, binders, qualifiers, and declarations
// =========================================================================

/// Qualifier on a binder in F* function types.
///
/// F* distinguishes several kinds of arguments:
/// - Explicit: `(x:t)` or just `t`
/// - Implicit: `#x:t` or `{x:t}` (inferred by unification)
/// - Equality: `$x:t` (inferred by unification, with propositional equality)
/// - Meta/TypeClass: `{| tc |}` (resolved by type class instance search)
///
/// From FStar parser AST: `arg_qualifier = Implicit | Equality | Meta of term | TypeClassArg`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinderQualifier {
    /// Explicit argument: `(x:t)` or bare `t`.
    Explicit,
    /// Implicit argument: `#x:t` or `{x:t}`.
    Implicit,
    /// Equality constraint argument: `$x:t`.
    Equality,
    /// Type class instance argument: `{| tc |}`.
    TypeClassArg,
    /// Meta argument with attribute: resolved by tactic/plugin.
    Meta(String),
}

/// A binder in F* type signatures.
///
/// Represents a named or unnamed parameter in function types, forall quantifiers,
/// and type declarations. Captures the full structure including qualifiers and
/// optional refinement predicates.
///
/// Examples:
/// ```text
/// (x:nat)                     -- named explicit binder
/// #a:Type                     -- implicit binder
/// (x:nat{x > 0})             -- binder with refinement
/// {| hashable a |}           -- type class binder
/// _                           -- wildcard binder
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FStarBinder {
    /// Binder name, or `None` for anonymous/wildcard binders.
    pub name: Option<String>,
    /// The type annotation, if present.
    pub binder_type: Option<Box<FStarType>>,
    /// Qualifier: explicit, implicit (#), equality ($), or type class ({||}).
    pub qualifier: BinderQualifier,
    /// Attributes on this binder (from `[@@@...]`).
    pub attributes: Vec<String>,
}

/// F* type expression AST for lint analysis.
///
/// A lightweight representation of F* type expressions, sufficient for lint rules
/// (FST001 duplicate detection, FST002 ordering, FST003 comment analysis,
/// FST012 refinement simplification) without full desugaring.
///
/// Based on the FStar parser AST (`FStarC.Parser.AST.term'`), capturing the
/// constructs most relevant to static analysis:
///
/// - Refinement types: `{x:t | P}` (Refine)
/// - Dependent function types: `(x:a) -> b` (Arrow with binders)
/// - Universe polymorphism: `Type u#a`, `Type0`, `Type1` (Universe)
/// - Implicit arguments: `#a:Type` (in binders)
/// - Tuple types: `a & b & c` (Tuple)
/// - Record types: `{field1: t1; field2: t2}` (Record)
/// - Type application: `list nat`, `option (int & string)` (App)
/// - Simple named types: `nat`, `int`, `FStar.Seq.seq` (Named)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FStarType {
    /// A simple named type: `nat`, `int`, `bool`, `FStar.Seq.seq`.
    Named(String),

    /// Type application: `list nat`, `option int`, `buffer uint8`.
    /// First element is the type constructor, rest are arguments.
    App {
        head: Box<FStarType>,
        args: Vec<FStarType>,
    },

    /// Function/arrow type: `a -> b` or `(x:a) -> b` (dependent).
    /// Binders carry qualifier info (implicit, explicit, type class).
    Arrow {
        binders: Vec<FStarBinder>,
        result: Box<FStarType>,
    },

    /// Refinement type: `{x:t | P}` or `x:t{P}`.
    /// The variable is bound in the predicate.
    Refinement {
        binder_name: String,
        base_type: Box<FStarType>,
        predicate: String,
    },

    /// Universe-polymorphic type: `Type u#a`, `Type0`, `Type1`, `Type u#(max a b)`.
    Universe {
        /// The universe annotation, e.g., `0`, `1`, `a`, `max a b`.
        level: String,
    },

    /// Tuple (dependent sum) type: `a & b`, `(x:a & b x)`.
    /// In FStar AST this is `Sum`.
    Tuple {
        elements: Vec<FStarType>,
    },

    /// Record type: `{field1: t1; field2: t2}`.
    Record {
        fields: Vec<(String, FStarType)>,
    },

    /// Wildcard/placeholder: `_`.
    Wild,

    /// Parenthesized type: `(t)`.
    Paren(Box<FStarType>),

    /// Squash type: `squash P` (proof-irrelevant proposition).
    Squash(Box<FStarType>),

    /// Erased type: `erased t` (computationally irrelevant).
    Erased(Box<FStarType>),

    /// A type we could not fully parse -- preserves the raw text.
    Unknown(String),
}

impl FStarType {
    /// Whether this type is a refinement type.
    pub fn is_refinement(&self) -> bool {
        matches!(self, FStarType::Refinement { .. })
    }

    /// Whether this type is a function/arrow type.
    pub fn is_arrow(&self) -> bool {
        matches!(self, FStarType::Arrow { .. })
    }

    /// Whether this type is a universe type.
    pub fn is_universe(&self) -> bool {
        matches!(self, FStarType::Universe { .. })
    }

    /// Whether this type is a tuple type.
    pub fn is_tuple(&self) -> bool {
        matches!(self, FStarType::Tuple { .. })
    }

    /// Whether this type is a record type.
    pub fn is_record(&self) -> bool {
        matches!(self, FStarType::Record { .. })
    }

    /// Whether this type contains any implicit binders (in arrow types).
    pub fn has_implicit_binders(&self) -> bool {
        match self {
            FStarType::Arrow { binders, result } => {
                binders.iter().any(|b| b.qualifier == BinderQualifier::Implicit)
                    || result.has_implicit_binders()
            }
            FStarType::App { head, args } => {
                head.has_implicit_binders()
                    || args.iter().any(|a| a.has_implicit_binders())
            }
            _ => false,
        }
    }

    /// Collect all named type references from this type expression.
    /// Useful for dependency analysis (FST002).
    pub fn collect_type_references(&self) -> HashSet<String> {
        let mut refs = HashSet::new();
        self.collect_refs_inner(&mut refs);
        refs
    }

    fn collect_refs_inner(&self, refs: &mut HashSet<String>) {
        match self {
            FStarType::Named(name) => { refs.insert(name.clone()); }
            FStarType::App { head, args } => {
                head.collect_refs_inner(refs);
                for arg in args {
                    arg.collect_refs_inner(refs);
                }
            }
            FStarType::Arrow { binders, result } => {
                for b in binders {
                    if let Some(bt) = &b.binder_type {
                        bt.collect_refs_inner(refs);
                    }
                }
                result.collect_refs_inner(refs);
            }
            FStarType::Refinement { base_type, .. } => {
                base_type.collect_refs_inner(refs);
            }
            FStarType::Tuple { elements } => {
                for e in elements {
                    e.collect_refs_inner(refs);
                }
            }
            FStarType::Record { fields } => {
                for (_, ft) in fields {
                    ft.collect_refs_inner(refs);
                }
            }
            FStarType::Paren(inner) => inner.collect_refs_inner(refs),
            FStarType::Squash(inner) => inner.collect_refs_inner(refs),
            FStarType::Erased(inner) => inner.collect_refs_inner(refs),
            FStarType::Universe { .. } | FStarType::Wild | FStarType::Unknown(_) => {}
        }
    }

    /// Extract the base type name if this is a simple named type or application.
    pub fn base_type_name(&self) -> Option<&str> {
        match self {
            FStarType::Named(n) => Some(n),
            FStarType::App { head, .. } => head.base_type_name(),
            FStarType::Paren(inner) => inner.base_type_name(),
            _ => None,
        }
    }
}

/// Equality qualifier on a type declaration.
///
/// F* type declarations can opt out of derived decidable equality:
/// - `noeq type t = ...` -- no decidable equality generated
/// - `unopteq type t = ...` -- unoptimized equality (for debugging)
/// - (default) -- optimized decidable equality derived if possible
///
/// From FStar AST: `qualifier = Noeq | Unopteq | ...`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EqualityQualifier {
    /// Default: derive optimized decidable equality if possible.
    Default,
    /// `noeq`: do not derive decidable equality.
    Noeq,
    /// `unopteq`: derive unoptimized decidable equality.
    Unopteq,
}

/// Constructor payload kind, matching FStar's `constructor_payload`.
///
/// F* supports three forms of constructor payloads:
/// - `Of` notation: `| C of t` (single argument of type t)
/// - Arbitrary arity: `| C : t1 -> t2 -> ind_type` (GADT-style)
/// - Record payload: `| C { field1: t1; field2: t2 }` (inline record)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstructorPayload {
    /// `| C of t` -- constructor with "of" notation (arity 1 for kind Type).
    OfNotation(Box<FStarType>),
    /// `| C : t1 -> t2 -> ind` -- GADT-style with full type signature.
    Arbitrary(Box<FStarType>),
    /// `| C { f1: t1; f2: t2 }` -- record payload (with optional result type).
    Record {
        fields: Vec<(String, FStarType)>,
        result_type: Option<Box<FStarType>>,
    },
}

/// A constructor definition in an algebraic data type.
///
/// Examples:
/// ```text
/// | Red                                    -- nullary
/// | Lit of int                             -- "of" notation
/// | Add : expr -> expr -> expr             -- GADT-style
/// | MkPerson { name: string; age: nat }    -- record payload
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorDef {
    /// Constructor name (e.g., `Red`, `Lit`, `Add`, `MkPerson`).
    pub name: String,
    /// Constructor payload, if any.
    pub payload: Option<ConstructorPayload>,
    /// Attributes on the constructor.
    pub attributes: Vec<String>,
}

/// Kind of type declaration, matching FStar's `tycon` variants.
///
/// From FStar AST:
/// - `TyconAbstract`: abstract type (no definition body)
/// - `TyconAbbrev`: type alias/abbreviation
/// - `TyconRecord`: record type
/// - `TyconVariant`: algebraic data type with constructors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeDeclKind {
    /// Abstract type: `type t` (no `=` and body).
    Abstract,
    /// Type abbreviation/alias: `type t = existing_type`.
    Abbreviation,
    /// Record type: `type t = { field1: t1; field2: t2 }`.
    Record,
    /// Variant/ADT type: `type t = | C1 | C2 of t2`.
    Variant,
}

/// Rich information about an F* type declaration.
///
/// Captures the full structure of a type declaration for lint analysis,
/// including parameters, kind annotations, equality qualifiers,
/// constructors, and mutual recursion partners.
///
/// Examples:
/// ```text
/// type point = { x: int; y: int }
/// noeq type expr =
///   | Lit of int
///   | Add : expr -> expr -> expr
/// type vector (a:Type) (n:nat) : Type = ...
/// type tree (a:Type) = | Leaf : a -> tree a | Node : tree a -> tree a -> tree a
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDeclarationInfo {
    /// Type name.
    pub name: String,
    /// Type parameters (binders before `=` or `:`).
    pub params: Vec<FStarBinder>,
    /// Optional kind annotation (e.g., `: Type`, `: Type -> Type`).
    pub kind_annotation: Option<Box<FStarType>>,
    /// Equality qualifier: default, noeq, or unopteq.
    pub equality: EqualityQualifier,
    /// What kind of type declaration this is.
    pub decl_kind: TypeDeclKind,
    /// For abbreviations: the aliased type.
    pub body_type: Option<Box<FStarType>>,
    /// For variants: the list of constructors.
    pub constructors: Vec<ConstructorDef>,
    /// For records: the field definitions.
    pub record_fields: Vec<(String, FStarType)>,
    /// Names of mutual recursion partners (from `and` continuations).
    pub mutual_rec_partners: Vec<String>,
    /// Whether this type is private.
    pub is_private: bool,
}

// =========================================================================
// Type expression parser
// =========================================================================

/// Parse a simple F* type expression from text.
///
/// This is a lightweight parser for type expressions in signatures and
/// declarations. It handles the common patterns needed for lint analysis
/// without implementing a full F* parser.
///
/// Supported constructs:
/// - Named types: `nat`, `int`, `FStar.Seq.seq`
/// - Type application: `list nat`, `option (int & string)`
/// - Refinement types: `x:nat{x > 0}`, `{x:int | x >= 0}`
/// - Arrow types: `int -> int`, `(x:nat) -> vec x`
/// - Tuple types: `int & string`, `nat & bool & unit`
/// - Universe types: `Type`, `Type0`, `Type u#a`
/// - Implicit binders: `#a:Type -> a -> a`
/// - Wildcard: `_`
/// - Record types: `{ x: int; y: int }`
pub fn parse_type_expr(input: &str) -> FStarType {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return FStarType::Unknown(String::new());
    }

    // Try arrow type first (top-level)
    if let Some(ty) = try_parse_arrow(trimmed) {
        return ty;
    }

    // Try tuple type (uses & separator at top level)
    if let Some(ty) = try_parse_tuple(trimmed) {
        return ty;
    }

    parse_type_atom(trimmed)
}

/// Try to parse an arrow type: `a -> b` or `(x:a) -> b`.
///
/// Splits on `->` at the top level (not inside parens/braces/brackets).
fn try_parse_arrow(input: &str) -> Option<FStarType> {
    let segments = split_top_level(input, "->");
    if segments.len() < 2 {
        return None;
    }

    // Last segment is the result type
    let last_seg = segments.last()?;
    let result_str = last_seg.trim();
    let result = parse_type_expr(result_str);

    // All preceding segments are binders
    let mut binders = Vec::new();
    for seg in &segments[..segments.len() - 1] {
        let b = parse_binder_from_segment(seg.trim());
        binders.push(b);
    }

    Some(FStarType::Arrow {
        binders,
        result: Box::new(result),
    })
}

/// Try to parse a tuple type: `a & b & c`.
///
/// The `&` must be at the top level (not inside parens).
fn try_parse_tuple(input: &str) -> Option<FStarType> {
    // Only split on standalone `&` (not `&&` or `&&&`)
    let segments = split_top_level_ampersand(input);
    if segments.len() < 2 {
        return None;
    }

    let elements: Vec<FStarType> = segments.iter()
        .map(|s| parse_type_atom(s.trim()))
        .collect();

    Some(FStarType::Tuple { elements })
}

/// Parse a single type atom (non-arrow, non-tuple).
fn parse_type_atom(input: &str) -> FStarType {
    let trimmed = input.trim();

    if trimmed.is_empty() {
        return FStarType::Unknown(String::new());
    }

    // Wildcard
    if trimmed == "_" {
        return FStarType::Wild;
    }

    // Parenthesized expression
    if trimmed.starts_with('(') && find_matching_close(trimmed, 0, b'(', b')') == Some(trimmed.len() - 1) {
        let inner = &trimmed[1..trimmed.len() - 1];
        return FStarType::Paren(Box::new(parse_type_expr(inner)));
    }

    // Record type: { field1: t1; field2: t2 }
    if trimmed.starts_with('{') && !trimmed.contains('|') {
        if let Some(close) = find_matching_close(trimmed, 0, b'{', b'}') {
            if close == trimmed.len() - 1 {
                if let Some(fields) = try_parse_record_fields(&trimmed[1..close]) {
                    return FStarType::Record { fields };
                }
            }
        }
    }

    // Refinement type: {x:t | P} (curly-brace form with pipe)
    if trimmed.starts_with('{') && trimmed.contains('|') {
        if let Some(ty) = try_parse_brace_refinement(trimmed) {
            return ty;
        }
    }

    // Inline refinement: x:t{P} - only if we see `identifier : type { pred }`
    // This form appears in binders more than standalone, but we handle it.
    if let Some(ty) = try_parse_inline_refinement(trimmed) {
        return ty;
    }

    // Universe type: Type, Type0, Type1, Type u#a, Type u#(max a b)
    if let Some(ty) = try_parse_universe(trimmed) {
        return ty;
    }

    // Squash
    if let Some(rest) = trimmed.strip_prefix("squash ") {
        return FStarType::Squash(Box::new(parse_type_atom(rest)));
    }
    if let Some(rest) = trimmed.strip_prefix("squash(") {
        return FStarType::Squash(Box::new(parse_type_atom(rest)));
    }

    // Erased
    if let Some(rest) = trimmed.strip_prefix("erased ") {
        return FStarType::Erased(Box::new(parse_type_atom(rest)));
    }
    if let Some(rest) = trimmed.strip_prefix("erased(") {
        return FStarType::Erased(Box::new(parse_type_atom(rest)));
    }

    // Type application: `list nat`, `option int`, `buffer uint8 32ul`
    // Split into head + args on whitespace (respecting parens)
    let tokens = split_type_application_tokens(trimmed);
    if tokens.len() > 1 {
        let head = parse_type_atom(tokens[0]);
        let args: Vec<FStarType> = tokens[1..].iter()
            .map(|t| parse_type_atom(t))
            .collect();
        return FStarType::App {
            head: Box::new(head),
            args,
        };
    }

    // Simple named type (possibly qualified)
    if is_fstar_type_identifier(trimmed) {
        return FStarType::Named(trimmed.to_string());
    }

    FStarType::Unknown(trimmed.to_string())
}

/// Parse a binder from an arrow segment.
///
/// Handles:
/// - `(x:nat)` -- named explicit
/// - `#a:Type` -- implicit
/// - `(#a:Type)` -- implicit in parens
/// - `{| tc a |}` -- type class
/// - `nat` -- anonymous explicit
/// - `(x:nat{x > 0})` -- with refinement
fn parse_binder_from_segment(input: &str) -> FStarBinder {
    let trimmed = input.trim();

    // Type class binder: {| tc |}
    if trimmed.starts_with("{|") && trimmed.ends_with("|}") {
        let inner = trimmed[2..trimmed.len() - 2].trim();
        return FStarBinder {
            name: None,
            binder_type: Some(Box::new(parse_type_expr(inner))),
            qualifier: BinderQualifier::TypeClassArg,
            attributes: Vec::new(),
        };
    }

    // Implicit with hash: #x:t or #t
    if let Some(rest) = trimmed.strip_prefix('#') {
        return parse_named_or_anon_binder(rest.trim(), BinderQualifier::Implicit);
    }

    // Equality with dollar: $x:t
    if let Some(rest) = trimmed.strip_prefix('$') {
        return parse_named_or_anon_binder(rest.trim(), BinderQualifier::Equality);
    }

    // Parenthesized binder: (x:t) or (#x:t) or (x:t{P})
    if trimmed.starts_with('(') && trimmed.ends_with(')') {
        let inner = trimmed[1..trimmed.len() - 1].trim();

        // Check for implicit inside parens: (#x:t)
        if let Some(rest) = inner.strip_prefix('#') {
            return parse_named_or_anon_binder(rest.trim(), BinderQualifier::Implicit);
        }
        // Check for equality inside parens: ($x:t)
        if let Some(rest) = inner.strip_prefix('$') {
            return parse_named_or_anon_binder(rest.trim(), BinderQualifier::Equality);
        }

        return parse_named_or_anon_binder(inner, BinderQualifier::Explicit);
    }

    // Plain binder: either `name:type` or just `type`
    parse_named_or_anon_binder(trimmed, BinderQualifier::Explicit)
}

/// Parse either `name:type` or just `type` as a binder.
fn parse_named_or_anon_binder(input: &str, qualifier: BinderQualifier) -> FStarBinder {
    // Try to find `:` at the top level (not inside braces or parens)
    if let Some(colon_pos) = find_top_level_colon(input) {
        let name_part = input[..colon_pos].trim();
        let type_part = input[colon_pos + 1..].trim();

        // Check for inline refinement: x:nat{P}
        if let Some(brace_pos) = type_part.find('{') {
            if let Some(close_brace) = find_matching_close(type_part, brace_pos, b'{', b'}') {
                let base = &type_part[..brace_pos].trim();
                let pred = &type_part[brace_pos + 1..close_brace].trim();
                if !base.is_empty() && !pred.is_empty() {
                    return FStarBinder {
                        name: if name_part.is_empty() || name_part == "_" { None } else { Some(name_part.to_string()) },
                        binder_type: Some(Box::new(FStarType::Refinement {
                            binder_name: name_part.to_string(),
                            base_type: Box::new(parse_type_atom(base)),
                            predicate: pred.to_string(),
                        })),
                        qualifier,
                        attributes: Vec::new(),
                    };
                }
            }
        }

        let name = if name_part.is_empty() || name_part == "_" {
            None
        } else if is_fstar_identifier(name_part) {
            Some(name_part.to_string())
        } else {
            None
        };

        return FStarBinder {
            name,
            binder_type: Some(Box::new(parse_type_expr(type_part))),
            qualifier,
            attributes: Vec::new(),
        };
    }

    // No colon -- anonymous binder
    FStarBinder {
        name: None,
        binder_type: Some(Box::new(parse_type_atom(input))),
        qualifier,
        attributes: Vec::new(),
    }
}

/// Try to parse a curly-brace refinement: `{x:t | P}`.
fn try_parse_brace_refinement(input: &str) -> Option<FStarType> {
    if !input.starts_with('{') {
        return None;
    }
    let close = find_matching_close(input, 0, b'{', b'}')?;
    let inner = &input[1..close];

    // Find the `|` separator at the top level
    let pipe_pos = find_top_level_char(inner, '|')?;
    let binding = inner[..pipe_pos].trim();
    let predicate = inner[pipe_pos + 1..].trim();

    if predicate.is_empty() {
        return None;
    }

    // Parse binding: `x:t` or just `x`
    if let Some(colon_pos) = find_top_level_colon(binding) {
        let name = binding[..colon_pos].trim();
        let base = binding[colon_pos + 1..].trim();
        Some(FStarType::Refinement {
            binder_name: name.to_string(),
            base_type: Box::new(parse_type_atom(base)),
            predicate: predicate.to_string(),
        })
    } else {
        // Just a name with no type annotation: `{x | P}`
        Some(FStarType::Refinement {
            binder_name: binding.to_string(),
            base_type: Box::new(FStarType::Unknown("_".to_string())),
            predicate: predicate.to_string(),
        })
    }
}

/// Try to parse inline refinement: `x:t{P}` (when appearing standalone).
fn try_parse_inline_refinement(input: &str) -> Option<FStarType> {
    // Must contain both `:` and `{...}`
    let colon_pos = find_top_level_colon(input)?;
    let name = input[..colon_pos].trim();
    if !is_fstar_identifier(name) {
        return None;
    }

    let after_colon = input[colon_pos + 1..].trim();
    let brace_pos = after_colon.find('{')?;
    let close_brace = find_matching_close(after_colon, brace_pos, b'{', b'}')?;

    // Must end at or near the closing brace
    let after_close = after_colon[close_brace + 1..].trim();
    if !after_close.is_empty() {
        return None;
    }

    let base = after_colon[..brace_pos].trim();
    let pred = after_colon[brace_pos + 1..close_brace].trim();

    if base.is_empty() || pred.is_empty() {
        return None;
    }

    Some(FStarType::Refinement {
        binder_name: name.to_string(),
        base_type: Box::new(parse_type_atom(base)),
        predicate: pred.to_string(),
    })
}

/// Try to parse a universe type: `Type`, `Type0`, `Type u#a`, `Type u#(max a b)`.
fn try_parse_universe(input: &str) -> Option<FStarType> {
    let trimmed = input.trim();

    // Exact match for Type levels
    match trimmed {
        "Type" | "Type0" => return Some(FStarType::Universe { level: "0".to_string() }),
        "Type1" => return Some(FStarType::Universe { level: "1".to_string() }),
        "eqtype" => return Some(FStarType::Universe { level: "0".to_string() }),
        "prop" => return Some(FStarType::Universe { level: "0".to_string() }),
        _ => {}
    }

    // Type u#level
    if trimmed.starts_with("Type u#") || trimmed.starts_with("Type u#(") {
        let level_str = &trimmed[7..]; // skip "Type u#"
        let level = if level_str.starts_with('(') && level_str.ends_with(')') {
            level_str[1..level_str.len() - 1].trim().to_string()
        } else {
            level_str.trim().to_string()
        };
        return Some(FStarType::Universe { level });
    }

    None
}

/// Try to parse record fields from content inside `{ ... }`.
fn try_parse_record_fields(input: &str) -> Option<Vec<(String, FStarType)>> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return None;
    }

    let segments = split_respecting_parens(trimmed, ';');
    let mut fields = Vec::new();

    for seg in segments {
        let s = seg.trim();
        if s.is_empty() {
            continue;
        }

        // Each field is `name : type` or `name = expr` (we look for `:`)
        if let Some(colon_pos) = find_top_level_colon(s) {
            let fname = s[..colon_pos].trim().to_string();
            let ftype_str = s[colon_pos + 1..].trim();
            if is_fstar_identifier(&fname) {
                fields.push((fname, parse_type_expr(ftype_str)));
            } else {
                return None; // Not a record
            }
        } else {
            return None; // Not a record field
        }
    }

    if fields.is_empty() {
        None
    } else {
        Some(fields)
    }
}

/// Parse constructor definitions from a type declaration body.
///
/// Handles:
/// - Nullary: `| Red`
/// - Of notation: `| Lit of int`
/// - GADT-style: `| Add : expr -> expr -> expr`
/// - Record payload: `| MkPerson { name: string; age: nat }`
pub fn parse_constructors(body: &str) -> Vec<ConstructorDef> {
    let mut constructors = Vec::new();
    let clean = strip_comments_and_strings(body);

    // Split on `|` at the top level
    let segments = split_top_level_pipe(&clean);

    for seg in segments {
        let trimmed = seg.trim();
        if trimmed.is_empty() {
            continue;
        }

        // Extract constructor name (first identifier)
        let first_token_end = trimmed.find(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
            .unwrap_or(trimmed.len());
        let ctor_name = &trimmed[..first_token_end];

        if ctor_name.is_empty() || !ctor_name.starts_with(|c: char| c.is_uppercase()) {
            continue; // Not a constructor name
        }

        let rest = trimmed[first_token_end..].trim();

        let payload = if rest.is_empty() {
            // Nullary constructor
            None
        } else if let Some(type_str) = rest.strip_prefix("of ").or_else(|| rest.strip_prefix("of(")) {
            // Of notation: `| C of t`
            Some(ConstructorPayload::OfNotation(Box::new(parse_type_expr(type_str))))
        } else if let Some(colon_rest) = rest.strip_prefix(':') {
            // GADT-style: `| C : t1 -> t2 -> result`
            let type_str = colon_rest.trim();
            Some(ConstructorPayload::Arbitrary(Box::new(parse_type_expr(type_str))))
        } else if rest.starts_with('{') {
            // Record payload: `| C { f1: t1; f2: t2 }`
            if let Some(close) = find_matching_close(rest, 0, b'{', b'}') {
                let fields_str = &rest[1..close];
                if let Some(fields) = try_parse_record_fields(fields_str) {
                    let after_brace = rest[close + 1..].trim();
                    let result_type = after_brace.strip_prefix("->")
                        .map(|arrow_rest| Box::new(parse_type_expr(arrow_rest.trim())));
                    Some(ConstructorPayload::Record { fields, result_type })
                } else {
                    Some(ConstructorPayload::Arbitrary(Box::new(FStarType::Unknown(rest.to_string()))))
                }
            } else {
                Some(ConstructorPayload::Arbitrary(Box::new(FStarType::Unknown(rest.to_string()))))
            }
        } else {
            // Unknown payload form
            Some(ConstructorPayload::Arbitrary(Box::new(FStarType::Unknown(rest.to_string()))))
        };

        constructors.push(ConstructorDef {
            name: ctor_name.to_string(),
            payload,
            attributes: Vec::new(),
        });
    }

    constructors
}

/// Check if a type body contains variant constructors (lines starting with `|`).
fn has_variant_constructors(body: &str) -> bool {
    let trimmed = body.trim();
    // Body starts with `|`
    if trimmed.starts_with('|') {
        return true;
    }
    // Any line starts with `|` (after optional whitespace)
    for line in trimmed.lines() {
        let lt = line.trim();
        if lt.starts_with('|') && !lt.starts_with("||") {
            return true;
        }
    }
    false
}

/// Parse a type declaration from a `DeclarationBlock`.
///
/// Extracts rich type declaration information including parameters,
/// kind annotations, equality qualifiers, constructors, and mutual
/// recursion partners.
pub fn parse_type_declaration(block: &DeclarationBlock) -> Option<TypeDeclarationInfo> {
    if block.block_type != BlockType::Type {
        return None;
    }

    let text = block.text();
    let clean = strip_comments_and_strings(&text);
    let trimmed = clean.trim();

    // Parse modifiers and extract name
    let primary_name = block.name()?.to_string();

    // Detect equality qualifier
    let equality = if trimmed.contains("noeq ") || trimmed.contains("noeq\n") {
        EqualityQualifier::Noeq
    } else if trimmed.contains("unopteq ") || trimmed.contains("unopteq\n") {
        EqualityQualifier::Unopteq
    } else {
        EqualityQualifier::Default
    };

    let is_private = block.is_private;

    // Find the `type NAME` part and what follows.
    // Uses (?s) dotall flag so `.` matches newlines in the body.
    lazy_static! {
        static ref TYPE_DECL_RE: Regex = Regex::new(
            r"(?s)(?:(?:private|abstract|noeq|unopteq|inline_for_extraction|noextract|unfold)\s+)*type\s+([a-zA-Z_][\w']*)(.*)"
        ).unwrap_or_else(|e| panic!("regex: {e}"));
    }

    let caps = TYPE_DECL_RE.captures(trimmed)?;
    let after_name = caps.get(2).map(|m| m.as_str().trim()).unwrap_or("");

    // Parse parameters and kind annotation before `=`
    let (params, kind_annotation, body_str) = parse_type_params_and_body(after_name);

    // Determine declaration kind and parse body
    let (decl_kind, body_type, constructors, record_fields) = if let Some(body) = body_str {
        let body_trimmed = body.trim();
        if body_trimmed.is_empty() {
            (TypeDeclKind::Abstract, None, Vec::new(), Vec::new())
        } else if body_trimmed.starts_with('{') && !body_trimmed.starts_with("{|") {
            // Record type (but not `{| typeclass |}`)
            if let Some(close) = find_matching_close(body_trimmed, 0, b'{', b'}') {
                let fields_str = &body_trimmed[1..close];
                if let Some(fields) = try_parse_record_fields(fields_str) {
                    (TypeDeclKind::Record, None, Vec::new(), fields)
                } else {
                    (TypeDeclKind::Abbreviation, Some(Box::new(parse_type_expr(body_trimmed))), Vec::new(), Vec::new())
                }
            } else {
                (TypeDeclKind::Abbreviation, Some(Box::new(parse_type_expr(body_trimmed))), Vec::new(), Vec::new())
            }
        } else if has_variant_constructors(body_trimmed) {
            // Variant type: detect `|` at the start of a line or after whitespace
            let ctors = parse_constructors(body_trimmed);
            if ctors.is_empty() {
                (TypeDeclKind::Abbreviation, Some(Box::new(parse_type_expr(body_trimmed))), Vec::new(), Vec::new())
            } else {
                (TypeDeclKind::Variant, None, ctors, Vec::new())
            }
        } else {
            // Type abbreviation
            (TypeDeclKind::Abbreviation, Some(Box::new(parse_type_expr(body_trimmed))), Vec::new(), Vec::new())
        }
    } else {
        (TypeDeclKind::Abstract, None, Vec::new(), Vec::new())
    };

    // Collect mutual recursion partners
    let mutual_rec_partners: Vec<String> = block.names.iter()
        .filter(|n| n.as_str() != primary_name)
        .cloned()
        .collect();

    Some(TypeDeclarationInfo {
        name: primary_name,
        params,
        kind_annotation,
        equality,
        decl_kind,
        body_type,
        constructors,
        record_fields,
        mutual_rec_partners,
        is_private,
    })
}

/// Parse type parameters, optional kind annotation, and body from text after the type name.
///
/// Input is everything after `type Name`, e.g.:
/// - `(a:Type) (n:nat) : Type = ...` -> params, kind, body
/// - `= nat` -> no params, no kind, body "nat"
/// - `: Type` -> no params, kind "Type", no body
fn parse_type_params_and_body(input: &str) -> (Vec<FStarBinder>, Option<Box<FStarType>>, Option<String>) {
    let trimmed = input.trim();

    if trimmed.is_empty() {
        return (Vec::new(), None, None);
    }

    // Find the `=` at the top level, separating params/kind from body
    let eq_pos = find_top_level_equals(trimmed);

    let (before_eq, body_str) = if let Some(pos) = eq_pos {
        let before = trimmed[..pos].trim();
        let after = trimmed[pos + 1..].trim();
        (before, Some(after.to_string()))
    } else {
        (trimmed, None)
    };

    // Parse parameters and kind annotation from `before_eq`
    // Kind annotation comes after `:` at the end
    let (param_str, kind_str) = split_params_and_kind(before_eq);

    let params = parse_type_params(param_str);
    let kind_annotation = kind_str.map(|k| Box::new(parse_type_expr(k)));

    (params, kind_annotation, body_str)
}

/// Split parameter section from kind annotation.
/// The kind annotation follows the last top-level `:` that is not inside parens.
fn split_params_and_kind(input: &str) -> (&str, Option<&str>) {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return ("", None);
    }

    // Find last top-level `:` (not inside parens/braces)
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut last_colon = None;
    let bytes = trimmed.as_bytes();

    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' => depth_paren += 1,
            b')' => depth_paren -= 1,
            b'{' => depth_brace += 1,
            b'}' => depth_brace -= 1,
            b':' if depth_paren == 0 && depth_brace == 0 => {
                last_colon = Some(i);
            }
            _ => {}
        }
    }

    if let Some(pos) = last_colon {
        let params = trimmed[..pos].trim();
        let kind = trimmed[pos + 1..].trim();
        if kind.is_empty() {
            (params, None)
        } else {
            (params, Some(kind))
        }
    } else {
        (trimmed, None)
    }
}

/// Parse type parameters from a string of binders.
/// E.g., `(a:Type) (n:nat)` or `a n`.
fn parse_type_params(input: &str) -> Vec<FStarBinder> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Vec::new();
    }

    let mut params = Vec::new();
    let tokens = split_top_level_params(trimmed);

    for tok in tokens {
        let t = tok.trim();
        if t.is_empty() {
            continue;
        }
        params.push(parse_binder_from_segment(t));
    }

    params
}

// =========================================================================
// Helper functions for type parsing
// =========================================================================

/// Check if a string is a valid F* identifier.
fn is_fstar_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let mut chars = s.chars();
    let Some(first) = chars.next() else { return false };
    if !first.is_alphabetic() && first != '_' {
        return false;
    }
    chars.all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
}

/// Check if a string is a valid F* type identifier (possibly qualified).
fn is_fstar_type_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    // Qualified: A.B.c
    s.split('.').all(is_fstar_identifier)
}

/// Find matching closing delimiter starting from `start`.
fn find_matching_close(input: &str, start: usize, open: u8, close: u8) -> Option<usize> {
    let bytes = input.as_bytes();
    if start >= bytes.len() || bytes[start] != open {
        return None;
    }

    let mut depth = 0i32;
    for (i, &b) in bytes.iter().enumerate().skip(start) {
        if b == open {
            depth += 1;
        } else if b == close {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
    }
    None
}

/// Find the first occurrence of `ch` at the top level (not inside parens/braces/brackets).
fn find_top_level_char(input: &str, ch: char) -> Option<usize> {
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut depth_bracket = 0i32;

    for (i, c) in input.char_indices() {
        match c {
            '(' => depth_paren += 1,
            ')' => depth_paren -= 1,
            '{' => depth_brace += 1,
            '}' => depth_brace -= 1,
            '[' => depth_bracket += 1,
            ']' => depth_bracket -= 1,
            c2 if c2 == ch && depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 => {
                return Some(i);
            }
            _ => {}
        }
    }
    None
}

/// Find a top-level colon that is NOT part of `::` or `u#`.
fn find_top_level_colon(input: &str) -> Option<usize> {
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut depth_bracket = 0i32;
    let bytes = input.as_bytes();

    for i in 0..bytes.len() {
        match bytes[i] {
            b'(' => depth_paren += 1,
            b')' => depth_paren -= 1,
            b'{' => depth_brace += 1,
            b'}' => depth_brace -= 1,
            b'[' => depth_bracket += 1,
            b']' => depth_bracket -= 1,
            b':' if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 => {
                // Exclude `::` (cons operator) -- skip both directions
                if i + 1 < bytes.len() && bytes[i + 1] == b':' {
                    continue;
                }
                if i > 0 && bytes[i - 1] == b':' {
                    continue;
                }
                // Exclude part of `u#`
                if i > 0 && bytes[i - 1] == b'u' {
                    continue;
                }
                return Some(i);
            }
            _ => {}
        }
    }
    None
}

/// Find top-level `=` (not `==`, `==>`, `=/=`, or inside delimiters).
fn find_top_level_equals(input: &str) -> Option<usize> {
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut depth_bracket = 0i32;
    let bytes = input.as_bytes();

    for i in 0..bytes.len() {
        match bytes[i] {
            b'(' => depth_paren += 1,
            b')' => depth_paren -= 1,
            b'{' => depth_brace += 1,
            b'}' => depth_brace -= 1,
            b'[' => depth_bracket += 1,
            b']' => depth_bracket -= 1,
            b'=' if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 => {
                // Exclude `==`, `==>`, `=/=`
                if i + 1 < bytes.len() && (bytes[i + 1] == b'=' || bytes[i + 1] == b'>' || bytes[i + 1] == b'/') {
                    continue;
                }
                // Exclude `<=`, `>=`, `!=`, `==` (second = of ==)
                if i > 0 && (bytes[i - 1] == b'<' || bytes[i - 1] == b'>' || bytes[i - 1] == b'!' || bytes[i - 1] == b'=') {
                    continue;
                }
                return Some(i);
            }
            _ => {}
        }
    }
    None
}

/// Split on `->` at the top level (not inside delimiters).
fn split_top_level(input: &str, sep: &str) -> Vec<String> {
    let sep_bytes = sep.as_bytes();
    let sep_len = sep_bytes.len();
    let bytes = input.as_bytes();
    let mut segments = Vec::new();
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut depth_bracket = 0i32;
    let mut last_start = 0;

    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => { depth_paren += 1; i += 1; }
            b')' => { depth_paren -= 1; i += 1; }
            b'{' => { depth_brace += 1; i += 1; }
            b'}' => { depth_brace -= 1; i += 1; }
            b'[' => { depth_bracket += 1; i += 1; }
            b']' => { depth_bracket -= 1; i += 1; }
            _ if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0
                && i + sep_len <= bytes.len()
                && &bytes[i..i + sep_len] == sep_bytes =>
            {
                segments.push(input[last_start..i].to_string());
                i += sep_len;
                last_start = i;
            }
            _ => { i += 1; }
        }
    }
    segments.push(input[last_start..].to_string());
    segments
}

/// Split on `&` at the top level, but not `&&` or `&&&`.
fn split_top_level_ampersand(input: &str) -> Vec<String> {
    let bytes = input.as_bytes();
    let mut segments = Vec::new();
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut depth_bracket = 0i32;
    let mut last_start = 0;

    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => { depth_paren += 1; i += 1; }
            b')' => { depth_paren -= 1; i += 1; }
            b'{' => { depth_brace += 1; i += 1; }
            b'}' => { depth_brace -= 1; i += 1; }
            b'[' => { depth_bracket += 1; i += 1; }
            b']' => { depth_bracket -= 1; i += 1; }
            b'&' if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 => {
                // Must be standalone `&`, not `&&`
                let next_is_amp = i + 1 < bytes.len() && bytes[i + 1] == b'&';
                let prev_is_amp = i > 0 && bytes[i - 1] == b'&';
                if !next_is_amp && !prev_is_amp {
                    segments.push(input[last_start..i].to_string());
                    i += 1;
                    last_start = i;
                } else {
                    i += 1;
                }
            }
            _ => { i += 1; }
        }
    }
    segments.push(input[last_start..].to_string());
    segments
}

/// Split on `|` at the top level for constructor parsing.
fn split_top_level_pipe(input: &str) -> Vec<String> {
    let bytes = input.as_bytes();
    let mut segments = Vec::new();
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut depth_bracket = 0i32;
    let mut last_start = 0;

    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => { depth_paren += 1; i += 1; }
            b')' => { depth_paren -= 1; i += 1; }
            b'{' => { depth_brace += 1; i += 1; }
            b'}' => { depth_brace -= 1; i += 1; }
            b'[' => { depth_bracket += 1; i += 1; }
            b']' => { depth_bracket -= 1; i += 1; }
            b'|' if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 => {
                // Exclude `||`, `/\`, `\/`
                let next_is_pipe = i + 1 < bytes.len() && bytes[i + 1] == b'|';
                let prev_is_pipe = i > 0 && bytes[i - 1] == b'|';
                if !next_is_pipe && !prev_is_pipe {
                    let seg = input[last_start..i].to_string();
                    if !seg.trim().is_empty() {
                        segments.push(seg);
                    }
                    i += 1;
                    last_start = i;
                } else {
                    i += 1;
                }
            }
            _ => { i += 1; }
        }
    }
    let last = input[last_start..].to_string();
    if !last.trim().is_empty() {
        segments.push(last);
    }
    segments
}

/// Split a type application into head and argument tokens.
///
/// Respects parentheses, braces, and brackets so that
/// `option (int & string)` splits into `["option", "(int & string)"]`.
fn split_type_application_tokens(input: &str) -> Vec<&str> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut depth_bracket = 0i32;
    let mut token_start = None;

    for i in 0..bytes.len() {
        match bytes[i] {
            b'(' => { depth_paren += 1; if token_start.is_none() { token_start = Some(i); } }
            b')' => { depth_paren -= 1; }
            b'{' => { depth_brace += 1; if token_start.is_none() { token_start = Some(i); } }
            b'}' => { depth_brace -= 1; }
            b'[' => { depth_bracket += 1; if token_start.is_none() { token_start = Some(i); } }
            b']' => { depth_bracket -= 1; }
            b' ' | b'\t' | b'\n' if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 => {
                if let Some(start) = token_start {
                    let tok = &input[start..i];
                    if !tok.trim().is_empty() {
                        tokens.push(tok);
                    }
                    token_start = None;
                }
            }
            _ => {
                if token_start.is_none() {
                    token_start = Some(i);
                }
            }
        }
    }
    if let Some(start) = token_start {
        let tok = &input[start..];
        if !tok.trim().is_empty() {
            tokens.push(tok);
        }
    }
    tokens
}

/// Split parameter binders at the top level.
///
/// Handles sequences like `(a:Type) (n:nat) #b:Type {| tc |}`.
fn split_top_level_params(input: &str) -> Vec<String> {
    let bytes = input.as_bytes();
    let mut params = Vec::new();
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut token_start = None;

    for i in 0..bytes.len() {
        match bytes[i] {
            b'(' => {
                if depth_paren == 0 && depth_brace == 0 {
                    // Flush any preceding token
                    if let Some(start) = token_start {
                        let tok = input[start..i].trim();
                        if !tok.is_empty() {
                            params.push(tok.to_string());
                        }
                    }
                    token_start = Some(i);
                }
                depth_paren += 1;
            }
            b')' => {
                depth_paren -= 1;
                if depth_paren == 0 && depth_brace == 0 {
                    if let Some(start) = token_start {
                        params.push(input[start..=i].trim().to_string());
                        token_start = None;
                    }
                }
            }
            b'{' => {
                if depth_paren == 0 && depth_brace == 0 {
                    if let Some(start) = token_start {
                        let tok = input[start..i].trim();
                        if !tok.is_empty() {
                            params.push(tok.to_string());
                        }
                    }
                    token_start = Some(i);
                }
                depth_brace += 1;
            }
            b'}' => {
                depth_brace -= 1;
                if depth_paren == 0 && depth_brace == 0 {
                    if let Some(start) = token_start {
                        params.push(input[start..=i].trim().to_string());
                        token_start = None;
                    }
                }
            }
            b' ' | b'\t' if depth_paren == 0 && depth_brace == 0 => {
                if let Some(start) = token_start {
                    let tok = input[start..i].trim();
                    if !tok.is_empty() {
                        params.push(tok.to_string());
                    }
                    token_start = None;
                }
            }
            _ => {
                if token_start.is_none() && depth_paren == 0 && depth_brace == 0 {
                    token_start = Some(i);
                }
            }
        }
    }

    if let Some(start) = token_start {
        let tok = input[start..].trim();
        if !tok.is_empty() {
            params.push(tok.to_string());
        }
    }

    params
}

// =========================================================================
// Pragma parsing
// =========================================================================

/// Parse a pragma directive line into a structured `Pragma` value.
///
/// Handles all five F* pragma forms:
/// - `#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"`
/// - `#push-options "--fuel 2"`
/// - `#pop-options`
/// - `#reset-options` or `#reset-options "--z3rlimit 5"`
/// - `#restart-solver`
///
/// Returns `None` if the line is not a recognized pragma.
pub fn parse_pragma(line: &str) -> Option<Pragma> {
    let stripped = line.trim();

    if let Some(caps) = SET_OPTIONS_VALUE.captures(stripped) {
        let opts = caps.get(1).map(|m| m.as_str().to_string()).unwrap_or_default();
        return Some(Pragma::SetOptions(opts));
    }

    if let Some(caps) = PUSH_OPTIONS_VALUE.captures(stripped) {
        let opts = caps.get(1).map(|m| m.as_str().to_string()).unwrap_or_default();
        return Some(Pragma::PushOptions(opts));
    }

    if POP_OPTIONS.is_match(stripped) {
        return Some(Pragma::PopOptions);
    }

    if let Some(caps) = RESET_OPTIONS_VALUE.captures(stripped) {
        let opts = caps.get(1).map(|m| m.as_str().to_string());
        return Some(Pragma::ResetOptions(opts));
    }

    if RESTART_SOLVER.is_match(stripped) {
        return Some(Pragma::RestartSolver);
    }

    None
}

/// Extract individual option key-value pairs from a pragma option string.
///
/// F* options look like: `--z3rlimit 50 --fuel 0 --ifuel 0`
/// Returns a list of (key, optional_value) pairs.
pub fn parse_pragma_options(option_str: &str) -> Vec<(String, Option<String>)> {
    let mut result = Vec::new();
    let parts: Vec<&str> = option_str.split_whitespace().collect();
    let mut i = 0;

    while i < parts.len() {
        if parts[i].starts_with("--") {
            let key = parts[i].to_string();
            // Check if next token is a value (not another flag)
            if i + 1 < parts.len() && !parts[i + 1].starts_with("--") {
                result.push((key, Some(parts[i + 1].to_string())));
                i += 2;
            } else {
                result.push((key, None));
                i += 1;
            }
        } else {
            i += 1;
        }
    }

    result
}

// =========================================================================
// Attribute parsing
// =========================================================================

/// Parse F* attribute annotations from a line or block of text.
///
/// Handles all three bracket forms:
/// - `[@ attr]`   -- old-style
/// - `[@@ attr]`  -- declaration attribute
/// - `[@@@ attr]` -- binder attribute
///
/// Also handles multiple attributes separated by semicolons:
/// `[@@ attr1; attr2]`
///
/// And quoted attribute names: `[@@"opaque_to_smt"]`
pub fn parse_attributes(text: &str) -> Vec<FStarAttribute> {
    let mut attrs = Vec::new();

    for line in text.lines() {
        let stripped = line.trim();
        if let Some(caps) = ATTRIBUTE_CONTENT.captures(stripped) {
            let at_prefix = caps.get(1).map(|m| m.as_str()).unwrap_or("@@");
            let style = match at_prefix.len() {
                1 => AttributeStyle::OldStyle,
                2 => AttributeStyle::Declaration,
                _ => AttributeStyle::Binder,
            };

            let body = caps.get(2).map(|m| m.as_str().trim()).unwrap_or("");

            // Split on `;` for multiple attributes in one bracket,
            // respecting nested brackets (e.g., `strict_on_arguments [1;2]`)
            for part_str in split_respecting_parens(body, ';') {
                let part = part_str.trim();
                if part.is_empty() {
                    continue;
                }

                if let Some(name_caps) = ATTRIBUTE_NAME.captures(part) {
                    let name = name_caps.get(1)
                        .or_else(|| name_caps.get(2))
                        .map(|m| m.as_str().to_string())
                        .unwrap_or_default();

                    let args = name_caps.get(3)
                        .map(|m| m.as_str().trim().to_string())
                        .filter(|s| !s.is_empty());

                    if !name.is_empty() {
                        attrs.push(FStarAttribute { style, name, args });
                    }
                }
            }
        }
    }

    attrs
}

/// Extract attribute names from a standalone attribute line.
///
/// Returns just the names (without args) for quick lookup.
pub fn extract_attribute_names(text: &str) -> Vec<String> {
    parse_attributes(text).into_iter().map(|a| a.name).collect()
}

// =========================================================================
// SMT pattern parsing
// =========================================================================

/// Extract balanced parenthesized expression starting at `start` in `text`.
///
/// Tracks nested `(` and `)` to find the matching close.
/// Returns the content inside (exclusive of outer parens) and the end index.
fn extract_balanced_parens(text: &str, start: usize) -> Option<(String, usize)> {
    let bytes = text.as_bytes();
    if start >= bytes.len() || bytes[start] != b'(' {
        return None;
    }

    let mut depth = 0;
    let mut i = start;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    let content = &text[start + 1..i];
                    return Some((content.to_string(), i + 1));
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Extract balanced bracketed expression starting at `start` in `text`.
///
/// Tracks nested `[` and `]` to find the matching close.
/// Returns the content inside (exclusive of outer brackets) and the end index.
fn extract_balanced_brackets(text: &str, start: usize) -> Option<(String, usize)> {
    let bytes = text.as_bytes();
    if start >= bytes.len() || bytes[start] != b'[' {
        return None;
    }

    let mut depth = 0;
    let mut i = start;
    while i < bytes.len() {
        match bytes[i] {
            b'[' => depth += 1,
            b']' => {
                depth -= 1;
                if depth == 0 {
                    let content = &text[start + 1..i];
                    return Some((content.to_string(), i + 1));
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Parse SMT patterns from a val/lemma signature text.
///
/// Finds the trailing `[SMTPat ...]` or `[SMTPatOr [...]]` bracket
/// at the end of a declaration and parses its contents.
///
/// Real-world patterns from FStar/ulib:
/// ```text
/// [SMTPat (f x)]
/// [SMTPat (f x); SMTPat (g y)]
/// [SMTPatOr [[SMTPat (f x)]; [SMTPat (g x)]]]
/// ```
pub fn parse_smt_patterns(text: &str) -> Vec<SmtPattern> {
    let clean = strip_comments_and_strings(text);

    // Find the outermost SMT pattern bracket
    let bracket_start = match SMT_PATTERN_BRACKET.find(&clean) {
        Some(m) => m.start(),
        None => return Vec::new(),
    };

    // Extract the full bracketed content
    let (bracket_content, _) = match extract_balanced_brackets(&clean, bracket_start) {
        Some(pair) => pair,
        None => return Vec::new(),
    };

    parse_smt_pattern_list(&bracket_content)
}

/// Parse a semicolon-separated list of SMT patterns from bracket content.
///
/// Input is the content inside `[...]` (without the outer brackets).
fn parse_smt_pattern_list(content: &str) -> Vec<SmtPattern> {
    let mut patterns = Vec::new();
    let trimmed = content.trim();

    if trimmed.is_empty() {
        return patterns;
    }

    // Check for SMTPatOr at the start
    if let Some(m) = SMTPATOR_START.find(trimmed) {
        let after = trimmed[m.end()..].trim();
        // SMTPatOr should be followed by [[pats]; [pats]; ...]
        if let Some(bracket_pos) = after.find('[') {
            let abs_pos = m.end() + (after.len() - after.len()) + bracket_pos;
            let full_after = &trimmed[m.end()..].trim_start();
            if let Some(start) = full_after.find('[') {
                if let Some((or_content, _)) = extract_balanced_brackets(full_after, start) {
                    // Parse each alternative: [pats]; [pats]; ...
                    let alternatives = split_smt_alternatives(&or_content);
                    let mut alt_pats = Vec::new();
                    for alt in alternatives {
                        alt_pats.push(parse_smt_pattern_list(&alt));
                    }
                    patterns.push(SmtPattern::PatOr(alt_pats));
                    return patterns;
                }
            }
            // Fallback: just record as PatOr with content
            let _ = abs_pos; // suppress unused warning
            let _ = bracket_pos;
        }
        return patterns;
    }

    // Otherwise, parse semicolon-separated SMTPat entries
    // We need to respect balanced parens when splitting on semicolons
    let entries = split_respecting_parens(trimmed, ';');
    for entry in entries {
        let entry = entry.trim();
        if entry.is_empty() {
            continue;
        }
        if let Some(m) = SMTPAT_START.find(entry) {
            let after = entry[m.end()..].trim();
            // Find the parenthesized expression
            if let Some(paren_start) = after.find('(') {
                if let Some((expr, _)) = extract_balanced_parens(after, paren_start) {
                    patterns.push(SmtPattern::Pat(expr.trim().to_string()));
                }
            } else {
                // SMTPat without parens - the rest is the pattern
                patterns.push(SmtPattern::Pat(after.to_string()));
            }
        }
    }

    patterns
}

/// Split text on `delimiter`, respecting balanced parentheses and brackets.
fn split_respecting_parens(text: &str, delimiter: char) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut paren_depth = 0;
    let mut bracket_depth = 0;

    for ch in text.chars() {
        match ch {
            '(' => { paren_depth += 1; current.push(ch); }
            ')' => { paren_depth -= 1; current.push(ch); }
            '[' => { bracket_depth += 1; current.push(ch); }
            ']' => { bracket_depth -= 1; current.push(ch); }
            c if c == delimiter && paren_depth == 0 && bracket_depth == 0 => {
                parts.push(current.clone());
                current.clear();
            }
            _ => { current.push(ch); }
        }
    }
    if !current.is_empty() {
        parts.push(current);
    }
    parts
}

/// Split SMTPatOr alternatives: `[pats]; [pats]; ...` into individual bracket contents.
fn split_smt_alternatives(content: &str) -> Vec<String> {
    let mut alternatives = Vec::new();
    let bytes = content.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        if bytes[i] == b'[' {
            if let Some((inner, end)) = extract_balanced_brackets(content, i) {
                alternatives.push(inner);
                i = end;
            } else {
                i += 1;
            }
        } else {
            i += 1;
        }
    }

    alternatives
}

/// Extract identifiers referenced inside SMT patterns.
///
/// Useful for dependency analysis: identifiers in SMTPat triggers
/// are real references to functions/values.
pub fn extract_smt_pattern_references(patterns: &[SmtPattern]) -> HashSet<String> {
    let mut refs = HashSet::new();
    for pat in patterns {
        match pat {
            SmtPattern::Pat(expr) => {
                // Extract identifiers from the expression
                for caps in TYPE_REF_PATTERN
                    .captures_iter(expr)
                    .filter_map(|r| r.ok())
                {
                    if let Some(m) = caps.get(1) {
                        let name = m.as_str();
                        if !FSTAR_KEYWORDS.contains(name) {
                            refs.insert(name.to_string());
                        }
                    }
                }
            }
            SmtPattern::PatOr(alternatives) => {
                for alt in alternatives {
                    refs.extend(extract_smt_pattern_references(alt));
                }
            }
        }
    }
    refs
}

// =========================================================================
// Tactic expression parsing
// =========================================================================

/// Extract tactic expressions from F* code text.
///
/// Finds all occurrences of:
/// - `assert <prop> by (<tactic>)` -- assert with tactic proof
/// - `_ by (<tactic>)` -- wildcard with tactic (calc blocks, definitions)
/// - `synth_by_tactic (<tactic>)` -- synthesize via tactic
///
/// The tactic body is extracted using balanced parenthesis tracking.
pub fn extract_tactic_bodies(text: &str) -> Vec<TacticExpr> {
    let clean = strip_comments_and_strings(text);
    let mut tactics = Vec::new();

    // Find assert ... by (...) patterns
    for m in ASSERT_BY_PATTERN.find_iter(&clean) {
        let after_by = &clean[m.end()..];
        // We're positioned right after the opening `(` of `by (`
        // Need to find the matching `)` (start counting from depth=1)
        if let Some(body) = extract_paren_body_from(after_by) {
            let assertion = ASSERT_BY_PATTERN
                .captures(&clean[m.start()..])
                .and_then(|c| c.get(1))
                .map(|m| m.as_str().trim().to_string())
                .unwrap_or_default();
            tactics.push(TacticExpr::AssertBy {
                assertion,
                tactic_body: body.trim().to_string(),
            });
        }
    }

    // Find _ by (...) patterns
    for m in WILDCARD_BY_PATTERN.find_iter(&clean) {
        let after_paren = &clean[m.end()..];
        if let Some(body) = extract_paren_body_from(after_paren) {
            tactics.push(TacticExpr::WildcardBy {
                tactic_body: body.trim().to_string(),
            });
        }
    }

    // Find synth_by_tactic (...) patterns
    for m in SYNTH_BY_TACTIC_PATTERN.find_iter(&clean) {
        let after_paren = &clean[m.end()..];
        if let Some(body) = extract_paren_body_from(after_paren) {
            tactics.push(TacticExpr::SynthByTactic {
                tactic_body: body.trim().to_string(),
            });
        }
    }

    tactics
}

/// Extract body from text starting right after an opening `(`.
///
/// Tracks balanced parens to find the matching `)`.
/// Returns content inside the parens (exclusive).
fn extract_paren_body_from(text: &str) -> Option<String> {
    let mut depth = 1;

    for (i, ch) in text.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(text[..i].to_string());
                }
            }
            _ => {}
        }
    }
    None
}

/// Check if text contains any tactic-related constructs.
///
/// Quick check useful for deciding whether to run full tactic extraction.
pub fn contains_tactic_constructs(text: &str) -> bool {
    let clean = strip_comments_and_strings(text);
    ASSERT_BY_PATTERN.is_match(&clean)
        || WILDCARD_BY_PATTERN.is_match(&clean)
        || SYNTH_BY_TACTIC_PATTERN.is_match(&clean)
}

// =========================================================================
// Quotation parsing
// =========================================================================

/// Extract backtick quotation forms from F* metaprogramming code.
///
/// Finds all quotation forms:
/// - `` `name `` -- quote identifier
/// - `` `%name `` -- quote fully qualified name
/// - `` `#name `` -- antiquotation
/// - `` `(expr) `` -- quote expression
///
/// Real-world examples from FStar/ulib:
/// ```text
/// delta_only [`%calc_chain_related]
/// apply_lemma (`other_lemma)
/// norm [delta_only [`%on_domain]]
/// ```
pub fn extract_quotations(text: &str) -> Vec<Quotation> {
    let clean = strip_comments_and_strings(text);
    let mut quotations = Vec::new();

    for caps in QUOTATION_PATTERN
        .captures_iter(&clean)
        .filter_map(|r| r.ok())
    {
        if let Some(m) = caps.get(1) {
            let content = m.as_str();
            if let Some(rest) = content.strip_prefix('%') {
                quotations.push(Quotation::QualifiedName(rest.to_string()));
            } else if let Some(rest) = content.strip_prefix('#') {
                quotations.push(Quotation::Antiquote(rest.to_string()));
            } else if content.starts_with('(') && content.ends_with(')') {
                quotations.push(Quotation::Expr(content[1..content.len()-1].to_string()));
            } else {
                quotations.push(Quotation::Name(content.to_string()));
            }
        }
    }

    quotations
}

/// Extract identifiers referenced through quotation.
///
/// Quoted identifiers are real references to definitions:
/// `` `%foo `` refers to the definition `foo`.
/// `` `name `` refers to `name`.
pub fn extract_quotation_references(text: &str) -> HashSet<String> {
    let mut refs = HashSet::new();
    for q in extract_quotations(text) {
        match q {
            Quotation::Name(name) | Quotation::QualifiedName(name) => {
                // For qualified names like `Foo.bar`, extract the last component
                if let Some(last) = name.rsplit('.').next() {
                    if !FSTAR_KEYWORDS.contains(last) {
                        refs.insert(last.to_string());
                    }
                }
            }
            Quotation::Antiquote(name) => {
                if let Some(last) = name.rsplit('.').next() {
                    if !FSTAR_KEYWORDS.contains(last) {
                        refs.insert(last.to_string());
                    }
                }
            }
            Quotation::Expr(expr) => {
                // Extract identifiers from the expression
                for caps in TYPE_REF_PATTERN
                    .captures_iter(&expr)
                    .filter_map(|r| r.ok())
                {
                    if let Some(m) = caps.get(1) {
                        let name = m.as_str();
                        if !FSTAR_KEYWORDS.contains(name) {
                            refs.insert(name.to_string());
                        }
                    }
                }
            }
        }
    }
    refs
}

/// Extract type/val references from declaration text.
///
/// Filters out comments and string literals to avoid false dependencies.
/// Also recognizes F* operator syntax and maps to op_* function names.
/// Additionally extracts references from quotation forms and SMT patterns.
pub fn extract_references(text: &str, exclude_names: &HashSet<String>) -> HashSet<String> {
    let clean_text = strip_comments_and_strings(text);
    let mut refs = HashSet::new();

    // Extract identifier references
    // fancy-regex captures_iter returns Results, so we filter_map
    for caps in TYPE_REF_PATTERN
        .captures_iter(&clean_text)
        .filter_map(|r| r.ok())
    {
        if let Some(m) = caps.get(1) {
            let name = m.as_str();
            if !FSTAR_KEYWORDS.contains(name) && !exclude_names.contains(name) {
                refs.insert(name.to_string());
            }
        }
    }

    // Extract operator references: @%. -> op_At_Percent_Dot
    // fancy_regex captures_iter returns Results
    for caps in FSTAR_OP_PATTERN.captures_iter(&clean_text).filter_map(|r| r.ok()) {
        if let Some(m) = caps.get(1) {
            let op_str = m.as_str();
            if let Some(func_name) = operator_to_function_name(op_str) {
                if !exclude_names.contains(&func_name) {
                    refs.insert(func_name);
                }
            }
        }
    }

    // Extract references from backtick quotations (metaprogramming).
    // Quoted names like `%foo or `bar are real references to definitions.
    for q_ref in extract_quotation_references(text) {
        if !exclude_names.contains(&q_ref) {
            refs.insert(q_ref);
        }
    }

    refs
}

/// Parse an F* file into header lines and declaration blocks.
pub fn parse_fstar_file(content: &str) -> (Vec<String>, Vec<DeclarationBlock>) {
    let lines: Vec<&str> = content.lines().collect();
    let mut header_lines: Vec<String> = Vec::new();
    let mut blocks: Vec<DeclarationBlock> = Vec::new();

    let n = lines.len();
    let mut i = 0;

    // Phase 1: Collect header (module, opens, friends, initial comments, initial #set-options)
    let in_header = true;
    let mut comment_depth: i32 = 0;

    while i < n && in_header {
        let line = lines[i];
        let stripped = line.trim();

        // Track comment depth
        let (opens, closes) = count_comment_opens_closes(line);
        let prev_depth = comment_depth;
        comment_depth += opens as i32 - closes as i32;

        // Empty line in header
        if stripped.is_empty() {
            header_lines.push(line_newline(line));
            i += 1;
            continue;
        }

        // Inside multi-line comment
        if prev_depth > 0 || (opens > 0 && comment_depth > 0) {
            header_lines.push(line_newline(line));
            i += 1;
            continue;
        }

        // Check for module/open/friend
        if is_header_line(line).is_some() {
            header_lines.push(line_newline(line));
            i += 1;
            continue;
        }

        // Check for standalone #set-options at file level
        if is_standalone_options(line) {
            header_lines.push(line_newline(line));
            i += 1;
            continue;
        }

        // Check if this is a file-level comment (doc comment before declarations)
        if stripped.starts_with("(*") {
            // Collect entire comment
            let mut comment_lines_temp = vec![line];
            let mut temp_depth = comment_depth;
            let mut j = i + 1;

            while j < n && temp_depth > 0 {
                let (c_opens, c_closes) = count_comment_opens_closes(lines[j]);
                temp_depth += c_opens as i32 - c_closes as i32;
                comment_lines_temp.push(lines[j]);
                j += 1;
            }

            // Skip blank lines after comment
            let mut peek = j;
            while peek < n && lines[peek].trim().is_empty() {
                peek += 1;
            }

            // Check what follows
            if peek < n {
                let next_header = is_header_line(lines[peek]);
                let next_opts = is_standalone_options(lines[peek]);
                if next_header.is_some() || next_opts {
                    // Comment is part of header
                    for cl in comment_lines_temp {
                        header_lines.push(line_newline(cl));
                    }
                    i = j;
                    comment_depth = 0;
                    continue;
                }
            }

            // This comment is before declarations - ends header
            break;
        }

        // Any other content ends header
        break;
    }

    // Reset comment depth for declaration parsing
    comment_depth = 0;

    // Phase 2: Parse declarations
    let mut pending_lines: Vec<String> = Vec::new();
    let mut pending_start = i + 1;
    let mut pending_push_options = false;

    while i < n {
        let line = lines[i];
        let stripped = line.trim();

        // Track comment depth for multi-line comments
        let (opens, closes) = count_comment_opens_closes(line);
        let prev_depth = comment_depth;
        comment_depth += opens as i32 - closes as i32;

        // Inside multi-line comment - accumulate
        if prev_depth > 0 {
            pending_lines.push(line_newline(line));
            i += 1;
            continue;
        }

        // Blank line - accumulate sparingly
        if stripped.is_empty() {
            // Only keep if we have content before, and not too many blanks
            if !pending_lines.is_empty()
                && !pending_lines
                    .last()
                    .map(|l| l.trim().is_empty())
                    .unwrap_or(true)
            {
                pending_lines.push(line_newline(line));
            }
            i += 1;
            continue;
        }

        // #push-options - starts potential block
        if is_push_options(line) {
            if pending_lines.is_empty() {
                pending_start = i + 1;
            }
            pending_lines.push(line_newline(line));
            pending_push_options = true;
            i += 1;
            continue;
        }

        // #pop-options - attach to current block if we have one with push
        if is_pop_options(line) {
            let attach_to_block = blocks.last().is_some_and(|b| {
                b.has_push_options && !b.has_pop_options
            });
            if attach_to_block {
                if let Some(last) = blocks.last_mut() {
                    last.lines.push(line_newline(line));
                    last.has_pop_options = true;
                }
            } else {
                pending_lines.push(line_newline(line));
            }
            i += 1;
            continue;
        }

        // Standalone #set-options in body - attach to pending
        if is_standalone_options(line) {
            if pending_lines.is_empty() {
                pending_start = i + 1;
            }
            pending_lines.push(line_newline(line));
            i += 1;
            continue;
        }

        // `//` line comment - accumulate as pending content
        if is_line_comment(line) {
            if pending_lines.is_empty() {
                pending_start = i + 1;
            }
            pending_lines.push(line_newline(line));
            i += 1;
            continue;
        }

        // Block comment start: `(* ... *)`
        if stripped.starts_with("(*") {
            let mut comment_lines_here = vec![line];
            let mut temp_depth = comment_depth;
            let mut j = i + 1;

            while j < n && temp_depth > 0 {
                let (c_opens, c_closes) = count_comment_opens_closes(lines[j]);
                temp_depth += c_opens as i32 - c_closes as i32;
                comment_lines_here.push(lines[j]);
                j += 1;
            }

            if pending_lines.is_empty() {
                pending_start = i + 1;
            }
            for cl in comment_lines_here {
                pending_lines.push(line_newline(cl));
            }
            i = j;
            comment_depth = 0;
            continue;
        }

        // Multi-line attribute: `[@@ Comment "..." ` without closing `]` on same line.
        // Consume all lines until we find the closing `]`.
        if is_multiline_attribute_start(line) {
            if pending_lines.is_empty() {
                pending_start = i + 1;
            }
            pending_lines.push(line_newline(line));
            i += 1;
            // Consume continuation lines until the attribute closes
            while i < n {
                let attr_line = lines[i];
                pending_lines.push(line_newline(attr_line));
                i += 1;
                if attr_line.trim().ends_with(']') {
                    break;
                }
            }
            continue;
        }

        // Mid-file module system constructs: open, friend, include, module abbreviation.
        // In real F* code (HACL*, EverParse) these appear interspersed with declarations.
        // They should be emitted as single-line blocks, not accumulated as pending content.
        if let Some((block_type, name, mod_path)) = extract_module_construct_info(line) {
            // Module constructs that are NOT the top-level `module Name` declaration
            // (top-level module is already handled in the header).
            let is_module_decl = block_type == BlockType::Module;
            if !is_module_decl {
                // Flush any pending lines as a comment block first
                if !pending_lines.is_empty() {
                    // Take ownership instead of cloning + clear
                    let mut flush_lines = std::mem::take(&mut pending_lines);
                    pending_push_options = false;
                    while !flush_lines.is_empty()
                        && flush_lines.last().map(|l| l.trim().is_empty()).unwrap_or(false)
                    {
                        flush_lines.pop();
                    }
                    if !flush_lines.is_empty() {
                        blocks.push(DeclarationBlock {
                            block_type: BlockType::Comment,
                            names: Vec::new(),
                            lines: flush_lines,
                            start_line: pending_start,
                            has_push_options: pending_push_options,
                            has_pop_options: false,
                            references: HashSet::new(),
                            module_path: None,
                            is_private: false,
                            is_abstract: false,
                            effect_signature: None,
                        });
                    }
                }

                blocks.push(DeclarationBlock {
                    block_type,
                    names: vec![name],
                    lines: vec![line_newline(line)],
                    start_line: i + 1,
                    has_push_options: false,
                    has_pop_options: false,
                    references: HashSet::new(),
                    module_path: mod_path,
                    is_private: false,
                    is_abstract: false,
                    effect_signature: None,
                });
                i += 1;
                continue;
            }
        }

        // Standalone modifier lines (e.g., `inline_for_extraction noextract`)
        // These are accumulated as pending lines to attach to the next declaration.
        if is_standalone_modifier(line) {
            if pending_lines.is_empty() {
                pending_start = i + 1;
            }
            pending_lines.push(line_newline(line));
            i += 1;
            continue;
        }

        // Check for declaration start
        if let Some((decl_name, decl_type)) = get_declaration_info(line) {
            let mut all_names = vec![decl_name];

            // Check for inline 'and' on the same line
            // e.g., "type expr = ELit of int and stmt = SExpr of expr"
            let inline_and_names = extract_inline_and_names(line);
            all_names.extend(inline_and_names);

            // Collect the declaration lines -- take ownership to avoid clone
            let had_pending = !pending_lines.is_empty();
            let mut decl_lines: Vec<String> = std::mem::take(&mut pending_lines);
            decl_lines.push(line_newline(line));
            let decl_start = if !had_pending {
                i + 1
            } else {
                pending_start
            };
            let has_push = pending_push_options;
            pending_push_options = false;

            i += 1;

            // Continue reading declaration body and 'and' continuations
            while i < n {
                let next_line = lines[i];
                let next_stripped = next_line.trim();

                // Track comments within declaration
                let (c_opens, c_closes) = count_comment_opens_closes(next_line);
                comment_depth += c_opens as i32 - c_closes as i32;

                if comment_depth > 0 {
                    decl_lines.push(line_newline(next_line));
                    i += 1;
                    continue;
                }

                // Check for 'and' continuation (mutual recursion)
                if let Some(and_name) = get_and_name(next_line) {
                    all_names.push(and_name);
                    decl_lines.push(line_newline(next_line));
                    i += 1;
                    continue;
                }

                // Check for new declaration (ends current)
                if get_declaration_info(next_line).is_some() {
                    break;
                }

                // Check for #pop-options
                if is_pop_options(next_line) {
                    if has_push {
                        decl_lines.push(line_newline(next_line));
                        i += 1;
                    }
                    break;
                }

                // Check for #push-options (starts new context)
                if is_push_options(next_line) {
                    break;
                }

                // Header-like items shouldn't appear in body
                if is_header_line(next_line).is_some() {
                    break;
                }

                // Standalone modifiers (e.g., `noextract`, `inline_for_extraction`)
                // at column 0 indicate the start of a new declaration, not
                // continuation of the current one.
                if is_standalone_modifier(next_line) {
                    break;
                }

                // Blank lines - check if declaration continues
                if next_stripped.is_empty() {
                    // Look ahead for continuation
                    let mut peek = i + 1;
                    let mut blank_count = 1;
                    while peek < n && lines[peek].trim().is_empty() {
                        blank_count += 1;
                        peek += 1;
                    }

                    if blank_count >= 2 && peek < n {
                        // Two+ blank lines often indicate section break
                        let peek_decl = get_declaration_info(lines[peek]);
                        let peek_and = get_and_name(lines[peek]);
                        if peek_decl.is_some() || peek_and.is_some() {
                            break;
                        }
                    }

                    decl_lines.push(line_newline(next_line));
                    i += 1;
                    continue;
                }

                // Regular content line
                decl_lines.push(line_newline(next_line));
                i += 1;
            }

            // Extract references from declaration
            let decl_text: String = decl_lines.concat();
            let exclude: HashSet<String> = all_names.iter().cloned().collect();
            let refs = extract_references(&decl_text, &exclude);

            // Detect visibility modifiers on the declaration line AND on
            // any pending modifier lines that precede it.
            // Real-world pattern from HACL* (`Hacl.Streaming.SHA2.fst`):
            //   [@@ CInline ]
            //   private
            //   let update_224_256 = ...
            let (mut is_priv, mut is_abs) = detect_visibility_modifiers(line);
            if !is_priv || !is_abs {
                for pending in &decl_lines {
                    let (p, a) = detect_visibility_modifiers(pending);
                    is_priv = is_priv || p;
                    is_abs = is_abs || a;
                }
            }

            // For module abbreviations or include declarations, extract module path
            let mod_path = if decl_type == BlockType::ModuleAbbrev {
                MODULE_ABBREV_PATTERN
                    .captures(line.trim())
                    .and_then(|caps| caps.get(2).map(|m| m.as_str().to_string()))
            } else if decl_type == BlockType::Include {
                INCLUDE_MODULE_PATTERN
                    .captures(line.trim())
                    .and_then(|caps| caps.get(1).map(|m| m.as_str().to_string()))
            } else {
                None
            };

            let mut block = DeclarationBlock {
                block_type: decl_type,
                names: all_names,
                lines: decl_lines,
                start_line: decl_start,
                has_push_options: has_push,
                has_pop_options: false,
                references: refs,
                module_path: mod_path,
                is_private: is_priv,
                is_abstract: is_abs,
                effect_signature: None,
            };
            // Extract effect signature for relevant block types
            block.effect_signature = extract_effect_signature(&block);
            blocks.push(block);
            comment_depth = 0;
            continue;
        }

        // Unrecognized content - accumulate
        if pending_lines.is_empty() {
            pending_start = i + 1;
        }
        pending_lines.push(line_newline(line));
        i += 1;
    }

    // Flush any remaining pending content as comment block
    if !pending_lines.is_empty() {
        // Strip trailing blank lines
        while !pending_lines.is_empty()
            && pending_lines
                .last()
                .map(|l| l.trim().is_empty())
                .unwrap_or(false)
        {
            pending_lines.pop();
        }
        if !pending_lines.is_empty() {
            blocks.push(DeclarationBlock {
                block_type: BlockType::Comment,
                names: Vec::new(),
                lines: pending_lines,
                start_line: pending_start,
                has_push_options: pending_push_options,
                has_pop_options: false,
                references: HashSet::new(),
                module_path: None,
                is_private: false,
                is_abstract: false,
                effect_signature: None,
            });
        }
    }

    (header_lines, blocks)
}

/// Extract ordered list of definition names from .fst implementation file.
pub fn get_definition_order(content: &str) -> Vec<String> {
    let (_, blocks) = parse_fstar_file(content);
    let mut names = Vec::new();
    for block in blocks {
        for name in block.names {
            if !names.contains(&name) {
                names.push(name);
            }
        }
    }
    names
}

/// Build a dependency graph from declaration blocks.
pub fn build_dependency_graph(blocks: &[DeclarationBlock]) -> HashMap<String, HashSet<String>> {
    // Collect all declared names
    let mut declared_names = HashSet::new();
    for block in blocks {
        declared_names.extend(block.names.iter().cloned());
    }

    // Build dependency graph
    let mut deps: HashMap<String, HashSet<String>> = HashMap::new();
    for block in blocks {
        for name in &block.names {
            // Filter references to only include names declared in this file
            let valid_refs: HashSet<String> = block
                .references
                .intersection(&declared_names)
                .cloned()
                .collect();
            // Remove self-references (same block)
            let block_names: HashSet<String> = block.names.iter().cloned().collect();
            let final_refs: HashSet<String> =
                valid_refs.difference(&block_names).cloned().collect();
            deps.insert(name.clone(), final_refs);
        }
    }

    deps
}

/// Count balanced delimiter pairs.
/// Returns the net difference (opens - closes).

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_file() {
        let content = r#"module Test

open FStar.All

val foo : int -> int
let foo x = x + 1

type mytype = int
"#;
        let (header, blocks) = parse_fstar_file(content);
        assert!(!header.is_empty());
        assert!(blocks.iter().any(|b| b.names.contains(&"foo".to_string())));
        assert!(blocks
            .iter()
            .any(|b| b.names.contains(&"mytype".to_string())));
    }

    #[test]
    fn test_mutual_recursion() {
        let content = r#"module Test

type a = A of b
and b = B of a
"#;
        let (_, blocks) = parse_fstar_file(content);
        // Both a and b should be in the same block
        let type_block = blocks.iter().find(|b| b.names.contains(&"a".to_string()));
        assert!(type_block.is_some());
        assert!(type_block.unwrap().names.contains(&"b".to_string()));
    }

    #[test]
    fn test_no_leading_whitespace() {
        // Indented 'let' should NOT be parsed as declaration
        let content = r#"module Test

val foo : int -> int
let foo x =
  let y = x + 1 in
  y
"#;
        let (_, blocks) = parse_fstar_file(content);
        // Should only have 'foo' as declaration, not 'y'
        let names: Vec<&str> = blocks
            .iter()
            .flat_map(|b| b.names.iter().map(|s| s.as_str()))
            .collect();
        assert!(names.contains(&"foo"));
        assert!(!names.contains(&"y"));
    }

    #[test]
    fn test_extract_references_qualified_names_excluded() {
        // In F*, `S.bn_add` means `bn_add` from module alias `S`.
        // The `bn_add` part should NOT be extracted as a local reference
        // because it's a qualified name, not a reference to a locally
        // declared `bn_add`.
        let text = "val foo: S.bn_add -> Module.bar -> baz";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        // `S` and `Module` are module-level names (still extracted)
        assert!(refs.contains("S"), "Module alias S should be extracted");
        assert!(
            refs.contains("Module"),
            "Module name should be extracted"
        );

        // `bn_add` and `bar` follow a dot - they are qualified and should NOT be extracted
        assert!(
            !refs.contains("bn_add"),
            "Qualified name bn_add (after dot) should NOT be extracted"
        );
        assert!(
            !refs.contains("bar"),
            "Qualified name bar (after dot) should NOT be extracted"
        );

        // `baz` is unqualified - should be extracted
        assert!(refs.contains("baz"), "Unqualified name baz should be extracted");
    }

    #[test]
    fn test_extract_references_nested_qualified_names() {
        // Nested qualified: A.B.c - only A should match
        let text = "val foo: A.B.c -> int";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(refs.contains("A"), "Top-level module A should be extracted");
        assert!(
            !refs.contains("B"),
            "Nested module B (after dot) should NOT be extracted"
        );
        assert!(
            !refs.contains("c"),
            "Nested name c (after dot) should NOT be extracted"
        );
    }

    #[test]
    fn test_extract_references_unqualified_still_works() {
        // Unqualified references should still work normally
        let text = "val foo: mytype -> result_t";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(refs.contains("mytype"));
        assert!(refs.contains("result_t"));
        assert!(refs.contains("foo"));
    }

    #[test]
    fn test_inline_and_extraction() {
        // Single-line mutual recursion
        let line = "type expr = ELit of int and stmt = SExpr of expr";
        let names = extract_inline_and_names(line);
        assert_eq!(names, vec!["stmt"]);
    }

    #[test]
    fn test_inline_and_extraction_multiple() {
        // Multiple inline 'and' patterns
        let line = "type a = A and b = B and c = C";
        let names = extract_inline_and_names(line);
        assert_eq!(names, vec!["b", "c"]);
    }

    #[test]
    fn test_inline_and_extraction_none() {
        // No inline 'and' - just regular type
        let line = "type foo = int";
        let names = extract_inline_and_names(line);
        assert!(names.is_empty());
    }

    #[test]
    fn test_operator_to_function_name() {
        assert_eq!(operator_to_function_name("@%."), Some("op_At_Percent_Dot".to_string()));
        assert_eq!(operator_to_function_name("|>"), Some("op_Bar_Greater".to_string()));
        assert_eq!(operator_to_function_name("+"), Some("op_Plus".to_string()));
        assert_eq!(operator_to_function_name("*"), Some("op_Star".to_string()));
        assert_eq!(operator_to_function_name("<=>"), Some("op_Less_Equals_Greater".to_string()));
    }

    #[test]
    fn test_operator_to_function_name_invalid() {
        // Characters not in the operator mapping
        assert_eq!(operator_to_function_name("abc"), None);
        assert_eq!(operator_to_function_name(""), None);
    }

    #[test]
    fn test_extract_references_operators() {
        // Operators should be extracted as op_* function names
        let text = "let f x y = x @%. y";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        // Note: The pattern requires whitespace around the operator
        // "x @%. y" should extract op_At_Percent_Dot
        assert!(refs.contains("x"));
        assert!(refs.contains("y"));
        // The operator pattern matches operators surrounded by whitespace
    }

    #[test]
    fn test_parse_inline_mutual_recursion() {
        let content = r#"module Test

type expr = ELit of int and stmt = SExpr of expr
"#;
        let (_, blocks) = parse_fstar_file(content);
        // The type block should contain both names
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type);
        assert!(type_block.is_some());
        let names = &type_block.unwrap().names;
        assert!(names.contains(&"expr".to_string()), "Should contain expr");
        assert!(names.contains(&"stmt".to_string()), "Should contain stmt from inline and");
    }

    // =========================================================================
    // count_comment_opens_closes: state machine tests
    // =========================================================================

    #[test]
    fn test_comment_count_basic() {
        assert_eq!(count_comment_opens_closes("(* comment *)"), (1, 1));
    }

    #[test]
    fn test_comment_count_no_delimiters() {
        assert_eq!(count_comment_opens_closes("let x = 1"), (0, 0));
    }

    #[test]
    fn test_comment_count_nested() {
        // (* outer (* inner *) outer *)
        assert_eq!(
            count_comment_opens_closes("(* outer (* inner *) outer *)"),
            (2, 2)
        );
    }

    #[test]
    fn test_comment_count_open_only() {
        assert_eq!(count_comment_opens_closes("(* start of comment"), (1, 0));
    }

    #[test]
    fn test_comment_count_close_only() {
        assert_eq!(count_comment_opens_closes("end of comment *)"), (0, 1));
    }

    #[test]
    fn test_comment_count_overlap_open_close() {
        // (*)  ->  (* is consumed first, then ) is alone (not *))
        // This is 1 open, 0 closes
        assert_eq!(count_comment_opens_closes("(*)"), (1, 0));
    }

    #[test]
    fn test_comment_count_string_with_open() {
        // "(*" inside a string should NOT be counted
        assert_eq!(count_comment_opens_closes(r#"let x = "(*""#), (0, 0));
    }

    #[test]
    fn test_comment_count_string_with_close() {
        // "*)" inside a string should NOT be counted
        assert_eq!(count_comment_opens_closes(r#"let x = "*)""#), (0, 0));
    }

    #[test]
    fn test_comment_count_string_then_real_comment() {
        // String "(*" followed by a real (* comment *)
        assert_eq!(
            count_comment_opens_closes(r#"let x = "(*" (* real comment *)"#),
            (1, 1)
        );
    }

    #[test]
    fn test_comment_count_escaped_quote_in_string() {
        // String with escaped quote: "hello\"(*" - the (* is still inside the string
        assert_eq!(
            count_comment_opens_closes(r#"let x = "hello\"(*""#),
            (0, 0)
        );
    }

    #[test]
    fn test_comment_count_escaped_backslash_before_quote() {
        // "test\\" -> string content is test\ (escaped backslash),
        // then (* is OUTSIDE the string
        assert_eq!(
            count_comment_opens_closes(r#""test\\" (* comment *)"#),
            (1, 1)
        );
    }

    #[test]
    fn test_comment_count_multiple_escaped_backslashes() {
        // "\\\\" -> four backslashes = two escaped pairs, string closes at next "
        // Then (* is outside
        assert_eq!(
            count_comment_opens_closes(r#""\\\\" (* c *)"#),
            (1, 1)
        );
    }

    #[test]
    fn test_comment_count_odd_backslashes_before_quote() {
        // "\\\"" -> \\=escaped backslash, then \"=escaped quote, string continues
        // No comment delimiters at all
        assert_eq!(
            count_comment_opens_closes(r#""\\\"" "#),
            (0, 0)
        );
    }

    #[test]
    fn test_comment_count_doc_comment() {
        // (** doc comment *) is one open, one close
        assert_eq!(count_comment_opens_closes("(** doc comment *)"), (1, 1));
    }

    #[test]
    fn test_comment_count_empty_string() {
        assert_eq!(count_comment_opens_closes(""), (0, 0));
    }

    #[test]
    fn test_comment_count_string_only() {
        assert_eq!(
            count_comment_opens_closes(r#""(* not a comment *) ""#),
            (0, 0)
        );
    }

    // =========================================================================
    // strip_comments_and_strings: comprehensive tests
    // =========================================================================

    #[test]
    fn test_strip_basic_comment() {
        assert_eq!(
            strip_comments_and_strings("code (* comment *) more"),
            "code  more"
        );
    }

    #[test]
    fn test_strip_basic_string() {
        assert_eq!(strip_comments_and_strings(r#"code "string" more"#), "code  more");
    }

    #[test]
    fn test_strip_nested_comments() {
        assert_eq!(
            strip_comments_and_strings("before (* outer (* inner *) outer *) after"),
            "before  after"
        );
    }

    #[test]
    fn test_strip_string_inside_comment() {
        // F*/OCaml convention: strings inside comments are respected
        // (* "*)" *) should be ONE comment, the *) inside the string is ignored
        assert_eq!(
            strip_comments_and_strings(r#"before (* "*)" *) after"#),
            "before  after"
        );
    }

    #[test]
    fn test_strip_string_with_comment_marker() {
        // "(*" in a string should not start a comment
        assert_eq!(
            strip_comments_and_strings(r#"before "(*" after"#),
            "before  after"
        );
    }

    #[test]
    fn test_strip_string_with_close_marker() {
        // "*)" in a string should not close anything
        assert_eq!(
            strip_comments_and_strings(r#"before "*)" after"#),
            "before  after"
        );
    }

    #[test]
    fn test_strip_escaped_quote_in_string() {
        // String: "hello\"world" contains hello"world
        assert_eq!(
            strip_comments_and_strings(r#"before "hello\"world" after"#),
            "before  after"
        );
    }

    #[test]
    fn test_strip_escaped_backslash_at_string_end() {
        // String: "test\\" -> content is test\ (escaped backslash)
        // After the string, "visible" should remain
        assert_eq!(
            strip_comments_and_strings(r#""test\\" visible"#),
            " visible"
        );
    }

    #[test]
    fn test_strip_escaped_backslash_then_comment() {
        // String "test\\" ends with escaped backslash, then (* comment *) follows
        assert_eq!(
            strip_comments_and_strings(r#""test\\" (* comment *) end"#),
            "  end"
        );
    }

    #[test]
    fn test_strip_string_inside_nested_comment() {
        // Deeply nested: (* a (* "b *)" *) c *)
        // The *) inside "b *)" should not close the inner comment
        assert_eq!(
            strip_comments_and_strings(r#"start (* a (* "b *)" *) c *) end"#),
            "start  end"
        );
    }

    #[test]
    fn test_strip_no_comments_or_strings() {
        assert_eq!(
            strip_comments_and_strings("let x = 1 + 2"),
            "let x = 1 + 2"
        );
    }

    #[test]
    fn test_strip_empty_input() {
        assert_eq!(strip_comments_and_strings(""), "");
    }

    #[test]
    fn test_strip_multiple_strings() {
        assert_eq!(
            strip_comments_and_strings(r#""a" middle "b""#),
            " middle "
        );
    }

    #[test]
    fn test_strip_adjacent_comment_and_string() {
        assert_eq!(
            strip_comments_and_strings(r#"(* c *)"s""#),
            ""
        );
    }

    #[test]
    fn test_strip_comment_with_escaped_backslash_string() {
        // Inside a comment: (* "ab\\" *) - the string is "ab\" (escaped backslash),
        // then *) closes the comment
        assert_eq!(
            strip_comments_and_strings(r#"a (* "ab\\" *) z"#),
            "a  z"
        );
    }

    // =========================================================================
    // Line comment (//) handling in strip_comments_and_strings
    // =========================================================================

    #[test]
    fn test_strip_line_comment() {
        // Basic // line comment should be stripped
        assert_eq!(
            strip_comments_and_strings("code // comment\nmore code"),
            "code \nmore code"
        );
    }

    #[test]
    fn test_strip_line_comment_with_block_markers() {
        // HACL* pattern: // with (* inside should NOT count as block comment
        // Real pattern from Hacl.Streaming.Functor.fsti:178
        assert_eq!(
            strip_comments_and_strings("// \"know\" that the value depends only on the state_s (*not* on a\nlet x = 1"),
            "\nlet x = 1"
        );
    }

    #[test]
    fn test_strip_line_comment_end_of_input() {
        // Line comment at end of input (no trailing newline)
        assert_eq!(
            strip_comments_and_strings("code // comment"),
            "code "
        );
    }

    #[test]
    fn test_strip_line_comment_inside_block_comment() {
        // // inside (* *) is just text, NOT a line comment
        assert_eq!(
            strip_comments_and_strings("(* // not a line comment *)code"),
            "code"
        );
    }

    #[test]
    fn test_strip_line_comment_inside_string() {
        // // inside a string is just string content
        assert_eq!(
            strip_comments_and_strings(r#""// not a comment" code"#),
            " code"
        );
    }

    #[test]
    fn test_strip_multiple_line_comments() {
        assert_eq!(
            strip_comments_and_strings("a // c1\nb // c2\nc"),
            "a \nb \nc"
        );
    }

    #[test]
    fn test_strip_mixed_line_and_block_comments() {
        assert_eq!(
            strip_comments_and_strings("a // line\nb (* block *) c"),
            "a \nb  c"
        );
    }

    // =========================================================================
    // Line comment (//) handling in count_comment_opens_closes
    // =========================================================================

    #[test]
    fn test_comment_count_line_comment_hides_block() {
        // (* after // should NOT be counted as block comment open
        assert_eq!(count_comment_opens_closes("code // (* not real *)"), (0, 0));
    }

    #[test]
    fn test_comment_count_line_comment_after_block() {
        // Block comment then line comment
        assert_eq!(count_comment_opens_closes("(* real *) // (* not real *)"), (1, 1));
    }

    #[test]
    fn test_comment_count_line_comment_in_string() {
        // // inside string should not start a line comment
        assert_eq!(
            count_comment_opens_closes(r#""// not comment" (* real *)"#),
            (1, 1)
        );
    }

    // =========================================================================
    // Module system constructs: friend, include, module abbreviation
    // =========================================================================

    #[test]
    fn test_friend_declaration_in_header() {
        // Friend declarations in the header area (before any let/val/type)
        let content = r#"module Hacl.Streaming.Poly1305_32

open FStar.HyperStack.ST

friend Hacl.Meta.Poly1305

val foo : int -> int
"#;
        let (header, blocks) = parse_fstar_file(content);
        // Friend should be in header
        let header_text: String = header.concat();
        assert!(
            header_text.contains("friend Hacl.Meta.Poly1305"),
            "Friend should be in header"
        );
        // Should have the val declaration
        assert!(blocks.iter().any(|b| b.block_type == BlockType::Val));
    }

    #[test]
    fn test_friend_declaration_mid_file() {
        // Friend declarations appearing after other declarations (real HACL* pattern)
        let content = r#"module Test

open FStar.All

val foo : int -> int
let foo x = x + 1

friend OtherModule

val bar : int -> int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let friend_block = blocks.iter().find(|b| b.block_type == BlockType::Friend);
        assert!(
            friend_block.is_some(),
            "Mid-file friend should be parsed as a Friend block"
        );
        assert_eq!(
            friend_block.unwrap().module_path.as_deref(),
            Some("OtherModule"),
            "Friend block should capture module path"
        );
    }

    #[test]
    fn test_include_declaration_in_header() {
        // Include in header (real EverParse/HACL* pattern)
        let content = r#"module Hacl.Hash.SHA1

include Hacl.Hash.Core.SHA1

val foo : int
"#;
        let (header, _blocks) = parse_fstar_file(content);
        let header_text: String = header.concat();
        assert!(
            header_text.contains("include Hacl.Hash.Core.SHA1"),
            "Include should be in header"
        );
    }

    #[test]
    fn test_include_declaration_mid_file() {
        // Include appearing after declarations
        let content = r#"module Test

val foo : int
let foo = 42

include Another.Module

val bar : int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let include_block = blocks.iter().find(|b| b.block_type == BlockType::Include);
        assert!(
            include_block.is_some(),
            "Mid-file include should be parsed as Include block"
        );
        assert_eq!(
            include_block.unwrap().names[0],
            "Another.Module",
            "Include name should be the qualified module path"
        );
        assert_eq!(
            include_block.unwrap().module_path.as_deref(),
            Some("Another.Module"),
        );
    }

    #[test]
    fn test_module_abbreviation_in_header() {
        // Module abbreviation in header (very common HACL*/EverParse pattern)
        let content = r#"module Hacl.Streaming.MD

open FStar.HyperStack.ST

module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32

val foo : int
"#;
        let (header, _blocks) = parse_fstar_file(content);
        let header_text: String = header.concat();
        assert!(
            header_text.contains("module G = FStar.Ghost"),
            "Module abbreviation should be in header"
        );
        assert!(
            header_text.contains("module U32 = FStar.UInt32"),
            "Multi-segment abbreviation should be in header"
        );
    }

    #[test]
    fn test_module_abbreviation_mid_file() {
        // Module abbreviation after declarations (real HACL* pattern from Hacl.Streaming.MD)
        let content = r#"module Test

open FStar.All

let uint8 = Lib.IntTypes.uint8

module D = Hacl.Hash.Definitions
module Agile = Spec.Agile.Hash

let alg = md_alg
"#;
        let (_, blocks) = parse_fstar_file(content);
        let abbrev_blocks: Vec<&DeclarationBlock> = blocks
            .iter()
            .filter(|b| b.block_type == BlockType::ModuleAbbrev)
            .collect();
        assert_eq!(
            abbrev_blocks.len(),
            2,
            "Should find two mid-file module abbreviations"
        );
        assert_eq!(abbrev_blocks[0].names[0], "D");
        assert_eq!(
            abbrev_blocks[0].module_path.as_deref(),
            Some("Hacl.Hash.Definitions")
        );
        assert_eq!(abbrev_blocks[1].names[0], "Agile");
        assert_eq!(
            abbrev_blocks[1].module_path.as_deref(),
            Some("Spec.Agile.Hash")
        );
    }

    #[test]
    fn test_module_abbreviation_deeply_qualified() {
        // Module abbreviation with 4+ segment qualified name
        let content = r#"module Test

module SF51 = Hacl.Spec.Curve25519.Field51.Definition

val foo : int
"#;
        let (header, _) = parse_fstar_file(content);
        let header_text: String = header.concat();
        assert!(
            header_text.contains("module SF51 = Hacl.Spec.Curve25519.Field51.Definition"),
            "Deeply qualified module abbreviation should be in header"
        );
    }

    #[test]
    fn test_open_mid_file() {
        // Opens appearing after declarations (common in HACL*)
        let content = r#"module Test

let uint8 = Lib.IntTypes.uint8

open Spec.Hash.Definitions

open Hacl.Streaming.Interface

let alg = md_alg
"#;
        let (_, blocks) = parse_fstar_file(content);
        let open_blocks: Vec<&DeclarationBlock> = blocks
            .iter()
            .filter(|b| b.block_type == BlockType::Open)
            .collect();
        assert_eq!(
            open_blocks.len(),
            2,
            "Should find two mid-file opens"
        );
        assert_eq!(
            open_blocks[0].module_path.as_deref(),
            Some("Spec.Hash.Definitions")
        );
        assert_eq!(
            open_blocks[1].module_path.as_deref(),
            Some("Hacl.Streaming.Interface")
        );
    }

    // =========================================================================
    // Private and abstract declarations
    // =========================================================================

    #[test]
    fn test_private_val_declaration() {
        let content = r#"module Test

private val helper : int -> int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let val_block = blocks.iter().find(|b| b.block_type == BlockType::Val);
        assert!(val_block.is_some());
        assert_eq!(val_block.unwrap().names[0], "helper");
        assert!(
            val_block.unwrap().is_private,
            "private val should be marked as private"
        );
    }

    #[test]
    fn test_private_let_declaration() {
        let content = r#"module Test

private let lemma_mul_nat (a:nat) (b:nat) = ()
"#;
        let (_, blocks) = parse_fstar_file(content);
        let let_block = blocks.iter().find(|b| b.block_type == BlockType::Let);
        assert!(let_block.is_some());
        assert!(
            let_block.unwrap().is_private,
            "private let should be marked as private"
        );
    }

    #[test]
    fn test_abstract_type_declaration() {
        let content = r#"module Test

abstract type mytype = int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type);
        assert!(type_block.is_some());
        assert_eq!(type_block.unwrap().names[0], "mytype");
        assert!(
            type_block.unwrap().is_abstract,
            "abstract type should be marked as abstract"
        );
    }

    // =========================================================================
    // Standalone modifier lines
    // =========================================================================

    #[test]
    fn test_standalone_modifier_inline_for_extraction() {
        assert!(is_standalone_modifier("inline_for_extraction noextract"));
        assert!(is_standalone_modifier("inline_for_extraction"));
        assert!(is_standalone_modifier("noextract"));
        assert!(is_standalone_modifier("private"));
        assert!(is_standalone_modifier("private unfold"));
        assert!(is_standalone_modifier("unfold"));
        assert!(is_standalone_modifier("irreducible"));
        assert!(is_standalone_modifier("opaque_to_smt"));
    }

    #[test]
    fn test_standalone_modifier_not_declaration() {
        // These should NOT be standalone modifiers
        assert!(!is_standalone_modifier("let x = 1"));
        assert!(!is_standalone_modifier("val foo : int"));
        assert!(!is_standalone_modifier("inline_for_extraction let x = 1"));
        assert!(!is_standalone_modifier("  private")); // Leading whitespace
    }

    #[test]
    fn test_modifier_on_separate_line() {
        // Real HACL* pattern: modifier on separate line from declaration
        let content = r#"module Test

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

noextract
val internal_fn : int -> int
"#;
        let (_, blocks) = parse_fstar_file(content);
        // The modifier lines should be attached to the subsequent declaration
        let let_block = blocks.iter().find(|b| b.names.contains(&"uint8".to_string()));
        assert!(let_block.is_some(), "Should find uint8 declaration");
        let let_text = let_block.unwrap().text();
        assert!(
            let_text.contains("inline_for_extraction noextract"),
            "Modifier should be attached to declaration block"
        );

        let val_block = blocks.iter().find(|b| b.names.contains(&"internal_fn".to_string()));
        assert!(val_block.is_some(), "Should find internal_fn declaration");
        let val_text = val_block.unwrap().text();
        assert!(
            val_text.contains("noextract"),
            "noextract modifier should be attached to val block"
        );
    }

    // =========================================================================
    // extract_module_construct_info tests
    // =========================================================================

    #[test]
    fn test_extract_module_construct_info_abbrev() {
        let result = extract_module_construct_info("module U32 = FStar.UInt32");
        assert!(result.is_some());
        let (bt, name, path) = result.unwrap();
        assert_eq!(bt, BlockType::ModuleAbbrev);
        assert_eq!(name, "U32");
        assert_eq!(path.as_deref(), Some("FStar.UInt32"));
    }

    #[test]
    fn test_extract_module_construct_info_module_decl() {
        let result = extract_module_construct_info("module Hacl.Streaming.MD");
        assert!(result.is_some());
        let (bt, name, path) = result.unwrap();
        assert_eq!(bt, BlockType::Module);
        assert_eq!(name, "Hacl.Streaming.MD");
        assert!(path.is_none());
    }

    #[test]
    fn test_extract_module_construct_info_open() {
        let result = extract_module_construct_info("open FStar.HyperStack.ST");
        assert!(result.is_some());
        let (bt, name, path) = result.unwrap();
        assert_eq!(bt, BlockType::Open);
        assert_eq!(name, "FStar.HyperStack.ST");
        assert_eq!(path.as_deref(), Some("FStar.HyperStack.ST"));
    }

    #[test]
    fn test_extract_module_construct_info_include() {
        let result = extract_module_construct_info("include Hacl.Hash.Core.SHA1");
        assert!(result.is_some());
        let (bt, name, path) = result.unwrap();
        assert_eq!(bt, BlockType::Include);
        assert_eq!(name, "Hacl.Hash.Core.SHA1");
        assert_eq!(path.as_deref(), Some("Hacl.Hash.Core.SHA1"));
    }

    #[test]
    fn test_extract_module_construct_info_friend() {
        let result = extract_module_construct_info("friend Hacl.Spec.Bignum.ModInvLimb");
        assert!(result.is_some());
        let (bt, name, path) = result.unwrap();
        assert_eq!(bt, BlockType::Friend);
        assert_eq!(name, "Hacl.Spec.Bignum.ModInvLimb");
        assert_eq!(path.as_deref(), Some("Hacl.Spec.Bignum.ModInvLimb"));
    }

    #[test]
    fn test_extract_module_construct_info_indented() {
        // Indented lines should NOT match
        assert!(extract_module_construct_info("  open FStar.All").is_none());
        assert!(extract_module_construct_info("\tmodule M = Foo").is_none());
    }

    #[test]
    fn test_extract_module_construct_info_not_module() {
        // Non-module-system lines should return None
        assert!(extract_module_construct_info("let x = 1").is_none());
        assert!(extract_module_construct_info("val foo : int").is_none());
        assert!(extract_module_construct_info("(* comment *)").is_none());
    }

    // =========================================================================
    // is_header_line with new constructs
    // =========================================================================

    #[test]
    fn test_is_header_line_include() {
        assert_eq!(
            is_header_line("include Hacl.Hash.Core.SHA1"),
            Some(BlockType::Include)
        );
    }

    #[test]
    fn test_is_header_line_module_abbrev() {
        assert_eq!(
            is_header_line("module U32 = FStar.UInt32"),
            Some(BlockType::ModuleAbbrev)
        );
    }

    #[test]
    fn test_is_header_line_module_decl() {
        assert_eq!(
            is_header_line("module Hacl.Streaming.MD"),
            Some(BlockType::Module)
        );
    }

    #[test]
    fn test_is_header_line_open() {
        assert_eq!(
            is_header_line("open FStar.All"),
            Some(BlockType::Open)
        );
    }

    #[test]
    fn test_is_header_line_friend() {
        assert_eq!(
            is_header_line("friend Other.Module"),
            Some(BlockType::Friend)
        );
    }

    // =========================================================================
    // detect_visibility_modifiers tests
    // =========================================================================

    #[test]
    fn test_detect_visibility_private() {
        let (priv_, abs_) = detect_visibility_modifiers("private val foo : int");
        assert!(priv_);
        assert!(!abs_);
    }

    #[test]
    fn test_detect_visibility_abstract() {
        let (priv_, abs_) = detect_visibility_modifiers("abstract type mytype = int");
        assert!(!priv_);
        assert!(abs_);
    }

    #[test]
    fn test_detect_visibility_neither() {
        let (priv_, abs_) = detect_visibility_modifiers("val foo : int -> int");
        assert!(!priv_);
        assert!(!abs_);
    }

    // =========================================================================
    // get_declaration_info with new constructs
    // =========================================================================

    #[test]
    fn test_get_declaration_info_include() {
        let result = get_declaration_info("include Hacl.Hash.Core.SHA1");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::Include);
        assert_eq!(name, "Hacl.Hash.Core.SHA1");
    }

    #[test]
    fn test_get_declaration_info_module_abbrev() {
        let result = get_declaration_info("module D = Hacl.Hash.Definitions");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::ModuleAbbrev);
        assert_eq!(name, "D");
    }

    #[test]
    fn test_get_declaration_info_unchanged_for_val() {
        let result = get_declaration_info("val foo : int -> int");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::Val);
        assert_eq!(name, "foo");
    }

    #[test]
    fn test_get_declaration_info_unchanged_for_let() {
        let result = get_declaration_info("let foo x = x + 1");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::Let);
        assert_eq!(name, "foo");
    }

    // =========================================================================
    // Full file parse: real-world HACL* pattern
    // =========================================================================

    #[test]
    fn test_parse_hacl_style_file() {
        // Simulates the structure of Hacl.Streaming.MD.fst
        let content = r#"module Hacl.Streaming.MD

open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32

open LowStar.BufferOps
open FStar.Mul

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

open Spec.Hash.Definitions

module D = Hacl.Hash.Definitions
module Agile = Spec.Agile.Hash

let alg = md_alg

val process : alg -> int -> int
"#;
        let (header, blocks) = parse_fstar_file(content);

        // Header should contain module, opens, options, module abbreviations
        let header_text: String = header.concat();
        assert!(header_text.contains("module Hacl.Streaming.MD"));
        assert!(header_text.contains("open FStar.HyperStack.ST"));
        assert!(header_text.contains("#set-options"));
        assert!(header_text.contains("module G = FStar.Ghost"));
        assert!(header_text.contains("module U32 = FStar.UInt32"));
        assert!(header_text.contains("open LowStar.BufferOps"));
        assert!(header_text.contains("open FStar.Mul"));

        // Mid-file constructs should be blocks
        let uint8_block = blocks.iter().find(|b| b.names.contains(&"uint8".to_string()));
        assert!(uint8_block.is_some(), "Should find uint8 let binding");

        // Mid-file open after declarations
        let open_blocks: Vec<&DeclarationBlock> = blocks
            .iter()
            .filter(|b| b.block_type == BlockType::Open)
            .collect();
        assert!(
            open_blocks.iter().any(|b| b.module_path.as_deref() == Some("Spec.Hash.Definitions")),
            "Should find mid-file open Spec.Hash.Definitions"
        );

        // Mid-file module abbreviations
        let abbrev_blocks: Vec<&DeclarationBlock> = blocks
            .iter()
            .filter(|b| b.block_type == BlockType::ModuleAbbrev)
            .collect();
        assert!(
            abbrev_blocks.iter().any(|b| b.names[0] == "D"),
            "Should find mid-file module D = Hacl.Hash.Definitions"
        );
        assert!(
            abbrev_blocks.iter().any(|b| b.names[0] == "Agile"),
            "Should find mid-file module Agile = Spec.Agile.Hash"
        );

        // Should still find regular declarations
        assert!(blocks.iter().any(|b| b.names.contains(&"alg".to_string())));
        assert!(blocks.iter().any(|b| b.names.contains(&"process".to_string())));
    }

    #[test]
    fn test_parse_everparse_style_file() {
        // Simulates EverParse pattern with multiple includes
        let content = r#"module LowParse.Low.List

include LowParse.Spec.List
include LowParse.Low.Base

module U32 = FStar.UInt32
module HS = FStar.HyperStack

val parse_list : int -> int
"#;
        let (header, blocks) = parse_fstar_file(content);

        let header_text: String = header.concat();
        assert!(header_text.contains("include LowParse.Spec.List"));
        assert!(header_text.contains("include LowParse.Low.Base"));
        assert!(header_text.contains("module U32 = FStar.UInt32"));
        assert!(header_text.contains("module HS = FStar.HyperStack"));

        assert!(blocks.iter().any(|b| b.names.contains(&"parse_list".to_string())));
    }

    #[test]
    fn test_parse_multiple_friends() {
        // Multiple friend declarations (real HACL* pattern)
        let content = r#"module Hacl.Streaming.HMAC.Definitions

open FStar.HyperStack.ST

friend Spec.Agile.HMAC
friend Spec.HMAC.Incremental
friend Hacl.HMAC

val foo : int
"#;
        let (header, _) = parse_fstar_file(content);
        let header_text: String = header.concat();
        assert!(header_text.contains("friend Spec.Agile.HMAC"));
        assert!(header_text.contains("friend Spec.HMAC.Incremental"));
        assert!(header_text.contains("friend Hacl.HMAC"));
    }

    #[test]
    fn test_parse_private_declarations_in_file() {
        // Real HACL* pattern from Hacl.Spec.BignumQ.Lemmas
        let content = r#"module Test

private let lemma_mul (a:nat) (b:nat) = ()

private val lemma_mod :
  a:nat -> b:pos -> int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let let_block = blocks.iter().find(|b| b.names.contains(&"lemma_mul".to_string()));
        assert!(let_block.is_some());
        assert!(let_block.unwrap().is_private);

        let val_block = blocks.iter().find(|b| b.names.contains(&"lemma_mod".to_string()));
        assert!(val_block.is_some());
        assert!(val_block.unwrap().is_private);
    }

    #[test]
    fn test_val_let_distinction() {
        // Interface checking: val vs let are distinct block types
        let content = r#"module Test

val foo : int -> int
let foo x = x + 1

val bar : int -> int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let val_blocks: Vec<&DeclarationBlock> = blocks
            .iter()
            .filter(|b| b.block_type == BlockType::Val)
            .collect();
        let let_blocks: Vec<&DeclarationBlock> = blocks
            .iter()
            .filter(|b| b.block_type == BlockType::Let)
            .collect();
        assert_eq!(val_blocks.len(), 2, "Should have two val declarations");
        assert_eq!(let_blocks.len(), 1, "Should have one let declaration");
    }

    #[test]
    fn test_qualified_name_five_segments() {
        // Five-segment qualified module path
        let result = extract_module_construct_info(
            "module SF51 = Hacl.Spec.Curve25519.Field51.Definition"
        );
        assert!(result.is_some());
        let (_, name, path) = result.unwrap();
        assert_eq!(name, "SF51");
        assert_eq!(path.as_deref(), Some("Hacl.Spec.Curve25519.Field51.Definition"));
    }

    #[test]
    fn test_include_get_declaration_info_qualified() {
        // Include with deeply qualified name
        let result = get_declaration_info("include Hacl.Spec.K256.Field52.Definitions");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::Include);
        assert_eq!(name, "Hacl.Spec.K256.Field52.Definitions");
    }

    // =========================================================================
    // Effect declaration parsing tests
    // =========================================================================

    #[test]
    fn test_effect_abbrev_parsing() {
        let content = "module Test\n\neffect Stack (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =\n       STATE a\n             (fun (p:st_post a) (h:mem) -> pre h)\n";
        let (_, blocks) = parse_fstar_file(content);
        let effect_block = blocks.iter().find(|b| b.block_type == BlockType::EffectAbbrev);
        assert!(effect_block.is_some(), "Should parse effect abbreviation");
        assert!(
            effect_block.unwrap().names.contains(&"Stack".to_string()),
            "Effect abbreviation name should be 'Stack'"
        );
    }

    #[test]
    fn test_effect_abbrev_simple() {
        let content = "module Test\n\neffect Dv (a: Type) = DIV a (pure_null_wp a)\n";
        let (_, blocks) = parse_fstar_file(content);
        let effect_block = blocks.iter().find(|b| b.block_type == BlockType::EffectAbbrev);
        assert!(effect_block.is_some(), "Should parse simple effect abbreviation");
        assert!(effect_block.unwrap().names.contains(&"Dv".to_string()));
    }

    #[test]
    fn test_effect_abbrev_lemma() {
        let content = "module Test\n\neffect Lemma (a: eqtype_u) (pre: Type) (post: (squash pre -> Type)) (pats: list pattern) =\n  Pure unit pre (fun _ -> post ())\n";
        let (_, blocks) = parse_fstar_file(content);
        let effect_block = blocks.iter().find(|b| b.block_type == BlockType::EffectAbbrev);
        assert!(effect_block.is_some(), "Should parse Lemma effect abbreviation");
        assert!(effect_block.unwrap().names.contains(&"Lemma".to_string()));
    }

    #[test]
    fn test_effect_abbrev_multiple() {
        let content = "module Test\n\neffect ST (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =\n       STATE a (fun (p:st_post a) (h:mem) -> pre h)\n\neffect St (a:Type) = ST a (fun _ -> True) (fun _ _ _ -> True)\n";
        let (_, blocks) = parse_fstar_file(content);
        let effect_blocks: Vec<_> = blocks.iter()
            .filter(|b| b.block_type == BlockType::EffectAbbrev)
            .collect();
        assert!(
            effect_blocks.len() >= 2,
            "Should parse both ST and St abbreviations, got {}",
            effect_blocks.len()
        );
    }

    #[test]
    fn test_new_effect_parsing() {
        // new_effect with name on the same line as `new_effect {`
        let content = "module Test\n\nnew_effect { STATE : result:Type -> wp:st_wp result -> Effect\n  with return_wp = fun (a:Type) (x:a) -> x\n     ; bind_wp   = fun (a:Type) (b:Type) (wp1:st_wp a) -> wp1\n}\n";
        let (_, blocks) = parse_fstar_file(content);
        let ne_block = blocks.iter().find(|b| b.block_type == BlockType::NewEffect);
        assert!(ne_block.is_some(), "Should parse new_effect declaration");
        assert!(ne_block.unwrap().names.contains(&"STATE".to_string()));
    }

    #[test]
    fn test_new_effect_multiline() {
        // new_effect with braces on next line (name extraction from block text)
        let content = "module Test\n\nnew_effect {\n  STATE : result:Type -> wp:st_wp result -> Effect\n  with return_wp = fun (a:Type) (x:a) -> x\n}\n";
        let (_, blocks) = parse_fstar_file(content);
        // The first line `new_effect {` won't match NEW_EFFECT_PATTERN since
        // the name is on the next line. It should still be detected as a new_effect block.
        let ne_block = blocks.iter().find(|b| {
            b.block_type == BlockType::NewEffect || (
                b.block_type == BlockType::Unknown && b.text().contains("new_effect")
            )
        });
        assert!(ne_block.is_some(), "Should detect new_effect even with name on next line");
    }

    #[test]
    fn test_sub_effect_parsing() {
        // sub_effect with ~> on the same line
        let content = "module Test\n\nsub_effect DIV ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:mem) -> wp (fun a -> p a h)\n";
        let (_, blocks) = parse_fstar_file(content);
        let se_block = blocks.iter().find(|b| b.block_type == BlockType::SubEffect);
        assert!(se_block.is_some(), "Should parse sub_effect declaration");
        assert!(
            se_block.unwrap().names.iter().any(|n| n.contains("DIV") && n.contains("STATE")),
            "sub_effect should capture source~>dest names"
        );
    }

    #[test]
    fn test_sub_effect_multiline() {
        // sub_effect with ~> on the next (continuation) line
        let content = "module Test\n\nsub_effect\n  DIV   ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:mem) -> wp (fun a -> p a h)\n";
        let (_, blocks) = parse_fstar_file(content);
        let se_block = blocks.iter().find(|b| b.block_type == BlockType::SubEffect);
        assert!(se_block.is_some(), "Should parse sub_effect on its own line");
        // Name may be just "sub_effect" since detail is on next line
        assert!(
            se_block.unwrap().names.iter().any(|n| n.contains("sub_effect") || n.contains("DIV")),
            "sub_effect should be detected"
        );
    }

    #[test]
    fn test_sub_effect_inline() {
        let content = "module Test\n\nsub_effect PURE ~> MyEffect = lift_pure_my\n";
        let (_, blocks) = parse_fstar_file(content);
        let se_block = blocks.iter().find(|b| b.block_type == BlockType::SubEffect);
        assert!(se_block.is_some(), "Should parse inline sub_effect");
        assert!(
            se_block.unwrap().names.iter().any(|n| n.contains("PURE") && n.contains("MyEffect")),
            "Should capture PURE~>MyEffect"
        );
    }

    #[test]
    fn test_layered_effect_parsing() {
        // layered_effect with name on the same line as the opening brace
        let content = "module Test\n\nlayered_effect { TAC : a:Type -> tac_wp a -> Effect\n  with repr = __tac\n     ; return = fun a x -> fun ps -> Success x ps\n     ; bind = fun a b m f -> fun ps -> match m ps with x -> x\n}\n";
        let (_, blocks) = parse_fstar_file(content);
        let le_block = blocks.iter().find(|b| b.block_type == BlockType::Effect);
        assert!(le_block.is_some(), "Should parse layered_effect declaration");
        assert!(le_block.unwrap().names.contains(&"TAC".to_string()));
    }

    #[test]
    fn test_reflectable_standalone_modifier() {
        assert!(is_standalone_modifier("reflectable"));
        assert!(is_standalone_modifier("reifiable"));
        assert!(!is_standalone_modifier("  reflectable"));
    }

    #[test]
    fn test_effect_stl_alias() {
        let content = "module Test\n\neffect STL (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) = Stack a pre post\n";
        let (_, blocks) = parse_fstar_file(content);
        let effect_block = blocks.iter().find(|b| b.block_type == BlockType::EffectAbbrev);
        assert!(effect_block.is_some(), "Should parse STL effect alias");
        assert!(effect_block.unwrap().names.contains(&"STL".to_string()));
    }

    #[test]
    fn test_get_declaration_info_effect_abbrev() {
        let result = get_declaration_info("effect Stack (a:Type) (pre:st_pre) = STATE a");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::EffectAbbrev);
        assert_eq!(name, "Stack");
    }

    #[test]
    fn test_get_declaration_info_new_effect() {
        let result = get_declaration_info("new_effect { STATE : result:Type -> Effect");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::NewEffect);
        assert_eq!(name, "STATE");
    }

    #[test]
    fn test_get_declaration_info_sub_effect() {
        let result = get_declaration_info("sub_effect PURE ~> MyEffect = lift_pure");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::SubEffect);
        assert!(name.contains("PURE") && name.contains("MyEffect"),
            "Should capture source~>dest, got: {}", name);
    }

    #[test]
    fn test_get_declaration_info_layered_effect() {
        let result = get_declaration_info("layered_effect { TAC : a:Type -> tac_wp a -> Effect");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::Effect);
        assert_eq!(name, "TAC");
    }

    #[test]
    fn test_get_declaration_info_effect_div() {
        let result = get_declaration_info("effect Div (a: Type) (pre: pure_pre) = DIV a");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(name, "Div");
        assert!(bt == BlockType::EffectAbbrev || bt == BlockType::Effect,
            "Should be EffectAbbrev or Effect, got: {:?}", bt);
    }

    #[test]
    fn test_get_declaration_info_total_effect() {
        let result = get_declaration_info("total_effect { PURE : a:Type -> pure_wp a -> Effect");
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::NewEffect);
        assert_eq!(name, "PURE");
    }

    #[test]
    fn test_effect_with_requires_ensures_stack() {
        let content = "module Test\n\nval bn_sub:\n    #t:limb_t\n  -> aLen:size_t\n  -> a:lbignum t aLen\n  -> res:lbignum t aLen ->\n  Stack (carry t)\n  (requires fun h -> live h a /\\ live h res)\n  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1)\n";
        let (_, blocks) = parse_fstar_file(content);
        let val_blocks: Vec<_> = blocks.iter()
            .filter(|b| b.block_type == BlockType::Val)
            .collect();
        assert!(val_blocks.len() >= 1, "Should parse val with Stack effect");
        let text = val_blocks[0].text();
        assert!(text.contains("Stack"), "Val text should contain 'Stack': {}", text);
    }

    #[test]
    fn test_multiple_effect_types_in_file() {
        // File with effect abbreviations, sub_effect (inline), and a val with Stack
        let content = "module Test\n\neffect Unsafe (a:Type) (pre:st_pre) (post:Type) =\n       STATE a (fun p h -> pre h)\n\neffect Stack (a:Type) (pre:st_pre) (post:Type) =\n       STATE a (fun p h -> pre h)\n\nsub_effect DIV ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:mem) -> wp (fun a -> p a h)\n\nval push_frame (_:unit) : Stack unit\n  (requires (fun m -> True))\n  (ensures (fun m0 _ m1 -> fresh_frame m0 m1))\n";
        let (_, blocks) = parse_fstar_file(content);

        let abbrev_count = blocks.iter()
            .filter(|b| b.block_type == BlockType::EffectAbbrev)
            .count();
        assert!(abbrev_count >= 2, "Should find at least 2 effect abbreviations, got {}", abbrev_count);

        let sub_count = blocks.iter()
            .filter(|b| b.block_type == BlockType::SubEffect)
            .count();
        assert!(sub_count >= 1, "Should find at least 1 sub_effect, got {}", sub_count);

        let val_count = blocks.iter()
            .filter(|b| b.block_type == BlockType::Val)
            .count();
        assert!(val_count >= 1, "Should find at least 1 val, got {}", val_count);
    }

    // =========================================================================
    // Tactic and metaprogramming construct tests
    // =========================================================================

    #[test]
    fn test_tactic_by_syntax_not_new_declaration() {
        // `_ by (tactic)` inside a let body should not create a new block
        let content = r#"module Test

let proof x =
  assert (P x) by (trefl ());
  ()
"#;
        let (_, blocks) = parse_fstar_file(content);
        // Should only have one declaration: 'proof'
        let decl_names: Vec<&str> = blocks
            .iter()
            .filter(|b| !matches!(b.block_type, BlockType::Comment))
            .flat_map(|b| b.names.iter().map(|s| s.as_str()))
            .collect();
        assert!(decl_names.contains(&"proof"), "Should find proof declaration");
        // The tactic body should be part of the proof declaration
        let proof_block = blocks.iter().find(|b| b.names.contains(&"proof".to_string()));
        assert!(proof_block.is_some());
        let text = proof_block.unwrap().text();
        assert!(text.contains("by (trefl"), "Tactic body should be in declaration text");
    }

    #[test]
    fn test_assert_by_tactic_inline() {
        // assert ... by (...) inside function body
        let content = r#"module Test

let lemma_helper (a b : int) =
  assert (a + b == b + a) by (FStar.Tactics.Canon.canon ());
  ()
"#;
        let (_, blocks) = parse_fstar_file(content);
        let helper = blocks.iter().find(|b| b.names.contains(&"lemma_helper".to_string()));
        assert!(helper.is_some(), "Should find lemma_helper");
        let text = helper.unwrap().text();
        assert!(text.contains("by (FStar.Tactics.Canon.canon"), "assert by should be in body");
    }

    #[test]
    fn test_synth_by_tactic() {
        // synth_by_tactic usage
        let content = r#"module Test

let witness : int = synth_by_tactic (fun () -> exact (`42))
"#;
        let (_, blocks) = parse_fstar_file(content);
        let witness = blocks.iter().find(|b| b.names.contains(&"witness".to_string()));
        assert!(witness.is_some(), "Should find witness declaration");
        let text = witness.unwrap().text();
        assert!(text.contains("synth_by_tactic"), "synth_by_tactic should be in body");
    }

    #[test]
    fn test_tactic_keywords_not_false_dependencies() {
        // Tactic combinator names should not appear as references
        let text = "let proof x = assert (P x) by (trefl (); smt (); trivial ())";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        // Tactic combinators should be filtered by keywords
        assert!(!refs.contains("trefl"), "trefl should be keyword, not reference");
        assert!(!refs.contains("smt"), "smt should be keyword, not reference");
        assert!(!refs.contains("trivial"), "trivial should be keyword, not reference");
        assert!(!refs.contains("by"), "by should be keyword, not reference");

        // Real references should still be extracted
        assert!(refs.contains("proof"), "proof should be extracted");
        assert!(refs.contains("P"), "P should be extracted as reference");
        assert!(refs.contains("x"), "x should be extracted as reference");
    }

    #[test]
    fn test_norm_steps_not_false_dependencies() {
        // Normalization step names should not be false dependencies
        let text = "by (norm [delta_only [`%foo]; primops; iota; zeta])";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(!refs.contains("delta_only"), "delta_only is a keyword");
        assert!(!refs.contains("primops"), "primops is a keyword");
        assert!(!refs.contains("iota"), "iota is a keyword");
        assert!(!refs.contains("zeta"), "zeta is a keyword");
        assert!(!refs.contains("norm"), "norm is a keyword");
        assert!(!refs.contains("by"), "by is a keyword");
        assert!(refs.contains("foo"), "foo is a real reference");
    }

    #[test]
    fn test_smt_pat_keyword() {
        // SMTPat and SMTPatOr should be keywords
        let text = "val lemma : x:nat -> Lemma (P x) [SMTPat (f x)]";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(!refs.contains("SMTPat"), "SMTPat should be keyword");
        assert!(refs.contains("P"), "P should be reference");
        assert!(refs.contains("f"), "f should be reference");
    }

    #[test]
    fn test_smt_pat_or_keyword() {
        let text = "[SMTPatOr [[SMTPat (f x)]; [SMTPat (g x)]]]";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(!refs.contains("SMTPatOr"), "SMTPatOr should be keyword");
        assert!(!refs.contains("SMTPat"), "SMTPat should be keyword");
        assert!(refs.contains("f"), "f should be reference");
        assert!(refs.contains("g"), "g should be reference");
    }

    #[test]
    fn test_backtick_quotation_extracts_name() {
        // Backtick quotation: `term references a real definition
        let text = "by (apply_lemma (`other_lemma); trefl ())";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        // The identifier after backtick should still be extracted
        assert!(refs.contains("other_lemma"), "quoted name should be extracted");
        // Tactic combinators should be filtered
        assert!(!refs.contains("apply_lemma"), "apply_lemma is a keyword");
        assert!(!refs.contains("trefl"), "trefl is a keyword");
    }

    #[test]
    fn test_backtick_percent_quotation() {
        // `%foo quotes the name of top-level definition foo
        let text = "norm [delta_only [`%my_function]; primops]";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(refs.contains("my_function"), "backtick-percent quoted name should be extracted");
        assert!(!refs.contains("delta_only"), "delta_only is a keyword");
    }

    #[test]
    fn test_backtick_hash_quotation() {
        // `#term is an antiquotation
        let text = "`(_ by (prove_left_right (`#(quote_at cfg.at))))";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        // quote_at and cfg are identifiers that should be extracted
        assert!(refs.contains("prove_left_right"), "prove_left_right should be ref");
        assert!(refs.contains("cfg"), "cfg should be extracted");
    }

    #[test]
    fn test_decreases_percent_bracket() {
        // %[...] syntax in decreases clauses
        let content = r#"module Test

let rec eval_code (c:code) (fuel:nat) (s:state)
  : Tot (option state) (decreases %[fuel; c]) =
  match c with
  | Skip -> Some s
"#;
        let (_, blocks) = parse_fstar_file(content);
        let eval = blocks.iter().find(|b| b.names.contains(&"eval_code".to_string()));
        assert!(eval.is_some(), "Should find eval_code declaration");
        let text = eval.unwrap().text();
        assert!(text.contains("decreases %[fuel; c]"), "decreases clause should be preserved");
    }

    // =========================================================================
    // Pragma and debug command tests
    // =========================================================================

    #[test]
    fn test_check_command_recognized() {
        assert!(is_standalone_options("#check (some_term)"));
        assert!(is_standalone_options("#check some_term"));
    }

    #[test]
    fn test_normalize_command_recognized() {
        assert!(is_standalone_options("#normalize (some_term) [delta; zeta; iota]"));
        assert!(is_standalone_options("#normalize some_term"));
    }

    #[test]
    fn test_check_command_in_file() {
        let content = r#"module Test

val foo : int -> int

#check (foo 42)

let bar = 1
"#;
        let (_, blocks) = parse_fstar_file(content);
        // #check should not become a declaration
        let names: Vec<&str> = blocks
            .iter()
            .flat_map(|b| b.names.iter().map(|s| s.as_str()))
            .collect();
        assert!(names.contains(&"foo"), "Should find foo");
        assert!(names.contains(&"bar"), "Should find bar");
        // #check should not create a named block
        assert!(!names.iter().any(|n| n.contains("check")),
            "#check should not be a named declaration");
    }

    #[test]
    fn test_normalize_command_in_file() {
        let content = r#"module Test

val foo : int -> int

#normalize (foo 42) [delta; zeta]

let bar = 1
"#;
        let (_, blocks) = parse_fstar_file(content);
        let names: Vec<&str> = blocks
            .iter()
            .flat_map(|b| b.names.iter().map(|s| s.as_str()))
            .collect();
        assert!(names.contains(&"foo"), "Should find foo");
        assert!(names.contains(&"bar"), "Should find bar");
    }

    #[test]
    fn test_existing_pragmas_still_work() {
        // Ensure existing pragma handling is not broken
        assert!(is_standalone_options("#set-options \"--fuel 0\""));
        assert!(is_standalone_options("#reset-options"));
        assert!(is_standalone_options("#restart-solver"));
        assert!(is_push_options("#push-options \"--z3rlimit 100\""));
        assert!(is_pop_options("#pop-options"));
    }

    // =========================================================================
    // Attribute syntax tests
    // =========================================================================

    #[test]
    fn test_standalone_attribute_double_at() {
        // [@@...] on its own line
        assert!(is_standalone_attribute("[@@\"opaque_to_smt\"]"));
        assert!(is_standalone_attribute("[@@ __reduce__]"));
        assert!(is_standalone_attribute("[@@do_not_unrefine]"));
        assert!(is_standalone_attribute("[@@admitted]"));
    }

    #[test]
    fn test_standalone_attribute_single_at() {
        // [@ ...] old-style attribute
        assert!(is_standalone_attribute("[@ CNoInline ]"));
        assert!(is_standalone_attribute("[@CInline]"));
    }

    #[test]
    fn test_standalone_attribute_triple_at() {
        // [@@@...] binder attribute (rare at top level, but valid)
        assert!(is_standalone_attribute("[@@@strictly_positive]"));
    }

    #[test]
    fn test_standalone_attribute_multiple() {
        // Multiple attributes separated by semicolons
        assert!(is_standalone_attribute("[@@resolve_implicits; abc]"));
    }

    #[test]
    fn test_standalone_attribute_with_args() {
        // Attribute with arguments
        assert!(is_standalone_attribute("[@@(strict_on_arguments [1;2])]"));
    }

    #[test]
    fn test_standalone_attribute_not_smt_pat() {
        // [SMTPat ...] should NOT be a standalone attribute (no @ after [)
        assert!(!is_standalone_attribute("[SMTPat (f x)]"));
        assert!(!is_standalone_attribute("[SMTPatOr [[SMTPat (f x)]]]"));
    }

    #[test]
    fn test_standalone_attribute_not_indented() {
        // Indented attributes should not be standalone
        assert!(!is_standalone_attribute("  [@@foo]"));
        assert!(!is_standalone_attribute("\t[@bar]"));
    }

    #[test]
    fn test_standalone_modifier_includes_attributes() {
        // is_standalone_modifier should now also match attributes
        assert!(is_standalone_modifier("[@@\"opaque_to_smt\"]"));
        assert!(is_standalone_modifier("[@ CNoInline ]"));
        assert!(is_standalone_modifier("[@@ __reduce__]"));
    }

    #[test]
    fn test_attribute_before_declaration() {
        // Attribute line should be attached to subsequent declaration
        let content = r#"module Test

[@@"opaque_to_smt"]
val foo : int -> int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let foo_block = blocks.iter().find(|b| b.names.contains(&"foo".to_string()));
        assert!(foo_block.is_some(), "Should find foo declaration");
        let text = foo_block.unwrap().text();
        assert!(
            text.contains("[@@\"opaque_to_smt\"]"),
            "Attribute should be attached to foo declaration. Got: {}",
            text
        );
    }

    #[test]
    fn test_multiple_attributes_before_declaration() {
        // Multiple attribute lines before a declaration
        let content = r#"module Test

[@@ __reduce__]
[@@"opaque_to_smt"]
val helper : int -> int -> int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let helper = blocks.iter().find(|b| b.names.contains(&"helper".to_string()));
        assert!(helper.is_some(), "Should find helper declaration");
        let text = helper.unwrap().text();
        assert!(text.contains("__reduce__"), "First attribute should be attached");
        assert!(text.contains("opaque_to_smt"), "Second attribute should be attached");
    }

    #[test]
    fn test_inline_attribute_with_let() {
        // Attribute on same line as let (already supported by regex)
        let result = get_declaration_info("[@@CInline] let fast_helper x = x + 1");
        // Note: the current regex matches [@ not [@@, but [@@...] also matches
        // because the regex is \[@[^\]]*\] which accepts any chars after [@
        assert!(result.is_some());
        let (name, bt) = result.unwrap();
        assert_eq!(bt, BlockType::Let);
        assert_eq!(name, "fast_helper");
    }

    #[test]
    fn test_attribute_cno_inline() {
        let content = r#"module Test

[@ CNoInline ]
val expensive_fn : int -> int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let block = blocks.iter().find(|b| b.names.contains(&"expensive_fn".to_string()));
        assert!(block.is_some());
        let text = block.unwrap().text();
        assert!(text.contains("CNoInline"), "CNoInline attribute should be attached");
    }

    // =========================================================================
    // SMT pattern tests (in val signatures)
    // =========================================================================

    #[test]
    fn test_smt_pat_in_val_signature() {
        let content = r#"module Test

val lemma_hide_reveal : x:erased int -> Lemma
  (ensures (hide (reveal x) == x))
  [SMTPat (reveal x)]
"#;
        let (_, blocks) = parse_fstar_file(content);
        let lemma = blocks.iter().find(|b| b.names.contains(&"lemma_hide_reveal".to_string()));
        assert!(lemma.is_some(), "Should find lemma_hide_reveal");
        let text = lemma.unwrap().text();
        assert!(text.contains("[SMTPat"), "SMT pattern should be in declaration body");
    }

    #[test]
    fn test_smt_pat_or_in_val_signature() {
        let content = r#"module Test

val length_reveal : x:bytes -> Lemma
  (ensures (S.length (reveal x) = len x))
  [SMTPatOr [[SMTPat (S.length (reveal x))];
             [SMTPat (len x)]]]
"#;
        let (_, blocks) = parse_fstar_file(content);
        let lemma = blocks.iter().find(|b| b.names.contains(&"length_reveal".to_string()));
        assert!(lemma.is_some(), "Should find length_reveal");
        let text = lemma.unwrap().text();
        assert!(text.contains("[SMTPatOr"), "SMTPatOr should be in body");
    }

    // =========================================================================
    // Calc block with tactic justification tests
    // =========================================================================

    #[test]
    fn test_calc_block_with_tactic() {
        let content = r#"module Test

let calc_proof (a b : int) =
  calc (==) {
    a * b;
    == { _ by (FStar.Tactics.CanonCommSemiring.int_semiring ()) }
    b * a;
  }
"#;
        let (_, blocks) = parse_fstar_file(content);
        let proof = blocks.iter().find(|b| b.names.contains(&"calc_proof".to_string()));
        assert!(proof.is_some(), "Should find calc_proof");
        let text = proof.unwrap().text();
        assert!(text.contains("_ by ("), "calc justification with tactic should be in body");
    }

    // =========================================================================
    // Complex real-world tactic patterns from HACL*
    // =========================================================================

    #[test]
    fn test_hacl_tactic_pattern() {
        // Real HACL* pattern from Hacl.Spec.BignumQ.Lemmas
        let content = r#"module Test

let lemma_abc (a b c : int) =
  assert (a * (b * (c * 1)) == c * (a * (b * 1)))
    by (FStar.Tactics.CanonCommSemiring.int_semiring ())
"#;
        let (_, blocks) = parse_fstar_file(content);
        let lemma = blocks.iter().find(|b| b.names.contains(&"lemma_abc".to_string()));
        assert!(lemma.is_some());
        let text = lemma.unwrap().text();
        assert!(text.contains("by (FStar.Tactics.CanonCommSemiring"));
    }

    #[test]
    fn test_loop_combinator_tactic_pattern() {
        // Real HACL* pattern from Lib.LoopCombinators
        let content = r#"module Test

let unfold_repeati n f acc0 =
  assert (repeati n f acc0 == repeat_gen n (fixed_a n) f acc0)
    by (norm [delta_only [`%repeati]; iota]; trefl ())
"#;
        let (_, blocks) = parse_fstar_file(content);
        let block = blocks.iter().find(|b| b.names.contains(&"unfold_repeati".to_string()));
        assert!(block.is_some());
        let text = block.unwrap().text();
        assert!(text.contains("delta_only"), "norm step should be in body");
    }

    // =========================================================================
    // Attribute keywords not false dependencies
    // =========================================================================

    #[test]
    fn test_attribute_names_not_false_dependencies() {
        let text = "[@@CInline] let f x = x + 1";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(!refs.contains("CInline"), "CInline should be keyword, not reference");
        assert!(refs.contains("f"), "f should be extracted");
        assert!(refs.contains("x"), "x should be extracted");
    }

    #[test]
    fn test_deprecated_attribute_not_false_dep() {
        let text = "[@@ (deprecated \"Use arrow instead\")] val old_fn : int -> int";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(!refs.contains("deprecated"), "deprecated is a keyword");
        assert!(refs.contains("old_fn"), "old_fn should be extracted");
    }

    // =========================================================================
    // Full file with tactics, attributes, and pragmas
    // =========================================================================

    #[test]
    fn test_full_file_with_tactics_and_attributes() {
        let content = r#"module Test

open FStar.Tactics.V2

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

[@@"opaque_to_smt"]
val secret_fn : int -> int

let secret_fn x = x + 1

#push-options "--fuel 1"

val lemma_add_comm : a:int -> b:int -> Lemma
  (ensures (a + b == b + a))
  [SMTPat (a + b)]

let lemma_add_comm a b = ()

#pop-options

#restart-solver

[@@ __reduce__]
let helper x y = x + y

let tactic_proof (a b c : int) =
  assert (a * b * c == c * b * a)
    by (FStar.Tactics.CanonCommSemiring.int_semiring ())

#check (helper 1 2)

val synth_example : int
let synth_example = synth_by_tactic (fun () -> exact (`42))
"#;
        let (header, blocks) = parse_fstar_file(content);

        // Header should contain module, open, options
        let header_text: String = header.concat();
        assert!(header_text.contains("module Test"));
        assert!(header_text.contains("open FStar.Tactics.V2"));
        assert!(header_text.contains("#set-options"));

        // Check that declarations are found
        let names: Vec<&str> = blocks
            .iter()
            .flat_map(|b| b.names.iter().map(|s| s.as_str()))
            .collect();
        assert!(names.contains(&"secret_fn"), "Should find secret_fn");
        assert!(names.contains(&"lemma_add_comm"), "Should find lemma_add_comm");
        assert!(names.contains(&"helper"), "Should find helper");
        assert!(names.contains(&"tactic_proof"), "Should find tactic_proof");
        assert!(names.contains(&"synth_example"), "Should find synth_example");

        // Check attribute attachment
        let secret_block = blocks.iter().find(|b| {
            b.names.contains(&"secret_fn".to_string()) && b.block_type == BlockType::Val
        });
        assert!(secret_block.is_some());
        let text = secret_block.unwrap().text();
        assert!(text.contains("opaque_to_smt"), "Attribute should be attached to val");

        // Check helper has __reduce__ attribute
        let helper_block = blocks.iter().find(|b| b.names.contains(&"helper".to_string()));
        assert!(helper_block.is_some());
        let text = helper_block.unwrap().text();
        assert!(text.contains("__reduce__"), "__reduce__ attribute should be attached");

        // Check tactic_proof body contains tactic
        let tactic_block = blocks.iter().find(|b| b.names.contains(&"tactic_proof".to_string()));
        assert!(tactic_block.is_some());
        let text = tactic_block.unwrap().text();
        assert!(text.contains("int_semiring"), "Tactic body should be in declaration");
    }

    // =========================================================================
    // Edge cases
    // =========================================================================

    #[test]
    fn test_by_not_parsed_as_declaration() {
        // "by" at column 0 is not a declaration keyword
        assert!(get_declaration_info("by (trefl ())").is_none());
    }

    #[test]
    fn test_smt_pat_bracket_not_attribute() {
        // [SMTPat ...] should not be confused with [@ ...] attribute
        assert!(!is_standalone_attribute("[SMTPat (f x)]"));
        assert!(!is_standalone_modifier("[SMTPat (f x)]"));
    }

    #[test]
    fn test_empty_attribute() {
        // Degenerate case: empty attribute brackets
        assert!(is_standalone_attribute("[@@]"));
        assert!(is_standalone_attribute("[@]"));
    }

    #[test]
    fn test_attribute_with_noextract_to() {
        let content = r#"module Test

[@@ noextract_to "krml"]
val endianness_fn : int -> int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let block = blocks.iter().find(|b| b.names.contains(&"endianness_fn".to_string()));
        assert!(block.is_some());
        let text = block.unwrap().text();
        assert!(text.contains("noextract_to"), "noextract_to attribute should be attached");
    }

    #[test]
    fn test_binder_attribute_in_val() {
        // [@@@strictly_positive] is a binder attribute on parameters
        let text = "val on_domain (a: Type) (#b: (a -> Type)) ([@@@strictly_positive] f: arrow a b) : Tot (arrow a b)";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(!refs.contains("strictly_positive"), "strictly_positive is a keyword");
        assert!(refs.contains("on_domain"), "on_domain should be extracted");
        assert!(refs.contains("arrow"), "arrow should be extracted");
    }

    #[test]
    fn test_multiple_tactic_combinators() {
        // Multiple tactic calls in sequence
        let text = "by (intro (); apply (`foo); split (); assumption (); smt ())";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(!refs.contains("intro"), "intro is a keyword");
        assert!(!refs.contains("apply"), "apply is a keyword");
        assert!(!refs.contains("split"), "split is a keyword");
        assert!(!refs.contains("assumption"), "assumption is a keyword");
        assert!(!refs.contains("smt"), "smt is a keyword");
        assert!(!refs.contains("by"), "by is a keyword");
        assert!(refs.contains("foo"), "foo is a real reference");
    }

    #[test]
    fn test_check_command_not_declaration() {
        // #check should not be parsed as a declaration
        assert!(get_declaration_info("#check (some_term)").is_none());
        assert!(get_declaration_info("#normalize (some_term)").is_none());
    }

    #[test]
    fn test_synth_by_tactic_keyword() {
        let text = "let x : t = synth_by_tactic (fun () -> exact (`value))";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        assert!(!refs.contains("synth_by_tactic"), "synth_by_tactic is a keyword");
        assert!(!refs.contains("exact"), "exact is a keyword");
        assert!(refs.contains("value"), "value should be extracted");
    }

    #[test]
    fn test_decreases_percent_bracket_refs() {
        // %[...] in decreases clause - identifiers inside are real references
        let text = "Tot (option state) (decreases %[fuel; c])";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);

        // state would be filtered as keyword
        assert!(refs.contains("fuel"), "fuel should be extracted");
        assert!(refs.contains("c"), "c should be extracted");
    }

    // =========================================================================
    // Standalone modifier: noeq on its own line
    // =========================================================================

    #[test]
    fn test_noeq_standalone_modifier() {
        // noeq on its own line before a type declaration (real HACL* pattern)
        assert!(is_standalone_modifier("noeq"), "noeq should be a standalone modifier");
        assert!(!is_standalone_modifier("  noeq"), "indented noeq is not standalone");
    }

    #[test]
    fn test_noeq_before_type_declaration() {
        // Real HACL* pattern: noeq on its own line, then type on next line
        let content = r#"module Test

noeq
type state_s : impl -> Type0 =
| MD5_a: p:int -> state_s MD5
| SHA1_a: p:int -> state_s SHA1
"#;
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type);
        assert!(type_block.is_some(), "Should find type declaration after noeq");
        assert_eq!(type_block.unwrap().names[0], "state_s");
        let text = type_block.unwrap().text();
        assert!(text.contains("noeq"), "noeq modifier should be part of the type block text");
    }

    // =========================================================================
    // Standalone modifier: combined private + noextract/inline
    // =========================================================================

    #[test]
    fn test_private_noextract_standalone() {
        assert!(is_standalone_modifier("private noextract"),
            "private noextract should be standalone modifier");
        assert!(is_standalone_modifier("noextract private"),
            "noextract private should be standalone modifier");
        assert!(is_standalone_modifier("private inline_for_extraction"),
            "private inline_for_extraction should be standalone modifier");
        assert!(is_standalone_modifier("private inline_for_extraction noextract"),
            "private inline_for_extraction noextract should be standalone");
    }

    #[test]
    fn test_private_noextract_before_let() {
        // Real HACL* pattern: Hacl.Impl.SHA3.Vec.fst line 158
        let content = r#"module Test

private noextract
let helper (x:int) = x + 1
"#;
        let (_, blocks) = parse_fstar_file(content);
        let let_block = blocks.iter().find(|b| b.names.contains(&"helper".to_string()));
        assert!(let_block.is_some(), "Should find helper declaration");
        assert!(let_block.unwrap().is_private,
            "Declaration with 'private' on preceding modifier line should be marked private");
        let text = let_block.unwrap().text();
        assert!(text.contains("private noextract"),
            "Modifier line should be attached to declaration");
    }

    // =========================================================================
    // Multi-line attributes
    // =========================================================================

    #[test]
    fn test_multiline_attribute_start_detection() {
        assert!(is_multiline_attribute_start(r#"[@@ Comment "Hello"#),
            "Opening [@@  without ] should be multiline start");
        assert!(!is_multiline_attribute_start(r#"[@@ CInline ]"#),
            "Completed attribute should NOT be multiline start");
        assert!(!is_multiline_attribute_start(r#"  [@@ Comment "Hello"#),
            "Indented multiline attr should not match");
    }

    #[test]
    fn test_multiline_attribute_in_file() {
        // Real HACL* pattern from Hacl.HMAC.fsti
        let content = r#"module Test

[@@ Comment "Write the HMAC-MD5 MAC of a message
by using a key into dst.
dst must point to 16 bytes of memory."]
val compute_md5 : key:int -> data:int -> int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let val_block = blocks.iter().find(|b| b.block_type == BlockType::Val);
        assert!(val_block.is_some(), "Should find val after multi-line attribute");
        assert_eq!(val_block.unwrap().names[0], "compute_md5");
        let text = val_block.unwrap().text();
        assert!(text.contains("[@@ Comment"), "Multi-line attr should be in block text");
        assert!(text.contains("16 bytes of memory."), "Full attribute should be captured");
    }

    #[test]
    fn test_multiline_attribute_with_private_modifier() {
        // Real HACL* pattern from Hacl.Streaming.SHA2.fst:
        //   [@@ CInline ]
        //   private
        //   let update_224_256 = ...
        let content = r#"module Test

[@@ CInline ]
private
let update_fn = F.update hacl_sha2_256
"#;
        let (_, blocks) = parse_fstar_file(content);
        let let_block = blocks.iter().find(|b| b.names.contains(&"update_fn".to_string()));
        assert!(let_block.is_some(), "Should find update_fn declaration");
        assert!(let_block.unwrap().is_private,
            "Declaration with 'private' on modifier line should be marked private");
        let text = let_block.unwrap().text();
        assert!(text.contains("[@@ CInline ]"), "Attribute should be part of block");
    }

    // =========================================================================
    // // line comment handling
    // =========================================================================

    #[test]
    fn test_line_comment_detection() {
        assert!(is_line_comment("// This is a comment"));
        assert!(is_line_comment("//"));
        assert!(is_line_comment("// Test1_SHA3"));
        assert!(!is_line_comment("let x = 1 // inline comment"));
    }

    #[test]
    fn test_line_comments_as_pending_content() {
        // // comments should be accumulated as pending and attached to
        // the subsequent declaration
        let content = r#"module Test

//
// Test1_SHA3
//
let test1 () = run_sha3 ()
"#;
        let (_, blocks) = parse_fstar_file(content);
        let test_block = blocks.iter().find(|b| b.names.contains(&"test1".to_string()));
        assert!(test_block.is_some(), "Should find test1 declaration");
        let text = test_block.unwrap().text();
        assert!(text.contains("// Test1_SHA3"), "// comment should be in block text");
    }

    // =========================================================================
    // Friend declaration: qualified names with many segments
    // =========================================================================

    #[test]
    fn test_friend_deeply_qualified() {
        let result = extract_module_construct_info("friend Hacl.Spec.Curve25519.Field51.Definition");
        assert!(result.is_some());
        let (bt, name, path) = result.unwrap();
        assert_eq!(bt, BlockType::Friend);
        assert_eq!(name, "Hacl.Spec.Curve25519.Field51.Definition");
        assert_eq!(path.as_deref(), Some("Hacl.Spec.Curve25519.Field51.Definition"));
    }

    #[test]
    fn test_friend_with_underscore_and_digits() {
        // Module names can contain underscores and digits
        let result = extract_module_construct_info("friend Hacl.Streaming.Poly1305_32");
        assert!(result.is_some());
        let (bt, name, path) = result.unwrap();
        assert_eq!(bt, BlockType::Friend);
        assert_eq!(name, "Hacl.Streaming.Poly1305_32");
        assert_eq!(path.as_deref(), Some("Hacl.Streaming.Poly1305_32"));
    }

    // =========================================================================
    // Include: multiple includes in sequence
    // =========================================================================

    #[test]
    fn test_multiple_includes_in_header() {
        // Real EverParse pattern: multiple includes at top of file
        let content = r#"module LowParse.Pulse.VCList

include LowParse.Spec.VCList
include LowParse.Pulse.Combinators

module U32 = FStar.UInt32

val parse_vclist : int -> int
"#;
        let (header, _blocks) = parse_fstar_file(content);
        let header_text: String = header.concat();
        assert!(header_text.contains("include LowParse.Spec.VCList"),
            "First include should be in header");
        assert!(header_text.contains("include LowParse.Pulse.Combinators"),
            "Second include should be in header");
        assert!(header_text.contains("module U32 = FStar.UInt32"),
            "Module abbreviation should be in header");
    }

    // =========================================================================
    // Module abbreviation: verify module_path extraction
    // =========================================================================

    #[test]
    fn test_module_abbrev_module_path_in_block() {
        // When module abbreviation appears mid-file, verify module_path is set
        let content = r#"module Test

val foo : int

module H = Spec.Agile.Hash

val bar : int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let abbrev = blocks.iter().find(|b| b.block_type == BlockType::ModuleAbbrev);
        assert!(abbrev.is_some(), "Should find module abbreviation block");
        assert_eq!(abbrev.unwrap().names[0], "H");
        assert_eq!(abbrev.unwrap().module_path.as_deref(), Some("Spec.Agile.Hash"),
            "module_path should capture the target qualified name");
    }

    // =========================================================================
    // Open: verify module_path for mid-file opens
    // =========================================================================

    #[test]
    fn test_open_module_path_in_block() {
        let content = r#"module Test

let x = 1

open LowStar.BufferOps

let y = 2
"#;
        let (_, blocks) = parse_fstar_file(content);
        let open_block = blocks.iter().find(|b| b.block_type == BlockType::Open);
        assert!(open_block.is_some(), "Should find mid-file open block");
        assert_eq!(open_block.unwrap().module_path.as_deref(), Some("LowStar.BufferOps"));
    }

    // =========================================================================
    // Private/abstract: standalone modifier propagation
    // =========================================================================

    #[test]
    fn test_abstract_standalone_before_type() {
        let content = r#"module Test

abstract
type secret_key = int
"#;
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type);
        assert!(type_block.is_some());
        assert!(type_block.unwrap().is_abstract,
            "Type with standalone 'abstract' modifier should be marked abstract");
    }

    // =========================================================================
    // val vs let distinction: verify block types
    // =========================================================================

    #[test]
    fn test_val_let_type_distinction_comprehensive() {
        let content = r#"module Test

val foo : int -> int
let foo x = x + 1

type color = Red | Green | Blue

assume val magic : int -> int

unfold let helper = 42

inline_for_extraction
let uint8 = UInt8.t

class eq (a:Type) = { equals : a -> a -> bool }

instance eq_int : eq int = { equals = fun x y -> x = y }

exception ParseError
"#;
        let (_, blocks) = parse_fstar_file(content);

        // Count block types
        let val_count = blocks.iter().filter(|b| b.block_type == BlockType::Val).count();
        let type_count = blocks.iter().filter(|b| b.block_type == BlockType::Type).count();
        let assume_count = blocks.iter().filter(|b| b.block_type == BlockType::Assume).count();
        let unfold_count = blocks.iter().filter(|b| b.block_type == BlockType::UnfoldLet).count();
        let class_count = blocks.iter().filter(|b| b.block_type == BlockType::Class).count();
        let instance_count = blocks.iter().filter(|b| b.block_type == BlockType::Instance).count();
        let exception_count = blocks.iter().filter(|b| b.block_type == BlockType::Exception).count();

        assert_eq!(val_count, 1, "Should have exactly 1 val (foo)");
        assert_eq!(type_count, 1, "Should have exactly 1 type (color)");
        assert_eq!(assume_count, 1, "Should have exactly 1 assume val (magic)");
        assert_eq!(unfold_count, 1, "Should have exactly 1 unfold let (helper)");
        assert_eq!(class_count, 1, "Should have exactly 1 class (eq)");
        assert_eq!(instance_count, 1, "Should have exactly 1 instance (eq_int)");
        assert_eq!(exception_count, 1, "Should have exactly 1 exception (ParseError)");

        // Note: `inline_for_extraction` on its own line means the `let uint8` line
        // is parsed as a regular Let (the modifier is in pending lines, the declaration
        // line itself starts with `let`). So we have 2 Let blocks: foo and uint8.
        let let_count = blocks.iter().filter(|b| b.block_type == BlockType::Let).count();
        assert_eq!(let_count, 2, "Should have 2 let declarations (foo + uint8 with separate modifier)");

        // Verify the uint8 declaration has the modifier in its block text
        let uint8_block = blocks.iter().find(|b| b.names.contains(&"uint8".to_string()));
        assert!(uint8_block.is_some());
        assert!(uint8_block.unwrap().text().contains("inline_for_extraction"),
            "inline_for_extraction modifier should be in block text even when on separate line");
    }

    // =========================================================================
    // Comprehensive real-world: HACL* streaming module pattern
    // =========================================================================

    #[test]
    fn test_hacl_streaming_hmac_pattern() {
        // Simulates Hacl.Streaming.HMAC.Definitions.fst structure
        let content = r#"module Hacl.Streaming.HMAC.Definitions

open FStar.HyperStack.ST
open LowStar.BufferOps

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost
module S = FStar.Seq
module D = Hacl.Hash.Definitions

open Hacl.Agile.Hash
open Hacl.Streaming.Interface

friend Spec.Agile.HMAC
friend Spec.HMAC.Incremental
friend Hacl.HMAC

#set-options "--fuel 0 --ifuel 0 --z3rlimit 400"

let _sync_decl = ()

noextract inline_for_extraction
val alloca_block : int -> int

let alloca_block i = 42
"#;
        let (header, blocks) = parse_fstar_file(content);

        // Verify header has module, opens, module abbrevs, friends, options
        let header_text: String = header.concat();
        assert!(header_text.contains("module Hacl.Streaming.HMAC.Definitions"));
        assert!(header_text.contains("open FStar.HyperStack.ST"));
        assert!(header_text.contains("module HS = FStar.HyperStack"));
        assert!(header_text.contains("module D = Hacl.Hash.Definitions"));
        assert!(header_text.contains("open Hacl.Agile.Hash"));
        assert!(header_text.contains("friend Spec.Agile.HMAC"));
        assert!(header_text.contains("friend Hacl.HMAC"));
        assert!(header_text.contains("#set-options"));

        // Verify declarations
        assert!(blocks.iter().any(|b| b.names.contains(&"_sync_decl".to_string())),
            "Should find _sync_decl let binding");
        assert!(blocks.iter().any(|b| b.block_type == BlockType::Val
            && b.names.contains(&"alloca_block".to_string())),
            "Should find alloca_block val");
    }

    // =========================================================================
    // Comprehensive real-world: EverParse lowparse pattern
    // =========================================================================

    #[test]
    fn test_everparse_lowparse_pattern() {
        // Simulates LowParse.Low.List.fst structure
        let content = r#"module LowParse.Low.List

include LowParse.Spec.List
include LowParse.Low.Base

module B = LowStar.Buffer
module U32 = FStar.UInt32
module CL = C.Loops
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module G = FStar.Ghost

let valid_exact_list_nil
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures True)
= ()
"#;
        let (header, blocks) = parse_fstar_file(content);

        let header_text: String = header.concat();
        assert!(header_text.contains("include LowParse.Spec.List"));
        assert!(header_text.contains("include LowParse.Low.Base"));
        assert!(header_text.contains("module B = LowStar.Buffer"));
        assert!(header_text.contains("module G = FStar.Ghost"));

        let let_block = blocks.iter().find(|b| b.names.contains(&"valid_exact_list_nil".to_string()));
        assert!(let_block.is_some(), "Should find valid_exact_list_nil");
    }

    // =========================================================================
    // Comprehensive: HACL* streaming SHA2 with multiline attrs + private
    // =========================================================================

    #[test]
    fn test_hacl_sha2_multiline_attr_private() {
        // Simulates Hacl.Streaming.SHA2.fst pattern
        let content = r#"module Test

[@@ Comment
"Allocate initial state for SHA2_256.
The state is to be freed by calling free_256."]
let malloc_256 = F.malloc hacl_sha2_256

[@@ CInline ]
private
let update_224_256 = F.update hacl_sha2_256

[@@ Comment "Feed data into the hash.";
]
let update_256 = update_224_256
"#;
        let (_, blocks) = parse_fstar_file(content);

        // malloc_256 should have the multiline attribute
        let malloc_block = blocks.iter().find(|b| b.names.contains(&"malloc_256".to_string()));
        assert!(malloc_block.is_some(), "Should find malloc_256");
        let text = malloc_block.unwrap().text();
        assert!(text.contains("[@@ Comment"), "Should contain multiline attribute");

        // update_224_256 should be private
        let update_block = blocks.iter().find(|b| b.names.contains(&"update_224_256".to_string()));
        assert!(update_block.is_some(), "Should find update_224_256");
        assert!(update_block.unwrap().is_private,
            "update_224_256 should be marked private");

        // update_256 should have the inline attribute with semicolons
        let update256_block = blocks.iter().find(|b| b.names.contains(&"update_256".to_string()));
        assert!(update256_block.is_some(), "Should find update_256");
    }

    // =========================================================================
    // Ghost modifier
    // =========================================================================

    #[test]
    fn test_ghost_standalone_modifier() {
        assert!(is_standalone_modifier("ghost"),
            "ghost should be a standalone modifier");
    }

    #[test]
    fn test_ghost_let_declaration() {
        let content = r#"module Test

ghost
let ghost_helper (x:int) = x
"#;
        let (_, blocks) = parse_fstar_file(content);
        let let_block = blocks.iter().find(|b| b.names.contains(&"ghost_helper".to_string()));
        assert!(let_block.is_some(), "Should find ghost_helper let binding");
        let text = let_block.unwrap().text();
        assert!(text.contains("ghost"), "ghost modifier should be in block text");
    }

    // =========================================================================
    // Qualified name in module abbreviation: edge cases
    // =========================================================================

    #[test]
    fn test_module_abbrev_single_segment() {
        // Single-segment target (unusual but valid)
        let result = extract_module_construct_info("module M = Prims");
        assert!(result.is_some());
        let (bt, name, path) = result.unwrap();
        assert_eq!(bt, BlockType::ModuleAbbrev);
        assert_eq!(name, "M");
        assert_eq!(path.as_deref(), Some("Prims"));
    }

    #[test]
    fn test_module_abbrev_with_underscore_and_digits() {
        let result = extract_module_construct_info("module SF51 = Hacl.Spec.Curve25519.Field51");
        assert!(result.is_some());
        let (bt, name, path) = result.unwrap();
        assert_eq!(bt, BlockType::ModuleAbbrev);
        assert_eq!(name, "SF51");
        assert_eq!(path.as_deref(), Some("Hacl.Spec.Curve25519.Field51"));
    }

    // =========================================================================
    // is_standalone_modifier: token-based matching edge cases
    // =========================================================================

    #[test]
    fn test_standalone_modifier_all_combos() {
        // All valid single-token modifiers
        assert!(is_standalone_modifier("inline_for_extraction"));
        assert!(is_standalone_modifier("noextract"));
        assert!(is_standalone_modifier("private"));
        assert!(is_standalone_modifier("abstract"));
        assert!(is_standalone_modifier("irreducible"));
        assert!(is_standalone_modifier("opaque_to_smt"));
        assert!(is_standalone_modifier("unfold"));
        assert!(is_standalone_modifier("noeq"));
        assert!(is_standalone_modifier("reflectable"));
        assert!(is_standalone_modifier("reifiable"));
        assert!(is_standalone_modifier("ghost"));
        assert!(is_standalone_modifier("total"));
    }

    #[test]
    fn test_standalone_modifier_combos() {
        // Multi-token combos
        assert!(is_standalone_modifier("private unfold"));
        assert!(is_standalone_modifier("noeq private"));
        assert!(is_standalone_modifier("inline_for_extraction noextract private"));
        assert!(is_standalone_modifier("ghost inline_for_extraction"));
    }

    #[test]
    fn test_standalone_modifier_rejects_non_modifiers() {
        // These should NOT match standalone modifier
        assert!(!is_standalone_modifier("let x = 1"));
        assert!(!is_standalone_modifier("val foo : int"));
        assert!(!is_standalone_modifier("type mytype = int"));
        assert!(!is_standalone_modifier("open FStar.All"));
        assert!(!is_standalone_modifier("private let x = 1")); // 'let' is not a modifier token
        assert!(!is_standalone_modifier("noextract let x = 1")); // 'let' is not a modifier token
        assert!(!is_standalone_modifier("")); // empty
    }

    // =========================================================================
    // detect_visibility_modifiers: comprehensive tests
    // =========================================================================

    #[test]
    fn test_detect_visibility_standalone_private() {
        // Standalone private (on its own line)
        let (priv_, abs_) = detect_visibility_modifiers("private");
        assert!(priv_, "standalone private should be detected");
        assert!(!abs_);
    }

    #[test]
    fn test_detect_visibility_standalone_abstract() {
        let (priv_, abs_) = detect_visibility_modifiers("abstract");
        assert!(!priv_);
        assert!(abs_, "standalone abstract should be detected");
    }

    #[test]
    fn test_detect_visibility_private_in_combo() {
        let (priv_, _) = detect_visibility_modifiers("private noextract");
        assert!(priv_, "private in combo should be detected");

        let (priv2, _) = detect_visibility_modifiers("noextract private");
        assert!(priv2, "private in reversed combo should be detected");
    }

    // =========================================================================
    // Complete file: friend declarations after sync_decl pattern
    // =========================================================================

    #[test]
    fn test_friend_after_sync_decl() {
        // Pattern from Hacl.Agile.Hash.fst: friend in header, then sync_decl,
        // then module abbreviation mid-file
        let content = r#"module Hacl.Agile.Hash

open FStar.HyperStack.ST

module B = LowStar.Buffer

friend EverCrypt.Hash

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let _sync_decl1 = ()
let _sync_decl2 = ()

module H = Spec.Agile.Hash

noeq
type state_s : impl -> Type0 =
| MD5_a: p:int -> state_s MD5
"#;
        let (header, blocks) = parse_fstar_file(content);

        // Header should contain friend
        let header_text: String = header.concat();
        assert!(header_text.contains("friend EverCrypt.Hash"),
            "friend should be in header");

        // Should find sync declarations
        assert!(blocks.iter().any(|b| b.names.contains(&"_sync_decl1".to_string())));
        assert!(blocks.iter().any(|b| b.names.contains(&"_sync_decl2".to_string())));

        // Mid-file module abbreviation
        let abbrev = blocks.iter().find(|b| b.block_type == BlockType::ModuleAbbrev);
        assert!(abbrev.is_some(), "Should find mid-file module H abbreviation");
        assert_eq!(abbrev.unwrap().names[0], "H");
        assert_eq!(abbrev.unwrap().module_path.as_deref(), Some("Spec.Agile.Hash"));

        // noeq type should be found
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type);
        assert!(type_block.is_some(), "Should find type state_s");
        assert_eq!(type_block.unwrap().names[0], "state_s");
    }

    // =========================================================================
    // is_line_comment edge cases
    // =========================================================================

    #[test]
    fn test_line_comment_edge_cases() {
        assert!(is_line_comment("// hello"), "basic // comment");
        assert!(is_line_comment("//"), "bare // is a comment");
        assert!(is_line_comment("  // indented"), "indented // is still a comment");
        assert!(!is_line_comment("let x = 1 // trailing"), "not a top-level line comment");
        assert!(!is_line_comment("(* block *)"), "not a line comment");
        assert!(!is_line_comment(""), "empty is not a comment");
    }

    // =========================================================================
    // Comprehensive: all module system constructs in one file
    // =========================================================================

    #[test]
    fn test_all_module_system_constructs() {
        let content = r#"module All.Constructs.Test

open FStar.HyperStack.ST
open FStar.Mul

include LowParse.Spec.Base

module B = LowStar.Buffer
module U32 = FStar.UInt32

friend Spec.Agile.Hash

#set-options "--fuel 0 --ifuel 0"

val foo : int -> int
let foo x = x + 1

open Spec.Hash.Definitions

module D = Hacl.Hash.Definitions

include LowParse.Low.Base

friend Hacl.HMAC

private let helper x = x

noeq
type my_state = { buf: int; len: int }

assume val magic : int -> int

let bar x = helper x + foo x
"#;
        let (header, blocks) = parse_fstar_file(content);

        // Header verification
        let ht: String = header.concat();
        assert!(ht.contains("module All.Constructs.Test"));
        assert!(ht.contains("open FStar.HyperStack.ST"));
        assert!(ht.contains("open FStar.Mul"));
        assert!(ht.contains("include LowParse.Spec.Base"));
        assert!(ht.contains("module B = LowStar.Buffer"));
        assert!(ht.contains("module U32 = FStar.UInt32"));
        assert!(ht.contains("friend Spec.Agile.Hash"));
        assert!(ht.contains("#set-options"));

        // Mid-file constructs
        let mid_opens: Vec<_> = blocks.iter().filter(|b| b.block_type == BlockType::Open).collect();
        assert!(mid_opens.iter().any(|b| b.module_path.as_deref() == Some("Spec.Hash.Definitions")),
            "Should find mid-file open Spec.Hash.Definitions");

        let mid_abbrevs: Vec<_> = blocks.iter().filter(|b| b.block_type == BlockType::ModuleAbbrev).collect();
        assert!(mid_abbrevs.iter().any(|b| b.names[0] == "D"),
            "Should find mid-file module D abbreviation");

        let mid_includes: Vec<_> = blocks.iter().filter(|b| b.block_type == BlockType::Include).collect();
        assert!(mid_includes.iter().any(|b| b.module_path.as_deref() == Some("LowParse.Low.Base")),
            "Should find mid-file include");

        let mid_friends: Vec<_> = blocks.iter().filter(|b| b.block_type == BlockType::Friend).collect();
        assert!(mid_friends.iter().any(|b| b.module_path.as_deref() == Some("Hacl.HMAC")),
            "Should find mid-file friend");

        // Declarations
        assert!(blocks.iter().any(|b| b.block_type == BlockType::Val && b.names.contains(&"foo".to_string())));
        assert!(blocks.iter().any(|b| b.block_type == BlockType::Let && b.names.contains(&"foo".to_string())));

        let helper_block = blocks.iter().find(|b| b.names.contains(&"helper".to_string()));
        assert!(helper_block.is_some());
        assert!(helper_block.unwrap().is_private, "helper should be marked private");

        assert!(blocks.iter().any(|b| b.block_type == BlockType::Type && b.names.contains(&"my_state".to_string())));
        assert!(blocks.iter().any(|b| b.block_type == BlockType::Assume && b.names.contains(&"magic".to_string())));
        assert!(blocks.iter().any(|b| b.block_type == BlockType::Let && b.names.contains(&"bar".to_string())));
    }

    // =========================================================================
    // EffectSignature extraction tests
    // =========================================================================

    #[test]
    fn test_extract_effect_sig_stack_requires_ensures() {
        let content = r#"module Test

val my_fn : buf:buffer uint8 -> Stack unit
  (requires fun h -> live h buf)
  (ensures  fun h0 _ h1 -> modifies (loc_buffer buf) h0 h1)
"#;
        let (_, blocks) = parse_fstar_file(content);
        let val_b = blocks.iter().find(|b| b.block_type == BlockType::Val).unwrap();
        let sig = val_b.effect_signature.as_ref().expect("Should have effect sig");
        assert_eq!(sig.effect_name, "Stack");
        assert!(sig.has_requires);
        assert!(sig.has_ensures);
        assert!(sig.has_modifies);
        assert!(sig.is_stateful_effect());
    }

    #[test]
    fn test_extract_effect_sig_tot_decreases() {
        let content = "module Test\n\nval fib : n:nat -> Tot nat (decreases n)\n";
        let (_, blocks) = parse_fstar_file(content);
        let val_b = blocks.iter().find(|b| b.block_type == BlockType::Val).unwrap();
        let sig = val_b.effect_signature.as_ref().expect("Should have effect sig");
        assert_eq!(sig.effect_name, "Tot");
        assert!(sig.has_decreases);
    }

    #[test]
    fn test_extract_effect_sig_lemma() {
        let content = "module Test\n\nval lem : x:nat -> Lemma (ensures x >= 0) [SMTPat x]\n";
        let (_, blocks) = parse_fstar_file(content);
        let val_b = blocks.iter().find(|b| b.block_type == BlockType::Val).unwrap();
        let sig = val_b.effect_signature.as_ref().expect("Should have effect sig");
        assert_eq!(sig.effect_name, "Lemma");
        assert!(sig.has_ensures);
        assert!(sig.is_lemma_effect());
    }

    #[test]
    fn test_extract_effect_sig_pure_hoare() {
        let content = "module Test\n\nval safe_div : x:int -> y:int -> Pure int (requires y <> 0) (ensures fun r -> r * y == x)\n";
        let (_, blocks) = parse_fstar_file(content);
        let val_b = blocks.iter().find(|b| b.block_type == BlockType::Val).unwrap();
        let sig = val_b.effect_signature.as_ref().expect("Should have effect sig");
        assert_eq!(sig.effect_name, "Pure");
        assert!(sig.has_requires);
        assert!(sig.has_ensures);
        assert!(sig.is_pure_hoare_effect());
    }

    #[test]
    fn test_extract_effect_sig_no_effect() {
        let content = "module Test\n\nval add : int -> int -> int\n";
        let (_, blocks) = parse_fstar_file(content);
        let val_b = blocks.iter().find(|b| b.block_type == BlockType::Val).unwrap();
        assert!(val_b.effect_signature.is_none(), "No explicit effect -> no signature");
    }

    #[test]
    fn test_extract_effect_sig_effect_abbrev_base() {
        let content = "module Test\n\neffect Dv (a: Type) = DIV a (pure_null_wp a)\n";
        let (_, blocks) = parse_fstar_file(content);
        let eff_b = blocks.iter().find(|b| b.block_type == BlockType::EffectAbbrev).unwrap();
        let sig = eff_b.effect_signature.as_ref().expect("Should have effect sig");
        assert_eq!(sig.base_effect.as_deref(), Some("DIV"));
    }

    #[test]
    fn test_extract_effect_sig_sub_effect_src_dst() {
        let content = "module Test\n\nsub_effect PURE ~> DIV = fun a wp -> wp\n";
        let (_, blocks) = parse_fstar_file(content);
        let se_b = blocks.iter().find(|b| b.block_type == BlockType::SubEffect).unwrap();
        let sig = se_b.effect_signature.as_ref().expect("Should have effect sig");
        assert_eq!(sig.sub_effect_src.as_deref(), Some("PURE"));
        assert_eq!(sig.sub_effect_dst.as_deref(), Some("DIV"));
    }

    #[test]
    fn test_extract_effect_sig_new_effect_combinators() {
        let content = "module Test\n\nnew_effect { STATE : a:Type -> Effect\n  with return_wp = fun a x -> x\n     ; bind_wp = fun a b w1 w2 -> w1\n}\n";
        let (_, blocks) = parse_fstar_file(content);
        let ne_b = blocks.iter().find(|b| b.block_type == BlockType::NewEffect).unwrap();
        let sig = ne_b.effect_signature.as_ref().expect("Should have effect sig");
        assert!(sig.combinators.contains(&"return_wp".to_string()));
        assert!(sig.combinators.contains(&"bind_wp".to_string()));
    }

    #[test]
    fn test_extract_effect_sig_layered_repr_return_bind() {
        let content = "module Test\n\nlayered_effect { TAC : a:Type -> tac_wp a -> Effect\n  with repr = __tac\n     ; return = fun a x -> x\n     ; bind = fun a b m f -> m\n     ; subcomp = fun a f -> f\n}\n";
        let (_, blocks) = parse_fstar_file(content);
        let le_b = blocks.iter().find(|b| b.block_type == BlockType::Effect).unwrap();
        let sig = le_b.effect_signature.as_ref().expect("Should have effect sig");
        assert!(sig.combinators.contains(&"repr".to_string()));
        assert!(sig.combinators.contains(&"return".to_string()));
        assert!(sig.combinators.contains(&"bind".to_string()));
        assert!(sig.combinators.contains(&"subcomp".to_string()));
    }

    #[test]
    fn test_effect_signature_methods() {
        // Test EffectSignature helper methods
        let stack_sig = EffectSignature {
            effect_name: "Stack".to_string(),
            has_requires: true,
            has_ensures: true,
            has_decreases: false,
            has_modifies: true,
            effect_line: 1,
            sub_effect_src: None,
            sub_effect_dst: None,
            base_effect: None,
            combinators: Vec::new(),
        };
        assert!(stack_sig.is_stateful_effect());
        assert!(!stack_sig.is_lemma_effect());
        assert!(!stack_sig.is_pure_hoare_effect());

        let lemma_sig = EffectSignature {
            effect_name: "Lemma".to_string(),
            has_requires: false,
            has_ensures: true,
            has_decreases: false,
            has_modifies: false,
            effect_line: 1,
            sub_effect_src: None,
            sub_effect_dst: None,
            base_effect: None,
            combinators: Vec::new(),
        };
        assert!(!lemma_sig.is_stateful_effect());
        assert!(lemma_sig.is_lemma_effect());
        assert!(!lemma_sig.is_pure_hoare_effect());

        let pure_sig = EffectSignature {
            effect_name: "Pure".to_string(),
            has_requires: true,
            has_ensures: true,
            has_decreases: false,
            has_modifies: false,
            effect_line: 1,
            sub_effect_src: None,
            sub_effect_dst: None,
            base_effect: None,
            combinators: Vec::new(),
        };
        assert!(!pure_sig.is_stateful_effect());
        assert!(!pure_sig.is_lemma_effect());
        assert!(pure_sig.is_pure_hoare_effect());
    }

    // =========================================================================
    // Pragma parsing tests
    // =========================================================================

    #[test]
    fn test_parse_pragma_set_options() {
        let p = parse_pragma(r#"#set-options "--z3rlimit 50 --fuel 0 --ifuel 0""#);
        assert_eq!(
            p,
            Some(Pragma::SetOptions("--z3rlimit 50 --fuel 0 --ifuel 0".to_string()))
        );
    }

    #[test]
    fn test_parse_pragma_push_options() {
        let p = parse_pragma(r#"#push-options "--fuel 2""#);
        assert_eq!(p, Some(Pragma::PushOptions("--fuel 2".to_string())));
    }

    #[test]
    fn test_parse_pragma_pop_options() {
        let p = parse_pragma("#pop-options");
        assert_eq!(p, Some(Pragma::PopOptions));
    }

    #[test]
    fn test_parse_pragma_reset_options_no_value() {
        let p = parse_pragma("#reset-options");
        assert_eq!(p, Some(Pragma::ResetOptions(None)));
    }

    #[test]
    fn test_parse_pragma_reset_options_with_value() {
        let p = parse_pragma(r#"#reset-options "--z3rlimit 5""#);
        assert_eq!(
            p,
            Some(Pragma::ResetOptions(Some("--z3rlimit 5".to_string())))
        );
    }

    #[test]
    fn test_parse_pragma_restart_solver() {
        let p = parse_pragma("#restart-solver");
        assert_eq!(p, Some(Pragma::RestartSolver));
    }

    #[test]
    fn test_parse_pragma_not_a_pragma() {
        assert_eq!(parse_pragma("let x = 1"), None);
        assert_eq!(parse_pragma("val foo : int"), None);
        assert_eq!(parse_pragma("// comment"), None);
    }

    #[test]
    fn test_parse_pragma_options_key_value_pairs() {
        let opts = parse_pragma_options("--z3rlimit 50 --fuel 0 --ifuel 0");
        assert_eq!(opts.len(), 3);
        assert_eq!(opts[0], ("--z3rlimit".to_string(), Some("50".to_string())));
        assert_eq!(opts[1], ("--fuel".to_string(), Some("0".to_string())));
        assert_eq!(opts[2], ("--ifuel".to_string(), Some("0".to_string())));
    }

    #[test]
    fn test_parse_pragma_options_flag_only() {
        let opts = parse_pragma_options("--smtencoding.valid_intro true --smtencoding.valid_elim true");
        assert_eq!(opts.len(), 2);
        assert_eq!(
            opts[0],
            ("--smtencoding.valid_intro".to_string(), Some("true".to_string()))
        );
    }

    #[test]
    fn test_parse_pragma_options_empty() {
        let opts = parse_pragma_options("");
        assert!(opts.is_empty());
    }

    // =========================================================================
    // Attribute parsing tests
    // =========================================================================

    #[test]
    fn test_parse_attribute_old_style() {
        let attrs = parse_attributes("[@ CNoInline ]");
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].style, AttributeStyle::OldStyle);
        assert_eq!(attrs[0].name, "CNoInline");
    }

    #[test]
    fn test_parse_attribute_declaration() {
        let attrs = parse_attributes("[@@ CInline ]");
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].style, AttributeStyle::Declaration);
        assert_eq!(attrs[0].name, "CInline");
    }

    #[test]
    fn test_parse_attribute_binder() {
        let attrs = parse_attributes("[@@@ strict_on_arguments [1;2]]");
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].style, AttributeStyle::Binder);
        assert_eq!(attrs[0].name, "strict_on_arguments");
        assert!(attrs[0].args.is_some());
        assert_eq!(attrs[0].args.as_deref(), Some("[1;2]"));
    }

    #[test]
    fn test_parse_attribute_quoted_name() {
        let attrs = parse_attributes(r#"[@@"opaque_to_smt"]"#);
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].style, AttributeStyle::Declaration);
        assert_eq!(attrs[0].name, "opaque_to_smt");
    }

    #[test]
    fn test_parse_attribute_with_string_arg() {
        let attrs = parse_attributes(r#"[@@ Comment "Write the HMAC-MD5 MAC"]"#);
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].name, "Comment");
        assert!(attrs[0].args.is_some());
    }

    #[test]
    fn test_parse_attribute_no_auto_projectors() {
        let attrs = parse_attributes("[@@ no_auto_projectors]");
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].name, "no_auto_projectors");
    }

    #[test]
    fn test_parse_multiple_attributes_semicolon() {
        let attrs = parse_attributes("[@@ CInline; CMacro]");
        assert_eq!(attrs.len(), 2);
        assert_eq!(attrs[0].name, "CInline");
        assert_eq!(attrs[1].name, "CMacro");
    }

    #[test]
    fn test_extract_attribute_names_fn() {
        let names = extract_attribute_names("[@@ CInline ]");
        assert_eq!(names, vec!["CInline"]);
    }

    #[test]
    fn test_parse_attribute_empty() {
        let attrs = parse_attributes("let x = 1");
        assert!(attrs.is_empty());
    }

    // =========================================================================
    // SMT pattern parsing tests
    // =========================================================================

    #[test]
    fn test_parse_smt_pattern_single() {
        let patterns = parse_smt_patterns("val foo : x:int -> Lemma (P x) [SMTPat (f x)]");
        assert_eq!(patterns.len(), 1);
        match &patterns[0] {
            SmtPattern::Pat(expr) => assert_eq!(expr, "f x"),
            _ => panic!("Expected SmtPattern::Pat"),
        }
    }

    #[test]
    fn test_parse_smt_pattern_multiple() {
        let text = "val foo : x:int -> y:int -> Lemma (P x y) [SMTPat (f x); SMTPat (g y)]";
        let patterns = parse_smt_patterns(text);
        assert_eq!(patterns.len(), 2);
        match &patterns[0] {
            SmtPattern::Pat(expr) => assert_eq!(expr, "f x"),
            _ => panic!("Expected SmtPattern::Pat for first"),
        }
        match &patterns[1] {
            SmtPattern::Pat(expr) => assert_eq!(expr, "g y"),
            _ => panic!("Expected SmtPattern::Pat for second"),
        }
    }

    #[test]
    fn test_parse_smt_pattern_or() {
        let text = "val foo : x:int -> Lemma (P x) [SMTPatOr [[SMTPat (f x)]; [SMTPat (g x)]]]";
        let patterns = parse_smt_patterns(text);
        assert_eq!(patterns.len(), 1);
        match &patterns[0] {
            SmtPattern::PatOr(alts) => {
                assert_eq!(alts.len(), 2);
                assert_eq!(alts[0].len(), 1);
                assert_eq!(alts[1].len(), 1);
                match &alts[0][0] {
                    SmtPattern::Pat(expr) => assert_eq!(expr, "f x"),
                    _ => panic!("Expected Pat in first alt"),
                }
                match &alts[1][0] {
                    SmtPattern::Pat(expr) => assert_eq!(expr, "g x"),
                    _ => panic!("Expected Pat in second alt"),
                }
            }
            _ => panic!("Expected SmtPattern::PatOr"),
        }
    }

    #[test]
    fn test_parse_smt_pattern_nested_parens() {
        let text = "val foo : Lemma (P x) [SMTPat (S.index (seq_uint32_of_be n b) i)]";
        let patterns = parse_smt_patterns(text);
        assert_eq!(patterns.len(), 1);
        match &patterns[0] {
            SmtPattern::Pat(expr) => {
                assert!(expr.contains("S.index"));
                assert!(expr.contains("seq_uint32_of_be"));
            }
            _ => panic!("Expected SmtPattern::Pat"),
        }
    }

    #[test]
    fn test_parse_smt_pattern_none() {
        let text = "val foo : int -> int";
        let patterns = parse_smt_patterns(text);
        assert!(patterns.is_empty());
    }

    #[test]
    fn test_extract_smt_pattern_references_simple() {
        let patterns = vec![
            SmtPattern::Pat("f x".to_string()),
            SmtPattern::Pat("g y".to_string()),
        ];
        let refs = extract_smt_pattern_references(&patterns);
        assert!(refs.contains("f"));
        assert!(refs.contains("x"));
        assert!(refs.contains("g"));
        assert!(refs.contains("y"));
    }

    #[test]
    fn test_extract_smt_pattern_references_pat_or() {
        let patterns = vec![SmtPattern::PatOr(vec![
            vec![SmtPattern::Pat("f x".to_string())],
            vec![SmtPattern::Pat("g x".to_string())],
        ])];
        let refs = extract_smt_pattern_references(&patterns);
        assert!(refs.contains("f"));
        assert!(refs.contains("g"));
        assert!(refs.contains("x"));
    }

    // =========================================================================
    // Tactic expression parsing tests
    // =========================================================================

    #[test]
    fn test_extract_tactic_assert_by() {
        let text = "assert (big_and' f [] == True) by (T.compute())";
        let tactics = extract_tactic_bodies(text);
        assert!(!tactics.is_empty(), "Should find assert...by tactic");
        let found = tactics.iter().any(|t| matches!(t, TacticExpr::AssertBy { .. }));
        assert!(found, "Should find AssertBy variant");
    }

    #[test]
    fn test_extract_tactic_wildcard_by() {
        let text = "= _ by (FStar.Tactics.Canon.canon())";
        let tactics = extract_tactic_bodies(text);
        let found = tactics.iter().any(|t| matches!(t, TacticExpr::WildcardBy { .. }));
        assert!(found, "Should find WildcardBy variant");
    }

    #[test]
    fn test_extract_tactic_wildcard_by_body() {
        let text = "= _ by (FStar.Tactics.Canon.canon ())";
        let tactics = extract_tactic_bodies(text);
        if let Some(TacticExpr::WildcardBy { tactic_body }) = tactics.first() {
            assert!(
                tactic_body.contains("FStar.Tactics.Canon.canon"),
                "Tactic body should contain the tactic call, got: {}",
                tactic_body
            );
        } else {
            panic!("Expected WildcardBy tactic");
        }
    }

    #[test]
    fn test_extract_tactic_synth_by_tactic() {
        let text = r#"let f :int -> St int = synth_by_tactic (specialize (foo [1; 2]))"#;
        let tactics = extract_tactic_bodies(text);
        let found = tactics.iter().any(|t| matches!(t, TacticExpr::SynthByTactic { .. }));
        assert!(found, "Should find SynthByTactic variant");
    }

    #[test]
    fn test_extract_tactic_nested_parens() {
        let text = "assert (x + (y * z) == w) by (norm [delta_only [`%on_domain]]; trefl ())";
        let tactics = extract_tactic_bodies(text);
        assert!(!tactics.is_empty(), "Should find tactic with nested parens");
    }

    #[test]
    fn test_extract_tactic_multiline() {
        let text = "assert (larger) by (\n    let open FStar.Stubs.Tactics.V2.Builtins in\n    smt ()\n  )";
        let tactics = extract_tactic_bodies(text);
        assert!(!tactics.is_empty(), "Should find multiline tactic");
    }

    #[test]
    fn test_contains_tactic_constructs_positive() {
        assert!(contains_tactic_constructs("_ by (smt())"));
        assert!(contains_tactic_constructs("assert P by (trivial())"));
        assert!(contains_tactic_constructs("synth_by_tactic (fun () -> exact ())"));
    }

    #[test]
    fn test_contains_tactic_constructs_negative() {
        assert!(!contains_tactic_constructs("let x = 1"));
        assert!(!contains_tactic_constructs("val foo : int -> int"));
        assert!(!contains_tactic_constructs("type mytype = int"));
    }

    #[test]
    fn test_no_tactic_in_comment() {
        let text = "(* assert P by (smt()) *)";
        let tactics = extract_tactic_bodies(text);
        assert!(tactics.is_empty(), "Should not find tactics inside comments");
    }

    #[test]
    fn test_no_tactic_in_string() {
        let text = r#"let msg = "assert P by (smt())""#;
        let tactics = extract_tactic_bodies(text);
        assert!(tactics.is_empty(), "Should not find tactics inside strings");
    }

    // =========================================================================
    // Quotation parsing tests
    // =========================================================================

    #[test]
    fn test_extract_quotation_name() {
        let quots = extract_quotations("apply_lemma (`other_lemma)");
        let found = quots.iter().any(|q| matches!(q, Quotation::Name(n) if n == "other_lemma"));
        assert!(found, "Should find `other_lemma quotation, got: {:?}", quots);
    }

    #[test]
    fn test_extract_quotation_qualified_name() {
        let quots = extract_quotations("delta_only [`%calc_chain_related]");
        let found = quots
            .iter()
            .any(|q| matches!(q, Quotation::QualifiedName(n) if n == "calc_chain_related"));
        assert!(found, "Should find `%calc_chain_related, got: {:?}", quots);
    }

    #[test]
    fn test_extract_quotation_multiple() {
        let text = "norm [delta_only [`%canon; `%xsdenote; `%flatten]]";
        let quots = extract_quotations(text);
        assert!(quots.len() >= 3, "Should find at least 3 quotations, got: {:?}", quots);
        let names: Vec<_> = quots
            .iter()
            .filter_map(|q| match q {
                Quotation::QualifiedName(n) => Some(n.as_str()),
                _ => None,
            })
            .collect();
        assert!(names.contains(&"canon"), "Should find canon");
        assert!(names.contains(&"xsdenote"), "Should find xsdenote");
        assert!(names.contains(&"flatten"), "Should find flatten");
    }

    #[test]
    fn test_extract_quotation_expr() {
        let quots = extract_quotations("exact (`(1 + 1))");
        let found = quots.iter().any(|q| matches!(q, Quotation::Expr(_)));
        assert!(found, "Should find expression quotation, got: {:?}", quots);
    }

    #[test]
    fn test_extract_quotation_none() {
        let quots = extract_quotations("let x = 1 + 2");
        assert!(quots.is_empty(), "Should find no quotations in plain code");
    }

    #[test]
    fn test_extract_quotation_not_in_comment() {
        let quots = extract_quotations("(* `foo *)");
        assert!(
            quots.is_empty(),
            "Should not find quotation inside comment"
        );
    }

    #[test]
    fn test_extract_quotation_not_in_string() {
        let quots = extract_quotations(r#"let s = "`foo""#);
        assert!(
            quots.is_empty(),
            "Should not find quotation inside string"
        );
    }

    #[test]
    fn test_extract_quotation_references_qualified() {
        let refs = extract_quotation_references("delta_only [`%calc_chain_related; `%on_domain]");
        assert!(refs.contains("calc_chain_related"));
        assert!(refs.contains("on_domain"));
    }

    #[test]
    fn test_extract_quotation_references_name() {
        let refs = extract_quotation_references("apply_lemma (`my_lemma)");
        assert!(refs.contains("my_lemma"));
    }

    // =========================================================================
    // Integration: tactic/metaprogramming in full file parsing
    // =========================================================================

    #[test]
    fn test_parse_file_with_tactics() {
        let content = r#"module Test

open FStar.All

val foo : x:nat -> Lemma (ensures x + 0 = x) [SMTPat (x + 0)]

let proof_with_tactic x =
  assert (x + 0 = x) by (T.compute())

let synthesized = synth_by_tactic (fun () -> exact (`42))
"#;
        let (header, blocks) = parse_fstar_file(content);
        assert!(!header.is_empty());

        let val_block = blocks.iter().find(|b| b.block_type == BlockType::Val);
        assert!(val_block.is_some(), "Should find val foo");

        assert!(
            blocks
                .iter()
                .any(|b| b.names.contains(&"proof_with_tactic".to_string())),
            "Should find proof_with_tactic"
        );

        assert!(
            blocks
                .iter()
                .any(|b| b.names.contains(&"synthesized".to_string())),
            "Should find synthesized"
        );
    }

    #[test]
    fn test_parse_file_with_pragmas() {
        let content = r#"module Test

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val foo : int -> int

#push-options "--fuel 2"
let foo x = x + 1
#pop-options

#restart-solver

val bar : int -> int
"#;
        let (header, blocks) = parse_fstar_file(content);

        let header_text: String = header.concat();
        assert!(
            header_text.contains("#set-options"),
            "Header should contain #set-options"
        );

        assert!(parse_pragma(r#"#set-options "--z3rlimit 50 --fuel 0 --ifuel 0""#).is_some());

        assert!(
            blocks.iter().any(|b| b.block_type == BlockType::Val),
            "Should have val blocks"
        );
    }

    #[test]
    fn test_parse_file_with_attributes() {
        let content = r#"module Test

open FStar.All

[@@ CInline ]
let helper x = x + 1

[@@"opaque_to_smt"]
val secret : int -> int
"#;
        let (_, blocks) = parse_fstar_file(content);

        assert!(
            blocks.iter().any(|b| b.names.contains(&"helper".to_string())),
            "Should find helper"
        );
        assert!(
            blocks.iter().any(|b| b.names.contains(&"secret".to_string())),
            "Should find secret"
        );
    }

    #[test]
    fn test_parse_file_with_smt_patterns() {
        let content = r#"module Test

val lemma1 : x:nat -> Lemma (x + 0 = x) [SMTPat (x + 0)]

val lemma2 : x:int -> y:int -> Lemma (P x y)
  [SMTPatOr [[SMTPat (f x); SMTPat (g y)];
             [SMTPat (h x)]]]
"#;
        let (_, blocks) = parse_fstar_file(content);

        let lemma1 = blocks.iter().find(|b| b.names.contains(&"lemma1".to_string()));
        assert!(lemma1.is_some(), "Should find lemma1");

        let lemma2 = blocks.iter().find(|b| b.names.contains(&"lemma2".to_string()));
        assert!(lemma2.is_some(), "Should find lemma2");

        let lemma1_text = lemma1.unwrap().text();
        let pats = parse_smt_patterns(&lemma1_text);
        assert!(!pats.is_empty(), "lemma1 should have SMT patterns");
    }

    #[test]
    fn test_parse_file_with_quotations_in_tactic() {
        let content = r#"module Test

let proof () =
  assert True by (
    norm [delta_only [`%my_def]];
    trefl ()
  )
"#;
        let (_, blocks) = parse_fstar_file(content);

        let proof_block = blocks.iter().find(|b| b.names.contains(&"proof".to_string()));
        assert!(proof_block.is_some(), "Should find proof");

        let quots = extract_quotations(&proof_block.unwrap().text());
        let has_my_def = quots
            .iter()
            .any(|q| matches!(q, Quotation::QualifiedName(n) if n == "my_def"));
        assert!(has_my_def, "Should find `%my_def quotation");
    }

    #[test]
    fn test_calc_block_with_wildcard_by() {
        let content = r#"module Test

let lemma x =
  calc (==) {
    x + 0;
    == { _ by (FStar.Tactics.Canon.canon()) }
    x;
  }
"#;
        let (_, blocks) = parse_fstar_file(content);
        assert!(
            blocks.iter().any(|b| b.names.contains(&"lemma".to_string())),
            "Should find lemma"
        );

        let lemma_block = blocks
            .iter()
            .find(|b| b.names.contains(&"lemma".to_string()))
            .unwrap();
        let tactics = extract_tactic_bodies(&lemma_block.text());
        let has_wildcard = tactics
            .iter()
            .any(|t| matches!(t, TacticExpr::WildcardBy { .. }));
        assert!(has_wildcard, "Should find _ by (...) in calc block");
    }

    // =========================================================================
    // Balanced delimiter helper tests
    // =========================================================================

    #[test]
    fn test_balanced_parens_simple() {
        let (content, end) = extract_balanced_parens("(hello)", 0).unwrap();
        assert_eq!(content, "hello");
        assert_eq!(end, 7);
    }

    #[test]
    fn test_balanced_parens_nested() {
        let (content, _) = extract_balanced_parens("(a (b c) d)", 0).unwrap();
        assert_eq!(content, "a (b c) d");
    }

    #[test]
    fn test_balanced_parens_unmatched() {
        assert!(extract_balanced_parens("(open", 0).is_none());
    }

    #[test]
    fn test_balanced_brackets_simple() {
        let (content, end) = extract_balanced_brackets("[hello]", 0).unwrap();
        assert_eq!(content, "hello");
        assert_eq!(end, 7);
    }

    #[test]
    fn test_balanced_brackets_nested() {
        let (content, _) = extract_balanced_brackets("[a [b] c]", 0).unwrap();
        assert_eq!(content, "a [b] c");
    }

    #[test]
    fn test_split_respecting_parens_simple() {
        let parts = split_respecting_parens("a; b; c", ';');
        assert_eq!(parts, vec!["a", " b", " c"]);
    }

    #[test]
    fn test_split_respecting_parens_nested() {
        let parts = split_respecting_parens("SMTPat (f x); SMTPat (g (h y))", ';');
        assert_eq!(parts.len(), 2);
        assert!(parts[0].contains("SMTPat (f x)"));
        assert!(parts[1].contains("SMTPat (g (h y))"));
    }

    // =========================================================================
    // Real-world pattern tests (from FStar/ulib and HACL*)
    // =========================================================================

    #[test]
    fn test_smt_pattern_from_real_hyperstack() {
        let text = r#"val lemma :
  Lemma (ensures P)
  [SMTPatOr [[SMTPat (same_refs m0 m1); SMTPat (m0 r)];
             [SMTPat (same_refs m0 m1); SMTPat (m1 r)]]]"#;
        let patterns = parse_smt_patterns(text);
        assert!(!patterns.is_empty(), "Should parse SMTPatOr from HyperStack");
    }

    #[test]
    fn test_smt_pattern_from_real_bv() {
        let text =
            "val int2bv_bv2int: #n:pos -> vec:bv_t n -> Lemma (ensures vec = (int2bv (bv2int vec))) [SMTPat (int2bv (bv2int vec))]";
        let patterns = parse_smt_patterns(text);
        assert_eq!(patterns.len(), 1);
        match &patterns[0] {
            SmtPattern::Pat(expr) => {
                assert!(expr.contains("int2bv"));
                assert!(expr.contains("bv2int"));
            }
            _ => panic!("Expected SmtPattern::Pat"),
        }
    }

    #[test]
    fn test_assert_by_from_real_bigops() {
        let text = "= assert (big_and' f [] == True) by (T.compute())";
        let tactics = extract_tactic_bodies(text);
        assert!(!tactics.is_empty(), "Should find tactic in BigOps pattern");
    }

    #[test]
    fn test_wildcard_by_from_real_uint128() {
        // Incomplete text (missing closing paren) should not panic
        let text = "= _ by (T.norm [delta_only [`%carry_uint64]; unascribe];";
        let _ = extract_tactic_bodies(text);
    }

    #[test]
    fn test_quotation_from_real_calc() {
        let text = "let unfold steps = [delta_only [`%calc_chain_related]; iota; zeta]";
        let quots = extract_quotations(text);
        let has_calc = quots
            .iter()
            .any(|q| matches!(q, Quotation::QualifiedName(n) if n == "calc_chain_related"));
        assert!(has_calc, "Should find `%calc_chain_related quotation");
    }

    #[test]
    fn test_quotation_from_real_canon() {
        let text = "norm [delta_only [`%canon; `%xsdenote; `%flatten; `%sort]]";
        let quots = extract_quotations(text);
        assert!(quots.len() >= 4, "Should find at least 4 quotations, got {}", quots.len());
    }

    #[test]
    fn test_pragma_from_real_hacl() {
        let p = parse_pragma(r#"#set-options "--z3rlimit 50 --fuel 0 --ifuel 0""#);
        assert!(p.is_some());
        if let Some(Pragma::SetOptions(opts)) = p {
            let parsed = parse_pragma_options(&opts);
            assert_eq!(parsed.len(), 3);
            assert!(parsed.iter().any(|(k, v)| k == "--z3rlimit" && v.as_deref() == Some("50")));
        }
    }

    #[test]
    fn test_attribute_from_real_hacl_streaming() {
        let attrs = parse_attributes("[@@ CInline ]");
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].name, "CInline");
        assert_eq!(attrs[0].style, AttributeStyle::Declaration);
    }

    #[test]
    fn test_references_include_quotation_targets() {
        // Extract references should pick up `%my_def as a reference
        let text = "let proof () = assert True by (norm [delta_only [`%my_def]]; trefl ())";
        let exclude = HashSet::new();
        let refs = extract_references(text, &exclude);
        assert!(
            refs.contains("my_def"),
            "extract_references should include `%my_def target, got: {:?}",
            refs
        );
    }

    #[test]
    fn test_quotation_with_qualified_name() {
        let quots = extract_quotations("`%FStar.List.Tot.length");
        assert_eq!(quots.len(), 1);
        match &quots[0] {
            Quotation::QualifiedName(n) => assert_eq!(n, "FStar.List.Tot.length"),
            other => panic!("Expected QualifiedName, got: {:?}", other),
        }
    }

    #[test]
    fn test_extract_paren_body_from_simple() {
        let body = extract_paren_body_from("smt())");
        assert_eq!(body, Some("smt()".to_string()));
    }

    #[test]
    fn test_extract_paren_body_from_nested() {
        let body = extract_paren_body_from("norm [delta_only [`%on_domain]]; trefl ())");
        assert_eq!(
            body,
            Some("norm [delta_only [`%on_domain]]; trefl ()".to_string())
        );
    }

    #[test]
    fn test_extract_paren_body_from_unmatched() {
        let body = extract_paren_body_from("smt(");
        assert!(body.is_none());
    }

    // =========================================================================
    // KNOWN_FSTAR_ATTRIBUTES and is_known_fstar_attribute tests
    // =========================================================================

    #[test]
    fn test_known_extraction_attributes() {
        assert!(is_known_fstar_attribute("inline_for_extraction"));
        assert!(is_known_fstar_attribute("noextract"));
        assert!(is_known_fstar_attribute("CInline"));
        assert!(is_known_fstar_attribute("CMacro"));
        assert!(is_known_fstar_attribute("CPrologue"));
        assert!(is_known_fstar_attribute("CEpilogue"));
        assert!(is_known_fstar_attribute("CAbstractStruct"));
        assert!(is_known_fstar_attribute("CConst"));
        assert!(is_known_fstar_attribute("CNoInline"));
        assert!(is_known_fstar_attribute("specialize"));
        assert!(is_known_fstar_attribute("noextract_to"));
        assert!(is_known_fstar_attribute("substitute"));
    }

    #[test]
    fn test_known_verification_attributes() {
        assert!(is_known_fstar_attribute("opaque_to_smt"));
        assert!(is_known_fstar_attribute("unfold"));
        assert!(is_known_fstar_attribute("irreducible"));
        assert!(is_known_fstar_attribute("strict_on_arguments"));
    }

    #[test]
    fn test_known_equality_erasure_attributes() {
        assert!(is_known_fstar_attribute("noeq"));
        assert!(is_known_fstar_attribute("unopteq"));
        assert!(is_known_fstar_attribute("erasable"));
    }

    #[test]
    fn test_known_diagnostic_attributes() {
        assert!(is_known_fstar_attribute("deprecated"));
        assert!(is_known_fstar_attribute("expect_failure"));
        assert!(is_known_fstar_attribute("expect_lax_failure"));
        assert!(is_known_fstar_attribute("plugin"));
    }

    #[test]
    fn test_known_doc_and_projector_attributes() {
        assert!(is_known_fstar_attribute("Comment"));
        assert!(is_known_fstar_attribute("no_auto_projectors"));
    }

    #[test]
    fn test_known_tactic_attributes() {
        assert!(is_known_fstar_attribute("va_qattr"));
        assert!(is_known_fstar_attribute("qmodattr"));
        assert!(is_known_fstar_attribute("postprocess_with"));
        assert!(is_known_fstar_attribute("preprocess_with"));
    }

    #[test]
    fn test_unknown_attribute_rejected() {
        assert!(!is_known_fstar_attribute("not_a_real_attribute"));
        assert!(!is_known_fstar_attribute(""));
        assert!(!is_known_fstar_attribute("cinline")); // Case-sensitive: CInline, not cinline
    }

    // =========================================================================
    // FStarAttribute method tests
    // =========================================================================

    #[test]
    fn test_fstar_attribute_is_known() {
        let attr = FStarAttribute {
            style: AttributeStyle::Declaration,
            name: "CInline".to_string(),
            args: None,
        };
        assert!(attr.is_known());

        let unknown = FStarAttribute {
            style: AttributeStyle::Declaration,
            name: "bogus".to_string(),
            args: None,
        };
        assert!(!unknown.is_known());
    }

    #[test]
    fn test_fstar_attribute_is_extraction() {
        let attr = FStarAttribute {
            style: AttributeStyle::Declaration,
            name: "CInline".to_string(),
            args: None,
        };
        assert!(attr.is_extraction_attribute());

        let non_extraction = FStarAttribute {
            style: AttributeStyle::Declaration,
            name: "opaque_to_smt".to_string(),
            args: None,
        };
        assert!(!non_extraction.is_extraction_attribute());
    }

    #[test]
    fn test_fstar_attribute_is_verification() {
        let attr = FStarAttribute {
            style: AttributeStyle::Declaration,
            name: "opaque_to_smt".to_string(),
            args: None,
        };
        assert!(attr.is_verification_attribute());

        let non_verif = FStarAttribute {
            style: AttributeStyle::Declaration,
            name: "CInline".to_string(),
            args: None,
        };
        assert!(!non_verif.is_verification_attribute());
    }

    // =========================================================================
    // Multi-attribute parsing (HACL*/Vale patterns)
    // =========================================================================

    #[test]
    fn test_parse_multi_attr_vale_style() {
        // From Vale.X64.QuickCodes.fsti: [@@va_qattr; "opaque_to_smt"]
        let attrs = parse_attributes(r#"[@@va_qattr; "opaque_to_smt"]"#);
        assert_eq!(attrs.len(), 2);
        assert_eq!(attrs[0].name, "va_qattr");
        assert_eq!(attrs[1].name, "opaque_to_smt");
    }

    #[test]
    fn test_parse_multi_attr_three_attrs() {
        let attrs = parse_attributes("[@@va_qattr; qmodattr; erasable]");
        assert_eq!(attrs.len(), 3);
        assert_eq!(attrs[0].name, "va_qattr");
        assert_eq!(attrs[1].name, "qmodattr");
        assert_eq!(attrs[2].name, "erasable");
    }

    #[test]
    fn test_parse_multi_attr_with_struct() {
        // From EverCrypt.AEAD.fsti: [@@ CAbstractStruct; Comment "..."]
        let attrs = parse_attributes(r#"[@@ CAbstractStruct; Comment "Both encryption and decryption require a state."]"#);
        assert_eq!(attrs.len(), 2);
        assert_eq!(attrs[0].name, "CAbstractStruct");
        assert_eq!(attrs[1].name, "Comment");
        assert!(attrs[1].args.is_some());
    }

    #[test]
    fn test_parse_expect_failure_with_error_code() {
        // [@@expect_failure [19]]
        let attrs = parse_attributes("[@@expect_failure [19]]");
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].name, "expect_failure");
        assert_eq!(attrs[0].args.as_deref(), Some("[19]"));
    }

    #[test]
    fn test_parse_deprecated_with_message() {
        // [@@ deprecated "Use new_fn instead"]
        let attrs = parse_attributes(r#"[@@ deprecated "Use new_fn instead"]"#);
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].name, "deprecated");
        assert!(attrs[0].args.is_some());
    }

    #[test]
    fn test_parse_plugin_attribute() {
        let attrs = parse_attributes("[@@plugin]");
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].name, "plugin");
    }

    #[test]
    fn test_parse_erasable_attribute() {
        let attrs = parse_attributes("[@@erasable]");
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].name, "erasable");
        assert!(attrs[0].is_known());
        assert!(attrs[0].is_verification_attribute());
    }

    #[test]
    fn test_parse_multiple_lines_of_attributes() {
        // Multiple attribute lines before a declaration
        let text = "[@@\"opaque_to_smt\"]\n[@@va_qattr]";
        let attrs = parse_attributes(text);
        assert_eq!(attrs.len(), 2);
        assert_eq!(attrs[0].name, "opaque_to_smt");
        assert_eq!(attrs[1].name, "va_qattr");
    }

    #[test]
    fn test_parse_all_bracket_styles_multi() {
        // Old-style with multi
        let attrs = parse_attributes("[@ CInline; CMacro]");
        assert_eq!(attrs.len(), 2);
        assert_eq!(attrs[0].style, AttributeStyle::OldStyle);
        assert_eq!(attrs[1].style, AttributeStyle::OldStyle);

        // Binder style with multi
        let attrs = parse_attributes("[@@@ strictly_positive; unused]");
        assert_eq!(attrs.len(), 2);
        assert_eq!(attrs[0].style, AttributeStyle::Binder);
    }

    #[test]
    fn test_parse_inline_for_extraction_as_attribute() {
        // inline_for_extraction can appear as an attribute
        let attrs = parse_attributes("[@@inline_for_extraction]");
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].name, "inline_for_extraction");
        assert!(attrs[0].is_known());
        assert!(attrs[0].is_extraction_attribute());
    }

    // =========================================================================
    // Low*/LowStar parser tests
    // =========================================================================

    #[test]
    fn test_machine_int_type_parsing() {
        assert_eq!(MachineIntType::parse("uint8"), Some(MachineIntType::U8));
        assert_eq!(MachineIntType::parse("uint32"), Some(MachineIntType::U32));
        assert_eq!(MachineIntType::parse("uint64"), Some(MachineIntType::U64));
        assert_eq!(MachineIntType::parse("uint128"), Some(MachineIntType::U128));
        assert_eq!(MachineIntType::parse("size_t"), Some(MachineIntType::SizeT));
        assert_eq!(MachineIntType::parse("UInt32.t"), Some(MachineIntType::U32));
        assert_eq!(MachineIntType::parse("garbage"), None);
    }

    #[test]
    fn test_machine_int_type_properties() {
        assert_eq!(MachineIntType::U8.bit_width(), 8);
        assert_eq!(MachineIntType::U32.bit_width(), 32);
        assert_eq!(MachineIntType::U64.bit_width(), 64);
        assert!(MachineIntType::SizeT.is_public());
        assert!(!MachineIntType::U64.is_public());
        assert!(!MachineIntType::U8.is_public());
    }

    #[test]
    fn test_is_lowstar_module_with_hyperstack() {
        let content = "module Test\n\nopen FStar.HyperStack\nopen FStar.HyperStack.ST\n";
        assert!(is_lowstar_module(content));
    }

    #[test]
    fn test_is_lowstar_module_with_lib_buffer() {
        let content = "module Test\n\nopen Lib.Buffer\nopen Lib.IntTypes\n";
        assert!(is_lowstar_module(content));
    }

    #[test]
    fn test_is_lowstar_module_pure_spec() {
        let content = "module Spec.Test\n\nopen FStar.Seq\nopen FStar.Math.Lemmas\n";
        assert!(!is_lowstar_module(content));
    }

    #[test]
    fn test_extract_module_aliases() {
        let content = r#"module Test

open FStar.HyperStack.All
module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
"#;
        let aliases = extract_module_aliases(content);
        assert_eq!(aliases.get("ST"), Some(&"FStar.HyperStack.ST".to_string()));
        assert_eq!(aliases.get("LSeq"), Some(&"Lib.Sequence".to_string()));
        assert_eq!(aliases.get("BSeq"), Some(&"Lib.ByteSequence".to_string()));
    }

    #[test]
    fn test_extract_module_aliases_empty() {
        let content = "module Test\n\nopen FStar.Seq\n";
        let aliases = extract_module_aliases(content);
        assert!(aliases.is_empty());
    }

    #[test]
    fn test_extract_module_aliases_skip_comments() {
        let content = r#"module Test
// module Commented = Not.Real
(* module AlsoCommented = Not.Real *)
module ST = FStar.HyperStack.ST
"#;
        let aliases = extract_module_aliases(content);
        assert_eq!(aliases.len(), 1);
        assert_eq!(aliases.get("ST"), Some(&"FStar.HyperStack.ST".to_string()));
    }

    #[test]
    fn test_effect_sig_lowstar_stack() {
        let stack_sig = EffectSignature {
            effect_name: "Stack".to_string(),
            has_requires: true,
            has_ensures: true,
            has_decreases: false,
            has_modifies: true,
            effect_line: 1,
            sub_effect_src: None,
            sub_effect_dst: None,
            base_effect: None,
            combinators: Vec::new(),
        };
        assert!(stack_sig.is_lowstar_stack_effect());
        assert!(stack_sig.is_lowstar_effect());
    }

    #[test]
    fn test_effect_sig_lowstar_st() {
        let st_sig = EffectSignature {
            effect_name: "ST".to_string(),
            has_requires: true,
            has_ensures: true,
            has_decreases: false,
            has_modifies: true,
            effect_line: 1,
            sub_effect_src: None,
            sub_effect_dst: None,
            base_effect: None,
            combinators: Vec::new(),
        };
        assert!(!st_sig.is_lowstar_stack_effect()); // ST is not Stack
        assert!(st_sig.is_lowstar_effect()); // But it IS a Low* effect
    }

    #[test]
    fn test_effect_sig_lemma_not_lowstar() {
        let lemma_sig = EffectSignature {
            effect_name: "Lemma".to_string(),
            has_requires: false,
            has_ensures: true,
            has_decreases: false,
            has_modifies: false,
            effect_line: 1,
            sub_effect_src: None,
            sub_effect_dst: None,
            base_effect: None,
            combinators: Vec::new(),
        };
        assert!(!lemma_sig.is_lowstar_stack_effect());
        assert!(!lemma_sig.is_lowstar_effect());
    }

    #[test]
    fn test_hacl_chacha20poly1305_module_aliases() {
        // Real HACL* imports from Hacl.Impl.Chacha20Poly1305
        let content = r#"module Hacl.Impl.Chacha20Poly1305

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module Spec = Spec.Chacha20Poly1305
module SpecPoly = Spec.Poly1305
module Poly = Hacl.Impl.Poly1305
"#;
        assert!(is_lowstar_module(content));
        let aliases = extract_module_aliases(content);
        assert_eq!(aliases.get("ST"), Some(&"FStar.HyperStack.ST".to_string()));
        assert_eq!(aliases.get("LSeq"), Some(&"Lib.Sequence".to_string()));
        assert_eq!(aliases.get("BSeq"), Some(&"Lib.ByteSequence".to_string()));
        assert_eq!(aliases.get("Spec"), Some(&"Spec.Chacha20Poly1305".to_string()));
        assert_eq!(aliases.get("Poly"), Some(&"Hacl.Impl.Poly1305".to_string()));
    }

    #[test]
    fn test_hacl_curve25519_module_detection() {
        let content = r#"module Hacl.Impl.Curve25519.AddAndDouble

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
"#;
        assert!(is_lowstar_module(content));
    }

    #[test]
    fn test_parse_hacl_stack_effect_sig() {
        let content = r#"module Test

val copy_buffer :
    src:lbuffer uint8 32ul
  -> dst:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h src /\ live h dst /\ disjoint src dst)
  (ensures fun h0 _ h1 ->
    modifies (loc dst) h0 h1)
"#;
        let (_, blocks) = parse_fstar_file(content);
        let val_b = blocks.iter().find(|b| b.block_type == BlockType::Val).unwrap();
        let sig = val_b.effect_signature.as_ref().expect("Should have effect sig");
        assert_eq!(sig.effect_name, "Stack");
        assert!(sig.has_requires);
        assert!(sig.has_ensures);
        assert!(sig.has_modifies);
        assert!(sig.is_lowstar_stack_effect());
        assert!(sig.is_lowstar_effect());
    }

    // =========================================================================
    // Type expression parser tests
    // =========================================================================

    #[test]
    fn test_parse_simple_named_type() {
        let ty = parse_type_expr("nat");
        assert_eq!(ty, FStarType::Named("nat".to_string()));
    }

    #[test]
    fn test_parse_qualified_named_type() {
        let ty = parse_type_expr("FStar.Seq.seq");
        assert_eq!(ty, FStarType::Named("FStar.Seq.seq".to_string()));
    }

    #[test]
    fn test_parse_wildcard_type() {
        let ty = parse_type_expr("_");
        assert_eq!(ty, FStarType::Wild);
    }

    #[test]
    fn test_parse_parenthesized_type() {
        let ty = parse_type_expr("(nat)");
        assert_eq!(ty, FStarType::Paren(Box::new(FStarType::Named("nat".to_string()))));
    }

    #[test]
    fn test_parse_type_application_single() {
        let ty = parse_type_expr("list nat");
        match ty {
            FStarType::App { head, args } => {
                assert_eq!(*head, FStarType::Named("list".to_string()));
                assert_eq!(args.len(), 1);
                assert_eq!(args[0], FStarType::Named("nat".to_string()));
            }
            other => panic!("Expected App, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_type_application_multi_arg() {
        let ty = parse_type_expr("buffer uint8 32ul");
        match ty {
            FStarType::App { head, args } => {
                assert_eq!(*head, FStarType::Named("buffer".to_string()));
                assert_eq!(args.len(), 2);
            }
            other => panic!("Expected App, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_type_application_with_parens() {
        let ty = parse_type_expr("option (int & string)");
        match ty {
            FStarType::App { head, args } => {
                assert_eq!(*head, FStarType::Named("option".to_string()));
                assert_eq!(args.len(), 1);
                // The arg should be a Paren wrapping a Tuple
                match &args[0] {
                    FStarType::Paren(inner) => {
                        assert!(inner.is_tuple());
                    }
                    other => panic!("Expected Paren(Tuple), got {:?}", other),
                }
            }
            other => panic!("Expected App, got {:?}", other),
        }
    }

    // =========================================================================
    // Arrow/function type tests
    // =========================================================================

    #[test]
    fn test_parse_simple_arrow() {
        let ty = parse_type_expr("int -> int");
        match ty {
            FStarType::Arrow { binders, result } => {
                assert_eq!(binders.len(), 1);
                assert_eq!(binders[0].qualifier, BinderQualifier::Explicit);
                assert!(binders[0].name.is_none());
                assert_eq!(*result, FStarType::Named("int".to_string()));
            }
            other => panic!("Expected Arrow, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_multi_arrow() {
        let ty = parse_type_expr("int -> string -> bool");
        match ty {
            FStarType::Arrow { binders, result } => {
                assert_eq!(binders.len(), 2);
                assert_eq!(*result, FStarType::Named("bool".to_string()));
            }
            other => panic!("Expected Arrow, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_dependent_function_type() {
        let ty = parse_type_expr("(x:nat) -> vec x");
        match ty {
            FStarType::Arrow { binders, result: _ } => {
                assert_eq!(binders.len(), 1);
                assert_eq!(binders[0].name.as_deref(), Some("x"));
                assert_eq!(binders[0].qualifier, BinderQualifier::Explicit);
                match &**binders[0].binder_type.as_ref().unwrap() {
                    FStarType::Named(n) => assert_eq!(n, "nat"),
                    other => panic!("Expected Named(nat), got {:?}", other),
                }
            }
            other => panic!("Expected Arrow, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_implicit_binder_hash() {
        let ty = parse_type_expr("#a:Type -> a -> a");
        match ty {
            FStarType::Arrow { binders, .. } => {
                assert_eq!(binders.len(), 2);
                assert_eq!(binders[0].qualifier, BinderQualifier::Implicit);
                assert_eq!(binders[0].name.as_deref(), Some("a"));
            }
            other => panic!("Expected Arrow, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_implicit_binder_parens() {
        let ty = parse_type_expr("(#a:Type) -> a -> a");
        match ty {
            FStarType::Arrow { binders, .. } => {
                assert_eq!(binders.len(), 2);
                assert_eq!(binders[0].qualifier, BinderQualifier::Implicit);
                assert_eq!(binders[0].name.as_deref(), Some("a"));
            }
            other => panic!("Expected Arrow, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_typeclass_binder() {
        let ty = parse_type_expr("{| hashable a |} -> a -> int");
        match ty {
            FStarType::Arrow { binders, .. } => {
                assert_eq!(binders.len(), 2);
                assert_eq!(binders[0].qualifier, BinderQualifier::TypeClassArg);
            }
            other => panic!("Expected Arrow, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_equality_binder() {
        let ty = parse_type_expr("($a:eqtype) -> a -> bool");
        match ty {
            FStarType::Arrow { binders, .. } => {
                assert_eq!(binders.len(), 2);
                assert_eq!(binders[0].qualifier, BinderQualifier::Equality);
                assert_eq!(binders[0].name.as_deref(), Some("a"));
            }
            other => panic!("Expected Arrow, got {:?}", other),
        }
    }

    // =========================================================================
    // Refinement type tests
    // =========================================================================

    #[test]
    fn test_parse_brace_refinement() {
        let ty = parse_type_expr("{x:int | x >= 0}");
        match ty {
            FStarType::Refinement { binder_name, base_type, predicate } => {
                assert_eq!(binder_name, "x");
                assert_eq!(*base_type, FStarType::Named("int".to_string()));
                assert_eq!(predicate, "x >= 0");
            }
            other => panic!("Expected Refinement, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_brace_refinement_complex_pred() {
        let ty = parse_type_expr("{x:nat | x > 0 /\\ x < 100}");
        match ty {
            FStarType::Refinement { binder_name, base_type, predicate } => {
                assert_eq!(binder_name, "x");
                assert_eq!(*base_type, FStarType::Named("nat".to_string()));
                assert!(predicate.contains("/\\"));
            }
            other => panic!("Expected Refinement, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_inline_refinement() {
        let ty = parse_type_expr("x:nat{x > 0}");
        match ty {
            FStarType::Refinement { binder_name, base_type, predicate } => {
                assert_eq!(binder_name, "x");
                assert_eq!(*base_type, FStarType::Named("nat".to_string()));
                assert_eq!(predicate, "x > 0");
            }
            other => panic!("Expected Refinement, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_refinement_in_arrow() {
        let ty = parse_type_expr("(x:nat{x > 0}) -> int");
        match ty {
            FStarType::Arrow { binders, .. } => {
                assert_eq!(binders.len(), 1);
                match binders[0].binder_type.as_deref() {
                    Some(FStarType::Refinement { binder_name, .. }) => {
                        assert_eq!(binder_name, "x");
                    }
                    other => panic!("Expected Refinement binder, got {:?}", other),
                }
            }
            other => panic!("Expected Arrow, got {:?}", other),
        }
    }

    #[test]
    fn test_refinement_is_refinement() {
        let ty = parse_type_expr("{x:int | x > 0}");
        assert!(ty.is_refinement());
    }

    // =========================================================================
    // Universe polymorphism tests
    // =========================================================================

    #[test]
    fn test_parse_type0() {
        let ty = parse_type_expr("Type0");
        assert_eq!(ty, FStarType::Universe { level: "0".to_string() });
    }

    #[test]
    fn test_parse_type1() {
        let ty = parse_type_expr("Type1");
        assert_eq!(ty, FStarType::Universe { level: "1".to_string() });
    }

    #[test]
    fn test_parse_type_bare() {
        let ty = parse_type_expr("Type");
        assert_eq!(ty, FStarType::Universe { level: "0".to_string() });
    }

    #[test]
    fn test_parse_type_universe_var() {
        let ty = parse_type_expr("Type u#a");
        match ty {
            FStarType::Universe { level } => {
                assert_eq!(level, "a");
            }
            other => panic!("Expected Universe, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_type_universe_max() {
        let ty = parse_type_expr("Type u#(max a b)");
        match ty {
            FStarType::Universe { level } => {
                assert_eq!(level, "max a b");
            }
            other => panic!("Expected Universe, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_eqtype() {
        let ty = parse_type_expr("eqtype");
        assert!(ty.is_universe());
    }

    #[test]
    fn test_parse_prop() {
        let ty = parse_type_expr("prop");
        assert!(ty.is_universe());
    }

    // =========================================================================
    // Tuple type tests
    // =========================================================================

    #[test]
    fn test_parse_tuple_pair() {
        let ty = parse_type_expr("int & string");
        match ty {
            FStarType::Tuple { elements } => {
                assert_eq!(elements.len(), 2);
                assert_eq!(elements[0], FStarType::Named("int".to_string()));
                assert_eq!(elements[1], FStarType::Named("string".to_string()));
            }
            other => panic!("Expected Tuple, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_tuple_triple() {
        let ty = parse_type_expr("int & string & bool");
        match ty {
            FStarType::Tuple { elements } => {
                assert_eq!(elements.len(), 3);
            }
            other => panic!("Expected Tuple, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_tuple_not_and_and() {
        // `&&` is logical AND, not a tuple separator
        let ty = parse_type_expr("a && b");
        assert!(!ty.is_tuple(), "a && b should NOT be parsed as tuple");
    }

    // =========================================================================
    // Record type tests
    // =========================================================================

    #[test]
    fn test_parse_record_type() {
        let ty = parse_type_expr("{ x: int; y: int }");
        match ty {
            FStarType::Record { fields } => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "x");
                assert_eq!(fields[0].1, FStarType::Named("int".to_string()));
                assert_eq!(fields[1].0, "y");
            }
            other => panic!("Expected Record, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_record_type_complex_fields() {
        let ty = parse_type_expr("{ name: string; age: nat; data: list int }");
        match ty {
            FStarType::Record { fields } => {
                assert_eq!(fields.len(), 3);
                assert_eq!(fields[0].0, "name");
                assert_eq!(fields[2].0, "data");
            }
            other => panic!("Expected Record, got {:?}", other),
        }
    }

    // =========================================================================
    // Squash and erased type tests
    // =========================================================================

    #[test]
    fn test_parse_squash_type() {
        let ty = parse_type_expr("squash (a == b)");
        match ty {
            FStarType::Squash(inner) => {
                match *inner {
                    FStarType::Paren(_) => {}  // Correct: `(a == b)` is parenthesized
                    other => panic!("Expected Paren inside squash, got {:?}", other),
                }
            }
            other => panic!("Expected Squash, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_erased_type() {
        let ty = parse_type_expr("erased nat");
        match ty {
            FStarType::Erased(inner) => {
                assert_eq!(*inner, FStarType::Named("nat".to_string()));
            }
            other => panic!("Expected Erased, got {:?}", other),
        }
    }

    // =========================================================================
    // Type reference collection tests
    // =========================================================================

    #[test]
    fn test_collect_refs_named() {
        let ty = parse_type_expr("nat");
        let refs = ty.collect_type_references();
        assert!(refs.contains("nat"));
    }

    #[test]
    fn test_collect_refs_arrow() {
        let ty = parse_type_expr("(x:nat) -> list x");
        let refs = ty.collect_type_references();
        assert!(refs.contains("nat"));
        assert!(refs.contains("list"));
    }

    #[test]
    fn test_collect_refs_refinement() {
        let ty = parse_type_expr("{x:int | x > 0}");
        let refs = ty.collect_type_references();
        assert!(refs.contains("int"));
    }

    #[test]
    fn test_collect_refs_tuple() {
        let ty = parse_type_expr("int & string & bool");
        let refs = ty.collect_type_references();
        assert!(refs.contains("int"));
        assert!(refs.contains("string"));
        assert!(refs.contains("bool"));
    }

    #[test]
    fn test_collect_refs_app() {
        let ty = parse_type_expr("option nat");
        let refs = ty.collect_type_references();
        assert!(refs.contains("option"));
        assert!(refs.contains("nat"));
    }

    #[test]
    fn test_base_type_name_simple() {
        let ty = parse_type_expr("nat");
        assert_eq!(ty.base_type_name(), Some("nat"));
    }

    #[test]
    fn test_base_type_name_app() {
        let ty = parse_type_expr("list nat");
        assert_eq!(ty.base_type_name(), Some("list"));
    }

    #[test]
    fn test_has_implicit_binders() {
        let ty = parse_type_expr("#a:Type -> a -> a");
        assert!(ty.has_implicit_binders());

        let ty2 = parse_type_expr("int -> int");
        assert!(!ty2.has_implicit_binders());
    }

    // =========================================================================
    // Constructor parsing tests
    // =========================================================================

    #[test]
    fn test_parse_nullary_constructors() {
        let ctors = parse_constructors("| Red | Green | Blue");
        assert_eq!(ctors.len(), 3);
        assert_eq!(ctors[0].name, "Red");
        assert!(ctors[0].payload.is_none());
        assert_eq!(ctors[1].name, "Green");
        assert_eq!(ctors[2].name, "Blue");
    }

    #[test]
    fn test_parse_of_notation_constructor() {
        let ctors = parse_constructors("| Lit of int | Add of expr");
        assert_eq!(ctors.len(), 2);
        assert_eq!(ctors[0].name, "Lit");
        match &ctors[0].payload {
            Some(ConstructorPayload::OfNotation(ty)) => {
                assert_eq!(**ty, FStarType::Named("int".to_string()));
            }
            other => panic!("Expected OfNotation, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_gadt_constructor() {
        let ctors = parse_constructors("| Leaf : a -> tree a | Node : tree a -> tree a -> tree a");
        assert_eq!(ctors.len(), 2);
        assert_eq!(ctors[0].name, "Leaf");
        match &ctors[0].payload {
            Some(ConstructorPayload::Arbitrary(ty)) => {
                assert!(ty.is_arrow());
            }
            other => panic!("Expected Arbitrary arrow, got {:?}", other),
        }
        assert_eq!(ctors[1].name, "Node");
    }

    #[test]
    fn test_parse_record_constructor() {
        let ctors = parse_constructors("| MkPerson { name: string; age: nat }");
        assert_eq!(ctors.len(), 1);
        assert_eq!(ctors[0].name, "MkPerson");
        match &ctors[0].payload {
            Some(ConstructorPayload::Record { fields, result_type }) => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "name");
                assert!(result_type.is_none());
            }
            other => panic!("Expected Record payload, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_mixed_constructors() {
        let ctors = parse_constructors(
            "| Nil | Cons : a -> list a -> list a"
        );
        assert_eq!(ctors.len(), 2);
        assert_eq!(ctors[0].name, "Nil");
        assert!(ctors[0].payload.is_none());
        assert_eq!(ctors[1].name, "Cons");
        assert!(ctors[1].payload.is_some());
    }

    // =========================================================================
    // Type declaration parsing tests
    // =========================================================================

    #[test]
    fn test_parse_type_decl_abbreviation() {
        let content = "module Test\n\ntype my_nat = nat\n";
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type).unwrap();
        let info = parse_type_declaration(type_block).unwrap();

        assert_eq!(info.name, "my_nat");
        assert_eq!(info.decl_kind, TypeDeclKind::Abbreviation);
        assert_eq!(info.equality, EqualityQualifier::Default);
        assert!(info.params.is_empty());
        assert!(info.kind_annotation.is_none());
        assert!(info.constructors.is_empty());
    }

    #[test]
    fn test_parse_type_decl_noeq() {
        let content = "module Test\n\nnoeq type state = {\n  pc: nat;\n  mem: list int\n}\n";
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type).unwrap();
        let info = parse_type_declaration(type_block).unwrap();

        assert_eq!(info.name, "state");
        assert_eq!(info.equality, EqualityQualifier::Noeq);
        assert_eq!(info.decl_kind, TypeDeclKind::Record);
        assert_eq!(info.record_fields.len(), 2);
        assert_eq!(info.record_fields[0].0, "pc");
    }

    #[test]
    fn test_parse_type_decl_unopteq() {
        let content = "module Test\n\nunopteq type expr = | Lit of int | Add of expr\n";
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type).unwrap();
        let info = parse_type_declaration(type_block).unwrap();

        assert_eq!(info.name, "expr");
        assert_eq!(info.equality, EqualityQualifier::Unopteq);
        assert_eq!(info.decl_kind, TypeDeclKind::Variant);
        assert_eq!(info.constructors.len(), 2);
    }

    #[test]
    fn test_parse_type_decl_with_params() {
        let content = "module Test\n\ntype vector (a:Type) (n:nat) = list a\n";
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type).unwrap();
        let info = parse_type_declaration(type_block).unwrap();

        assert_eq!(info.name, "vector");
        assert_eq!(info.params.len(), 2);
        assert_eq!(info.params[0].name.as_deref(), Some("a"));
        assert_eq!(info.params[1].name.as_deref(), Some("n"));
        assert_eq!(info.decl_kind, TypeDeclKind::Abbreviation);
    }

    #[test]
    fn test_parse_type_decl_abstract() {
        let content = "module Test\n\nval abstract_type : Type\n\ntype abstract_type\n";
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b|
            b.block_type == BlockType::Type && b.names.contains(&"abstract_type".to_string())
        ).unwrap();
        let info = parse_type_declaration(type_block).unwrap();

        assert_eq!(info.name, "abstract_type");
        assert_eq!(info.decl_kind, TypeDeclKind::Abstract);
    }

    #[test]
    fn test_parse_type_decl_mutual_rec() {
        let content = "module Test\n\ntype expr =\n  | Lit of int\n  | Stmt of stmt\nand stmt =\n  | SExpr of expr\n  | SSeq of stmt\n";
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b|
            b.block_type == BlockType::Type && b.names.contains(&"expr".to_string())
        ).unwrap();
        let info = parse_type_declaration(type_block).unwrap();

        assert_eq!(info.name, "expr");
        assert!(info.mutual_rec_partners.contains(&"stmt".to_string()));
    }

    #[test]
    fn test_parse_type_decl_private() {
        let content = "module Test\n\nprivate type helper = nat\n";
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type).unwrap();
        let info = parse_type_declaration(type_block).unwrap();

        assert_eq!(info.name, "helper");
        assert!(info.is_private);
    }

    // =========================================================================
    // Binder parsing tests
    // =========================================================================

    #[test]
    fn test_parse_binder_explicit_named() {
        let b = parse_binder_from_segment("(x:nat)");
        assert_eq!(b.name.as_deref(), Some("x"));
        assert_eq!(b.qualifier, BinderQualifier::Explicit);
    }

    #[test]
    fn test_parse_binder_implicit_hash() {
        let b = parse_binder_from_segment("#a:Type");
        assert_eq!(b.name.as_deref(), Some("a"));
        assert_eq!(b.qualifier, BinderQualifier::Implicit);
    }

    #[test]
    fn test_parse_binder_implicit_parens() {
        let b = parse_binder_from_segment("(#a:Type)");
        assert_eq!(b.name.as_deref(), Some("a"));
        assert_eq!(b.qualifier, BinderQualifier::Implicit);
    }

    #[test]
    fn test_parse_binder_typeclass() {
        let b = parse_binder_from_segment("{| hashable a |}");
        assert_eq!(b.qualifier, BinderQualifier::TypeClassArg);
        assert!(b.name.is_none());
    }

    #[test]
    fn test_parse_binder_equality() {
        let b = parse_binder_from_segment("($a:eqtype)");
        assert_eq!(b.name.as_deref(), Some("a"));
        assert_eq!(b.qualifier, BinderQualifier::Equality);
    }

    #[test]
    fn test_parse_binder_anonymous() {
        let b = parse_binder_from_segment("nat");
        assert!(b.name.is_none());
        assert_eq!(b.qualifier, BinderQualifier::Explicit);
    }

    #[test]
    fn test_parse_binder_with_refinement() {
        let b = parse_binder_from_segment("(x:nat{x > 0})");
        assert_eq!(b.name.as_deref(), Some("x"));
        match b.binder_type.as_deref() {
            Some(FStarType::Refinement { binder_name, predicate, .. }) => {
                assert_eq!(binder_name, "x");
                assert_eq!(predicate, "x > 0");
            }
            other => panic!("Expected Refinement, got {:?}", other),
        }
    }

    // =========================================================================
    // Helper function tests
    // =========================================================================

    #[test]
    fn test_is_fstar_identifier() {
        assert!(is_fstar_identifier("foo"));
        assert!(is_fstar_identifier("_bar"));
        assert!(is_fstar_identifier("expr'"));
        assert!(is_fstar_identifier("my_type'"));
        assert!(!is_fstar_identifier(""));
        assert!(!is_fstar_identifier("123"));
        assert!(!is_fstar_identifier("(x)"));
    }

    #[test]
    fn test_is_fstar_type_identifier() {
        assert!(is_fstar_type_identifier("nat"));
        assert!(is_fstar_type_identifier("FStar.Seq.seq"));
        assert!(is_fstar_type_identifier("A.B.C.d"));
        assert!(!is_fstar_type_identifier(""));
        assert!(!is_fstar_type_identifier("a."));
    }

    #[test]
    fn test_find_matching_close_parens() {
        assert_eq!(find_matching_close("(abc)", 0, b'(', b')'), Some(4));
        assert_eq!(find_matching_close("((a)b)", 0, b'(', b')'), Some(5));
        assert_eq!(find_matching_close("(a", 0, b'(', b')'), None);
    }

    #[test]
    fn test_find_matching_close_braces() {
        assert_eq!(find_matching_close("{x:int | P}", 0, b'{', b'}'), Some(10));
    }

    #[test]
    fn test_find_top_level_colon() {
        assert_eq!(find_top_level_colon("x:nat"), Some(1));
        assert_eq!(find_top_level_colon("(x:nat):Type"), Some(7));
        assert_eq!(find_top_level_colon("x::y"), None); // :: is excluded
        assert_eq!(find_top_level_colon("nat"), None);
    }

    #[test]
    fn test_find_top_level_equals() {
        assert_eq!(find_top_level_equals("type t = nat"), Some(7));
        assert_eq!(find_top_level_equals("a == b"), None); // == excluded
        assert_eq!(find_top_level_equals("a ==> b"), None); // ==> excluded
        assert_eq!(find_top_level_equals("(a = b) = c"), Some(8));
    }

    #[test]
    fn test_split_top_level_arrow() {
        let parts = split_top_level("int -> string -> bool", "->");
        assert_eq!(parts.len(), 3);
        assert_eq!(parts[0].trim(), "int");
        assert_eq!(parts[1].trim(), "string");
        assert_eq!(parts[2].trim(), "bool");
    }

    #[test]
    fn test_split_top_level_arrow_with_parens() {
        let parts = split_top_level("(int -> string) -> bool", "->");
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0].trim(), "(int -> string)");
        assert_eq!(parts[1].trim(), "bool");
    }

    #[test]
    fn test_split_top_level_ampersand() {
        let parts = split_top_level_ampersand("int & string & bool");
        assert_eq!(parts.len(), 3);
    }

    #[test]
    fn test_split_top_level_ampersand_excludes_double() {
        let parts = split_top_level_ampersand("a && b");
        assert_eq!(parts.len(), 1, "a && b should NOT split on &&");
    }

    #[test]
    fn test_split_type_application_tokens() {
        let tokens = split_type_application_tokens("list nat");
        assert_eq!(tokens, vec!["list", "nat"]);
    }

    #[test]
    fn test_split_type_application_with_parens() {
        let tokens = split_type_application_tokens("option (int & string)");
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0], "option");
        assert_eq!(tokens[1], "(int & string)");
    }

    // =========================================================================
    // Integration tests: real-world F* type patterns
    // =========================================================================

    #[test]
    fn test_real_world_hacl_buffer_type() {
        // From HACL*: lbuffer uint8 32ul
        let ty = parse_type_expr("lbuffer uint8 32ul");
        match ty {
            FStarType::App { head, args } => {
                assert_eq!(*head, FStarType::Named("lbuffer".to_string()));
                assert_eq!(args.len(), 2);
            }
            other => panic!("Expected App, got {:?}", other),
        }
    }

    #[test]
    fn test_real_world_lowstar_stack_sig() {
        // From LowStar: Stack unit (requires ...) (ensures ...)
        let ty = parse_type_expr("(src:buffer uint8) -> (dst:buffer uint8) -> Stack unit");
        assert!(ty.is_arrow());
    }

    #[test]
    fn test_real_world_pure_with_refinement() {
        // Common pattern: x:nat{x > 0} -> Pure int
        let ty = parse_type_expr("(x:nat{x > 0}) -> (y:nat{y > x}) -> Pure nat");
        match ty {
            FStarType::Arrow { binders, .. } => {
                assert_eq!(binders.len(), 2);
                // First binder should have refinement
                match binders[0].binder_type.as_deref() {
                    Some(FStarType::Refinement { binder_name, .. }) => {
                        assert_eq!(binder_name, "x");
                    }
                    other => panic!("Expected Refinement, got {:?}", other),
                }
            }
            other => panic!("Expected Arrow, got {:?}", other),
        }
    }

    #[test]
    fn test_real_world_list_type() {
        let ty = parse_type_expr("list (option nat)");
        match ty {
            FStarType::App { head, args } => {
                assert_eq!(*head, FStarType::Named("list".to_string()));
                assert_eq!(args.len(), 1);
            }
            other => panic!("Expected App, got {:?}", other),
        }
    }

    #[test]
    fn test_real_world_dependent_pair() {
        // Dependent tuple: (x:nat & vec nat x)
        let ty = parse_type_expr("nat & bool");
        assert!(ty.is_tuple());
    }

    #[test]
    fn test_real_world_universe_polymorphic_fn() {
        let ty = parse_type_expr("#a:Type u#a -> a -> a");
        match ty {
            FStarType::Arrow { binders, .. } => {
                assert_eq!(binders[0].qualifier, BinderQualifier::Implicit);
            }
            other => panic!("Expected Arrow, got {:?}", other),
        }
    }

    #[test]
    fn test_type_declaration_variant_from_block() {
        let content = r#"module Test

type color =
  | Red
  | Green
  | Blue
"#;
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type).unwrap();
        let info = parse_type_declaration(type_block).unwrap();

        assert_eq!(info.name, "color");
        assert_eq!(info.decl_kind, TypeDeclKind::Variant);
        assert_eq!(info.constructors.len(), 3);
        assert_eq!(info.constructors[0].name, "Red");
        assert_eq!(info.constructors[1].name, "Green");
        assert_eq!(info.constructors[2].name, "Blue");
    }

    #[test]
    fn test_type_declaration_record_from_block() {
        let content = r#"module Test

type point = {
  x: int;
  y: int
}
"#;
        let (_, blocks) = parse_fstar_file(content);
        let type_block = blocks.iter().find(|b| b.block_type == BlockType::Type).unwrap();
        let info = parse_type_declaration(type_block).unwrap();

        assert_eq!(info.name, "point");
        assert_eq!(info.decl_kind, TypeDeclKind::Record);
        assert_eq!(info.record_fields.len(), 2);
    }

    #[test]
    fn test_equality_qualifier_display() {
        // Verify enum values work correctly
        let noeq = EqualityQualifier::Noeq;
        let unopteq = EqualityQualifier::Unopteq;
        let default = EqualityQualifier::Default;
        assert_ne!(noeq, unopteq);
        assert_ne!(noeq, default);
        assert_ne!(unopteq, default);
    }
}
