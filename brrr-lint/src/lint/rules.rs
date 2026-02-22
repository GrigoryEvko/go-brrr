//! Lint rule definitions and diagnostic types.

use std::fmt;
use std::path::{Path, PathBuf};

/// Rule codes for F* linting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RuleCode {
    /// FST001: Type defined in both .fst and .fsti (duplicate definition).
    FST001,
    /// FST002: Interface/implementation consistency (order, missing val, qualifier mismatches).
    FST002,
    /// FST003: Comment syntax issues (unclosed comments, (*), (-*), etc.).
    FST003,
    /// FST004: Unused open statements that can be removed.
    FST004,
    /// FST005: Dead code detection (unused private bindings, unreachable code).
    FST005,
    /// FST006: Naming convention violations (snake_case, CamelCase).
    FST006,
    /// FST007: Z3 complexity patterns that cause slow verification.
    FST007,
    /// FST008: Import optimization (broad imports, heavy modules, circular deps).
    FST008,
    /// FST009: Proof hint suggester (helpful lemmas and techniques).
    FST009,
    /// FST010: Specification extractor (missing .fsti files).
    FST010,
    /// FST011: Effect checker (admit, magic, unsafe_coerce, ML effect).
    FST011,
    /// FST012: Refinement type simplifier (redundant, promotable, unsatisfiable).
    FST012,
    /// FST013: Documentation checker (missing docs on public declarations).
    FST013,
    /// FST014: Test generator (suggests test cases from type signatures).
    FST014,
    /// FST015: Module dependency analysis (self-deps, too many deps).
    FST015,
    /// FST016: Verification performance profiler (high fuel/ifuel/rlimit, etc.).
    FST016,
    /// FST017: Security checker for cryptographic code.
    FST017,
    /// FST018: LowStar buffer safety checker.
    FST018,
    /// FST019: LowStar verification performance checker.
    FST019,
    /// FST020: `(f: a -> b)` in val parses as `(f:a) -> b` — wrap in parens.
    FST020,
    /// FST021: F* reserved keyword used as identifier (e.g., `total`, `effect`).
    FST021,
    /// FST022: Record with function/abstract fields missing `noeq` qualifier.
    FST022,
    /// FST023: Unguarded `forall` in ensures without SMTPat — may cause Z3 divergence.
    FST023,
    /// FST024: `decreases` clause references name not bound in function parameters.
    FST024,
    /// FST025: `assume type` vs `assume val` confusion — different semantics.
    FST025,
    /// FST026: `reveal` used in Tot context — needs GTot (ghost).
    FST026,
    /// FST027: `*` operator used without `open FStar.Mul` — `*` means tuple type by default.
    FST027,
    /// FST028: Pattern match on implicit argument without `strict_on_arguments`.
    FST028,
    /// FST029: `{:pattern (f x)\/(g x)}` is disjunctive SMT trigger, not logical or.
    FST029,
    /// FST030: Direct function equality — use `feq`/`on_domain` from FunctionalExtensionality.
    FST030,
    /// FST031: `opaque_to_smt` definition used without `reveal_opaque`.
    FST031,
    /// FST032: Universe annotation consistency hint.
    FST032,
    /// FST033: Suggest tactic (simp, linarith, norm_num) where SMT is overkill.
    FST033,
    /// FST034: Equality lemma suitable for `[@@simp]` attribute.
    FST034,
    /// FST035: `[@@simp_comm]` lemma needs argument ordering guard.
    FST035,
    /// FST036: Suggest `$f` binder for lemma-taking function parameters.
    FST036,
    /// FST037: Tot vs GTot mismatch in higher-order erased positions.
    FST037,
    /// FST038: Suggest `introduce forall ... with` for universals/implications.
    FST038,
    /// FST039: Simple type alias missing `unfold` qualifier.
    FST039,
    /// FST040: Attribute target mismatch — `@@@` (val-level) vs `@@` (term-level).
    FST040,
    /// FST041: Suppression — `requires True` is intentional, not redundant.
    FST041,
    /// FST042: `Lemma post` vs `Lemma (ensures post)` ambiguity.
    FST042,
    /// FST043: Tick-variable `'a` vs explicit `#a` implicit consistency.
    FST043,
    /// FST044: `let rec` without `decreases` for non-structural recursion.
    FST044,
    /// FST045: Suggest `unopteq` when `noeq` used on record without function fields.
    FST045,
    /// FST046: Suggest `[@@ erasable]` for proof-only types.
    FST046,
    /// FST047: `Prims.sum` (constructive) vs `\/` (propositional) disjunction mismatch.
    FST047,
    /// FST048: Complex tactic missing `[@@plugin]` attribute.
    FST048,
    /// FST049: `[@@auto]` classification — suggest `auto_safe` or `auto_unsafe`.
    FST049,
    /// FST050: Suggest `give_proof`/`get_proof` for squash↔refinement bridge.
    FST050,
    /// FST051: Refined type alias missing `[@@do_not_unrefine]` attribute.
    FST051,
}

impl RuleCode {
    /// Parse a rule code from string (e.g., "FST001").
    pub fn parse_code(s: &str) -> Option<Self> {
        match s.to_uppercase().as_str() {
            "FST001" => Some(RuleCode::FST001),
            "FST002" => Some(RuleCode::FST002),
            "FST003" => Some(RuleCode::FST003),
            "FST004" => Some(RuleCode::FST004),
            "FST005" => Some(RuleCode::FST005),
            "FST006" => Some(RuleCode::FST006),
            "FST007" => Some(RuleCode::FST007),
            "FST008" => Some(RuleCode::FST008),
            "FST009" => Some(RuleCode::FST009),
            "FST010" => Some(RuleCode::FST010),
            "FST011" => Some(RuleCode::FST011),
            "FST012" => Some(RuleCode::FST012),
            "FST013" => Some(RuleCode::FST013),
            "FST014" => Some(RuleCode::FST014),
            "FST015" => Some(RuleCode::FST015),
            "FST016" => Some(RuleCode::FST016),
            "FST017" => Some(RuleCode::FST017),
            "FST018" => Some(RuleCode::FST018),
            "FST019" => Some(RuleCode::FST019),
            "FST020" => Some(RuleCode::FST020),
            "FST021" => Some(RuleCode::FST021),
            "FST022" => Some(RuleCode::FST022),
            "FST023" => Some(RuleCode::FST023),
            "FST024" => Some(RuleCode::FST024),
            "FST025" => Some(RuleCode::FST025),
            "FST026" => Some(RuleCode::FST026),
            "FST027" => Some(RuleCode::FST027),
            "FST028" => Some(RuleCode::FST028),
            "FST029" => Some(RuleCode::FST029),
            "FST030" => Some(RuleCode::FST030),
            "FST031" => Some(RuleCode::FST031),
            "FST032" => Some(RuleCode::FST032),
            "FST033" => Some(RuleCode::FST033),
            "FST034" => Some(RuleCode::FST034),
            "FST035" => Some(RuleCode::FST035),
            "FST036" => Some(RuleCode::FST036),
            "FST037" => Some(RuleCode::FST037),
            "FST038" => Some(RuleCode::FST038),
            "FST039" => Some(RuleCode::FST039),
            "FST040" => Some(RuleCode::FST040),
            "FST041" => Some(RuleCode::FST041),
            "FST042" => Some(RuleCode::FST042),
            "FST043" => Some(RuleCode::FST043),
            "FST044" => Some(RuleCode::FST044),
            "FST045" => Some(RuleCode::FST045),
            "FST046" => Some(RuleCode::FST046),
            "FST047" => Some(RuleCode::FST047),
            "FST048" => Some(RuleCode::FST048),
            "FST049" => Some(RuleCode::FST049),
            "FST050" => Some(RuleCode::FST050),
            "FST051" => Some(RuleCode::FST051),
            _ => None,
        }
    }

    /// All available rule codes.
    pub fn all() -> &'static [RuleCode] {
        &[
            RuleCode::FST001,
            RuleCode::FST002,
            RuleCode::FST003,
            RuleCode::FST004,
            RuleCode::FST005,
            RuleCode::FST006,
            RuleCode::FST007,
            RuleCode::FST008,
            RuleCode::FST009,
            RuleCode::FST010,
            RuleCode::FST011,
            RuleCode::FST012,
            RuleCode::FST013,
            RuleCode::FST014,
            RuleCode::FST015,
            RuleCode::FST016,
            RuleCode::FST017,
            RuleCode::FST018,
            RuleCode::FST019,
            RuleCode::FST020,
            RuleCode::FST021,
            RuleCode::FST022,
            RuleCode::FST023,
            RuleCode::FST024,
            RuleCode::FST025,
            RuleCode::FST026,
            RuleCode::FST027,
            RuleCode::FST028,
            RuleCode::FST029,
            RuleCode::FST030,
            RuleCode::FST031,
            RuleCode::FST032,
            RuleCode::FST033,
            RuleCode::FST034,
            RuleCode::FST035,
            RuleCode::FST036,
            RuleCode::FST037,
            RuleCode::FST038,
            RuleCode::FST039,
            RuleCode::FST040,
            RuleCode::FST041,
            RuleCode::FST042,
            RuleCode::FST043,
            RuleCode::FST044,
            RuleCode::FST045,
            RuleCode::FST046,
            RuleCode::FST047,
            RuleCode::FST048,
            RuleCode::FST049,
            RuleCode::FST050,
            RuleCode::FST051,
        ]
    }

    /// Whether this rule can produce automatic fixes.
    pub fn is_fixable(&self) -> bool {
        matches!(
            self,
            RuleCode::FST001
                | RuleCode::FST002
                | RuleCode::FST004
                | RuleCode::FST005
                | RuleCode::FST010
                | RuleCode::FST012
                | RuleCode::FST013
                | RuleCode::FST020
                | RuleCode::FST022
                | RuleCode::FST027
                | RuleCode::FST039
                | RuleCode::FST045
        )
    }

    /// Short name for the rule.
    pub fn name(&self) -> &'static str {
        match self {
            RuleCode::FST001 => "duplicate-types",
            RuleCode::FST002 => "interface-consistency",
            RuleCode::FST003 => "comment-syntax",
            RuleCode::FST004 => "unused-opens",
            RuleCode::FST005 => "dead-code",
            RuleCode::FST006 => "naming-conventions",
            RuleCode::FST007 => "z3-complexity",
            RuleCode::FST008 => "import-optimizer",
            RuleCode::FST009 => "proof-hints",
            RuleCode::FST010 => "spec-extractor",
            RuleCode::FST011 => "effect-checker",
            RuleCode::FST012 => "refinement-simplifier",
            RuleCode::FST013 => "doc-checker",
            RuleCode::FST014 => "test-generator",
            RuleCode::FST015 => "module-deps",
            RuleCode::FST016 => "perf-profiler",
            RuleCode::FST017 => "security",
            RuleCode::FST018 => "lowstar-buffer",
            RuleCode::FST019 => "lowstar-perf",
            RuleCode::FST020 => "val-binder-arrow",
            RuleCode::FST021 => "keyword-as-identifier",
            RuleCode::FST022 => "missing-noeq",
            RuleCode::FST023 => "unguarded-forall",
            RuleCode::FST024 => "decreases-unbound",
            RuleCode::FST025 => "assume-type-vs-val",
            RuleCode::FST026 => "reveal-in-tot",
            RuleCode::FST027 => "missing-mul-open",
            RuleCode::FST028 => "strict-on-arguments",
            RuleCode::FST029 => "pattern-disjunction",
            RuleCode::FST030 => "function-equality",
            RuleCode::FST031 => "opaque-without-reveal",
            RuleCode::FST032 => "universe-hint",
            RuleCode::FST033 => "tactic-suggestion",
            RuleCode::FST034 => "simp-candidate",
            RuleCode::FST035 => "simp-comm-guard",
            RuleCode::FST036 => "dollar-binder",
            RuleCode::FST037 => "tot-vs-gtot",
            RuleCode::FST038 => "introduce-with",
            RuleCode::FST039 => "unfold-alias",
            RuleCode::FST040 => "attribute-target",
            RuleCode::FST041 => "requires-true-ok",
            RuleCode::FST042 => "lemma-ensures-ambiguity",
            RuleCode::FST043 => "tick-vs-explicit",
            RuleCode::FST044 => "missing-decreases",
            RuleCode::FST045 => "noeq-vs-unopteq",
            RuleCode::FST046 => "erasable-suggestion",
            RuleCode::FST047 => "sum-vs-or",
            RuleCode::FST048 => "missing-plugin",
            RuleCode::FST049 => "auto-classification",
            RuleCode::FST050 => "squash-bridge",
            RuleCode::FST051 => "do-not-unrefine",
        }
    }

    /// Detailed description of what the rule checks.
    pub fn description(&self) -> &'static str {
        match self {
            RuleCode::FST001 => {
                "Detects type definitions that appear in both .fst and .fsti files. \
                 F* only requires type definitions in interface files; duplicating them \
                 in implementation files can cause maintenance issues and confusion."
            }
            RuleCode::FST002 => {
                "Checks .fsti/.fst consistency: declaration order (F* Error 233), \
                 missing val in interface, orphan declarations without implementation, \
                 qualifier mismatches (noeq, inline_for_extraction, noextract), \
                 assume val vs val confusion, implicit argument count differences, \
                 type equality modifier mismatches, and unnecessary friend declarations."
            }
            RuleCode::FST003 => {
                "Detects comment syntax issues including unclosed comments, \
                 premature comment closes, (*) which F* parses as unit value, \
                 and (-*) which is the magic wand operator from separation logic."
            }
            RuleCode::FST004 => {
                "Detects unused open statements that import modules which are never \
                 used in the file. Removing unused opens improves compilation time \
                 and keeps dependencies explicit."
            }
            RuleCode::FST005 => {
                "Detects dead code including unused private bindings, unreachable code \
                 after assert false/admit(), unused function parameters (with autofix), \
                 and unreachable match branches after wildcard patterns."
            }
            RuleCode::FST006 => {
                "Checks F* naming conventions derived from HACL*, FStar/ulib, and EverParse: \
                 modules must be dot-separated CamelCase (Spec.*/Impl.*/Hacl.*/FStar.*), \
                 types/functions must start lowercase (snake_case preferred), \
                 constructors must start uppercase (CamelCase), \
                 effects must be CamelCase, \
                 lemmas should use lemma_* prefix or *_lemma suffix, \
                 operator names (+., *!, |+|) are skipped."
            }
            RuleCode::FST007 => {
                "Detects Z3 complexity patterns: quantifiers without SMTPat triggers, \
                 non-linear arithmetic, deep quantifier nesting, large match expressions, \
                 recursive functions without decreases, and high z3rlimit settings."
            }
            RuleCode::FST008 => {
                "Detects import optimization opportunities: broad imports when selective would \
                 suffice, heavy modules (Tactics, Reflection) that slow verification, \
                 circular imports, and unnecessary transitive imports."
            }
            RuleCode::FST009 => {
                "Suggests helpful proof hints based on code patterns. Detects list append \
                 length properties, modular arithmetic lemmas, pow2 normalization needs, \
                 sequence operation lemmas, and bitwise operation hints."
            }
            RuleCode::FST010 => {
                "Detects .fst files without corresponding .fsti interface files. \
                 Interface files help with encapsulation, separate compilation, \
                 and documentation of public APIs."
            }
            RuleCode::FST011 => {
                "Detects effect-related issues: admit() bypassing verification, magic() producing \
                 arbitrary values, unsafe_coerce bypassing type safety, overly permissive ML effect, \
                 and assume val axioms."
            }
            RuleCode::FST012 => {
                "Simplifies refinement types: detects redundant refinements (nat{x >= 0}), \
                 promotable types (int{x >= 0} -> nat), useless refinements (T{True}), \
                 and unsatisfiable constraints (x > 5 /\\ x < 3)."
            }
            RuleCode::FST013 => {
                "Checks for missing documentation on public val and type declarations. \
                 Skips private declarations, internal names (starting with _), type abbreviations, \
                 and .fst files that have a corresponding .fsti interface."
            }
            RuleCode::FST014 => {
                "Generates test suggestions from type signatures. Analyzes function parameters \
                 for refinement type boundaries, collection edge cases (empty, singleton), \
                 integer bounds (min/max for U32, U64, etc.), and option type coverage."
            }
            RuleCode::FST015 => {
                "Analyzes module dependencies from open/friend/include statements. \
                 Detects self-dependencies and warns when modules have too many dependencies (>15)."
            }
            RuleCode::FST016 => {
                "Verification performance profiler that detects patterns causing slow verification: \
                 high fuel/ifuel settings, high z3rlimit values, --quake/--retry usage indicating \
                 instability, and high assertion density suggesting proof complexity."
            }
            RuleCode::FST017 => {
                "Security checker for cryptographic F* code. Detects hardcoded secrets, \
                 RawIntTypes usage that may break secret independence, and potential \
                 secret-dependent branches that could enable timing side-channel attacks."
            }
            RuleCode::FST018 => {
                "LowStar buffer safety checker for verified C code. Detects unmatched \
                 push_frame/pop_frame pairs, stack allocation outside frame scope, heap \
                 allocation without free, missing liveness predicates, and missing modifies \
                 clauses in Stack/ST effect signatures."
            }
            RuleCode::FST019 => {
                "LowStar verification performance checker. Detects patterns that slow \
                 Low* verification: large modifies clauses with many loc_union operators, \
                 excessive ST.get() heap snapshots, heavy disjointness conjunctions, \
                 excessive assert_norm usage, and missing inline_for_extraction on Low* helpers."
            }
            RuleCode::FST020 => {
                "Detects `(f: a -> b)` in val declarations which F* parses as `(f:a) -> b` \
                 (a parameter named `f` of type `a`, returning `b`). Wrap in double parens: \
                 `(f: (a -> b))` to get the intended function-typed parameter."
            }
            RuleCode::FST021 => {
                "Detects F* reserved keywords used as identifiers: `total`, `effect`, `match`, \
                 `friend`, `include`, `module`, `open`, `private`, `unfold`, `inline`. \
                 These cause cryptic parse errors when used as parameter or binding names."
            }
            RuleCode::FST022 => {
                "Detects records/inductives with function-typed or abstract-typed fields \
                 missing the `noeq` qualifier. Without `noeq`, F* tries to derive decidable \
                 equality which fails on function types, causing Error 76."
            }
            RuleCode::FST023 => {
                "Detects unguarded `forall` quantifiers in ensures/lemma postconditions \
                 without an accompanying SMTPat trigger. Unguarded quantifiers can cause \
                 Z3 to diverge or produce unstable proofs."
            }
            RuleCode::FST024 => {
                "Detects `decreases` clauses that reference names not bound in the \
                 function's parameter list. This silently creates a fresh variable \
                 instead of using the intended parameter."
            }
            RuleCode::FST025 => {
                "Detects confusion between `assume type t` (assumes a type exists) and \
                 `assume val f : t` (assumes a value exists). Using the wrong one can \
                 create unsound axioms or fail to compile."
            }
            RuleCode::FST026 => {
                "Detects `reveal` (from FStar.Ghost) used in a Tot computation context. \
                 `reveal` requires GTot (ghost) context since it unwraps erased values. \
                 Use `reveal` only in Ghost/Lemma contexts or wrap in `Ghost.elim_pure`."
            }
            RuleCode::FST027 => {
                "Detects arithmetic `*` operator used without `open FStar.Mul`. In F*, \
                 `*` defaults to the tuple type constructor (e.g., `int * int` is a pair). \
                 You must `open FStar.Mul` to use `*` as integer multiplication."
            }
            RuleCode::FST028 => {
                "Detects pattern matching on implicit arguments without the `strict_on_arguments` \
                 attribute. Without this, F* may not reduce the match even when the implicit \
                 is resolved, leading to verification failures."
            }
            RuleCode::FST029 => {
                "Detects `{:pattern (f x)\\/(g x)}` in SMT triggers which creates a disjunctive \
                 trigger (two alternative patterns), not a logical OR. This is a common source \
                 of unexpected SMT behavior. Use `\\/` outside patterns for logical disjunction."
            }
            RuleCode::FST030 => {
                "Detects direct equality comparison of functions (`f == g`). Function equality \
                 is undecidable in F*. Use `feq` or `on_domain` from \
                 FStar.FunctionalExtensionality for extensional function equality."
            }
            RuleCode::FST031 => {
                "Detects definitions marked `opaque_to_smt` that are never revealed with \
                 `reveal_opaque`. An opaque definition hidden from Z3 that is never revealed \
                 anywhere is likely an oversight — the SMT solver cannot reason about it."
            }
            RuleCode::FST032 => {
                "Provides hints about universe annotations (`u#a`, `Type u#0`). Detects \
                 inconsistent universe levels in related definitions and suggests explicit \
                 annotations where universe polymorphism might cause unexpected behavior."
            }
            RuleCode::FST033 => {
                "Suggests F* tactics (simp, linarith, norm_num, ring) where direct SMT \
                 is overkill or fragile. Detects arithmetic equalities suited for `norm_num`, \
                 linear inequalities suited for `linarith`, and algebraic identities for `ring`."
            }
            RuleCode::FST034 => {
                "Detects equality lemmas of the form `forall x. f x == g x` or \
                 `f x == expr` that could be annotated with `[@@simp]` to participate in \
                 the simplifier's rewriting engine, reducing manual proof burden."
            }
            RuleCode::FST035 => {
                "Detects `[@@simp_comm]` lemmas (commutativity: `f a b == f b a`) that \
                 lack an argument-ordering guard. Without a guard (e.g., `a <= b`), the \
                 simplifier may loop infinitely rewriting `f a b → f b a → f a b → ...`."
            }
            RuleCode::FST036 => {
                "Suggests using `$f` binder syntax for function parameters that receive \
                 lemmas or proof terms. The `$` binder prevents normalization of the \
                 argument, preserving its structure for the callee."
            }
            RuleCode::FST037 => {
                "Detects Tot vs GTot mismatches in higher-order positions involving erased \
                 types. A function `erased a -> Tot b` cannot call `reveal` (which requires \
                 GTot). Use GTot or restructure to avoid ghost/pure boundary violations."
            }
            RuleCode::FST038 => {
                "Suggests using `introduce forall x. P x with ...` or \
                 `introduce implies P ==> Q with ...` tactic-style proof syntax instead of \
                 manual `forall_intro`/`implies_intro` when proving universals or implications."
            }
            RuleCode::FST039 => {
                "Detects simple type aliases (`let my_type = existing_type`) missing the \
                 `unfold` qualifier. Without `unfold`, F* treats the alias as a new definition \
                 that the normalizer won't automatically expand, causing type mismatches."
            }
            RuleCode::FST040 => {
                "Detects attribute target mismatches: `@@@` (three `@`) applies to the \
                 enclosing val/let declaration, while `@@` (two `@`) applies to the next term. \
                 Using the wrong one silently attaches the attribute to the wrong target."
            }
            RuleCode::FST041 => {
                "Suppression rule: `requires True` is intentional in many F* patterns \
                 (e.g., Stack effect signatures) and should NOT be flagged as redundant. \
                 This rule documents the pattern as deliberate."
            }
            RuleCode::FST042 => {
                "Detects `Lemma post` (without `ensures`) which in F* means `Lemma (requires post) \
                 (ensures True)` — the opposite of what most users intend. Use \
                 `Lemma (ensures post)` to specify the postcondition."
            }
            RuleCode::FST043 => {
                "Detects inconsistent implicit variable syntax: mixing tick-variables (`'a`) \
                 with explicit implicit binders (`#a:Type`). Suggests consistent style within \
                 a module for readability."
            }
            RuleCode::FST044 => {
                "Detects `let rec` definitions without a `decreases` clause where the recursion \
                 is not obviously structural. Non-structural recursion without `decreases` may \
                 fail to verify or require excessive fuel."
            }
            RuleCode::FST045 => {
                "Suggests replacing `noeq` with `unopteq` on records that have no function-typed \
                 fields. `unopteq` still prevents F* from attempting equality derivation but \
                 signals that equality could be opt-in later if needed."
            }
            RuleCode::FST046 => {
                "Suggests adding `[@@ erasable]` attribute to proof-only types that are never \
                 used computationally. Erasable types are removed during extraction, producing \
                 cleaner generated code and catching accidental computational use."
            }
            RuleCode::FST047 => {
                "Detects confusion between `Prims.sum` (constructive disjunction with `Inl`/`Inr`) \
                 and `\\/` (`l_or`, propositional disjunction). Using `sum` in proofs or `\\/` in \
                 computations leads to extraction issues or proof difficulties."
            }
            RuleCode::FST048 => {
                "Detects complex tactic definitions (using `Tac` effect with multiple steps) \
                 missing the `[@@plugin]` attribute. Without `plugin`, tactics run interpreted \
                 rather than compiled, causing significant performance degradation."
            }
            RuleCode::FST049 => {
                "Provides guidance on `[@@auto]` lemma classification. Suggests `auto_safe` for \
                 lemmas that terminate quickly and are always useful, vs `auto_unsafe` for \
                 potentially expensive lemmas that should only fire with explicit opt-in."
            }
            RuleCode::FST050 => {
                "Suggests using `give_proof`/`get_proof` from FStar.Squash when bridging between \
                 squashed propositions (`squash p`) and refinement types (`x:unit{p}`). Manual \
                 coercion between these is error-prone; the Squash module provides safe bridges."
            }
            RuleCode::FST051 => {
                "Detects refined type aliases missing the `[@@do_not_unrefine]` attribute. \
                 Without this, F* may silently drop the refinement when normalizing, losing \
                 the intended invariant. Example: `type pos = x:int{x > 0}` needs the attribute."
            }
        }
    }

    /// Return the string representation (e.g., `"FST001"`).
    pub fn as_str(&self) -> &'static str {
        match self {
            RuleCode::FST001 => "FST001",
            RuleCode::FST002 => "FST002",
            RuleCode::FST003 => "FST003",
            RuleCode::FST004 => "FST004",
            RuleCode::FST005 => "FST005",
            RuleCode::FST006 => "FST006",
            RuleCode::FST007 => "FST007",
            RuleCode::FST008 => "FST008",
            RuleCode::FST009 => "FST009",
            RuleCode::FST010 => "FST010",
            RuleCode::FST011 => "FST011",
            RuleCode::FST012 => "FST012",
            RuleCode::FST013 => "FST013",
            RuleCode::FST014 => "FST014",
            RuleCode::FST015 => "FST015",
            RuleCode::FST016 => "FST016",
            RuleCode::FST017 => "FST017",
            RuleCode::FST018 => "FST018",
            RuleCode::FST019 => "FST019",
            RuleCode::FST020 => "FST020",
            RuleCode::FST021 => "FST021",
            RuleCode::FST022 => "FST022",
            RuleCode::FST023 => "FST023",
            RuleCode::FST024 => "FST024",
            RuleCode::FST025 => "FST025",
            RuleCode::FST026 => "FST026",
            RuleCode::FST027 => "FST027",
            RuleCode::FST028 => "FST028",
            RuleCode::FST029 => "FST029",
            RuleCode::FST030 => "FST030",
            RuleCode::FST031 => "FST031",
            RuleCode::FST032 => "FST032",
            RuleCode::FST033 => "FST033",
            RuleCode::FST034 => "FST034",
            RuleCode::FST035 => "FST035",
            RuleCode::FST036 => "FST036",
            RuleCode::FST037 => "FST037",
            RuleCode::FST038 => "FST038",
            RuleCode::FST039 => "FST039",
            RuleCode::FST040 => "FST040",
            RuleCode::FST041 => "FST041",
            RuleCode::FST042 => "FST042",
            RuleCode::FST043 => "FST043",
            RuleCode::FST044 => "FST044",
            RuleCode::FST045 => "FST045",
            RuleCode::FST046 => "FST046",
            RuleCode::FST047 => "FST047",
            RuleCode::FST048 => "FST048",
            RuleCode::FST049 => "FST049",
            RuleCode::FST050 => "FST050",
            RuleCode::FST051 => "FST051",
        }
    }
}

impl fmt::Display for RuleCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuleCode::FST001 => write!(f, "FST001"),
            RuleCode::FST002 => write!(f, "FST002"),
            RuleCode::FST003 => write!(f, "FST003"),
            RuleCode::FST004 => write!(f, "FST004"),
            RuleCode::FST005 => write!(f, "FST005"),
            RuleCode::FST006 => write!(f, "FST006"),
            RuleCode::FST007 => write!(f, "FST007"),
            RuleCode::FST008 => write!(f, "FST008"),
            RuleCode::FST009 => write!(f, "FST009"),
            RuleCode::FST010 => write!(f, "FST010"),
            RuleCode::FST011 => write!(f, "FST011"),
            RuleCode::FST012 => write!(f, "FST012"),
            RuleCode::FST013 => write!(f, "FST013"),
            RuleCode::FST014 => write!(f, "FST014"),
            RuleCode::FST015 => write!(f, "FST015"),
            RuleCode::FST016 => write!(f, "FST016"),
            RuleCode::FST017 => write!(f, "FST017"),
            RuleCode::FST018 => write!(f, "FST018"),
            RuleCode::FST019 => write!(f, "FST019"),
            RuleCode::FST020 => write!(f, "FST020"),
            RuleCode::FST021 => write!(f, "FST021"),
            RuleCode::FST022 => write!(f, "FST022"),
            RuleCode::FST023 => write!(f, "FST023"),
            RuleCode::FST024 => write!(f, "FST024"),
            RuleCode::FST025 => write!(f, "FST025"),
            RuleCode::FST026 => write!(f, "FST026"),
            RuleCode::FST027 => write!(f, "FST027"),
            RuleCode::FST028 => write!(f, "FST028"),
            RuleCode::FST029 => write!(f, "FST029"),
            RuleCode::FST030 => write!(f, "FST030"),
            RuleCode::FST031 => write!(f, "FST031"),
            RuleCode::FST032 => write!(f, "FST032"),
            RuleCode::FST033 => write!(f, "FST033"),
            RuleCode::FST034 => write!(f, "FST034"),
            RuleCode::FST035 => write!(f, "FST035"),
            RuleCode::FST036 => write!(f, "FST036"),
            RuleCode::FST037 => write!(f, "FST037"),
            RuleCode::FST038 => write!(f, "FST038"),
            RuleCode::FST039 => write!(f, "FST039"),
            RuleCode::FST040 => write!(f, "FST040"),
            RuleCode::FST041 => write!(f, "FST041"),
            RuleCode::FST042 => write!(f, "FST042"),
            RuleCode::FST043 => write!(f, "FST043"),
            RuleCode::FST044 => write!(f, "FST044"),
            RuleCode::FST045 => write!(f, "FST045"),
            RuleCode::FST046 => write!(f, "FST046"),
            RuleCode::FST047 => write!(f, "FST047"),
            RuleCode::FST048 => write!(f, "FST048"),
            RuleCode::FST049 => write!(f, "FST049"),
            RuleCode::FST050 => write!(f, "FST050"),
            RuleCode::FST051 => write!(f, "FST051"),
        }
    }
}

/// Severity level for diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    Error,
    Warning,
    Info,
    Hint,
}

impl fmt::Display for DiagnosticSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DiagnosticSeverity::Error => write!(f, "error"),
            DiagnosticSeverity::Warning => write!(f, "warning"),
            DiagnosticSeverity::Info => write!(f, "info"),
            DiagnosticSeverity::Hint => write!(f, "hint"),
        }
    }
}

/// A text range in a file (1-indexed lines and columns).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Range {
    pub start_line: usize,
    pub start_col: usize,
    pub end_line: usize,
    pub end_col: usize,
}

impl Range {
    /// Create a new range with validation.
    ///
    /// All values must be >= 1 (1-indexed). End must be >= start.
    /// When start_line == end_line, end_col must be >= start_col.
    pub fn new(start_line: usize, start_col: usize, end_line: usize, end_col: usize) -> Self {
        assert!(start_line >= 1, "start_line must be >= 1 (1-indexed), got {}", start_line);
        assert!(start_col >= 1, "start_col must be >= 1 (1-indexed), got {}", start_col);
        assert!(end_line >= 1, "end_line must be >= 1 (1-indexed), got {}", end_line);
        assert!(end_col >= 1, "end_col must be >= 1 (1-indexed), got {}", end_col);
        assert!(
            end_line >= start_line,
            "end_line ({}) must be >= start_line ({})",
            end_line, start_line
        );
        assert!(
            end_line > start_line || end_col >= start_col,
            "when start_line == end_line, end_col ({}) must be >= start_col ({})",
            end_col, start_col
        );
        Self {
            start_line,
            start_col,
            end_line,
            end_col,
        }
    }

    /// Create a range for a single point.
    pub fn point(line: usize, col: usize) -> Self {
        assert!(line >= 1, "line must be >= 1 (1-indexed), got {}", line);
        assert!(col >= 1, "col must be >= 1 (1-indexed), got {}", col);
        Self {
            start_line: line,
            start_col: col,
            end_line: line,
            end_col: col,
        }
    }
}

/// Confidence level for a fix.
/// Higher confidence means the fix is more likely to be correct and safe.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum FixConfidence {
    /// Low confidence - the analysis might have missed usages.
    /// Fix should NOT be auto-applied. Requires manual review.
    Low = 0,
    /// Medium confidence - likely correct but some uncertainty remains.
    /// Fix can be suggested but user should verify.
    #[default]
    Medium = 50,
    /// High confidence - analysis is comprehensive and fix is safe.
    /// Fix can be auto-applied with --fix flag.
    High = 100,
}

impl FixConfidence {
    /// Convert to f64 confidence score (0.0 to 1.0).
    pub fn as_f64(&self) -> f64 {
        match self {
            FixConfidence::Low => 0.25,
            FixConfidence::Medium => 0.5,
            FixConfidence::High => 1.0,
        }
    }

    /// Create from f64 confidence score (0.0 to 1.0).
    pub fn from_f64(score: f64) -> Self {
        if score >= 0.75 {
            FixConfidence::High
        } else if score >= 0.4 {
            FixConfidence::Medium
        } else {
            FixConfidence::Low
        }
    }
}


impl fmt::Display for FixConfidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FixConfidence::Low => write!(f, "low"),
            FixConfidence::Medium => write!(f, "medium"),
            FixConfidence::High => write!(f, "high"),
        }
    }
}

/// Safety level for fix application.
///
/// This determines how the fix is presented and applied:
/// - Safe: Can be auto-applied with `--apply`
/// - Caution: Shows warning, applies with `--apply` but warns
/// - Unsafe: Requires `--force` in addition to `--apply`
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum FixSafetyLevel {
    /// SAFE: Can auto-apply with --apply flag.
    /// The fix is guaranteed to preserve semantics and cannot break working code.
    /// Examples:
    /// - Removing exactly-matching duplicate type definitions
    /// - Removing redundant refinements (nat{x >= 0} -> nat)
    /// - Adding documentation comments
    Safe,

    /// CAUTION: Show warning, apply with --apply but display caution.
    /// The fix is likely correct but has some risk:
    /// - Reordering declarations (might affect later code)
    /// - Creating new files (spec extraction)
    /// - Type changes that are semantically equivalent
    #[default]
    Caution,

    /// UNSAFE: Requires --force in addition to --apply.
    /// The fix has significant risk and requires explicit confirmation:
    /// - Removing code that might be used (dead code detection)
    /// - Complex refactoring with potential side effects
    /// - Changes in files with circular dependencies
    Unsafe,
}

impl fmt::Display for FixSafetyLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FixSafetyLevel::Safe => write!(f, "safe"),
            FixSafetyLevel::Caution => write!(f, "caution"),
            FixSafetyLevel::Unsafe => write!(f, "unsafe"),
        }
    }
}

/// Type alias preserving dead-code-specific semantics while using the unified safety level.
///
/// CRITICAL: Dead code removal is HIGH RISK in F* because:
/// - "Unused" bindings may be used via SMTPat (auto-triggered by solver)
/// - Private bindings may be used by `friend` modules
/// - Ghost bindings exist for proofs only
/// - Lemmas prove properties without explicit call sites
pub type DeadCodeSafetyLevel = FixSafetyLevel;

/// A suggested fix for a diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fix {
    /// Description of what the fix does.
    pub message: String,
    /// The edits to apply (may span multiple ranges).
    pub edits: Vec<Edit>,
    /// Confidence level for this fix.
    /// Affects whether the fix can be auto-applied.
    pub confidence: FixConfidence,
    /// Reason if the fix is marked unsafe.
    pub unsafe_reason: Option<String>,
    /// Safety level for the fix (Safe, Caution, Unsafe).
    /// Determines how the fix is presented and what flags are needed to apply it.
    /// Safety is derived from this single field via `is_safe()`.
    pub safety_level: FixSafetyLevel,
    /// Whether this fix can be easily reversed.
    /// True for additive changes (adding comments, creating files).
    /// False for destructive changes (removing code, reordering).
    pub reversible: bool,
    /// Whether this fix requires human review before application.
    /// True for changes that might affect semantics or require context.
    pub requires_review: bool,
}

impl Fix {
    /// Create a new fix with default medium confidence and Safe level.
    pub fn new(message: impl Into<String>, edits: Vec<Edit>) -> Self {
        Self {
            message: message.into(),
            edits,
            confidence: FixConfidence::Medium,
            unsafe_reason: None,
            safety_level: FixSafetyLevel::Safe,
            reversible: true,
            requires_review: false,
        }
    }

    /// Create a fix marked as unsafe with a reason.
    pub fn unsafe_fix(
        message: impl Into<String>,
        edits: Vec<Edit>,
        confidence: FixConfidence,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            message: message.into(),
            edits,
            confidence,
            unsafe_reason: Some(reason.into()),
            safety_level: FixSafetyLevel::Unsafe,
            reversible: false,
            requires_review: true,
        }
    }

    /// Create a high-confidence safe fix.
    pub fn safe(message: impl Into<String>, edits: Vec<Edit>) -> Self {
        Self {
            message: message.into(),
            edits,
            confidence: FixConfidence::High,
            unsafe_reason: None,
            safety_level: FixSafetyLevel::Safe,
            reversible: true,
            requires_review: false,
        }
    }

    /// Create a fix with Caution safety level.
    pub fn caution(message: impl Into<String>, edits: Vec<Edit>) -> Self {
        Self {
            message: message.into(),
            edits,
            confidence: FixConfidence::Medium,
            unsafe_reason: None,
            safety_level: FixSafetyLevel::Caution,
            reversible: true,
            requires_review: true,
        }
    }

    /// Whether the fix is at the Safe safety level.
    ///
    /// Derived from `safety_level` -- a fix is safe only when
    /// `safety_level == FixSafetyLevel::Safe`.
    pub fn is_safe(&self) -> bool {
        self.safety_level == FixSafetyLevel::Safe
    }

    /// Set the confidence level.
    pub fn with_confidence(mut self, confidence: FixConfidence) -> Self {
        self.confidence = confidence;
        self
    }

    /// Set the safety level.
    pub fn with_safety_level(mut self, level: FixSafetyLevel) -> Self {
        self.safety_level = level;
        self
    }

    /// Mark as reversible or not.
    pub fn with_reversible(mut self, reversible: bool) -> Self {
        self.reversible = reversible;
        self
    }

    /// Mark as requiring review or not.
    pub fn with_requires_review(mut self, requires_review: bool) -> Self {
        self.requires_review = requires_review;
        self
    }

    /// Mark as unsafe with a reason.
    pub fn mark_unsafe(mut self, reason: impl Into<String>) -> Self {
        self.unsafe_reason = Some(reason.into());
        self.safety_level = FixSafetyLevel::Unsafe;
        self.requires_review = true;
        self
    }

    /// Check if this fix should be auto-applied.
    /// Only high-confidence safe fixes can be auto-applied.
    pub fn can_auto_apply(&self) -> bool {
        self.is_safe() && self.confidence == FixConfidence::High
    }

    /// Check if this fix can be applied with just --apply.
    /// Safe and Caution fixes can be applied, Unsafe requires --force.
    pub fn can_apply_without_force(&self) -> bool {
        self.safety_level != FixSafetyLevel::Unsafe
    }

    /// Check if this fix requires the --force flag.
    pub fn requires_force(&self) -> bool {
        self.safety_level == FixSafetyLevel::Unsafe
    }
}

/// A single text edit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edit {
    /// File to edit.
    pub file: PathBuf,
    /// Range to replace (or point to insert at).
    pub range: Range,
    /// New text to insert (empty string for deletion).
    pub new_text: String,
}

/// A lint diagnostic.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// The rule that produced this diagnostic.
    pub rule: RuleCode,
    /// Severity level.
    pub severity: DiagnosticSeverity,
    /// File path.
    pub file: PathBuf,
    /// Location in the file.
    pub range: Range,
    /// Human-readable message.
    pub message: String,
    /// Optional fix suggestion.
    pub fix: Option<Fix>,
}

/// A lint rule trait.
pub trait Rule: Send + Sync {
    /// The rule code.
    fn code(&self) -> RuleCode;

    /// Check a single file and return diagnostics.
    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic>;

    /// Check a file pair (.fst and .fsti).
    fn check_pair(
        &self,
        _fst_file: &Path,
        _fst_content: &str,
        _fsti_file: &Path,
        _fsti_content: &str,
    ) -> Vec<Diagnostic> {
        // Default: no pair checking
        vec![]
    }

    /// Whether this rule requires pair checking.
    fn requires_pair(&self) -> bool {
        false
    }
}

/// Print all available rules in a formatted table.
pub fn print_rules() {
    println!("Available F* lint rules:\n");
    println!(
        "{:<8} {:<20} {:<8} Description",
        "Code", "Name", "Fixable"
    );
    println!("{}", "-".repeat(80));

    for code in RuleCode::all() {
        let fixable = if code.is_fixable() { "Yes" } else { "No" };
        // Truncate description to first sentence for table
        let desc = code.description();
        let short_desc = desc.split('.').next().unwrap_or(desc);

        println!(
            "{:<8} {:<20} {:<8} {}",
            code,
            code.name(),
            fixable,
            short_desc
        );
    }

    println!("\nUse --select to enable specific rules (e.g., --select FST001,FST002)");
    println!("Use --ignore to disable specific rules (e.g., --ignore FST003)");
}

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // FixSafetyLevel Tests
    // =========================================================================

    #[test]
    fn test_fix_safety_level_ordering() {
        // Safe < Caution < Unsafe
        assert!(FixSafetyLevel::Safe < FixSafetyLevel::Caution);
        assert!(FixSafetyLevel::Caution < FixSafetyLevel::Unsafe);
        assert!(FixSafetyLevel::Safe < FixSafetyLevel::Unsafe);
    }

    #[test]
    fn test_fix_safety_level_display() {
        assert_eq!(format!("{}", FixSafetyLevel::Safe), "safe");
        assert_eq!(format!("{}", FixSafetyLevel::Caution), "caution");
        assert_eq!(format!("{}", FixSafetyLevel::Unsafe), "unsafe");
    }

    #[test]
    fn test_fix_safety_level_default() {
        assert_eq!(FixSafetyLevel::default(), FixSafetyLevel::Caution);
    }

    // =========================================================================
    // FixConfidence Tests
    // =========================================================================

    #[test]
    fn test_fix_confidence_as_f64() {
        assert_eq!(FixConfidence::Low.as_f64(), 0.25);
        assert_eq!(FixConfidence::Medium.as_f64(), 0.5);
        assert_eq!(FixConfidence::High.as_f64(), 1.0);
    }

    #[test]
    fn test_fix_confidence_from_f64() {
        assert_eq!(FixConfidence::from_f64(0.0), FixConfidence::Low);
        assert_eq!(FixConfidence::from_f64(0.3), FixConfidence::Low);
        assert_eq!(FixConfidence::from_f64(0.5), FixConfidence::Medium);
        assert_eq!(FixConfidence::from_f64(0.7), FixConfidence::Medium);
        assert_eq!(FixConfidence::from_f64(0.8), FixConfidence::High);
        assert_eq!(FixConfidence::from_f64(1.0), FixConfidence::High);
    }

    // =========================================================================
    // Fix Constructor Tests
    // =========================================================================

    #[test]
    fn test_fix_new_defaults() {
        let fix = Fix::new("test fix", vec![]);
        assert_eq!(fix.confidence, FixConfidence::Medium);
        assert!(fix.is_safe());
        assert!(fix.unsafe_reason.is_none());
        assert_eq!(fix.safety_level, FixSafetyLevel::Safe);
        assert!(fix.reversible);
        assert!(!fix.requires_review);
    }

    #[test]
    fn test_fix_safe() {
        let fix = Fix::safe("safe fix", vec![]);
        assert_eq!(fix.confidence, FixConfidence::High);
        assert!(fix.is_safe());
        assert!(fix.unsafe_reason.is_none());
        assert_eq!(fix.safety_level, FixSafetyLevel::Safe);
        assert!(fix.reversible);
        assert!(!fix.requires_review);
    }

    #[test]
    fn test_fix_caution() {
        let fix = Fix::caution("caution fix", vec![]);
        assert_eq!(fix.confidence, FixConfidence::Medium);
        assert!(!fix.is_safe());  // Caution is NOT safe
        assert!(fix.unsafe_reason.is_none());
        assert_eq!(fix.safety_level, FixSafetyLevel::Caution);
        assert!(fix.reversible);
        assert!(fix.requires_review);
    }

    #[test]
    fn test_fix_unsafe_fix() {
        let fix = Fix::unsafe_fix("unsafe fix", vec![], FixConfidence::Low, "reason");
        assert_eq!(fix.confidence, FixConfidence::Low);
        assert!(!fix.is_safe());
        assert_eq!(fix.unsafe_reason, Some("reason".to_string()));
        assert_eq!(fix.safety_level, FixSafetyLevel::Unsafe);
        assert!(!fix.reversible);
        assert!(fix.requires_review);
    }

    // =========================================================================
    // Fix Builder Methods Tests
    // =========================================================================

    #[test]
    fn test_fix_with_safety_level() {
        let fix = Fix::new("test", vec![])
            .with_safety_level(FixSafetyLevel::Safe);
        assert_eq!(fix.safety_level, FixSafetyLevel::Safe);
        assert!(fix.is_safe());

        let fix = Fix::new("test", vec![])
            .with_safety_level(FixSafetyLevel::Caution);
        assert_eq!(fix.safety_level, FixSafetyLevel::Caution);
        assert!(!fix.is_safe());

        let fix = Fix::new("test", vec![])
            .with_safety_level(FixSafetyLevel::Unsafe);
        assert_eq!(fix.safety_level, FixSafetyLevel::Unsafe);
        assert!(!fix.is_safe());
    }

    #[test]
    fn test_fix_consistency_caution_with_safety_level() {
        // Bug #12: Fix::caution() and Fix::caution().with_safety_level(Caution)
        // must produce the same is_safe() result.
        let fix_direct = Fix::caution("test", vec![]);
        let fix_via_builder = Fix::caution("test", vec![])
            .with_safety_level(FixSafetyLevel::Caution);
        assert_eq!(fix_direct.is_safe(), fix_via_builder.is_safe());
        assert_eq!(fix_direct.safety_level, fix_via_builder.safety_level);
    }

    #[test]
    fn test_fix_with_reversible() {
        let fix = Fix::new("test", vec![]).with_reversible(false);
        assert!(!fix.reversible);

        let fix = Fix::new("test", vec![]).with_reversible(true);
        assert!(fix.reversible);
    }

    #[test]
    fn test_fix_with_requires_review() {
        let fix = Fix::new("test", vec![]).with_requires_review(true);
        assert!(fix.requires_review);

        let fix = Fix::new("test", vec![]).with_requires_review(false);
        assert!(!fix.requires_review);
    }

    #[test]
    fn test_fix_mark_unsafe() {
        let fix = Fix::safe("originally safe", vec![])
            .mark_unsafe("now unsafe");
        assert!(!fix.is_safe());
        assert_eq!(fix.unsafe_reason, Some("now unsafe".to_string()));
        assert_eq!(fix.safety_level, FixSafetyLevel::Unsafe);
        assert!(fix.requires_review);
    }

    // =========================================================================
    // Fix Application Tests
    // =========================================================================

    #[test]
    fn test_can_auto_apply() {
        // Only high-confidence safe fixes can auto-apply
        let fix = Fix::safe("safe", vec![]);
        assert!(fix.can_auto_apply());

        let fix = Fix::caution("caution", vec![]);
        assert!(!fix.can_auto_apply());

        let fix = Fix::unsafe_fix("unsafe", vec![], FixConfidence::High, "reason");
        assert!(!fix.can_auto_apply());

        let fix = Fix::new("medium", vec![]);  // Medium confidence
        assert!(!fix.can_auto_apply());
    }

    #[test]
    fn test_can_apply_without_force() {
        // Safe and Caution can be applied without force
        let fix = Fix::safe("safe", vec![]);
        assert!(fix.can_apply_without_force());

        let fix = Fix::caution("caution", vec![]);
        assert!(fix.can_apply_without_force());

        // Unsafe requires force
        let fix = Fix::unsafe_fix("unsafe", vec![], FixConfidence::Low, "reason");
        assert!(!fix.can_apply_without_force());
    }

    #[test]
    fn test_requires_force() {
        let fix = Fix::safe("safe", vec![]);
        assert!(!fix.requires_force());

        let fix = Fix::caution("caution", vec![]);
        assert!(!fix.requires_force());

        let fix = Fix::unsafe_fix("unsafe", vec![], FixConfidence::Low, "reason");
        assert!(fix.requires_force());
    }

    // =========================================================================
    // Chained Builder Pattern Tests
    // =========================================================================

    #[test]
    fn test_chained_builders() {
        let fix = Fix::new("test", vec![])
            .with_confidence(FixConfidence::High)
            .with_safety_level(FixSafetyLevel::Safe)
            .with_reversible(true)
            .with_requires_review(false);

        assert_eq!(fix.confidence, FixConfidence::High);
        assert_eq!(fix.safety_level, FixSafetyLevel::Safe);
        assert!(fix.reversible);
        assert!(!fix.requires_review);
    }
}
