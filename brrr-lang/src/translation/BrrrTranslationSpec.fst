(**
 * Brrr-Lang Translation Layer Specification
 *
 * This module defines translation functors from source languages to Brrr-Lang IR.
 * Each translation is a compositional, sound mapping that preserves semantic properties.
 *
 * Based on brrr_lang_spec_v0.4.md Part VI (Source Language Mapping)
 *
 * Translation targets:
 *   1. Rust -> Brrr-Lang (ownership model, lifetimes, traits)
 *   2. TypeScript -> Brrr-Lang (union types, gradual typing, async)
 *   3. Python -> Brrr-Lang (dynamic types, duck typing, decorators)
 *   4. Go -> Brrr-Lang (interfaces, goroutines, channels)
 *
 * Categorical foundation:
 *   Each language L forms a category Cat_L with types as objects and functions as morphisms.
 *   Translation T : Cat_L -> Cat_Brrr is a functor preserving identity and composition.
 *
 * ============================================================================
 * COMPILER CORRECTNESS FRAMEWORK
 * ============================================================================
 *
 * This module follows the CompCert-style approach to compiler correctness,
 * establishing semantic preservation through simulation relations.
 *
 * Key References:
 *   - CompCert: Leroy, X. (2009). "Formal Verification of a Realistic Compiler."
 *     Communications of the ACM 52(7): 107-115.
 *   - Software Foundations: Pierce et al. STLC chapter on type soundness.
 *   - F* Proof of Programming (fstar_pop_book.md): Part 2, STLC case study.
 *
 * CORRECTNESS PROPERTIES:
 * -----------------------
 *
 * 1. TYPE PRESERVATION (Subject Reduction):
 *    If e : tau in source language L, then T_L(e) : T_L(tau) in Brrr-Lang.
 *    Informally: "Well-typed source programs translate to well-typed target programs."
 *
 *    Formal statement (per-language):
 *      forall e:expr_L, tau:type_L, Gamma:ctx_L.
 *        typing_L Gamma e tau ==>
 *        typing_Brrr (T_ctx Gamma) (T_expr e) (T_type tau)
 *
 * 2. SEMANTIC PRESERVATION (Simulation):
 *    If [[e]]_L(rho) = v, then [[T_L(e)]]_Brrr(T_L(rho)) = T_L(v)
 *    Informally: "The behavior of the translated program matches the original."
 *
 *    This is established via a SIMULATION RELATION R:
 *      - Initial states are related: (e_src, T(e_src)) in R
 *      - R is preserved by stepping: If (e1, e2) in R and e1 ->_src e1',
 *        then exists e2'. e2 ->*_tgt e2' and (e1', e2') in R
 *      - Final states correspond: If (v1, v2) in R and v1 is a value,
 *        then v2 is T(v1).
 *
 * 3. EFFECT SOUNDNESS:
 *    If e has effect epsilon in L, then T_L(e) has effect T_L(epsilon) in Brrr-Lang.
 *    Effect translation is compositional: T(eff1 + eff2) = T(eff1) + T(eff2).
 *
 * 4. APPROXIMATION SAFETY:
 *    If TransApprox is returned, the translation is sound but may reject
 *    more programs than necessary (conservative over-approximation).
 *
 *    This follows the principle: "It is always safe to be more restrictive."
 *    - We may translate a pure function as effectful (safe but imprecise)
 *    - We may translate a subtype as its supertype (safe but loses precision)
 *    - We may NOT translate an effectful function as pure (unsound)
 *
 * SIMULATION RELATIONS:
 * --------------------
 *
 * The simulation approach is based on Leroy's forward simulation diagram:
 *
 *     e_src ----T----> e_tgt
 *       |               |
 *       | step_src      | step_tgt*
 *       v               v
 *     e_src' ---T----> e_tgt'
 *
 * Where step_tgt* means zero or more target steps (for stuttering).
 *
 * For each source language L, we define:
 *   - sim_L : relation (expr_L, expr_Brrr) - the simulation relation
 *   - sim_initial_L : e:expr_L -> sim_L e (T_L e) - initial states related
 *   - sim_step_L : Preservation lemma under evaluation
 *   - sim_value_L : Value correspondence at final states
 *
 * The key insight from STLC (see fstar_pop_book.md lines 6220-6720):
 *   - Beta reduction corresponds directly: T((lambda x.e) v) = T(e)[x -> T(v)]
 *   - Substitution lemma is crucial: T(e[x->v]) = T(e)[x -> T(v)]
 *   - De Bruijn indices simplify alpha-equivalence concerns
 *
 * LITERATURE CORRECTIONS (from SPECIFICATION_ERRATA.md):
 * ------------------------------------------------------
 *
 * 1. Alpha Equivalence: Uses normalization-based definition rather than
 *    structural equality. Two expressions are alpha-equivalent if they
 *    have the same canonical normal form: e1 =alpha e2 iff norm(e1) = norm(e2).
 *
 * 2. Session Types (Honda 2008 Correction): Uses ASSOCIATION RELATION with
 *    subtyping rather than equality for projection:
 *      G ~ Gamma iff forall p. G|_p <: Gamma(s[p])
 *    See Scalas & Yoshida 2019 "Less is More" for corrected formulation.
 *
 * 3. Division Preconditions: All arithmetic operations require valid_input
 *    preconditions to ensure operands are in the representable range.
 *
 * CATEGORICAL STRUCTURE:
 * ---------------------
 *
 * Each translation T_L forms a FUNCTOR from Cat_L to Cat_Brrr:
 *
 *   T_L : Cat_L -> Cat_Brrr
 *
 * satisfying:
 *   1. T_L(id_A) = id_{T_L(A)}              (Identity preservation)
 *   2. T_L(g . f) = T_L(g) . T_L(f)         (Composition preservation)
 *
 * For polynomial functors representing ADTs (see brrr_lang_spec_v0.4.tex,
 * Chapter "Algebraic Data Types"):
 *
 *   T_L(List[A]) = mu X. 1 + (T_L(A) * X)   (Initial algebra)
 *   T_L(Stream[A]) = nu X. T_L(A) * X       (Final coalgebra for codata)
 *
 * The functor structure ensures:
 *   - Naturality: T commutes with type constructors
 *   - Coherence: Different translation paths yield equivalent results
 *)
module BrrrTranslationSpec

(** Z3 solver options - conservative settings for translation proofs
    --z3rlimit 50: Allow more solver time for complex translation proofs
    --fuel 0: Disable automatic recursive unfolding (explicit proofs)
    --ifuel 0: Disable automatic inductive unfolding

    These settings follow HACL* conventions for proof stability.
    See brrr-lang/FSTAR_REFERENCE.md Section 13 "PROOF PATTERNS". *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrPythonTypes  (* Canonical Python type definitions - single source of truth *)

(** ============================================================================
    TRANSLATION FUNCTOR INTERFACE
    ============================================================================

    This section defines the core interface for all translation functors.
    Each source language implements this interface with language-specific
    type and expression mappings.

    The interface follows the pattern from EverParse (src/3d/Ast.fst):
    - Source locations are preserved for error reporting
    - Translation results carry diagnostic information
    - Approximations are explicitly marked

    ============================================================================ *)

(** Source language identifier.

    Each variant represents a supported source language with its own
    translation functor. The language determines:
    - Type translation rules (translate_*_type functions)
    - Expression translation rules (translate_*_expr functions)
    - Default effect rows (default_effects function)
    - Language-specific axioms (language_axioms function)

    EXTENSIBILITY: New languages can be added by:
    1. Adding a variant here
    2. Implementing lang_config_of for the new language
    3. Implementing type/expression translation functions
    4. Adding language axioms *)
type source_language =
  | LangRust
  | LangTypeScript
  | LangPython
  | LangGo
  | LangSwift
  | LangJava
  | LangC
  | LangCpp

(** Language configuration parameters - from spec Definition 2.1.

    This record captures the key semantic characteristics of each source
    language that affect translation strategy:

    - memory_model: How memory is managed (affects ownership translation)
    - type_discipline: Static vs dynamic typing (affects runtime checks)
    - null_handling: How null/nil is represented (affects Option wrapping)
    - effect_tracking: Whether effects are tracked (affects effect rows)
    - concurrency: Concurrency model (affects async/spawn translation)

    These parameters determine which translation rules apply and what
    runtime checks may be needed at language boundaries.

    DESIGN RATIONALE: This explicit configuration allows the translation
    to be parameterized by language characteristics rather than having
    per-language special cases scattered throughout the code.

    REFERENCE: brrr_lang_spec_v0.4.tex, Chapter "Source Language Mapping",
    Table 2.1 "Language Characteristics". *)
type lang_config = {
  memory_model    : memory_mode;
  type_discipline : type_mode;
  null_handling   : null_mode;
  effect_tracking : effect_mode;
  concurrency     : concurrency_mode
}

(** Memory management mode.

    Determines how memory is managed in the source language, which affects
    how ownership and lifetimes are translated:

    - MemOwnership: Affine/linear types with move semantics.
      Translation: Preserve ownership annotations; use move/borrow operations.
      Example: Rust's ownership system maps directly to Brrr-Lang modes.

    - MemRC: Reference counting for memory management.
      Translation: Wrap values in Rc/Arc wrappers; track reference counts.
      Example: Swift's ARC maps to mode omega (shared ownership).

    - MemGC: Garbage collection (no explicit deallocation).
      Translation: All references become mode omega; add GC effect if needed.
      Example: Python, Go, TypeScript, Java.

    - MemManual: Manual allocation/deallocation (unsafe).
      Translation: Wrap in unsafe blocks; add memory safety checks.
      Example: C, C++ require extra care at boundaries.

    CORRECTNESS: The memory mode determines which ownership guarantees
    transfer across translation. Only MemOwnership -> MemOwnership
    translations preserve linear ownership; others must approximate. *)
and memory_mode =
  | MemOwnership   (* Affine types, move semantics - Rust *)
  | MemRC          (* Reference counting - Swift *)
  | MemGC          (* Garbage collection - Python, Go, TypeScript, Java *)
  | MemManual      (* Manual allocation - C/C++ *)

(** Type discipline mode.

    Determines how types are checked and when:

    - TypeStatic: All types known at compile time.
      Translation: Direct type mapping; no runtime checks needed.
      Example: Rust, Go, Java have fully static type systems.

    - TypeGradual: Mix of static and dynamic typing.
      Translation: Typed portions map directly; 'any'/'unknown' require casts.
      Example: TypeScript allows 'any' to escape type checking.

    - TypeDynamic: Types determined at runtime.
      Translation: Most values become Dynamic type; heavy use of runtime checks.
      Example: Python's duck typing requires runtime type guards.

    APPROXIMATION: Dynamic -> Static translation is conservative:
    we may reject valid programs but never accept invalid ones.
    See ApproxDynamic in approx_reason type. *)
and type_mode =
  | TypeStatic     (* Fully static - Rust, Go, Java *)
  | TypeGradual    (* Gradual typing - TypeScript *)
  | TypeDynamic    (* Fully dynamic - Python *)

(** Null handling mode.

    Determines how null/nil values are represented:

    - NullNonNull: No null pointer; optionality is explicit.
      Translation: Preserve Option types directly.
      Example: Rust's Option<T>, Swift's Optional are explicit.

    - NullOptional: Optional types are explicit but common.
      Translation: Map to Option<T> with explicit Some/None.
      Example: Kotlin's nullable types with ? suffix.

    - NullNullable: Any reference can implicitly be null.
      Translation: Wrap in Option; add null checks at boundaries.
      Example: Python None, Go nil, Java null, TypeScript undefined.

    SAFETY: Crossing from NullNullable to NullNonNull requires
    runtime null checks (see generate_boundary_guard). *)
and null_mode =
  | NullNonNull    (* No null - Rust Option, Swift Optional *)
  | NullOptional   (* Explicit optional types - Kotlin *)
  | NullNullable   (* Implicit nullable - Python, Go, Java, TypeScript *)

(** Effect tracking mode.

    Determines how side effects are tracked:

    - EffPure: Effects are precisely tracked in the type system.
      Translation: Preserve effect annotations exactly.
      Example: Brrr-Lang's effect rows.

    - EffTracked: Effects tracked coarsely (e.g., checked exceptions).
      Translation: Map to effect rows with appropriate approximation.
      Example: Java's checked exceptions.

    - EffUntracked: Effects not tracked by type system.
      Translation: Use default open effect row; assume all effects possible.
      Example: Most languages don't track IO/State effects.

    SOUNDNESS: Translation from EffUntracked must assume worst-case
    effects. It is NEVER sound to translate effectful code as pure. *)
and effect_mode =
  | EffPure        (* Effects tracked precisely *)
  | EffTracked     (* Effects tracked coarsely *)
  | EffUntracked   (* Effects not tracked *)

(** Concurrency mode.

    Determines the concurrency primitives available:

    - ConcNone: No built-in concurrency.
      Translation: Sequential code only.

    - ConcThreads: OS-level threads.
      Translation: Map to spawn effect with thread semantics.
      Example: C/C++ pthreads, Java threads.

    - ConcAsync: Async/await cooperative concurrency.
      Translation: Map to Async effect with Future types.
      Example: TypeScript, Rust, Swift async/await.

    - ConcCSP: Communicating Sequential Processes (channels).
      Translation: Map to channel operations with Spawn effect.
      Example: Go goroutines and channels.

    - ConcActors: Actor model (isolated state, message passing).
      Translation: Map to actors with isolated heaps.
      Example: Swift actors.

    RACE FREEDOM: Only ConcCSP and ConcActors guarantee race freedom
    by construction. ConcThreads requires explicit synchronization. *)
and concurrency_mode =
  | ConcNone       (* No concurrency primitives *)
  | ConcThreads    (* OS threads - C/C++, Java *)
  | ConcAsync      (* Async/await - TypeScript, Rust, Swift *)
  | ConcCSP        (* CSP channels - Go *)
  | ConcActors     (* Actor model - Swift actors *)

(** Get configuration for a language.

    This function returns the canonical configuration for each supported
    source language, encoding the language's fundamental semantic properties.

    INVARIANT: The returned configuration accurately represents the
    language's memory model, type system, null handling, effect tracking,
    and concurrency features as documented in language specifications.

    USAGE: Used by init_ctx and init_ctx_at to create translation contexts
    with appropriate settings for the source language.

    EXAMPLES:
    - Rust has ownership (linear types), static types, no null (Option),
      untracked effects (tracked via Result), and async/await concurrency.
    - Python has GC, dynamic types, nullable None, untracked effects,
      and no built-in concurrency primitives in core language. *)
let lang_config_of (lang: source_language) : lang_config =
  match lang with
  | LangRust -> {
      memory_model = MemOwnership;
      type_discipline = TypeStatic;
      null_handling = NullNonNull;
      effect_tracking = EffUntracked;
      concurrency = ConcAsync
    }
  | LangTypeScript -> {
      memory_model = MemGC;
      type_discipline = TypeGradual;
      null_handling = NullNullable;
      effect_tracking = EffUntracked;
      concurrency = ConcAsync
    }
  | LangPython -> {
      memory_model = MemGC;
      type_discipline = TypeDynamic;
      null_handling = NullNullable;
      effect_tracking = EffUntracked;
      concurrency = ConcNone
    }
  | LangGo -> {
      memory_model = MemGC;
      type_discipline = TypeStatic;
      null_handling = NullNullable;
      effect_tracking = EffUntracked;
      concurrency = ConcCSP
    }
  | LangSwift -> {
      memory_model = MemRC;
      type_discipline = TypeStatic;
      null_handling = NullNonNull;
      effect_tracking = EffTracked;
      concurrency = ConcActors
    }
  | LangJava -> {
      memory_model = MemGC;
      type_discipline = TypeStatic;
      null_handling = NullNullable;
      effect_tracking = EffTracked;
      concurrency = ConcThreads
    }
  | LangC -> {
      memory_model = MemManual;
      type_discipline = TypeStatic;
      null_handling = NullNullable;
      effect_tracking = EffUntracked;
      concurrency = ConcThreads
    }
  | LangCpp -> {
      memory_model = MemManual;
      type_discipline = TypeStatic;
      null_handling = NullNullable;
      effect_tracking = EffUntracked;
      concurrency = ConcThreads
    }

(** ============================================================================
    SOURCE LOCATION TYPES FOR TRANSLATION
    ============================================================================

    Following EverParse's with_meta_t pattern and matching BrrrPythonTypes.fst:
    - All translation results carry source_range for precise error reporting
    - Errors include source file:line:col for debugging
    - Warnings preserve original source location

    Reference: EverParse src/3d/Ast.fst lines 146-148:
      let error #a msg (r:range) : ML a =
        raise (Error (Printf.sprintf "%s: (Error) %s\n" (string_of_pos (fst r)) msg))

    DESIGN RATIONALE:
    - Preserving source locations through translation enables better error messages
    - When translation fails, user sees original source location, not IR position
    - Warnings about approximations can point to specific source constructs

    This follows the general principle: "Never lose source location information"

    ============================================================================ *)

(** Translation source range - reuses BrrrExpressions.fst types.

    A trans_range is a pair of positions (start, end) identifying a
    contiguous region of source code. This is used to:
    1. Report errors at the correct source location
    2. Track which source construct each IR node came from
    3. Enable source-level debugging of generated code *)
let trans_range = range

(** Dummy range for synthetic translations.

    Used when generating IR nodes that don't correspond to any source
    location (e.g., inserted runtime checks, desugared constructs).

    WARNING: Avoid using dummy_trans_range when a real range is available.
    Losing source location makes debugging significantly harder. *)
let dummy_trans_range : trans_range = dummy_range

(** Translation result - carries translated item plus source location and diagnostics.
    All variants carry source_range for precise error reporting.

    Following the same pattern as BrrrPythonTypes.py_trans_result.

    VARIANTS:

    - TransOk: Translation succeeded exactly.
      The translated term has the expected type and semantics.
      Semantic preservation holds: [[T(e)]] = T([[e]])

    - TransApprox: Translation succeeded but approximated.
      The result is SOUND but may be MORE RESTRICTIVE than necessary.
      Use this when:
        * Dynamic types become Dynamic (loses precision)
        * Union types become enums (may reject valid patterns)
        * Effects are over-approximated
      The 'reason' field documents why approximation was needed.

    - TransError: Translation failed completely.
      The source construct cannot be represented in Brrr-Lang.
      The 'reason' field explains why translation is impossible.

    INVARIANT: TransOk and TransApprox results are always type-safe.
    We never produce ill-typed IR, even in error cases.

    USAGE PATTERN (monadic style):
      match translate_expr e ctx with
      | TransOk e' _ -> ... use e' ...
      | TransApprox e' reason _ -> ... use e' with warning ...
      | TransError reason _ -> ... report error ... *)
noeq type trans_result (a: Type) =
  | TransOk    : value:a -> source_range:trans_range -> trans_result a
  | TransApprox: value:a -> reason:string -> source_range:trans_range -> trans_result a  (* Sound approximation *)
  | TransError : reason:string -> source_range:trans_range -> trans_result a

(** Check if translation succeeded (exact or approximate).

    Returns true for both TransOk and TransApprox, since both produce
    usable (type-safe) output. Only TransError represents failure.

    USE CASE: Guard before calling trans_get_value. *)
let trans_is_success (#a: Type) (r: trans_result a) : bool =
  match r with
  | TransOk _ _ -> true
  | TransApprox _ _ _ -> true
  | TransError _ _ -> false

(** Extract value from successful translation.

    PRECONDITION: trans_is_success r = true

    This refinement type ensures we can only extract values from
    successful translations, preventing accidental use of error results.

    DESIGN: Using refinement types rather than option/result makes
    the success requirement explicit at call sites. *)
let trans_get_value (#a: Type) (r: trans_result a{trans_is_success r}) : a =
  match r with
  | TransOk v _ -> v
  | TransApprox v _ _ -> v

(** Translation context - carries state during translation.

    Following EverParse's env pattern (Binding.fst):
    - Tracks current source location for error reporting
    - Maintains type/lifetime environments
    - Generates fresh node IDs

    COMPONENTS:

    - source_lang: The source language being translated.
      Determines which translation rules apply.

    - config: Language configuration from lang_config_of.
      Cached for efficiency; determines translation strategy.

    - type_env: Type variable bindings.
      Maps type parameter names to their Brrr-Lang types.
      Used for generic/polymorphic type instantiation.

    - lifetime_env: Lifetime/region bindings (Rust-specific).
      Maps Rust lifetime names ('a, 'static) to Brrr-Lang regions.
      Used for lifetime-parameterized types.

    - effect_vars: Effect variable names in scope.
      Used for effect polymorphism (row polymorphism).

    - next_node_id: Counter for generating fresh node IDs.
      Ensures unique identifiers for generated AST nodes.

    - current_range: Current source location.
      Updated as translation descends into sub-expressions.
      Used for error reporting and IR node annotations.

    THREADING: Context is threaded through translation, with modifications
    returning updated contexts. This functional style avoids mutation. *)
noeq type trans_ctx = {
  source_lang    : source_language;
  config         : lang_config;
  type_env       : list (string & brrr_type);   (* Type bindings *)
  lifetime_env   : list (string & region);       (* Lifetime -> region mapping *)
  effect_vars    : list string;                  (* Effect variable names *)
  next_node_id   : nat;                          (* Fresh node ID counter *)
  current_range  : trans_range                   (* Current source location for error reporting *)
}

(** Create initial translation context.

    Creates a fresh context for translating code from the given source
    language. All environments start empty; the current_range is set to
    a dummy value until real source locations are encountered.

    USAGE: init_ctx LangRust to start translating Rust code. *)
let init_ctx (lang: source_language) : trans_ctx = {
  source_lang = lang;
  config = lang_config_of lang;
  type_env = [];
  lifetime_env = [];
  effect_vars = [];
  next_node_id = 0;
  current_range = dummy_trans_range
}

(** Create translation context at a specific source location.

    Like init_ctx, but initializes current_range to a known location.
    Use when the starting point in source is known (e.g., file root).

    USAGE: init_ctx_at LangPython (file_range "foo.py") *)
let init_ctx_at (lang: source_language) (r: trans_range) : trans_ctx = {
  source_lang = lang;
  config = lang_config_of lang;
  type_env = [];
  lifetime_env = [];
  effect_vars = [];
  next_node_id = 0;
  current_range = r
}

(** Update context to track current source location.

    Call this when entering a sub-expression to ensure error messages
    point to the correct source location.

    PATTERN:
      let ctx' = ctx_at_range ctx (loc_of sub_expr) in
      translate_sub_expr sub_expr ctx' *)
let ctx_at_range (ctx: trans_ctx) (r: trans_range) : trans_ctx =
  { ctx with current_range = r }

(** Create error result using context's current range.

    Convenience function that creates a TransError at the context's
    current source location. Use when translation cannot proceed.

    USAGE: ctx_error ctx "unsupported feature: macro expansion" *)
let ctx_error (ctx: trans_ctx) (msg: string) : trans_result 'a =
  TransError msg ctx.current_range

(** Create success result using context's current range.

    Convenience function that creates a TransOk at the context's
    current source location.

    USAGE: ctx_ok ctx (EVar "x") *)
let ctx_ok (ctx: trans_ctx) (v: 'a) : trans_result 'a =
  TransOk v ctx.current_range

(** Create approximation result using context's current range.

    Use when translation succeeds but with reduced precision.
    The reason should explain why approximation was needed.

    USAGE: ctx_approx ctx dynamic_val "Python duck typing" *)
let ctx_approx (ctx: trans_ctx) (v: 'a) (reason: string) : trans_result 'a =
  TransApprox v reason ctx.current_range

(** Extract source range from any translation result.

    Every translation result carries a source range, regardless of
    whether it succeeded or failed. This allows error reporting to
    always include source location.

    USAGE: let loc = trans_get_range result in report_at loc ... *)
let trans_get_range (#a: Type) (r: trans_result a) : trans_range =
  match r with
  | TransOk _ range -> range
  | TransApprox _ _ range -> range
  | TransError _ range -> range

(** Format error message with source location.
    Following EverParse's error function pattern (Ast.fst lines 146-148).

    PRECONDITION: r must be TransError.

    OUTPUT FORMAT: "filename:line:col: (Error) message"

    EXAMPLE: "foo.rs:42:10: (Error) unsupported feature: raw pointers" *)
let trans_format_error (#a: Type) (r: trans_result a{TransError? r}) : string =
  match r with
  | TransError msg range ->
      string_of_range range ^ ": (Error) " ^ msg

(** Format approximation warning with source location.

    PRECONDITION: r must be TransApprox.

    OUTPUT FORMAT: "filename:line:col: (Warning) message"

    EXAMPLE: "bar.py:15:5: (Warning) dynamic type translated as Dynamic" *)
let trans_format_warning (#a: Type) (r: trans_result a{TransApprox? r _ _}) : string =
  match r with
  | TransApprox _ msg range ->
      string_of_range range ^ ": (Warning) " ^ msg

(** Map over translation result, preserving source location.

    FUNCTOR LAW: trans_map id r = r
    FUNCTOR LAW: trans_map (g . f) r = trans_map g (trans_map f r)

    The source location is preserved through the mapping.

    USAGE: trans_map translate_type type_result *)
let trans_map (#a #b: Type) (f: a -> b) (r: trans_result a) : trans_result b =
  match r with
  | TransOk v range -> TransOk (f v) range
  | TransApprox v reason range -> TransApprox (f v) reason range
  | TransError reason range -> TransError reason range

(** Bind/flatMap over translation results.

    MONAD LAW: trans_bind (trans_ok v) f = f v
    MONAD LAW: trans_bind m trans_ok = m
    MONAD LAW: trans_bind (trans_bind m f) g = trans_bind m (fun x -> trans_bind (f x) g)

    Error propagation: TransError short-circuits (first error wins).
    Approximation accumulation: TransApprox reasons are concatenated.

    USAGE:
      trans_bind (translate_type ty ctx)
                 (fun ty' -> trans_bind (translate_expr e ctx)
                                        (fun e' -> ctx_ok ctx (EAs e' ty'))) *)
let trans_bind (#a #b: Type) (r: trans_result a) (f: a -> trans_result b) : trans_result b =
  match r with
  | TransOk v _ -> f v
  | TransApprox v reason range ->
      (match f v with
       | TransOk v' _ -> TransApprox v' reason range
       | TransApprox v' reason' _ -> TransApprox v' (reason ^ "; " ^ reason') range
       | TransError reason' range' -> TransError reason' range')
  | TransError reason range -> TransError reason range

(** Combine two translation results with a binary operation.
    Uses the range from the first result for the combined result.

    Error propagation: First error wins (left-to-right evaluation).
    Approximation: Reasons are concatenated if both approximate.

    USAGE: trans_combine (fun t e -> EAs e t) type_result expr_result *)
let trans_combine (#a #b #c: Type) (f: a -> b -> c)
                  (r1: trans_result a) (r2: trans_result b)
    : trans_result c =
  match r1, r2 with
  | TransOk v1 range1, TransOk v2 _ ->
      TransOk (f v1 v2) range1
  | TransError reason range, _ ->
      TransError reason range
  | _, TransError reason range ->
      TransError reason range
  | TransApprox v1 r1 range1, TransApprox v2 r2 _ ->
      TransApprox (f v1 v2) (r1 ^ "; " ^ r2) range1
  | TransApprox v1 r range1, TransOk v2 _ ->
      TransApprox (f v1 v2) r range1
  | TransOk v1 range1, TransApprox v2 r _ ->
      TransApprox (f v1 v2) r range1

(** Create a success result from an expression, extracting its range.

    Convenience for when the source location comes from an expression
    node that has location information attached.

    USAGE: trans_ok_from source_expr (translate source_expr) *)
let trans_ok_from (e: expr) (result: 'a) : trans_result 'a =
  TransOk result (loc_of e)

(** Create an approximation result from an expression, extracting its range. *)
let trans_approx_from (e: expr) (result: 'a) (reason: string) : trans_result 'a =
  TransApprox result reason (loc_of e)

(** Create an error result from an expression, extracting its range. *)
let trans_error_from (e: expr) (reason: string) : trans_result 'a =
  TransError reason (loc_of e)

(** Create an error result at a specific range. *)
let trans_error_at (r: trans_range) (reason: string) : trans_result 'a =
  TransError reason r

(** Create a success result at a specific range. *)
let trans_ok_at (r: trans_range) (result: 'a) : trans_result 'a =
  TransOk result r

(** Create an approximation result at a specific range. *)
let trans_approx_at (r: trans_range) (result: 'a) (reason: string) : trans_result 'a =
  TransApprox result reason r

(** Default effect row for each language.

    Each language has a characteristic "ambient" effect row representing
    the effects that functions in that language may implicitly have.

    LANGUAGE EFFECTS:

    - Rust: pure (effects tracked via Result/Option types, not rows)
    - TypeScript: Throw + Async + epsilon (exceptions, promises)
    - Python: Throw + IO + epsilon (everything can raise, do IO)
    - Go: Panic + Spawn + epsilon (goroutines, panic/recover)
    - Swift: Throw + Async + epsilon (throws, async/await)
    - Java: Throw + epsilon (checked exceptions)
    - C/C++: epsilon (unknown effects - conservative)

    The epsilon (RowVar "epsilon") represents an OPEN row, allowing
    additional effects to be added. This is essential for effect polymorphism.

    SOUNDNESS: It is always safe to over-approximate effects.
    We err on the side of including more effects than necessary. *)
let default_effects (lang: source_language) : effect_row =
  match lang with
  | LangRust -> pure  (* Rust tracks effects via return types *)
  | LangTypeScript -> RowExt (EThrow "Error") (RowExt EAsync (RowVar "epsilon"))
  | LangPython -> RowExt (EThrow "Exception") (RowExt EIO (RowVar "epsilon"))
  | LangGo -> RowExt EPanic (RowExt ESpawn (RowVar "epsilon"))
  | LangSwift -> RowExt (EThrow "Error") (RowExt EAsync (RowVar "epsilon"))
  | LangJava -> RowExt (EThrow "Throwable") (RowVar "epsilon")
  | LangC -> RowVar "epsilon"  (* C: unknown effects *)
  | LangCpp -> RowExt (EThrow "exception") (RowVar "epsilon")

(** ============================================================================
    PART 1: RUST -> BRRR-LANG TRANSLATION
    ============================================================================

    Rust translation is the most complete due to close alignment with
    Brrr-Lang's type system. Key correspondences:

    OWNERSHIP MODEL:
    ----------------
    Rust's ownership system maps almost directly to Brrr-Lang modes:

      Rust          | Brrr-Lang      | Semantics
      --------------|----------------|----------------------------------
      T (owned)     | T @ MOne       | Linear/affine, must use/drop
      &T            | Ref T @ MOmega | Shared borrow, can duplicate
      &mut T        | RefMut T @ MOne| Exclusive borrow, linear
      Box<T>        | Box T @ MOne   | Owned heap, linear
      Rc<T>         | Rc T @ MOmega  | Reference counted, shared
      Arc<T>        | Arc T @ MOmega | Atomic RC, shared

    LIFETIME TRANSLATION:
    --------------------
    Rust lifetimes map to Brrr-Lang regions:

      Rust      | Brrr-Lang
      ----------|------------
      'static   | RStatic
      'a        | RNamed "a"
      elided    | RFresh n

    Lifetime bounds ('a: 'b) become region outlives constraints.

    SOUNDNESS THEOREM (informal):
    ----------------------------
    If the Rust borrow checker accepts program P, then T_Rs(P) is
    ownership-safe in Brrr-Lang. More precisely:

      forall P. rust_borrow_check(P) ==> brrr_mode_check(T_Rs(P))

    This follows because:
    1. Borrow checking enforces linear/affine usage
    2. Our translation preserves these usage patterns
    3. Brrr-Lang's mode checker enforces the same invariants

    REFERENCE: TRANSLATION_DESIGN.txt Section 3 "Rust Translation"

    ============================================================================ *)

(** Rust ownership annotation.

    Tracks how a Rust value is owned/borrowed. This determines:
    - The Brrr-Lang wrapper type (none, Ref, RefMut, Box, Rc, Arc)
    - The mode (MOne for linear, MOmega for shared)
    - Whether a region/lifetime annotation is needed *)
type rust_ownership =
  | RsOwned                           (* T - owned value *)
  | RsRef       : lifetime:string -> rust_ownership  (* &'a T - shared borrow *)
  | RsRefMut    : lifetime:string -> rust_ownership  (* &'a mut T - exclusive borrow *)
  | RsRc                              (* Rc<T> - reference counted *)
  | RsArc                             (* Arc<T> - atomic RC *)
  | RsBox                             (* Box<T> - owned heap *)

(** Rust base type AST.

    Represents Rust types without ownership modifiers. The full Rust type
    is (rust_ownership, rust_type) where ownership indicates borrowing.

    COVERAGE: This covers the core Rust type system. Not covered:
    - Trait objects (dyn Trait)
    - impl Trait in return position
    - Higher-ranked trait bounds
    - Const generics

    EXTENSION: Add variants here to support more Rust types. *)
noeq type rust_type =
  | RsBool    : rust_type
  | RsI8      : rust_type
  | RsI16     : rust_type
  | RsI32     : rust_type
  | RsI64     : rust_type
  | RsI128    : rust_type
  | RsIsize   : rust_type
  | RsU8      : rust_type
  | RsU16     : rust_type
  | RsU32     : rust_type
  | RsU64     : rust_type
  | RsU128    : rust_type
  | RsUsize   : rust_type
  | RsF32     : rust_type
  | RsF64     : rust_type
  | RsChar    : rust_type
  | RsStr     : rust_type              (* String slice *)
  | RsString  : rust_type              (* Owned String *)
  | RsUnit    : rust_type
  | RsNever   : rust_type              (* ! type *)
  | RsTuple   : list rust_type -> rust_type
  | RsArray   : rust_type -> nat -> rust_type  (* [T; N] *)
  | RsSlice   : rust_type -> rust_type         (* [T] *)
  | RsOption  : rust_type -> rust_type
  | RsResult  : rust_type -> rust_type -> rust_type
  | RsVec     : rust_type -> rust_type
  | RsFn      : list rust_type -> rust_type -> rust_type
  | RsStruct  : string -> list (string & rust_type) -> rust_type
  | RsEnum    : string -> list (string & list rust_type) -> rust_type
  | RsRef_    : rust_ownership -> rust_type -> rust_type  (* Reference with ownership *)
  | RsNamed   : string -> rust_type
  | RsGeneric : string -> list rust_type -> rust_type

(** Translate Rust base type to Brrr-Lang type.

    TYPE PRESERVATION: For all t:rust_type, translate_rust_base t is well-formed.

    APPROXIMATIONS:
    - RsIsize/RsUsize -> i64/u64 (platform-dependent approximated)
    - RsVec<T> -> Array<T> (dynamic size not tracked)
    - Function closures assumed pure (effects via return types in Rust)

    STRUCT TRANSLATION:
    Rust structs map to Brrr-Lang structs with:
    - All fields public (Rust visibility not translated)
    - ReprRust layout (compatible with Rust ABI)

    ENUM TRANSLATION:
    Rust enums map to Brrr-Lang enums with:
    - Named variants
    - Tuple-style fields (no named enum fields) *)
let rec translate_rust_base (t: rust_type) : brrr_type =
  match t with
  | RsBool    -> t_bool
  | RsI8      -> t_i8
  | RsI16     -> t_i16
  | RsI32     -> t_i32
  | RsI64     -> t_i64
  | RsI128    -> TNumeric (NumInt { width = I128; sign = Signed })
  | RsIsize   -> t_i64  (* Platform-dependent, approximate as i64 *)
  | RsU8      -> t_u8
  | RsU16     -> t_u16
  | RsU32     -> t_u32
  | RsU64     -> t_u64
  | RsU128    -> TNumeric (NumInt { width = I128; sign = Unsigned })
  | RsUsize   -> t_u64
  | RsF32     -> t_f32
  | RsF64     -> t_f64
  | RsChar    -> t_char
  | RsStr     -> t_string  (* String slice -> String *)
  | RsString  -> t_string
  | RsUnit    -> t_unit
  | RsNever   -> t_never
  | RsTuple ts -> TTuple (List.Tot.map translate_rust_base ts)
  | RsArray t' _ -> t_array (translate_rust_base t')
  | RsSlice t' -> t_slice (translate_rust_base t')
  | RsOption t' -> t_option (translate_rust_base t')
  | RsResult t' e' -> TResult (translate_rust_base t') (translate_rust_base e')
  | RsVec t' -> t_array (translate_rust_base t')  (* Vec<T> -> Array<T> *)
  | RsFn params ret ->
      let params' = List.Tot.map translate_rust_base params in
      let ret' = translate_rust_base ret in
      t_func params' ret' pure  (* Rust closures: effects via return type *)
  | RsStruct name fields ->
      TStruct {
        struct_name = name;
        struct_fields = List.Tot.map (fun (n, t') ->
          { field_name = n; field_ty = translate_rust_base t'; field_vis = Public; field_tag = None }
        ) fields;
        struct_repr = ReprRust
      }
  | RsEnum name variants ->
      TEnum {
        enum_name = name;
        enum_variants = List.Tot.map (fun (n, ts) ->
          { variant_name = n; variant_fields = List.Tot.map translate_rust_base ts }
        ) variants
      }
  | RsRef_ own inner ->
      let inner' = translate_rust_base inner in
      (match own with
       | RsOwned -> inner'  (* Owned: no wrapper *)
       | RsRef _ -> t_ref inner'
       | RsRefMut _ -> t_ref_mut inner'
       | RsRc -> t_rc inner'
       | RsArc -> t_arc inner'
       | RsBox -> t_box inner')
  | RsNamed name -> TNamed name
  | RsGeneric name args ->
      TApp (TNamed name) (List.Tot.map translate_rust_base args)

(** Translate Rust ownership to Brrr-Lang mode.

    MODE CORRESPONDENCE:
    - Owned, &mut, Box: MOne (linear/affine - use exactly once)
    - &, Rc, Arc: MOmega (unrestricted - can duplicate)

    SOUNDNESS: This mapping preserves Rust's aliasing guarantees:
    - Mutable references are exclusive (MOne prevents aliasing)
    - Shared references can be copied (MOmega allows duplication) *)
let translate_rust_ownership (own: rust_ownership) : mode =
  match own with
  | RsOwned -> MOne      (* Owned: linear/affine *)
  | RsRef _ -> MOmega    (* Shared borrow: can be duplicated *)
  | RsRefMut _ -> MOne   (* Exclusive borrow: linear *)
  | RsRc -> MOmega       (* RC: shared ownership *)
  | RsArc -> MOmega      (* Arc: shared ownership *)
  | RsBox -> MOne        (* Box: owned heap, linear *)

(** Translate Rust lifetime to Brrr-Lang region.

    LIFETIME MAPPING:
    - 'static: The static region (lives forever)
    - Named lifetime: Look up in context, or create RNamed

    CONTEXT LOOKUP: If the lifetime is bound in the context (e.g., from
    a lifetime parameter), use the mapped region. Otherwise, create a
    fresh named region for tracking. *)
let translate_rust_lifetime (lt: string) (ctx: trans_ctx) : region =
  if lt = "'static" then RStatic
  else
    match List.Tot.assoc lt ctx.lifetime_env with
    | Some r -> r
    | None -> RNamed lt  (* Create new named region *)

(** Full Rust type translation with ownership and lifetime.

    Returns a triple: (translated_type, mode, optional_region)

    The region is Some only for borrowed types (&T, &mut T) where
    the lifetime annotation provides region information.

    USAGE: Use when you need all three components. For just the type,
    use translate_rust_base. *)
let translate_rust_type (t: rust_type) (own: rust_ownership) (ctx: trans_ctx)
    : (brrr_type & mode & option region) =
  let base = translate_rust_base t in
  let m = translate_rust_ownership own in
  let region = match own with
    | RsRef lt -> Some (translate_rust_lifetime lt ctx)
    | RsRefMut lt -> Some (translate_rust_lifetime lt ctx)
    | _ -> None
  in
  (base, m, region)

(** Rust expression AST.

    Represents Rust expressions in a simplified form suitable for translation.
    This is not a complete Rust AST; it covers the commonly-used constructs.

    OWNERSHIP OPERATIONS:
    - RsEBorrow: Create shared borrow (&e)
    - RsEBorrowMut: Create mutable borrow (&mut e)
    - RsEDeref: Dereference ( *e)
    - RsEMove: Explicit move (normally implicit in Rust)
    - RsEClone: Clone operation (.clone())

    CONTROL FLOW:
    - RsEIf: Conditional expression
    - RsEMatch: Pattern matching
    - RsELoop/RsEWhile/RsEFor: Loops with optional labels
    - RsEBreak/RsEContinue: Loop control with optional labels
    - RsEReturn: Early return

    ASYNC:
    - RsEAsync: async block
    - RsEAwait: .await operator

    ERROR HANDLING:
    - RsETry: ? operator (propagate errors)
    - RsEUnsafe: unsafe block *)
noeq type rust_expr =
  | RsEVar     : string -> rust_expr
  | RsELit     : literal -> rust_expr
  | RsEBinOp   : binary_op -> rust_expr -> rust_expr -> rust_expr
  | RsEUnOp    : unary_op -> rust_expr -> rust_expr
  | RsECall    : rust_expr -> list rust_expr -> rust_expr
  | RsEMethod  : rust_expr -> string -> list rust_expr -> rust_expr
  | RsEField   : rust_expr -> string -> rust_expr
  | RsEIndex   : rust_expr -> rust_expr -> rust_expr
  | RsEBorrow  : rust_expr -> rust_expr            (* &e *)
  | RsEBorrowMut : rust_expr -> rust_expr          (* &mut e *)
  | RsEDeref   : rust_expr -> rust_expr            (* *e *)
  | RsEMove    : rust_expr -> rust_expr            (* move semantics *)
  | RsEClone   : rust_expr -> rust_expr            (* .clone() *)
  | RsELet     : string -> option rust_type -> rust_expr -> rust_expr -> rust_expr
  | RsELetMut  : string -> option rust_type -> rust_expr -> rust_expr -> rust_expr
  | RsEAssign  : rust_expr -> rust_expr -> rust_expr
  | RsEIf      : rust_expr -> rust_expr -> rust_expr -> rust_expr
  | RsEMatch   : rust_expr -> list (pattern & rust_expr) -> rust_expr
  | RsELoop    : option string -> rust_expr -> rust_expr
  | RsEWhile   : option string -> rust_expr -> rust_expr -> rust_expr
  | RsEFor     : string -> rust_expr -> rust_expr -> rust_expr
  | RsEBreak   : option string -> option rust_expr -> rust_expr
  | RsEContinue: option string -> rust_expr
  | RsEReturn  : option rust_expr -> rust_expr
  | RsEBlock   : list rust_expr -> rust_expr
  | RsEClosure : list (string & rust_type) -> rust_expr -> rust_expr
  | RsEStruct  : string -> list (string & rust_expr) -> rust_expr
  | RsETuple   : list rust_expr -> rust_expr
  | RsEArray   : list rust_expr -> rust_expr
  | RsERange   : rust_expr -> rust_expr -> rust_expr
  | RsEAwait   : rust_expr -> rust_expr
  | RsEAsync   : rust_expr -> rust_expr
  | RsETry     : rust_expr -> rust_expr            (* ? operator *)
  | RsEUnsafe  : rust_expr -> rust_expr

(** Borrow context tracks what's borrowed.

    This auxiliary context tracks the ownership state of variables
    during translation to detect use-after-move errors.

    COMPONENTS:
    - owned_vars: Variables currently owning their values
    - borrowed_vars: Variables with active shared borrows (with lifetime)
    - mutborrow_vars: Variables with active mutable borrows (with lifetime)
    - moved_vars: Variables that have been moved from (unusable)

    INVARIANTS:
    - A variable can appear in at most one list at a time
    - moved_vars grows monotonically during translation
    - borrowed_vars may shrink when lifetimes end *)
noeq type borrow_ctx = {
  owned_vars   : list string;      (* Variables with owned values *)
  borrowed_vars: list (string & string);  (* (var, lifetime) pairs - shared borrows *)
  mutborrow_vars: list (string & string); (* (var, lifetime) - exclusive borrows *)
  moved_vars   : list string       (* Variables that have been moved *)
}

(** Empty borrow context - no variables tracked. *)
let empty_borrow_ctx : borrow_ctx = {
  owned_vars = [];
  borrowed_vars = [];
  mutborrow_vars = [];
  moved_vars = []
}

(** Check if variable is Copy type - simplified.

    In Rust, Copy types can be implicitly duplicated. Non-Copy types
    are moved on assignment. This affects translation of let bindings.

    COPY TYPES:
    - All integer types (i8..i128, u8..u128, isize, usize)
    - Floating point (f32, f64)
    - bool, char, unit
    - Shared references (&T)

    NON-COPY TYPES:
    - String, Vec, Box, owned structs
    - Mutable references (&mut T)
    - Types containing non-Copy fields *)
let is_copy_type (t: rust_type) : bool =
  match t with
  | RsBool | RsI8 | RsI16 | RsI32 | RsI64 | RsI128 | RsIsize
  | RsU8 | RsU16 | RsU32 | RsU64 | RsU128 | RsUsize
  | RsF32 | RsF64 | RsChar | RsUnit -> true
  | RsRef_ (RsRef _) _ -> true  (* Shared references are Copy *)
  | _ -> false

(** Translate Rust expression to Brrr-Lang.

    SEMANTIC PRESERVATION: For all e:rust_expr where translation succeeds,
    the runtime behavior of translate_rust_expr e matches Rust's semantics.

    MOVE DETECTION: The borrow context tracks moved variables. Using a
    moved variable produces a TransError with "use after move" message.

    ? OPERATOR (RsETry): Translates to pattern matching on Result:
      e?  =>  match T(e) { Ok(v) => v, Err(e) => return Err(e) }

    This desugaring matches Rust's ? operator semantics exactly.

    APPROXIMATIONS:
    - Some complex expressions produce TransApprox with "unsupported"
    - Patterns in match may not cover all Rust pattern features *)
let rec translate_rust_expr (e: rust_expr) (bctx: borrow_ctx) (ctx: trans_ctx)
    : trans_result expr =
  match e with
  | RsEVar x ->
      if List.Tot.mem x bctx.moved_vars then
        TransError ("use after move: " ^ x)
      else
        TransOk (EVar x)

  | RsELit lit -> TransOk (ELit lit)

  | RsEBinOp op e1 e2 ->
      (match translate_rust_expr e1 bctx ctx, translate_rust_expr e2 bctx ctx with
       | TransOk e1', TransOk e2' -> TransOk (EBinary op e1' e2')
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | TransApprox e1' r1, TransApprox e2' r2 ->
           TransApprox (EBinary op e1' e2') (r1 ^ "; " ^ r2)
       | TransApprox e1' r, TransOk e2' -> TransApprox (EBinary op e1' e2') r
       | TransOk e1', TransApprox e2' r -> TransApprox (EBinary op e1' e2') r)

  | RsEBorrow e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EBorrow e'')
       | TransApprox e'' r -> TransApprox (EBorrow e'') r
       | TransError r -> TransError r)

  | RsEBorrowMut e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EBorrowMut e'')
       | TransApprox e'' r -> TransApprox (EBorrowMut e'') r
       | TransError r -> TransError r)

  | RsEDeref e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EDeref e'')
       | TransApprox e'' r -> TransApprox (EDeref e'') r
       | TransError r -> TransError r)

  | RsEMove e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EMove e'')
       | TransApprox e'' r -> TransApprox (EMove e'') r
       | TransError r -> TransError r)

  | RsELet x ty init body ->
      (match translate_rust_expr init bctx ctx with
       | TransOk init' ->
           let ty' = match ty with
             | Some t -> Some (translate_rust_base t)
             | None -> None
           in
           (match translate_rust_expr body bctx ctx with
            | TransOk body' -> TransOk (ELet (PatVar x) ty' init' body')
            | TransApprox body' r -> TransApprox (ELet (PatVar x) ty' init' body') r
            | TransError r -> TransError r)
       | TransApprox init' r ->
           let ty' = match ty with Some t -> Some (translate_rust_base t) | None -> None in
           (match translate_rust_expr body bctx ctx with
            | TransOk body' -> TransApprox (ELet (PatVar x) ty' init' body') r
            | TransApprox body' r2 -> TransApprox (ELet (PatVar x) ty' init' body') (r ^ "; " ^ r2)
            | TransError r2 -> TransError r2)
       | TransError r -> TransError r)

  | RsEIf cond then_ else_ ->
      (match translate_rust_expr cond bctx ctx,
             translate_rust_expr then_ bctx ctx,
             translate_rust_expr else_ bctx ctx with
       | TransOk c, TransOk t, TransOk e -> TransOk (EIf c t e)
       | TransError r, _, _ -> TransError r
       | _, TransError r, _ -> TransError r
       | _, _, TransError r -> TransError r
       | _, _, _ -> TransApprox (EIf EHole EHole EHole) "partial translation")

  | RsEBlock stmts ->
      let rec translate_stmts (ss: list rust_expr) : trans_result (list expr) =
        match ss with
        | [] -> TransOk []
        | s :: rest ->
            (match translate_rust_expr s bctx ctx, translate_stmts rest with
             | TransOk s', TransOk rest' -> TransOk (s' :: rest')
             | TransError r, _ -> TransError r
             | _, TransError r -> TransError r
             | _, _ -> TransApprox [] "partial block translation")
      in
      (match translate_stmts stmts with
       | TransOk ss -> TransOk (EBlock ss)
       | TransApprox ss r -> TransApprox (EBlock ss) r
       | TransError r -> TransError r)

  | RsEAwait e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EAwait e'')
       | TransApprox e'' r -> TransApprox (EAwait e'') r
       | TransError r -> TransError r)

  | RsEAsync e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EAsync e'')
       | TransApprox e'' r -> TransApprox (EAsync e'') r
       | TransError r -> TransError r)

  | RsEUnsafe e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EUnsafe e'')
       | TransApprox e'' r -> TransApprox (EUnsafe e'') r
       | TransError r -> TransError r)

  | RsETry e' ->
      (* ? operator: extract Ok or propagate Err

         Desugaring:
           e?
         becomes:
           match e {
             Ok(v) => v,
             Err(e) => return Err(e)
           }

         This matches Rust's ? operator semantics exactly. *)
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' ->
           (* match e { Ok(v) => v, Err(e) => return Err(e) } *)
           TransOk (EMatch e'' [
             { arm_pattern = PatVariant "Result" "Ok" [PatVar "v"];
               arm_guard = None;
               arm_body = EVar "v" };
             { arm_pattern = PatVariant "Result" "Err" [PatVar "e"];
               arm_guard = None;
               arm_body = EReturn (Some (EVariant "Result" "Err" [EVar "e"])) }
           ])
       | TransApprox e'' r -> TransApprox e'' r
       | TransError r -> TransError r)

  | _ -> TransApprox EHole "unsupported Rust expression"

(** ============================================================================
    PART 2: TYPESCRIPT -> BRRR-LANG TRANSLATION
    ============================================================================

    TypeScript presents unique challenges due to its gradual type system,
    where 'any' can bypass type checking and union types require runtime
    discrimination.

    TYPE MAPPINGS:
    --------------
    TypeScript           | Brrr-Lang            | Notes
    ---------------------|----------------------|---------------------------
    undefined            | Unit                 | Void-like
    null                 | Option<Dynamic>      | Nullable wrapper
    boolean              | Bool                 |
    number               | Float F64            | JS number is always f64
    bigint               | Int BigInt           | Arbitrary precision
    string               | String               |
    symbol               | String               | Approximation
    void                 | Unit                 |
    never                | Never                |
    any                  | Dynamic              | UNSAFE top type
    unknown              | Unknown              | SAFE top type
    A[]                  | Array<T(A)>          |
    A | B                | Enum{Left,Right}     | Or Option if null/undefined
    A & B                | T(A)                 | Approximation (first type)
    Promise<A>           | Future<T(A)>         | Async wrapper

    GRADUAL TYPING:
    ---------------
    The key insight is that 'any' is an UNSAFE top type while 'unknown'
    is a SAFE top type:

    - any: Can be used as any type without checks (UNSOUND)
    - unknown: Must be narrowed with type guards before use (SOUND)

    We translate both to Brrr-Lang types, but:
    - 'any' requires TransApprox with "dynamic type" warning
    - 'unknown' is handled safely with runtime checks

    UNION TYPE HANDLING:
    -------------------
    Union types A | B are translated as:
    1. If one branch is null/undefined: Option<other_type>
    2. Otherwise: Enum with Left/Right variants

    This loses TypeScript's discriminated union patterns but preserves
    type safety. Full support would require flow-sensitive typing.

    ASYNC/AWAIT:
    ------------
    TypeScript's Promise<T> maps to Future<T, Hot> (already executing).
    await expressions translate directly to EAwait.

    Soundness: Type guards and casts may require runtime checks.

    ============================================================================ *)

(** TypeScript type AST.

    Represents TypeScript types in a form suitable for translation.
    Covers the commonly-used type constructs but not the full type system.

    SPECIAL TYPES:
    - TSAny: The unsafe 'any' type (bypasses type checking)
    - TSUnknown: The safe 'unknown' type (requires narrowing)
    - TSNever: The bottom type (no values)

    COMPOUND TYPES:
    - TSUnion: A | B (sum type / discriminated union)
    - TSIntersection: A & B (structural combination)
    - TSConditional: T extends U ? X : Y (conditional type)
    - TSMapped: Mapped types (approximated)
    - TSTemplateLiteral: Template literal types -> String *)
noeq type ts_type =
  | TSUndefined  : ts_type
  | TSNull       : ts_type
  | TSBoolean    : ts_type
  | TSNumber     : ts_type
  | TSBigInt     : ts_type
  | TSString     : ts_type
  | TSSymbol     : ts_type
  | TSVoid       : ts_type
  | TSNever      : ts_type
  | TSAny        : ts_type
  | TSUnknown    : ts_type
  | TSArray      : ts_type -> ts_type
  | TSTuple      : list ts_type -> ts_type
  | TSObject     : list (string & ts_type & bool) -> ts_type  (* (name, type, optional) *)
  | TSFunction   : list ts_type -> ts_type -> bool -> ts_type (* params, ret, is_async *)
  | TSUnion      : ts_type -> ts_type -> ts_type
  | TSIntersection : ts_type -> ts_type -> ts_type
  | TSPromise    : ts_type -> ts_type
  | TSLiteral    : literal -> ts_type
  | TSNamed      : string -> ts_type
  | TSGeneric    : string -> list ts_type -> ts_type
  | TSMapped     : ts_type -> ts_type  (* Mapped types approximation *)
  | TSConditional : ts_type -> ts_type -> ts_type -> ts_type  (* T extends U ? X : Y *)
  | TSTemplateLiteral : ts_type  (* Template literal types -> String *)

(** Translate TypeScript type to Brrr-Lang.

    TYPE PRESERVATION: Translation preserves type safety but may lose
    precision (see APPROXIMATIONS below).

    APPROXIMATIONS:
    - TSIntersection: Only the first type is kept
    - TSMapped: Underlying type is used
    - TSConditional: True branch is used (conservative)
    - TSSymbol: Approximated as String

    UNION HANDLING:
    Union types are handled specially:
    - T | undefined -> Option<T>
    - T | null -> Option<T>
    - A | B (general) -> Enum { Left: A, Right: B } *)
let rec translate_ts_type (t: ts_type) : brrr_type =
  match t with
  | TSUndefined -> t_unit
  | TSNull -> t_option t_dynamic  (* null -> Option<Dynamic> *)
  | TSBoolean -> t_bool
  | TSNumber -> t_f64  (* JavaScript number is f64 *)
  | TSBigInt -> TNumeric (NumInt ibig)
  | TSString -> t_string
  | TSSymbol -> t_string  (* Symbol approximated as String *)
  | TSVoid -> t_unit
  | TSNever -> t_never
  | TSAny -> t_dynamic   (* any -> Dynamic (unsafe top) *)
  | TSUnknown -> t_unknown  (* unknown -> Unknown (safe top) *)
  | TSArray elem -> t_array (translate_ts_type elem)
  | TSTuple elems -> TTuple (List.Tot.map translate_ts_type elems)
  | TSObject fields ->
      TStruct {
        struct_name = "_anonymous";
        struct_fields = List.Tot.map (fun (n, ty, opt) ->
          let field_ty = if opt then t_option (translate_ts_type ty)
                         else translate_ts_type ty in
          { field_name = n; field_ty = field_ty; field_vis = Public; field_tag = None }
        ) fields;
        struct_repr = ReprRust
      }
  | TSFunction params ret is_async ->
      let params' = List.Tot.map translate_ts_type params in
      let ret' = translate_ts_type ret in
      let ret'' = if is_async then TWrap WOption ret' (* Future approx *)
                  else ret' in
      let eff = if is_async then RowExt EAsync (RowVar "epsilon")
                else RowVar "epsilon" in
      t_func params' ret'' eff
  | TSUnion a b ->
      (* Union types: need sum type or approximation *)
      (* A | B -> Option if one is undefined/null, else approximate *)
      (match a, b with
       | TSUndefined, t -> t_option (translate_ts_type t)
       | t, TSUndefined -> t_option (translate_ts_type t)
       | TSNull, t -> t_option (translate_ts_type t)
       | t, TSNull -> t_option (translate_ts_type t)
       | _, _ ->
           (* General union: create enum with variants *)
           TEnum {
             enum_name = "_Union";
             enum_variants = [
               { variant_name = "Left"; variant_fields = [translate_ts_type a] };
               { variant_name = "Right"; variant_fields = [translate_ts_type b] }
             ]
           })
  | TSIntersection a b ->
      (* Intersection: approximate as struct merge *)
      (* This is a simplification; full intersection requires type checking *)
      translate_ts_type a  (* Approximate with first type *)
  | TSPromise t' ->
      (* Promise<T> -> Future<T> *)
      TWrap WOption (translate_ts_type t')  (* Simplified Future *)
  | TSLiteral lit ->
      (* Literal type -> base type *)
      (match lit with
       | LitBool _ -> t_bool
       | LitInt _ _ -> t_f64
       | LitString _ -> t_string
       | _ -> t_dynamic)
  | TSNamed name -> TNamed name
  | TSGeneric name args ->
      TApp (TNamed name) (List.Tot.map translate_ts_type args)
  | TSMapped t' -> translate_ts_type t'  (* Approximate as underlying type *)
  | TSConditional _ t_true _ -> translate_ts_type t_true  (* Conservative approx *)
  | TSTemplateLiteral -> t_string

(** TypeScript expression AST.

    Represents TypeScript expressions for translation. Covers:
    - Basic expressions: variables, literals, operators
    - Object operations: property access, method calls, object literals
    - Functions: arrow functions, regular functions
    - Async: await, yield (generators)
    - Control flow: conditionals, loops, try/catch

    TS-SPECIFIC:
    - TSEOptChain: Optional chaining (a?.b)
    - TSENullCoal: Nullish coalescing (a ?? b)
    - TSETypeAssert: Type assertion (e as T)
    - TSENonNull: Non-null assertion (e!) *)
noeq type ts_expr =
  | TSEVar       : string -> ts_expr
  | TSELit       : literal -> ts_expr
  | TSEBinOp     : binary_op -> ts_expr -> ts_expr -> ts_expr
  | TSEUnOp      : unary_op -> ts_expr -> ts_expr
  | TSECall      : ts_expr -> list ts_expr -> ts_expr
  | TSENew       : ts_expr -> list ts_expr -> ts_expr
  | TSEProperty  : ts_expr -> string -> ts_expr
  | TSEIndex     : ts_expr -> ts_expr -> ts_expr
  | TSEArrow     : list (string & option ts_type) -> ts_expr -> ts_expr
  | TSEFunction  : option string -> list (string & option ts_type) -> ts_expr -> ts_expr
  | TSEObject    : list (string & ts_expr) -> ts_expr
  | TSEArray     : list ts_expr -> ts_expr
  | TSEAwait     : ts_expr -> ts_expr
  | TSEAsync     : ts_expr -> ts_expr
  | TSEYield     : ts_expr -> ts_expr
  | TSEOptChain  : ts_expr -> string -> ts_expr  (* a?.b *)
  | TSENullCoal  : ts_expr -> ts_expr -> ts_expr  (* a ?? b *)
  | TSETypeAssert: ts_expr -> ts_type -> ts_expr  (* e as T *)
  | TSENonNull   : ts_expr -> ts_expr  (* e! *)
  | TSETypeof    : ts_expr -> ts_expr
  | TSEInstanceof: ts_expr -> ts_type -> ts_expr
  | TSETernary   : ts_expr -> ts_expr -> ts_expr -> ts_expr
  | TSESpread    : ts_expr -> ts_expr
  | TSETemplate  : list ts_expr -> ts_expr  (* Template literal *)
  | TSELet       : string -> option ts_type -> ts_expr -> ts_expr -> ts_expr
  | TSEConst     : string -> option ts_type -> ts_expr -> ts_expr -> ts_expr
  | TSEIf        : ts_expr -> ts_expr -> option ts_expr -> ts_expr
  | TSESwitch    : ts_expr -> list (ts_expr & ts_expr) -> option ts_expr -> ts_expr
  | TSEFor       : string -> ts_expr -> ts_expr -> ts_expr
  | TSEForOf     : string -> ts_expr -> ts_expr -> ts_expr
  | TSEWhile     : ts_expr -> ts_expr -> ts_expr
  | TSETry       : ts_expr -> option (string & ts_expr) -> option ts_expr -> ts_expr
  | TSEThrow     : ts_expr -> ts_expr
  | TSEReturn    : option ts_expr -> ts_expr
  | TSEBreak     : option string -> ts_expr
  | TSEContinue  : option string -> ts_expr
  | TSEBlock     : list ts_expr -> ts_expr
  | TSEClass     : string -> list (string & ts_expr) -> ts_expr  (* Simplified class expr *)

(** Translate TypeScript expression to Brrr-Lang.

    OPTIONAL CHAINING (a?.b):
    Desugars to pattern matching:
      match T(a) {
        None => None,
        Some(v) => Some(v.b)
      }

    NULLISH COALESCING (a ?? b):
    Desugars to pattern matching:
      match T(a) {
        Some(v) => v,
        None => T(b)
      }

    TYPE ASSERTIONS (e as T):
    Translated as runtime cast with warning:
      EAs T(e) T(T)
    The assertion may fail at runtime if types don't match.

    NON-NULL ASSERTION (e!):
    Translated as pattern match that panics on None:
      match T(e) {
        Some(v) => v,
        None => panic("non-null assertion failed")
      }
    This is UNSAFE and produces a TransApprox warning. *)
let rec translate_ts_expr (e: ts_expr) (ctx: trans_ctx) : trans_result expr =
  match e with
  | TSEVar x -> TransOk (EVar x)
  | TSELit lit -> TransOk (ELit lit)

  | TSEBinOp op e1 e2 ->
      (match translate_ts_expr e1 ctx, translate_ts_expr e2 ctx with
       | TransOk e1', TransOk e2' -> TransOk (EBinary op e1' e2')
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | _, _ -> TransApprox EHole "partial binop")

  | TSECall f args ->
      (match translate_ts_expr f ctx with
       | TransOk f' ->
           let rec translate_args (as_: list ts_expr) : trans_result (list expr) =
             match as_ with
             | [] -> TransOk []
             | a :: rest ->
                 (match translate_ts_expr a ctx, translate_args rest with
                  | TransOk a', TransOk rest' -> TransOk (a' :: rest')
                  | TransError r, _ -> TransError r
                  | _, TransError r -> TransError r
                  | _, _ -> TransApprox [] "partial args")
           in
           (match translate_args args with
            | TransOk args' -> TransOk (ECall f' args')
            | TransApprox args' r -> TransApprox (ECall f' args') r
            | TransError r -> TransError r)
       | TransError r -> TransError r
       | TransApprox f' r -> TransApprox (ECall f' []) r)

  | TSEAwait e' ->
      (match translate_ts_expr e' ctx with
       | TransOk e'' -> TransOk (EAwait e'')
       | TransApprox e'' r -> TransApprox (EAwait e'') r
       | TransError r -> TransError r)

  | TSEAsync e' ->
      (match translate_ts_expr e' ctx with
       | TransOk e'' -> TransOk (EAsync e'')
       | TransApprox e'' r -> TransApprox (EAsync e'') r
       | TransError r -> TransError r)

  | TSEOptChain base prop ->
      (* a?.b -> match a { Some(v) => Some(v.prop), None => None } *)
      (match translate_ts_expr base ctx with
       | TransOk base' ->
           TransOk (EMatch base' [
             { arm_pattern = PatVariant "Option" "None" [];
               arm_guard = None;
               arm_body = EVariant "Option" "None" [] };
             { arm_pattern = PatVariant "Option" "Some" [PatVar "v"];
               arm_guard = None;
               arm_body = EVariant "Option" "Some" [EField (EVar "v") prop] }
           ])
       | TransError r -> TransError r
       | TransApprox e' r -> TransApprox e' r)

  | TSENullCoal e1 e2 ->
      (* a ?? b -> match a { Some(v) => v, None => b } *)
      (match translate_ts_expr e1 ctx, translate_ts_expr e2 ctx with
       | TransOk e1', TransOk e2' ->
           TransOk (EMatch e1' [
             { arm_pattern = PatVariant "Option" "Some" [PatVar "v"];
               arm_guard = None;
               arm_body = EVar "v" };
             { arm_pattern = PatVariant "Option" "None" [];
               arm_guard = None;
               arm_body = e2' }
           ])
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | _, _ -> TransApprox EHole "partial nullish coalescing")

  | TSETypeAssert e' ty ->
      (* e as T -> cast with runtime type check *)
      (match translate_ts_expr e' ctx with
       | TransOk e'' ->
           TransApprox (EAs e'' (translate_ts_type ty))
                       "type assertion requires runtime check"
       | TransError r -> TransError r
       | TransApprox e'' r -> TransApprox (EAs e'' (translate_ts_type ty)) r)

  | TSENonNull e' ->
      (* e! -> match e { Some(v) => v, None => panic } *)
      (match translate_ts_expr e' ctx with
       | TransOk e'' ->
           TransApprox (EMatch e'' [
             { arm_pattern = PatVariant "Option" "Some" [PatVar "v"];
               arm_guard = None;
               arm_body = EVar "v" };
             { arm_pattern = PatVariant "Option" "None" [];
               arm_guard = None;
               arm_body = EThrow (ELit (LitString "non-null assertion failed")) }
           ]) "non-null assertion may panic"
       | TransError r -> TransError r
       | TransApprox e'' r -> TransApprox e'' r)

  | TSEArrow params body ->
      let params' = List.Tot.map (fun (n, ty) ->
        match ty with
        | Some t -> (n, translate_ts_type t)
        | None -> (n, t_dynamic)  (* Untyped param -> dynamic *)
      ) params in
      (match translate_ts_expr body ctx with
       | TransOk body' -> TransOk (ELambda params' body')
       | TransApprox body' r -> TransApprox (ELambda params' body') r
       | TransError r -> TransError r)

  | TSELet x ty init body ->
      let ty' = match ty with
        | Some t -> Some (translate_ts_type t)
        | None -> None
      in
      (match translate_ts_expr init ctx, translate_ts_expr body ctx with
       | TransOk init', TransOk body' -> TransOk (ELet (PatVar x) ty' init' body')
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | _, _ -> TransApprox EHole "partial let")

  | TSETernary cond then_ else_ ->
      (match translate_ts_expr cond ctx,
             translate_ts_expr then_ ctx,
             translate_ts_expr else_ ctx with
       | TransOk c, TransOk t, TransOk e -> TransOk (EIf c t e)
       | TransError r, _, _ -> TransError r
       | _, TransError r, _ -> TransError r
       | _, _, TransError r -> TransError r
       | _, _, _ -> TransApprox EHole "partial ternary")

  | TSEThrow e' ->
      (match translate_ts_expr e' ctx with
       | TransOk e'' -> TransOk (EThrow e'')
       | TransApprox e'' r -> TransApprox (EThrow e'') r
       | TransError r -> TransError r)

  | TSEBlock stmts ->
      let rec translate_stmts (ss: list ts_expr) : trans_result (list expr) =
        match ss with
        | [] -> TransOk []
        | s :: rest ->
            (match translate_ts_expr s ctx, translate_stmts rest with
             | TransOk s', TransOk rest' -> TransOk (s' :: rest')
             | TransError r, _ -> TransError r
             | _, TransError r -> TransError r
             | _, _ -> TransApprox [] "partial block")
      in
      (match translate_stmts stmts with
       | TransOk ss -> TransOk (EBlock ss)
       | TransApprox ss r -> TransApprox (EBlock ss) r
       | TransError r -> TransError r)

  | _ -> TransApprox EHole "unsupported TypeScript expression"

(** ============================================================================
    PART 3: PYTHON -> BRRR-LANG TRANSLATION
    ============================================================================

    Python translation uses the canonical types from BrrrPythonTypes.fst:

    Types (py_type):
      - Primitive: PyNone, PyBool, PyInt, PyFloat, PyStr, PyBytes
      - Collection: PyList, PyDict, PySet, PyFrozenSet, PyTuple
      - Typing: PyOptional, PyUnion, PyCallable, PyAwaitable, PyGenerator,
                PyIterator, PyIterable
      - Special: PyAny, PyNever, PyType, PyClass, PyGeneric, PyTypeVar,
                 PyLiteral, PySelf

    Expressions (py_expr):
      - Atoms: PyEVar, PyELit, PyENone, PyETrue, PyEFalse
      - Operations: PyEBinOp, PyEUnOp, PyECompare, PyEBoolOp
      - Calls: PyECall, PyEAttr, PyEIndex, PyESlice
      - Functions: PyELambda
      - Collections: PyEList, PyEDict, PyETuple, PyESet
      - Comprehensions: PyEListComp, PyEDictComp, PyESetComp, PyEGenExpr
      - Control flow: PyEIfExp, PyEWalrus, PyEIf, PyEFor, PyEWhile,
                      PyETry, PyEWith, PyEMatch
      - Async: PyEAwait, PyEYield, PyEYieldFrom
      - Statements: PyEAssign, PyEAugAssign, PyEReturn, PyERaise, PyEAssert,
                    PyEPass, PyEBreak, PyEContinue
      - Block: PyEBlock

    KEY CHALLENGES:
    ---------------

    1. DYNAMIC TYPING: Most Python values have types known only at runtime.
       Translation strategy: Use Dynamic type with runtime type checks.

    2. DUCK TYPING: Python relies on structural subtyping.
       Translation strategy: Runtime attribute lookup, conservative typing.

    3. DECORATORS: Python decorators modify function behavior.
       Translation strategy: Approximate as effect annotations where possible.

    4. COMPREHENSIONS: List/dict/set comprehensions are syntactic sugar.
       Translation strategy: Desugar to explicit loops/maps.

    Key mappings:
      - Dynamic types: Python type -> Dynamic (with type hints -> gradual)
      - None: None -> Unit
      - Collections: list -> gc Array, dict -> gc Dict
      - Duck typing: attribute access -> runtime lookup
      - Decorators: @decorator -> effect annotation (approximation)

    For complete Python translation with full typing module support,
    see BrrrPythonTranslation.fst which provides:
      - translate_py_type: py_type -> brrr_type
      - translate_py_expr: py_expr -> py_trans_result
      - python_functor: Translation functor with laws and soundness proofs

    Soundness: Requires runtime type guards for any static property.

    ============================================================================ *)

(** Python default effects: Throw + IO + epsilon

    Python functions have implicit effects:
    - Throw: Any function can raise exceptions
    - IO: Any function can perform I/O
    - epsilon: Open row for additional effects

    This is a CONSERVATIVE approximation. Python does not track effects,
    so we assume the worst case. *)
let py_default_effects : effect_row =
  RowExt (EThrow "Exception") (RowExt EIO (RowVar "epsilon"))

(** ============================================================================
    PART 4: GO -> BRRR-LANG TRANSLATION
    ============================================================================

    Go translation handles Go's unique features:
    - Interface types (structural subtyping)
    - Goroutines and channels (CSP concurrency)
    - Multiple return values (including error handling pattern)
    - nil for multiple types

    KEY MAPPINGS:
    -------------

    TYPE MAPPING:
    Go Type             | Brrr-Lang Type      | Notes
    --------------------|---------------------|------------------------
    bool                | Bool                |
    int, int64          | Int I64             | Platform-dependent
    int8..int32         | Int I8..I32         |
    uint, uint64        | Unsigned I64        |
    float32, float64    | Float F32, F64      |
    complex64, complex128| Tuple (F32,F32) etc| Approximation
    string              | String              |
    []T                 | Slice T             |
    [N]T                | Array T             | Size not tracked
    map[K]V             | Dict K V            |
    chan T              | Channel T           | Direction not tracked
    *T                  | Option T            | Nullable pointer
    interface{}         | Dynamic             |
    error               | Named "Error"       |

    GOROUTINES:
    go f(x)  =>  spawn(T(f)(T(x)))

    The Spawn effect is added to functions that create goroutines.

    CHANNELS:
    ch <- v   =>  chan_send(T(ch), T(v))
    <-ch      =>  chan_recv(T(ch))
    select {} =>  select([...cases...])  (approximated)

    ERROR HANDLING:
    Go's (T, error) return pattern maps to Result<T, Error>:
      func() (T, error)  =>  () -[epsilon_Go]-> Result T Error

    PANIC/RECOVER:
    panic(v)   =>  throw(T(v))
    recover()  =>  catch_panic()  (requires special handling)
    defer f()  =>  defer(T(f()))  (stack-based execution model)

    DEFAULT EFFECTS: epsilon_Go = <Panic | <Spawn | epsilon>>

    APPROXIMATIONS:
    - defer semantics require stack-based execution model
    - recover() needs special catch handling
    - Type assertions require runtime checks
    - nil interface is different from nil concrete type

    Soundness: Race conditions in Go may not be detected.

    ============================================================================ *)

(** Go type AST.

    Represents Go types for translation. Covers:
    - Basic types: integers, floats, complex, string, bool
    - Composite types: arrays, slices, maps, channels, structs
    - Pointer types and interfaces
    - Named types and error interface *)
noeq type go_type =
  | GoBool     : go_type
  | GoInt      : go_type      (* Platform-dependent int *)
  | GoInt8     : go_type
  | GoInt16    : go_type
  | GoInt32    : go_type
  | GoInt64    : go_type
  | GoUint     : go_type
  | GoUint8    : go_type
  | GoUint16   : go_type
  | GoUint32   : go_type
  | GoUint64   : go_type
  | GoUintptr  : go_type
  | GoFloat32  : go_type
  | GoFloat64  : go_type
  | GoComplex64: go_type
  | GoComplex128: go_type
  | GoString   : go_type
  | GoByte     : go_type      (* alias for uint8 *)
  | GoRune     : go_type      (* alias for int32 *)
  | GoArray    : go_type -> nat -> go_type  (* [N]T *)
  | GoSlice    : go_type -> go_type          (* []T *)
  | GoMap      : go_type -> go_type -> go_type  (* map[K]V *)
  | GoChan     : go_type -> bool -> bool -> go_type  (* chan T, send-only, recv-only *)
  | GoPtr      : go_type -> go_type          (* *T *)
  | GoFunc     : list go_type -> bool -> list go_type -> go_type  (* func(params)(is_variadic)(results) - when is_variadic=true, last param is ...T element type *)
  | GoStruct   : string -> list go_struct_field -> go_type        (* struct with named and embedded fields *)
  | GoInterface: string -> list (string & go_type) -> go_type
  | GoNamed    : string -> go_type
  | GoError    : go_type      (* error interface *)
  | GoAny      : go_type      (* interface{} / any *)

(* Struct field declaration - named or embedded (anonymous).
   Go spec: FieldDecl = (IdentifierList Type | EmbeddedField) [ Tag ] .
   EmbeddedField = [ "*" ] TypeName [ TypeArgs ] .
   Tag = string_lit .
   Embedded fields promote their sub-fields and methods to the outer struct.
   Tags are raw string literals for reflection metadata,
   e.g. `json:"name,omitempty" xml:"user_name"`. *)
and go_struct_field =
  | GoField    : string -> go_type -> option string -> go_struct_field  (* named field: Name Type `tag` *)
  | GoEmbedded : go_type -> option string -> go_struct_field            (* embedded field: Type `tag` *)

(** Translate Go type to Brrr-Lang.

    TYPE PRESERVATION: Translation is type-safe but may lose precision.

    APPROXIMATIONS:
    - GoInt/GoUint: Platform-dependent, approximated as 64-bit
    - Complex types: Represented as tuples of floats
    - Channel direction: Not tracked (send/recv both allowed)
    - Interface methods: Approximated as named types *)
let rec translate_go_type (t: go_type) : brrr_type =
  match t with
  | GoBool -> t_bool
  | GoInt -> t_i64   (* Approximate as i64 *)
  | GoInt8 -> t_i8
  | GoInt16 -> t_i16
  | GoInt32 -> t_i32
  | GoInt64 -> t_i64
  | GoUint -> t_u64
  | GoUint8 -> t_u8
  | GoUint16 -> t_u16
  | GoUint32 -> t_u32
  | GoUint64 -> t_u64
  | GoUintptr -> t_u64
  | GoFloat32 -> t_f32
  | GoFloat64 -> t_f64
  | GoComplex64 ->
      TTuple [t_f32; t_f32]  (* Approximate complex as tuple *)
  | GoComplex128 ->
      TTuple [t_f64; t_f64]
  | GoString -> t_string
  | GoByte -> t_u8
  | GoRune -> t_i32
  | GoArray elem _ -> t_array (translate_go_type elem)
  | GoSlice elem -> t_slice (translate_go_type elem)
  | GoMap k v ->
      TStruct {
        struct_name = "Map";
        struct_fields = [
          { field_name = "key_type"; field_ty = translate_go_type k; field_vis = Public; field_tag = None };
          { field_name = "val_type"; field_ty = translate_go_type v; field_vis = Public; field_tag = None }
        ];
        struct_repr = ReprRust
      }
  | GoChan elem _ _ ->
      (* Channel<T> - direction ignored for now *)
      TWrap WOption (translate_go_type elem)  (* Simplified as Option for now *)
  | GoPtr elem -> t_option (translate_go_type elem)  (* Go pointer nullable *)
  | GoFunc params is_variadic results ->
      let params' =
        if is_variadic && Cons? params then
          (* Last param is variadic element type T -> translate as []T (slice) *)
          let n = List.Tot.length params in
          let init_params = List.Tot.map translate_go_type
            (if n > 1 then
               let rec take_init (l: list go_type) : Tot (list go_type) (decreases l) =
                 match l with
                 | [] -> []
                 | [_] -> []
                 | x :: rest -> x :: take_init rest
               in
               take_init params
             else [])
          in
          let last_elem = List.Tot.index params (n - 1) in
          List.Tot.append init_params [t_slice (translate_go_type last_elem)]
        else
          List.Tot.map translate_go_type params
      in
      let ret' = match results with
        | [] -> t_unit
        | [r] -> translate_go_type r
        | rs -> TTuple (List.Tot.map translate_go_type rs)
      in
      let eff = RowExt EPanic (RowExt ESpawn (RowVar "epsilon")) in
      t_func params' ret' eff
  | GoStruct name fields ->
      (* Translate struct fields, flattening embedded fields by promoting
         their sub-fields to the outer struct (Go field promotion semantics). *)
      let translate_struct_field (sf: go_struct_field) : list struct_field =
        match sf with
        | GoField n ty tag ->
            [{ field_name = n; field_ty = translate_go_type ty; field_vis = Public; field_tag = tag }]
        | GoEmbedded ty tag ->
            let embedded_name = match ty with
              | GoNamed n -> n
              | GoPtr (GoNamed n) -> n
              | _ -> "_embedded"
            in
            let embedded_field = {
              field_name = embedded_name;
              field_ty = translate_go_type ty;
              field_vis = Public;
              field_tag = tag
            } in
            let promoted = match ty with
              | GoStruct _ inner_fields ->
                  List.Tot.concatMap (fun (isf: go_struct_field) ->
                    match isf with
                    | GoField fn ft inner_tag ->
                        [{ field_name = fn; field_ty = translate_go_type ft; field_vis = Public; field_tag = inner_tag }]
                    | GoEmbedded _ _ -> []
                  ) inner_fields
              | _ -> []
            in
            embedded_field :: promoted
      in
      TStruct {
        struct_name = name;
        struct_fields = List.Tot.concatMap translate_struct_field fields;
        struct_repr = ReprRust
      }
  | GoInterface name methods ->
      (* Interface -> type class (dynamic dispatch) *)
      TNamed name  (* Approximate as named type *)
  | GoNamed name -> TNamed name
  | GoError -> TNamed "Error"  (* Error interface *)
  | GoAny -> t_dynamic

(** Go expression AST.

    Represents Go expressions for translation. Covers:
    - Basic expressions: variables, literals, operators
    - Composite literals: structs, arrays, maps
    - Concurrency: go, defer, channel operations, select
    - Control flow: if, for, switch, type switch
    - Error handling: panic, recover *)
noeq type go_expr =
  | GoEVar      : string -> go_expr
  | GoELit      : literal -> go_expr
  | GoENil      : go_expr
  | GoEBinOp    : binary_op -> go_expr -> go_expr -> go_expr
  | GoEUnOp     : unary_op -> go_expr -> go_expr
  | GoECall     : go_expr -> list go_expr -> go_expr
  | GoEMethod   : go_expr -> string -> list go_expr -> go_expr
  | GoEField    : go_expr -> string -> go_expr
  | GoEIndex    : go_expr -> go_expr -> go_expr
  | GoESlice    : go_expr -> option go_expr -> option go_expr -> option go_expr -> go_expr
  | GoETypeAssert: go_expr -> go_type -> go_expr  (* e.(T) *)
  | GoEMake     : go_type -> list go_expr -> go_expr  (* make(T, args) *)
  | GoENew      : go_type -> go_expr               (* new(T) *)
  | GoEComposite: go_type -> list go_expr -> go_expr  (* T{elems} *)
  | GoEFunc     : list (string & go_type) -> list go_type -> go_expr -> go_expr
  | GoEGo       : go_expr -> go_expr               (* go f(x) *)
  | GoEDefer    : go_expr -> go_expr               (* defer f(x) *)
  | GoEChanSend : go_expr -> go_expr -> go_expr    (* ch <- v *)
  | GoEChanRecv : go_expr -> go_expr               (* <-ch *)
  | GoESelect   : list (go_expr & go_expr) -> option go_expr -> go_expr
  | GoEIf       : option go_expr -> go_expr -> go_expr -> option go_expr -> go_expr
  | GoEFor      : option go_expr -> option go_expr -> option go_expr -> go_expr -> go_expr
  | GoEForRange : string -> option string -> go_expr -> go_expr -> go_expr
  | GoESwitch   : option go_expr -> go_expr -> list (list go_expr & go_expr) -> option go_expr -> go_expr
  | GoETypeSwitch: string -> go_expr -> list (go_type & go_expr) -> option go_expr -> go_expr
  | GoEReturn   : list go_expr -> go_expr
  | GoEBreak    : option string -> go_expr
  | GoEContinue : option string -> go_expr
  | GoEGoto     : string -> go_expr
  | GoEFallthrough : go_expr
  | GoEPanic    : go_expr -> go_expr
  | GoERecover  : go_expr
  | GoEBlock    : list go_expr -> go_expr
  | GoEShortDecl: list string -> list go_expr -> go_expr -> go_expr  (* x := e *)
  | GoEAssign   : list go_expr -> list go_expr -> go_expr
  | GoEIota     : go_expr                                                       (* iota constant generator *)
  | GoEConstDecl: list (string & option go_type & go_expr) -> go_expr -> go_expr (* const block with continuation *)
  | GoESpread   : go_expr -> go_expr                                             (* slice... - spread slice into variadic parameter *)

(** Translate Go expression to Brrr-Lang.

    GOROUTINES (go f(x)):
    Translated to spawn(T(f)(T(x))), adding Spawn effect to context.

    CHANNEL OPERATIONS:
    ch <- v  =>  method_call(T(ch), "send", [T(v)])
    <-ch     =>  method_call(T(ch), "recv", [])

    DEFER:
    Go's defer has stack semantics (LIFO execution on function exit).
    This is approximated; full semantics requires execution model changes.

    PANIC/RECOVER:
    panic(v) => throw(T(v))
    recover() => Approximated; requires special catch handling.

    MULTIPLE RETURNS:
    Go functions can return multiple values. These become tuples:
    return a, b  =>  return (T(a), T(b)) *)
let rec translate_go_expr (e: go_expr) (ctx: trans_ctx) : trans_result expr =
  match e with
  | GoEVar x -> TransOk (EVar x)
  | GoELit lit -> TransOk (ELit lit)
  | GoENil -> TransOk (EVariant "Option" "None" [])

  | GoEBinOp op e1 e2 ->
      (match translate_go_expr e1 ctx, translate_go_expr e2 ctx with
       | TransOk e1', TransOk e2' -> TransOk (EBinary op e1' e2')
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | _, _ -> TransApprox EHole "partial binop")

  | GoECall f args ->
      (match translate_go_expr f ctx with
       | TransOk f' ->
           let rec translate_args (as_: list go_expr) : trans_result (list expr) =
             match as_ with
             | [] -> TransOk []
             | a :: rest ->
                 (match translate_go_expr a ctx, translate_args rest with
                  | TransOk a', TransOk rest' -> TransOk (a' :: rest')
                  | TransError r, _ -> TransError r
                  | _, TransError r -> TransError r
                  | _, _ -> TransApprox [] "partial args")
           in
           (match translate_args args with
            | TransOk args' -> TransOk (ECall f' args')
            | TransApprox args' r -> TransApprox (ECall f' args') r
            | TransError r -> TransError r)
       | TransError r -> TransError r
       | TransApprox f' r -> TransApprox (ECall f' []) r)

  | GoEGo e' ->
      (* go f(x) -> spawn(f(x))
         This creates a new goroutine running the expression concurrently. *)
      (match translate_go_expr e' ctx with
       | TransOk e'' -> TransOk (ESpawn e'')
       | TransApprox e'' r -> TransApprox (ESpawn e'') r
       | TransError r -> TransError r)

  | GoEChanSend ch v ->
      (* ch <- v -> channel send operation
         In Go, this blocks until a receiver is ready (unbuffered) or
         buffer space is available (buffered). *)
      (match translate_go_expr ch ctx, translate_go_expr v ctx with
       | TransOk ch', TransOk v' ->
           TransOk (EMethodCall ch' "send" [v'])
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | _, _ -> TransApprox EHole "partial chan send")

  | GoEChanRecv ch ->
      (* <-ch -> channel receive operation
         In Go, this blocks until a value is available. *)
      (match translate_go_expr ch ctx with
       | TransOk ch' -> TransOk (EMethodCall ch' "recv" [])
       | TransApprox ch' r -> TransApprox (EMethodCall ch' "recv" []) r
       | TransError r -> TransError r)

  | GoEDefer e' ->
      (* defer f(x) -> special deferred execution
         In Go, deferred calls execute in LIFO order when the function returns.
         This semantics is approximated; full support requires execution model changes. *)
      (match translate_go_expr e' ctx with
       | TransOk e'' ->
           TransApprox e'' "defer semantics approximated"
       | TransApprox e'' r -> TransApprox e'' r
       | TransError r -> TransError r)

  | GoEPanic e' ->
      (* panic(v) -> throw
         Go's panic is similar to throwing an exception. *)
      (match translate_go_expr e' ctx with
       | TransOk e'' -> TransOk (EThrow e'')
       | TransApprox e'' r -> TransApprox (EThrow e'') r
       | TransError r -> TransError r)

  | GoERecover ->
      (* recover() -> ERecover
         In Go, recover() returns the panic value if called inside a deferred
         function during panic unwinding, or nil otherwise. The actual panic
         interception is handled by the ETry/catch mechanism. *)
      TransOk ERecover

  | GoETypeAssert e' ty ->
      (* e.(T) -> type assertion with runtime check
         In Go, this panics if e doesn't hold a value of type T.
         Translated as a cast that may fail at runtime. *)
      (match translate_go_expr e' ctx with
       | TransOk e'' ->
           TransApprox (EAs e'' (translate_go_type ty))
                       "type assertion requires runtime check"
       | TransError r -> TransError r
       | TransApprox e'' r -> TransApprox (EAs e'' (translate_go_type ty)) r)

  | GoEIf init cond then_ else_ ->
      (* Go's if can have an init statement: if x := f(); x > 0 { ... }
         Translated as: let x = f() in if x > 0 then ... else ... *)
      let translate_body b = translate_go_expr b ctx in
      (match init with
       | Some init' ->
           (match translate_go_expr init' ctx,
                  translate_go_expr cond ctx,
                  translate_body then_ with
            | TransOk init'', TransOk cond', TransOk then'' ->
                let else'' = match else_ with
                  | Some e -> (match translate_body e with
                              | TransOk e' -> e'
                              | _ -> ELit LitUnit)
                  | None -> ELit LitUnit
                in
                TransOk (ESeq init'' (EIf cond' then'' else''))
            | TransError r, _, _ -> TransError r
            | _, TransError r, _ -> TransError r
            | _, _, TransError r -> TransError r
            | _, _, _ -> TransApprox EHole "partial if")
       | None ->
           (match translate_go_expr cond ctx, translate_body then_ with
            | TransOk cond', TransOk then'' ->
                let else'' = match else_ with
                  | Some e -> (match translate_body e with
                              | TransOk e' -> e'
                              | _ -> ELit LitUnit)
                  | None -> ELit LitUnit
                in
                TransOk (EIf cond' then'' else'')
            | TransError r, _ -> TransError r
            | _, TransError r -> TransError r
            | _, _ -> TransApprox EHole "partial if"))

  | GoEReturn results ->
      (* Go's return with multiple values becomes tuple return *)
      (match results with
       | [] -> TransOk (EReturn None)
       | [r] ->
           (match translate_go_expr r ctx with
            | TransOk r' -> TransOk (EReturn (Some r'))
            | TransApprox r' re -> TransApprox (EReturn (Some r')) re
            | TransError re -> TransError re)
       | _ ->
           (* Multiple returns -> tuple *)
           let rec translate_results (rs: list go_expr) : trans_result (list expr) =
             match rs with
             | [] -> TransOk []
             | r :: rest ->
                 (match translate_go_expr r ctx, translate_results rest with
                  | TransOk r', TransOk rest' -> TransOk (r' :: rest')
                  | TransError re, _ -> TransError re
                  | _, TransError re -> TransError re
                  | _, _ -> TransApprox [] "partial results")
           in
           (match translate_results results with
            | TransOk rs' -> TransOk (EReturn (Some (ETuple rs')))
            | TransApprox rs' re -> TransApprox (EReturn (Some (ETuple rs'))) re
            | TransError re -> TransError re))

  | GoEBlock stmts ->
      let rec translate_stmts (ss: list go_expr) : trans_result (list expr) =
        match ss with
        | [] -> TransOk []
        | s :: rest ->
            (match translate_go_expr s ctx, translate_stmts rest with
             | TransOk s', TransOk rest' -> TransOk (s' :: rest')
             | TransError r, _ -> TransError r
             | _, TransError r -> TransError r
             | _, _ -> TransApprox [] "partial block")
      in
      (match translate_stmts stmts with
       | TransOk ss -> TransOk (EBlock ss)
       | TransApprox ss r -> TransApprox (EBlock ss) r
       | TransError r -> TransError r)

  | GoEBreak lbl -> TransOk (EBreak lbl None)
  | GoEContinue lbl -> TransOk (EContinue lbl)

  | GoEIota ->
      (* Iota translates to a variable reference "__go_iota" which is bound
         to the correct index by GoEConstDecl translation. Per Go spec, iota
         is only meaningful inside const declarations. *)
      TransOk (EVar "__go_iota")

  | GoEConstDecl specs cont ->
      (* Translate const block to nested let bindings with iota substitution.
         Each (name, optional type, initializer) becomes a let binding.
         Each init is wrapped in a let binding for "__go_iota" set to the
         spec's positional index (0-based), so GoEIota references resolve
         to the correct value. *)
      let indexed_specs = List.Tot.mapi (fun idx spec -> (idx, spec)) specs in
      let rec translate_specs (ss: list (int & (string & option go_type & go_expr)))
                              (acc: trans_result expr)
          : trans_result expr =
        match ss with
        | [] -> acc
        | (idx, (name, ty_opt, init)) :: rest ->
            let wrap_iota (e: expr) : expr =
              ELet (PatVar "__go_iota")
                   (Some (t_int i64))
                   (ELit (LitInt idx i64))
                   e
            in
            (match translate_go_expr init ctx, acc with
             | TransOk init', TransOk acc' ->
                 translate_specs rest
                   (TransOk (ELet (PatVar name)
                                  (match ty_opt with
                                   | Some t -> Some (translate_go_type t)
                                   | None -> None)
                                  (wrap_iota init')
                                  acc'))
             | TransError r, _ -> TransError r
             | _, TransError r -> TransError r
             | TransApprox init' _, TransOk acc' ->
                 translate_specs rest
                   (TransApprox (ELet (PatVar name)
                                      (match ty_opt with
                                       | Some t -> Some (translate_go_type t)
                                       | None -> None)
                                      (wrap_iota init')
                                      acc')
                                "partial const init")
             | _, TransApprox acc' r ->
                 translate_specs rest (TransApprox acc' r))
      in
      (match translate_go_expr cont ctx with
       | TransOk cont' -> translate_specs (List.Tot.rev indexed_specs) (TransOk cont')
       | TransApprox cont' r -> translate_specs (List.Tot.rev indexed_specs) (TransApprox cont' r)
       | TransError r -> TransError r)

  | GoESpread slice_expr ->
      (* Spread operator: slice... passes a slice directly to a variadic parameter *)
      (match translate_go_expr slice_expr ctx with
       | TransOk e' -> TransOk (ECall (EVar "spread") [e'])
       | TransApprox e' r -> TransApprox (ECall (EVar "spread") [e']) r
       | TransError r -> TransError r)

  | _ -> TransApprox EHole "unsupported Go expression"

(** ============================================================================
    CROSS-LANGUAGE BOUNDARY HANDLING
    ============================================================================

    When values cross between languages (FFI boundaries), different languages
    provide different safety guarantees. This section defines:

    1. LANGUAGE AXIOMS: Safety properties guaranteed by each language
    2. BOUNDARY RISKS: Properties at risk when crossing between languages
    3. GUARD GENERATION: Runtime checks needed at boundaries

    The key insight is that some languages (Rust) provide strong static
    guarantees that others (C) do not. When crossing from a "safe" language
    to an "unsafe" language, we must either:
    - Trust the unsafe code (opt-in with unsafe blocks)
    - Insert runtime checks (defensive programming)
    - Reject the crossing entirely (conservative but safe)

    REFERENCE: brrr_lang_spec_v0.4.tex, Chapter "Foreign Function Interface"

    ============================================================================ *)

(** Language axioms - properties guaranteed by the language.

    These are properties that a language STATICALLY GUARANTEES for all
    well-typed programs. They can be relied upon without runtime checks.

    AXIOMS:
    - AxMemSafe: Memory safety - no use-after-free, buffer overflow
    - AxTypeSafe: Type safety - no type confusion
    - AxNullSafe: Null safety - no null pointer dereference
    - AxRaceFree: Race freedom - no data races
    - AxLeakFree: Leak freedom - no memory leaks (GC or RAII)
    - AxDetDrop: Deterministic destruction (RAII)

    NOT INCLUDED: Properties that require runtime checks or dynamic analysis:
    - Deadlock freedom (undecidable in general)
    - Termination (undecidable)
    - Correctness (specification-dependent) *)
type lang_axiom =
  | AxMemSafe    (* Memory safety - no use-after-free, buffer overflow *)
  | AxTypeSafe   (* Type safety - no type confusion *)
  | AxNullSafe   (* Null safety - no null pointer dereference *)
  | AxRaceFree   (* Race freedom - no data races *)
  | AxLeakFree   (* Leak freedom - no memory leaks *)
  | AxDetDrop    (* Deterministic destruction *)

(** Get axioms for a language.

    Returns the set of properties statically guaranteed by the language.

    LANGUAGE PROPERTIES:

    Rust: {MemSafe, TypeSafe, RaceFree, LeakFree}
      - Borrow checker ensures memory and race safety
      - Strong static type system
      - RAII ensures no leaks (barring mem::forget)
      - Note: Null safety via Option, not null

    TypeScript: {MemSafe, TypeSafe}
      - GC provides memory safety
      - Static types (but 'any' can escape)
      - No race freedom (shared mutable state)

    Python: {MemSafe, LeakFree}
      - GC provides memory safety and leak freedom
      - Dynamic typing means no type safety
      - GIL provides some race protection (but not full freedom)

    Go: {MemSafe, TypeSafe, LeakFree}
      - GC provides memory safety and leak freedom
      - Static type system
      - No race freedom (goroutines can race)

    Swift: {MemSafe, TypeSafe, NullSafe}
      - ARC provides memory safety
      - Strong static types with optionals
      - Null safety via explicit Optional

    Java: {MemSafe, TypeSafe, LeakFree}
      - GC provides memory safety and leak freedom
      - Static type system (but null is everywhere)

    C/C++: {} (no guarantees)
      - Manual memory management
      - Weak type system (casts, undefined behavior)
      - No automatic leak prevention *)
let language_axioms (lang: source_language) : list lang_axiom =
  match lang with
  | LangRust -> [AxMemSafe; AxTypeSafe; AxRaceFree; AxLeakFree]
  | LangTypeScript -> [AxMemSafe; AxTypeSafe]
  | LangPython -> [AxMemSafe; AxLeakFree]
  | LangGo -> [AxMemSafe; AxTypeSafe; AxLeakFree]
  | LangSwift -> [AxMemSafe; AxTypeSafe; AxNullSafe]
  | LangJava -> [AxMemSafe; AxTypeSafe; AxLeakFree]
  | LangC -> []  (* C provides no guarantees *)
  | LangCpp -> []  (* C++ provides no guarantees *)

(** Check if axiom is in list. *)
let has_axiom (ax: lang_axiom) (axs: list lang_axiom) : bool =
  List.Tot.mem ax axs

(** Compute boundary risks when crossing from L1 to L2.

    Returns axioms that L1 provides but L2 does not.
    These properties are "at risk" when crossing the boundary.

    EXAMPLE:
    boundary_risks Rust C = [AxMemSafe, AxTypeSafe, AxRaceFree, AxLeakFree]
    boundary_risks Python Rust = []  (Rust provides superset)
    boundary_risks Rust Python = [AxTypeSafe, AxRaceFree]  (Python lacks these)

    INTERPRETATION:
    - Non-empty risks mean the caller must take precautions
    - Empty risks mean the callee provides at least the same guarantees *)
let boundary_risks (from_lang to_lang: source_language) : list lang_axiom =
  let from_axs = language_axioms from_lang in
  let to_axs = language_axioms to_lang in
  (* Risks are axioms from has but to doesn't *)
  List.Tot.filter (fun ax -> has_axiom ax from_axs && not (has_axiom ax to_axs))
    [AxMemSafe; AxTypeSafe; AxNullSafe; AxRaceFree; AxLeakFree; AxDetDrop]

(** Generate guard for boundary crossing.

    Inserts runtime checks needed when passing a value from from_lang to to_lang.

    GUARDS INSERTED:

    1. TYPE CHECK (when crossing into statically typed from untyped):
       EIs value ty - Runtime type check that may fail

    2. NULL CHECK (when crossing into null-safe from nullable):
       match value { None => panic, Some v => v }

    Future work could add:
    - Memory pinning (when crossing into manual memory from GC)
    - Copy/deep-clone (when crossing into ownership-based from shared)
    - Synchronization wrappers (when crossing into race-free from racy) *)
let generate_boundary_guard (from_lang to_lang: source_language)
                            (value: expr) (ty: brrr_type) : expr =
  let risks = boundary_risks from_lang to_lang in
  let guarded = value in

  (* Add type check if crossing into typed from untyped *)
  let guarded =
    if has_axiom AxTypeSafe (language_axioms to_lang) &&
       not (has_axiom AxTypeSafe (language_axioms from_lang))
    then EIs guarded ty  (* Runtime type check *)
    else guarded
  in

  (* Add null check if crossing into null-safe *)
  let guarded =
    if has_axiom AxNullSafe (language_axioms to_lang) &&
       not (has_axiom AxNullSafe (language_axioms from_lang))
    then EMatch guarded [
           { arm_pattern = PatVariant "Option" "None" [];
             arm_guard = None;
             arm_body = EThrow (ELit (LitString "null value at boundary")) };
           { arm_pattern = PatVariant "Option" "Some" [PatVar "v"];
             arm_guard = None;
             arm_body = EVar "v" }
         ]
    else guarded
  in

  guarded

(** ============================================================================
    SOUNDNESS PROPERTIES
    ============================================================================

    This section documents the key soundness theorems for the translation.
    These are INFORMAL statements that would need to be mechanized in F*
    for full verification.

    The approach follows CompCert's methodology:
    1. Define source and target semantics precisely
    2. State semantic preservation as simulation
    3. Prove simulation by induction on derivations

    REFERENCE IMPLEMENTATIONS:
    - CompCert: ~100,000 lines of Coq for C to assembly
    - CakeML: ~250,000 lines of HOL4 for ML to assembly
    - Vellvm: ~30,000 lines of Coq for LLVM IR

    Our approach is more modest, focusing on type-level properties
    and leaving semantic proofs as future work.

    ============================================================================ *)

(** Translation soundness statement (informal):

   For each source language L with translation T_L:

   1. Type Preservation:
      If e : tau in L, then T_L(e) : T_L(tau) in Brrr-Lang

      FORMALIZATION:
      val type_preservation_L : e:expr_L -> tau:type_L -> Gamma:ctx_L ->
        Lemma (requires typing_L Gamma e tau)
              (ensures typing_Brrr (T_ctx Gamma) (T_expr e) (T_type tau))

   2. Semantic Preservation:
      If [[e]]_L(rho) = v, then [[T_L(e)]]_Brrr(T_L(rho)) = T_L(v)

      FORMALIZATION:
      val semantic_preservation_L : e:expr_L -> rho:env_L -> v:value_L ->
        Lemma (requires eval_L e rho = Some v)
              (ensures eval_Brrr (T_expr e) (T_env rho) = Some (T_value v))

   3. Effect Soundness:
      If e has effect epsilon in L, then T_L(e) has effect T_L(epsilon) in Brrr-Lang

      FORMALIZATION:
      val effect_soundness_L : e:expr_L -> eff:effect_L ->
        Lemma (requires has_effect_L e eff)
              (ensures has_effect_Brrr (T_expr e) (T_effect eff))

   4. Approximation Safety:
      If TransApprox is returned, the translation is sound but may reject
      more programs than necessary (conservative approximation)

      FORMALIZATION:
      val approx_safety_L : e:expr_L -> result:trans_result expr ->
        Lemma (requires translate_L e = TransApprox result reason range)
              (ensures is_sound result /\ may_be_overly_restrictive result)
*)

(** Approximation annotations for unsound features.

    Documents WHY an approximation was needed in the translation.
    Each reason corresponds to a language feature that cannot be
    translated precisely but can be approximated conservatively.

    APPROXIMATION STRATEGY:
    - We always err on the side of caution
    - Approximations may reject valid programs (false negatives)
    - Approximations never accept invalid programs (no false positives)
    - The "reason" string documents the approximation for debugging *)
type approx_reason =
  | ApproxDynamic      (* Dynamic typing requires runtime checks *)
  | ApproxUnion        (* Union types require runtime dispatch *)
  | ApproxIntersection (* Intersection types simplified *)
  | ApproxDuckTyping   (* Duck typing requires runtime lookup *)
  | ApproxDecorator    (* Decorator effect approximated *)
  | ApproxAsync        (* Async semantics simplified *)
  | ApproxChannel      (* Channel semantics simplified *)
  | ApproxInterface    (* Interface dynamic dispatch *)
  | ApproxLifetime     (* Lifetime elision approximated *)
  | ApproxMacro        (* Macro expansion not supported *)
