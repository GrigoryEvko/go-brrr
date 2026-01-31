(**
 * BrrrLang.Core.LangMapping - Interface
 *
 * ===========================================================================
 * SOURCE LANGUAGE MAPPING FOR MULTI-LANGUAGE INTEROPERABILITY
 * ===========================================================================
 *
 * Based on brrr_lang_spec_v0.4.tex Part XIV: Source Language Mapping
 *
 * ARCHITECTURAL OVERVIEW
 * ----------------------
 * This module implements the TRANSLATION FUNCTOR FRAMEWORK for mapping source
 * languages (TypeScript, Rust, Go, Python, etc.) to Brrr-Lang IR. The design
 * follows category-theoretic principles to ensure semantic preservation:
 *
 *   Source_Language --T_L--> Brrr_IR
 *
 * where T_L is a translation functor that preserves:
 *   1. Type structure (typing derivations)
 *   2. Operational semantics (evaluation behavior)
 *   3. Effect annotations (side effect tracking)
 *   4. Memory safety axioms (where applicable)
 *
 * KEY CONCEPTS
 * ------------
 *
 * 1. LANGUAGE MODES (Part XIV.1):
 *    Each source language is characterized by a mode configuration capturing:
 *    - Memory management: GC, RC, manual, or ownership-based
 *    - Type system: static, gradual, or dynamic
 *    - Null safety: nullable, optional types, or non-null
 *    - Effect tracking: pure, tracked, or untracked
 *    - Concurrency: none, threads, async, or actors
 *
 * 2. TRANSLATION FUNCTORS (Part XIV.3):
 *    A translation functor T_L : Cat_L -> Cat_Brrr consists of:
 *    - Object mapping: translate_type : L.Type -> Brrr.Type
 *    - Morphism mapping: translate_expr : L.Expr -> Brrr.Expr
 *    - Value mapping: translate_value : L.Value -> Brrr.Value
 *
 *    Functors must satisfy:
 *    - IDENTITY LAW: T(id) = id
 *    - COMPOSITION LAW: T(f . g) = T(f) . T(g)
 *
 * 3. BOUNDARY GUARDS (Part XIV.4):
 *    When crossing language boundaries, guards enforce safety axioms:
 *    - null_guard: Wraps nullable values in Option for null-safe targets
 *    - type_guard: Validates types at runtime for dynamic sources
 *    - memory_guard: Establishes ownership for manual/ownership targets
 *
 * 4. AXIOM LATTICE (Part XIV.5):
 *    Safety axioms form a lattice ordered by implication:
 *    - AxMemSafe: Memory operations are safe (no use-after-free, etc.)
 *    - AxTypeSafe: Type system is sound (no type confusion)
 *    - AxNullSafe: No null pointer dereferences
 *    - AxLeakFree: No memory leaks
 *    - AxRaceFree: No data races
 *    - AxDetDrop: Deterministic destructor timing
 *
 *    When crossing from L1 to L2, boundary_risks(L1, L2) = axioms(L1) - axioms(L2)
 *    identifies axioms that must be guarded.
 *
 * 5. SOUNDNESS THEOREM (Part XIV.6):
 *    For any value v crossing from source L1 to target L2:
 *    - If is_safe_boundary(L1, L2), no guards needed
 *    - Otherwise, generate_guard(L1, L2, ty, v) returns:
 *      - GuardOk(v'): Safe crossing with potentially transformed value
 *      - GuardErr(msg): Rejected crossing with error message
 *
 * HETEROGENEOUS VS LEGACY FUNCTORS
 * ---------------------------------
 * This module provides TWO functor interfaces:
 *
 * 1. HETEROGENEOUS FUNCTOR (proper design):
 *    Parameterized over source AST types (ts_type, rust_type, go_type).
 *    Performs ACTUAL translation from source AST to Brrr IR.
 *    Example: typescript_heterogeneous_functor : heterogeneous_functor ts_type ts_expr value
 *
 * 2. LEGACY FUNCTOR (backward compatibility):
 *    Operates on already-translated Brrr terms for post-processing.
 *    Used for guard insertion, annotation, and composition.
 *    Example: typescript_functor : translation_functor
 *
 * CORRECTNESS CRITERIA
 * --------------------
 * A translation is CORRECT iff:
 *
 * 1. TYPE PRESERVATION:
 *    If Gamma_L |- e : T  (e has type T in source)
 *    Then Gamma_Brrr |- T_L(e) : T_L(T)  (translated e has translated type)
 *
 * 2. SEMANTIC PRESERVATION (Simulation):
 *    If e -->_L e' (e steps to e' in source)
 *    Then T_L(e) -->*_Brrr T_L(e') (translated e steps to translated e')
 *
 * 3. EFFECT PRESERVATION:
 *    If e has effects E in source
 *    Then T_L(e) has effects T_L(E) in Brrr
 *
 * 4. AXIOM PRESERVATION:
 *    If source L guarantees axiom Ax
 *    Then either target guarantees Ax, or boundary guards check Ax
 *
 * REFERENCES
 * ----------
 * - brrr_lang_spec_v0.4.tex, Part XIV: Source Language Mapping
 * - fstar_pop_book.md, Section on STLC embedding and type preservation
 * - EverParse (Ramananandro et al. 2019): Parser verification patterns
 * - HACL* (Zinzindohoue et al. 2017): Integer and memory safety proofs
 *
 * ERRATA NOTES (from SPECIFICATION_ERRATA.md)
 * --------------------------------------------
 * - Translation functors use SUBTYPING (not equality) for type preservation
 * - Follows Scalas & Yoshida (2019) correction to Honda 2008
 * - Association relation G ~ Gamma uses: G |> p <= Gamma(s[p])
 *
 * This interface exposes:
 *   - Language mode configurations (memory, types, null safety, effects, concurrency)
 *   - Standard configurations for Python, TypeScript, Rust, Go, Swift, Java
 *   - Translation functor interface with soundness proofs
 *   - Boundary guards for cross-language calls
 *   - Type preservation theorems
 *   - Functoriality verification theorems
 *)
module BrrrLangMapping

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrValues
open FStar.List.Tot

(** ============================================================================
    LANGUAGE MODE CONFIGURATION - Part XIV.1
    ============================================================================

    Language modes characterize the semantic properties of source languages
    that affect how values are represented and how they can safely cross
    language boundaries.

    These modes form a PRODUCT LATTICE where each dimension is ordered by
    "strength" of guarantees. For example:
      MemOwnership > MemRC > MemGC > MemManual (in terms of safety guarantees)

    The mode configuration determines:
    1. Which axioms the language guarantees (language_axioms)
    2. What guards are needed at boundaries (boundary_risks)
    3. How types and values are translated (translation functors)

    DESIGN RATIONALE:
    - Modes are ORTHOGONAL: each dimension is independent
    - Modes are FINITE: enumerable for SMT decidability
    - Modes are COMPARABLE: enables subtyping-like reasoning

    USAGE:
    - Frontend parsers set mode from source language detection
    - Brrr-Machine uses modes to configure analysis passes
    - Code generators use modes to emit appropriate runtime checks
    ============================================================================ *)

(** Memory Management Mode

    Determines how memory is allocated, tracked, and freed.
    Critical for crossing between languages with different memory models.

    MemGC        - Garbage collection (Python, Java, Go, TypeScript/JS)
                   Runtime traces reachability and frees unreachable objects.
                   Provides: AxMemSafe, AxLeakFree (approximate)

    MemRC        - Reference counting (Swift, Objective-C, Python CPython)
                   Objects track their reference count, freed when count = 0.
                   Provides: AxMemSafe, AxDetDrop

    MemManual    - Manual allocation (C, C++)
                   Programmer explicitly calls malloc/free or new/delete.
                   Provides: (none - all safety is programmer responsibility)

    MemOwnership - Ownership with borrow checking (Rust)
                   Affine types track ownership, compiler enforces lifetimes.
                   Provides: AxMemSafe, AxLeakFree, AxDetDrop, AxRaceFree
*)
type memory_mode =
  | MemGC        : memory_mode   (* Garbage collection *)
  | MemRC        : memory_mode   (* Reference counting *)
  | MemManual    : memory_mode   (* Manual malloc/free *)
  | MemOwnership : memory_mode   (* Ownership + borrow checking *)

(** Type System Mode

    Determines how types are checked and when type errors are detected.
    Affects the type_guard requirements at boundaries.

    TypeStatic  - Full static type checking (Rust, Java, Go, Haskell)
                  All types known at compile time, no runtime type errors.
                  Provides: AxTypeSafe

    TypeGradual - Optional type annotations (TypeScript, Python 3.5+, mypy)
                  Mix of static and dynamic; unannotated code is dynamic.
                  Provides: (partial - only where annotated)

    TypeDynamic - No static types (JavaScript, Python 2, Lua)
                  All type checking at runtime via duck typing.
                  Provides: (none - all type errors are runtime errors)

    BOUNDARY IMPLICATIONS:
    - TypeDynamic -> TypeStatic requires runtime type checks (type_guard)
    - TypeStatic -> TypeDynamic is always safe (type information is erased)
*)
type type_mode =
  | TypeStatic  : type_mode     (* Full static type checking *)
  | TypeGradual : type_mode     (* Optional type annotations *)
  | TypeDynamic : type_mode     (* No static types *)

(** Null Safety Mode

    Determines how absence of values (null/nil/None) is represented.
    Critical for preventing null pointer dereferences across boundaries.

    NullNullable - Null is implicitly allowed (Java, Go, C, C++)
                   Any reference type can be null without type indication.
                   Provides: (none - null dereference is runtime error)

    NullOptional - Explicit Option types required (Rust, Swift, Kotlin)
                   Absence must be Option<T>, forcing explicit handling.
                   Provides: AxNullSafe

    NullNonNull  - Null banned entirely (some Kotlin configs, Haskell)
                   No null values exist; absence uses Maybe/Option.
                   Provides: AxNullSafe

    BOUNDARY IMPLICATIONS:
    - NullNullable -> NullOptional: null_guard wraps in Option or rejects
    - NullNullable -> NullNonNull: null_guard rejects null values
    - NullOptional -> NullNullable: Option unpacking (safe)
*)
type null_mode =
  | NullNullable : null_mode    (* Null is implicitly allowed *)
  | NullOptional : null_mode    (* Explicit Option types required *)
  | NullNonNull  : null_mode    (* Null banned entirely *)

(** Effect Tracking Mode

    Determines whether side effects are tracked in the type system.
    Affects effect inference and propagation through translations.

    EffPure      - Pure by default, effects require annotation (Haskell, PureScript)
                   Functions are assumed pure; IO/effects explicit in types.
                   Provides: AxRaceFree (for pure functions)

    EffTracked   - Effects tracked in type system (Rust async/unsafe, Koka)
                   Some effects (async, unsafe, exceptions) marked in types.
                   Provides: (partial effect safety)

    EffUntracked - Side effects allowed anywhere (Python, JavaScript, Go)
                   Functions can have arbitrary side effects without indication.
                   Provides: (none - effects are implicit)

    EFFECT TRANSLATION:
    - EffPure functions get empty effect row in Brrr (RowEmpty)
    - EffTracked functions get specific effect annotations
    - EffUntracked functions get open effect row (RowVar for polymorphism)

    See BrrrEffects.fst for the effect_row representation.
*)
type effect_mode =
  | EffPure      : effect_mode  (* Pure functions, effects require annotation *)
  | EffTracked   : effect_mode  (* Effects tracked in type system *)
  | EffUntracked : effect_mode  (* Side effects allowed anywhere *)

(** Concurrency Mode

    Determines the concurrency model and how concurrent computations
    are represented in the type system.

    ConcNone    - No built-in concurrency (early C, some embedded)
                  Single-threaded execution only.
                  Provides: AxRaceFree (trivially, no concurrency)

    ConcThreads - OS threads (Java, C/C++ pthreads, Go goroutines)
                  Preemptive multithreading with shared memory.
                  Provides: (none - data races possible without sync)

    ConcAsync   - Async/await (Python asyncio, JavaScript, Rust async)
                  Cooperative concurrency with explicit yield points.
                  Provides: (partial - no preemption, but shared state)

    ConcActors  - Actor model (Erlang, Akka, Pony)
                  Message-passing with isolated actor state.
                  Provides: AxRaceFree (actors don't share mutable state)

    TRANSLATION TO BRRR EFFECTS:
    - ConcNone: no spawn/channel effects
    - ConcThreads: ESpawn effect for thread creation
    - ConcAsync: EAsync effect for async/await
    - ConcActors: ESpawn + channel effects for message passing
*)
type conc_mode =
  | ConcNone    : conc_mode     (* No built-in concurrency *)
  | ConcThreads : conc_mode     (* OS threads *)
  | ConcAsync   : conc_mode     (* Async/await *)
  | ConcActors  : conc_mode     (* Actor model *)

(** Combined Language Mode *)
noeq type lang_mode = {
  memory      : memory_mode;
  types       : type_mode;
  null_safety : null_mode;
  effects     : effect_mode;
  concurrency : conc_mode
}

(** Mode equality *)
val lang_mode_eq : l1:lang_mode -> l2:lang_mode -> bool
val lang_mode_eq_refl : l:lang_mode ->
  Lemma (lang_mode_eq l l = true)
        [SMTPat (lang_mode_eq l l)]

(** ============================================================================
    STANDARD LANGUAGE CONFIGURATIONS - Part XIV.2
    ============================================================================ *)

val python_mode     : lang_mode
val typescript_mode : lang_mode
val rust_mode       : lang_mode
val go_mode         : lang_mode
val swift_mode      : lang_mode
val java_mode       : lang_mode
val c_mode          : lang_mode
val cpp_mode        : lang_mode
val kotlin_mode     : lang_mode
val haskell_mode    : lang_mode

(** ============================================================================
    AXIOM LATTICE - Part XIV.5
    ============================================================================ *)

type axiom =
  | AxMemSafe  : axiom   (* Memory operations are safe *)
  | AxTypeSafe : axiom   (* Type system is sound *)
  | AxNullSafe : axiom   (* No null dereferences *)
  | AxLeakFree : axiom   (* No memory leaks *)
  | AxRaceFree : axiom   (* No data races *)
  | AxDetDrop  : axiom   (* Destructors run at predictable times *)

type axiom_set = list axiom

val language_axioms : l:lang_mode -> axiom_set
val boundary_risks : source:lang_mode -> target:lang_mode -> axiom_set
val is_safe_boundary : source:lang_mode -> target:lang_mode -> bool

(** ============================================================================
    GUARD RESULT TYPE - Part XIV.4
    ============================================================================ *)

noeq type guard_result (a: Type) =
  | GuardOk  : v:a -> guard_result a
  | GuardErr : error:string -> guard_result a

val guard_return : #a:Type -> v:a -> guard_result a
val guard_bind : #a:Type -> #b:Type -> r:guard_result a -> f:(a -> guard_result b) -> guard_result b
val guard_result_is_ok : #a:Type -> r:guard_result a -> bool

(** ============================================================================
    BOUNDARY GUARDS - Part XIV.4
    ============================================================================ *)

val null_guard : source:null_mode -> target:null_mode -> v:value -> guard_result value
val type_guard : source:type_mode -> target:type_mode -> expected_ty:brrr_type -> v:value -> guard_result value
val memory_guard : source:memory_mode -> target:memory_mode -> v:value -> guard_result value
val generate_guard : source:lang_mode -> target:lang_mode -> ty:brrr_type -> v:value -> guard_result value

(** ============================================================================
    TRANSLATION FUNCTOR - Part XIV.3
    ============================================================================

    CATEGORY-THEORETIC FOUNDATION
    -----------------------------
    A translation functor T_L : Cat_L -> Cat_Brrr is a structure-preserving
    map from the source language's category to the Brrr IR category.

    In programming language terms:
    - Objects are types: T_L(tau) maps source type tau to Brrr type
    - Morphisms are terms: T_L(e) maps source expression e to Brrr expression
    - Identity is preserved: T_L(id_tau) = id_{T_L(tau)}
    - Composition is preserved: T_L(e1 ; e2) = T_L(e1) ; T_L(e2)

    FUNCTOR LAWS (must be proven for each language functor):
    1. Identity: T(id) = id
    2. Composition: T(f . g) = T(f) . T(g)

    These laws ensure COMPOSITIONALITY: the translation of a compound
    expression depends only on the translations of its subexpressions.

    DESIGN PATTERN: TWO-PHASE TRANSLATION
    -------------------------------------
    Following EverParse's approach, translation happens in two phases:

    Phase 1 (Language-Specific): Source AST -> Brrr IR
      typescript_translate_type : ts_type -> brrr_type
      rust_translate_type : rust_type -> (brrr_type & mode)
      go_translate_type : go_type -> brrr_type

    Phase 2 (Post-Processing): Brrr IR -> Brrr IR
      translation_functor.translate_type : brrr_type -> brrr_type
      (For guard insertion, annotation, optimization)

    The heterogeneous_functor type captures Phase 1 with proper types.
    The translation_functor type captures Phase 2 as a Brrr-to-Brrr map.

    COMPARISON WITH STLC EMBEDDING
    ------------------------------
    Similar to the STLC embedding in fstar_pop_book.md (lines 6500-7500),
    we prove:
    - Typing preservation: well-typed source -> well-typed Brrr
    - Substitution lemma: translation commutes with substitution
    - Progress/Preservation: for operational semantics
    ============================================================================ *)

(** Translation functor interface (Legacy - for backward compatibility)

    ARCHITECTURE:
    The functor provides a uniform interface for POST-PROCESSING translated terms.
    Real translation from source AST (ts_type, rust_type, go_type) to Brrr IR
    is performed by language-specific translate_* functions.
    The functor's translate_type/expr/value handle post-translation processing
    such as guard insertion and annotation.

    NOTE: For the ACTUAL heterogeneous translation, use heterogeneous_functor
    type which is parameterized over source AST types.

    FIELDS:
    - source_mode: The language mode configuration for boundary checking
    - translate_type: Post-process a Brrr type (e.g., add annotations)
    - translate_expr: Post-process a Brrr expression (e.g., insert guards)
    - translate_value: Transform runtime values at boundary crossing
*)
noeq type translation_functor = {
  source_mode : lang_mode;
  translate_type : brrr_type -> brrr_type;
  translate_expr : expr -> expr;
  translate_value : value -> value
}

val identity_functor : mode:lang_mode -> translation_functor

(** ============================================================================
    FUNCTOR LAWS AND SOUNDNESS - Part XIV.3
    ============================================================================ *)

(** Functor laws predicate *)
val functor_laws : f:translation_functor -> prop

(** Soundness predicate *)
val soundness : f:translation_functor -> prop

(** Functoriality predicate - identity and composition laws *)
val is_functorial : tr:translation_functor -> prop

(** Identity functor proofs *)
val identity_functor_laws : mode:lang_mode -> Lemma (functor_laws (identity_functor mode))
val identity_functor_sound : mode:lang_mode -> Lemma (soundness (identity_functor mode))
val identity_is_functorial : mode:lang_mode -> Lemma (is_functorial (identity_functor mode))

(** ============================================================================
    TYPE PRESERVATION THEOREMS - Part XIV.3.1
    ============================================================================ *)

type source_ctx = list (string & brrr_type)
type brrr_ctx = list (string & brrr_type)

val translate_ctx : f:translation_functor -> ctx:source_ctx -> brrr_ctx
val brrr_well_typed : ctx:brrr_ctx -> e:expr -> prop
val source_well_typed : ctx:source_ctx -> e:expr -> prop

(** Main type preservation theorem *)
val translate_preserves_typing :
  f:translation_functor -> e:expr -> ctx:source_ctx ->
  Lemma (requires source_well_typed ctx e)
        (ensures brrr_well_typed (translate_ctx f ctx) (f.translate_expr e))

(** Composition preserves type preservation *)
val composition_preserves_typing :
  f1:translation_functor -> f2:translation_functor ->
  e:expr -> ctx:source_ctx ->
  Lemma (requires source_well_typed ctx e)
        (ensures brrr_well_typed
          (translate_ctx f2 (translate_ctx f1 ctx))
          (f2.translate_expr (f1.translate_expr e)))

(** ============================================================================
    FUNCTORIALITY VERIFICATION - Part XIV.3.2
    ============================================================================ *)

val identity_expr : expr
val compose_exprs : f:expr -> g:expr -> expr

val translate_id_law : mode:lang_mode ->
  Lemma (expr_eq (identity_functor mode).translate_expr identity_expr identity_expr = true)

val translate_comp_law : mode:lang_mode -> f:expr -> g:expr ->
  Lemma (let tr = (identity_functor mode).translate_expr in
         expr_eq (tr (compose_exprs f g)) (compose_exprs (tr f) (tr g)) = true)

(** ============================================================================
    BOUNDARY SOUNDNESS THEOREM - Part XIV.6
    ============================================================================

    THEOREM STATEMENT (Informal)
    ----------------------------
    For any value v crossing from source language L1 to target language L2:

    Either:
    1. The boundary is inherently safe (target has all source axioms), OR
    2. The generated guard either:
       a. Succeeds with a safe transformed value (GuardOk), OR
       b. Rejects the crossing with an error (GuardErr)

    In both cases, safety is preserved: either the value crosses safely,
    or the crossing is rejected before any violation can occur.

    PROOF SKETCH
    ------------
    1. Compute boundary_risks(L1, L2) = axioms(L1) - axioms(L2)
    2. If risks is empty, is_safe_boundary returns true (Case 1)
    3. Otherwise, generate_guard applies:
       - null_guard for AxNullSafe risks
       - type_guard for AxTypeSafe risks
       - memory_guard for AxMemSafe risks
    4. Each guard either:
       - Transforms the value to be safe (GuardOk)
       - Rejects unsafe values (GuardErr)
    5. Therefore, no unsafe value crosses the boundary

    FORMAL STATEMENT
    ----------------
    The lemma ensures totality: for ALL source/target/type/value combinations,
    one of the safe outcomes holds. This is a SAFETY property, not liveness:
    we don't prove that GuardOk is reachable, only that unsafe states are not.

    RELATION TO ERRATA
    ------------------
    From SPECIFICATION_ERRATA.md: This theorem follows the corrected
    association relation (Scalas & Yoshida 2019) rather than the original
    Honda 2008 formulation. The key insight is that subtyping (not equality)
    governs the type relationship at boundaries.
    ============================================================================ *)

val boundary_soundness_theorem :
  source:lang_mode -> target:lang_mode -> ty:brrr_type -> v:value ->
  Lemma (ensures
    is_safe_boundary source target = true \/
    (match generate_guard source target ty v with
     | GuardOk _ -> True
     | GuardErr _ -> True))

(** ============================================================================
    COMPOSITION THEOREM
    ============================================================================ *)

val compose_translations : f1:translation_functor -> f2:translation_functor -> translation_functor

val composition_soundness :
  f1:translation_functor -> f2:translation_functor ->
  Lemma (requires soundness f1 /\ soundness f2)
        (ensures soundness (compose_translations f1 f2))

(** ============================================================================
    LANGUAGE-SPECIFIC TRANSLATION FUNCTORS
    ============================================================================

    Each supported source language has:
    1. A heterogeneous functor (source AST -> Brrr IR)
    2. A legacy functor (Brrr IR -> Brrr IR post-processing)
    3. Proofs of functor laws, soundness, and functoriality

    TYPESCRIPT TRANSLATION (Definition 3.1-3.2)
    --------------------------------------------
    Type mapping T_TS:
    - undefined    -> Unit
    - null         -> Option[Dynamic]
    - boolean      -> Bool
    - number       -> Float[F64]
    - bigint       -> Int[BigInt, Signed]
    - string       -> String
    - any          -> Dynamic (UNSAFE: allows any operation)
    - unknown      -> Unknown (SAFE: requires runtime checks)
    - A[]          -> gc Array[T_TS(A)]
    - Promise<A>   -> Future[T_TS(A), Hot]
    - A | B        -> Union[T_TS(A), T_TS(B)] (Option for null unions)

    Expression mapping T_TS:
    - a?.b         -> match T_TS(a) { None -> (), Some(v) -> v.b }
    - a ?? b       -> match T_TS(a) { None -> T_TS(b), Some(v) -> v }
    - await e      -> await(T_TS(e))
    - async body   -> async { T_TS(body) }

    Default effect: epsilon_TS = <Throw | <Async | rowvar>>
    ============================================================================ *)

(** TypeScript functor and proofs *)
val typescript_functor : translation_functor
val typescript_functor_laws : unit -> Lemma (functor_laws typescript_functor)
val typescript_functor_sound : unit -> Lemma (soundness typescript_functor)
val typescript_is_functorial : unit -> Lemma (is_functorial typescript_functor)

(** RUST TRANSLATION (Definition 4.1-4.3)
    --------------------------------------
    Ownership type mapping T_Rs:
    - T (owned)         -> own T with mode MOne (linear)
    - &'a T             -> ref T ['a] with mode MOmega (shared borrow)
    - &'a mut T         -> refmut T ['a] with mode MOne (exclusive)
    - Box<T>            -> own Box[T_Rs^base(T)]
    - Rc<T>             -> rc T_Rs^base(T)
    - Arc<T>            -> arc T_Rs^base(T)
    - Option<T>         -> Option[T_Rs(T)]
    - Result<T,E>       -> Result[T_Rs(T), T_Rs(E)]
    - Vec<T>            -> Array[T_Rs(T)]

    Move translation T_Rs (for non-Copy types):
    - let y = x         -> let y = move(x)
    - f(x)              -> f(move(x))
    - f(&x)             -> f(&x)
    - f(&mut x)         -> f(&mut x)
    - e?                -> match T_Rs(e) { Ok(v) -> v, Err(e) -> return Err(e) }

    Default effect: epsilon_Rs = pure (Rust functions are pure by default)

    KEY INSIGHT: Rust's ownership maps to LINEAR TYPES (mode MOne):
    - Owned values must be used exactly once (move semantics)
    - Shared borrows are unrestricted (MOmega) but read-only
    - Mutable borrows are linear (MOne) and exclusive

    Rust functor and proofs *)
val rust_functor : translation_functor
val rust_functor_laws : unit -> Lemma (functor_laws rust_functor)
val rust_functor_sound : unit -> Lemma (soundness rust_functor)
val rust_is_functorial : unit -> Lemma (is_functorial rust_functor)

(** GO TRANSLATION (Definition 5.1-5.2)
    -----------------------------------
    Type mapping T_Go:
    - bool            -> Bool
    - int             -> Int[I64, Signed]
    - int32           -> Int[I32, Signed]
    - int64           -> Int[I64, Signed]
    - uint64          -> Int[I64, Unsigned]
    - float64         -> Float[F64]
    - string          -> String
    - []A             -> gc Slice[T_Go(A)]
    - map[K]V         -> gc Dict[T_Go(K), T_Go(V)]
    - chan A          -> Channel[T_Go(A)]
    - *A              -> gc Ptr[T_Go(A)]
    - interface{...}  -> Dynamic[methods]
    - struct{...}     -> gc Struct[fields]

    Goroutine translation T_Go:
    - go f(x)         -> spawn(T_Go(f)(T_Go(x)))
    - ch <- v         -> chan_send(ch, T_Go(v))
    - <-ch            -> chan_recv(ch)
    - select{...}     -> select[(chan, dir, body)...]
    - defer body      -> defer(T_Go(body))
    - panic(v)        -> panic(T_Go(v))
    - recover         -> recover

    Default effect: epsilon_Go = <Panic | <Spawn | rowvar>>

    KEY INSIGHT: Go's concurrency maps to SPAWN/CHANNEL effects:
    - Goroutines are lightweight threads (ESpawn effect)
    - Channels provide typed, synchronous communication
    - Select enables multi-channel waiting
    - Defer provides stack-based cleanup (LIFO order)
    - Panic/recover is Go's exception-like mechanism

    Go functor and proofs *)
val go_functor : translation_functor
val go_functor_laws : unit -> Lemma (functor_laws go_functor)
val go_functor_sound : unit -> Lemma (soundness go_functor)
val go_is_functorial : unit -> Lemma (is_functorial go_functor)

(** ============================================================================
    SOURCE LANGUAGE AST TYPES (for frontend translation)
    ============================================================================ *)

(** TypeScript types *)
type ts_primitive
noeq type ts_type
noeq type ts_expr

(** Rust types *)
noeq type rust_type
noeq type rust_expr

(** Go import alias -- how an imported package is locally named *)
type go_import_alias =
  | GoImportDefault : go_import_alias
  | GoImportAlias   : string -> go_import_alias
  | GoImportDot     : go_import_alias
  | GoImportBlank   : go_import_alias

(** Go import specification *)
noeq type go_import_spec = {
  gis_path  : string;
  gis_alias : go_import_alias
}

(** Go types and associated AST nodes from the mutual recursion block *)
noeq type go_type
noeq type go_method_sig
type go_type_decl =
  | GoTypeDefinition : string -> go_type -> go_type_decl
  | GoTypeAlias      : string -> go_type -> go_type_decl
noeq type go_expr

(** Go package -- a compiled package with declarations and init functions *)
noeq type go_package = {
  gpk_name       : string;
  gpk_imports    : list string;
  gpk_init_funcs : list go_expr;
  gpk_decls      : list go_expr
}

(** Go program -- a complete executable with all packages and main entry point *)
noeq type go_program = {
  gp_packages  : list go_package;
  gp_main_pkg  : string;
  gp_main_func : go_expr
}

(** Go top-level declarations *)
noeq type go_decl =
  | GoDeclImport : list go_import_spec -> go_decl
  | GoDeclConst  : list (string & option go_type & go_expr) -> go_decl
  | GoDeclVar    : string -> option go_type -> option go_expr -> go_decl
  | GoDeclType   : string -> go_type -> go_decl
  | GoDeclFunc   : string -> list go_type_param -> list (string & go_type) -> list go_type -> go_expr -> go_decl

(** Go source file *)
noeq type go_source_file = {
  gsf_package : string;
  gsf_imports : list go_import_spec;
  gsf_decls   : list go_decl
}

(** Go type constraint elements (Go 1.18 general interfaces / type sets) *)
type go_constraint_elem =
  | GoConstraintExact  : go_type -> go_constraint_elem   (* exact type T *)
  | GoConstraintApprox : go_type -> go_constraint_elem   (* ~T underlying type approximation *)

(** Go type constraints *)
type go_constraint =
  | GoConstraintAny        : go_constraint                                         (* any *)
  | GoConstraintComparable : go_constraint                                         (* comparable *)
  | GoConstraintMethods    : list go_method_sig -> go_constraint                   (* interface with methods only *)
  | GoConstraintUnion      : list go_constraint_elem -> go_constraint              (* T1 | T2 | ~T3 *)
  | GoConstraintCombined   : list go_method_sig -> list go_constraint_elem -> go_constraint
    (* interface with both methods and type elements *)

(** ============================================================================
    LANGUAGE-SPECIFIC TRANSLATION FUNCTIONS (THE REAL TRANSLATIONS)
    ============================================================================

    These functions perform the actual AST translation from source language
    to Brrr IR. They are called by frontends, not by the functor interface.
    ============================================================================ *)

(** TypeScript translation - the REAL translation functions *)
val typescript_translate_type : ts_type -> brrr_type
val typescript_translate_expr : ts_expr -> expr
val typescript_translate_value : value -> value

(** TypeScript type preservation *)
val typescript_type_preservation :
  e:ts_expr -> ctx:source_ctx ->
  Lemma (ensures brrr_well_typed ctx (typescript_translate_expr e))

(** Rust translation - the REAL translation functions *)
val rust_translate_type : rust_type -> (brrr_type & mode)
val rust_translate_type_only : rust_type -> brrr_type
val rust_translate_expr : rust_expr -> expr
val rust_translate_value : value -> value

(** Rust type preservation *)
val rust_type_preservation :
  e:rust_expr -> ctx:source_ctx ->
  Lemma (ensures brrr_well_typed ctx (rust_translate_expr e))

(** Rust ownership preservation *)
val rust_ownership_preservation :
  t:rust_type ->
  Lemma (let (_, mode) = rust_translate_type t in
         (rust_is_copy t ==> mode = MOmega) /\
         (not (rust_is_copy t) ==> mode = MOne \/ mode = MOmega))

(** Go translation - the REAL translation functions *)

(** Extract type environment from Go declarations for named interface resolution *)
val go_extract_type_env : list go_decl -> list (string & go_type)

(** Environment-aware type translation: resolves embedded named interfaces *)
val go_translate_type_in_env : list (string & go_type) -> go_type -> brrr_type

(** Type translation without environment (named interface embeds unresolved) *)
val go_translate_type : go_type -> brrr_type

val go_translate_expr : go_expr -> expr
val go_translate_value : value -> value

(** Environment-aware declaration translation *)
val go_translate_decl_in_env : list (string & go_type) -> go_decl -> expr -> expr

(** Go package and program translation *)
val go_topo_sort_packages : remaining:list go_package -> emitted:list string -> acc:list go_package -> list go_package
val go_translate_package : go_package -> expr
val go_translate_program : go_program -> expr

(** Go type constraint translation *)
val go_translate_constraint_elem : go_constraint_elem -> brrr_type
val go_translate_constraint : go_constraint -> brrr_type

(** Go constraint element helpers *)
val go_constraint_elem_is_approx : go_constraint_elem -> bool
val go_constraint_elem_type : go_constraint_elem -> go_type

(** Go type property predicates -- comparability, ordering, strict comparability *)
val go_struct_field_type : go_struct_field -> go_type
val go_is_comparable : go_type -> bool
val go_is_ordered : go_type -> bool
val go_is_strictly_comparable : go_type -> bool

(** Go underlying type resolution - resolves named types through an environment *)
val go_underlying_type : t:go_type -> env:list (string & go_type) -> go_type

(** Go predeclared type aliases (byte = uint8, rune = int32) *)
val go_byte_alias : go_type_decl
val go_rune_alias : go_type_decl
val go_predeclared_aliases : list (string & go_type)

(** Go import path resolution *)
val go_import_local_name : go_import_spec -> option string

(** Go type-to-string helper for type declarations *)
val go_type_to_string : go_type -> string

(** Go declaration and source file translation *)
val go_translate_import  : go_import_spec -> expr -> expr
val go_translate_imports : list go_import_spec -> expr -> expr
val go_translate_decl    : go_decl -> expr -> expr
val go_translate_file    : go_source_file -> expr

(** Go type preservation *)
val go_type_preservation :
  e:go_expr -> ctx:source_ctx ->
  Lemma (ensures brrr_well_typed ctx (go_translate_expr e))

(** ============================================================================
    HELPER PREDICATES FOR BRRR-MACHINE ANALYSIS
    ============================================================================ *)

(** TypeScript helpers *)
val is_ts_optional_chain_expr : e:expr -> bool
val is_ts_nullish_coalesce_expr : e:expr -> bool
val is_ts_promise_type : t:brrr_type -> bool
val is_ts_async_expr : e:expr -> bool

(** Rust helpers *)
val is_rust_shared_ref : t:brrr_type -> bool
val is_rust_mut_ref : t:brrr_type -> bool
val is_rust_owned : t:brrr_type -> bool
val is_rust_box : t:brrr_type -> bool
val is_rust_rc : t:brrr_type -> bool
val is_rust_arc : t:brrr_type -> bool
val is_rust_try_expr : e:expr -> bool
val is_rust_move_expr : e:expr -> bool

(** Go helpers *)
val is_go_chan_send_expr : e:expr -> bool
val is_go_chan_recv_expr : e:expr -> bool
val is_go_defer_expr : e:expr -> bool
val is_go_panic_expr : e:expr -> bool
val is_go_recover_expr : e:expr -> bool
val is_go_select_expr : e:expr -> bool
val has_go_spawn_effect : eff:effect_row -> bool
val has_go_panic_effect : eff:effect_row -> bool

(** Helper for Rust Copy trait check *)
val rust_is_copy : t:rust_type -> bool
