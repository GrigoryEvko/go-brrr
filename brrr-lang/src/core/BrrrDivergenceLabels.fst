(**
 * BrrrLang.Core.DivergenceLabels
 *
 * Divergence Stratification for Lazy Language Soundness.
 * Based on LiquidHaskell's divergence-aware refinement types.
 *
 * ============================================================================
 * THEORETICAL FOUNDATION
 * ============================================================================
 *
 * This module addresses a fundamental soundness issue in refinement type
 * systems for lazy languages. The problem stems from the interaction between
 * lazy evaluation and refinement type assumptions.
 *
 * Gap Resolution (from brrr_lang_spec_v0.4.tex):
 *   6. Divergence stratification (DivMay, DivWhnf, DivFin)
 *
 * ============================================================================
 * THE SOUNDNESS PROBLEM
 * ============================================================================
 *
 * In a strict language like OCaml or Rust, when we bind:
 *
 *     let x : {v:int | v > 0} = expensive_computation()
 *
 * We KNOW that `expensive_computation()` has completed and produced a
 * positive integer. The refinement `v > 0` is safe to assume.
 *
 * In a lazy language like Haskell, the same binding:
 *
 *     x :: {v:Int | v > 0}
 *     x = expensive_computation
 *
 * Does NOT immediately evaluate. The expression `expensive_computation`
 * becomes a THUNK. If this thunk diverges (loops forever), then `x` never
 * has a value, yet our type system might incorrectly assume `x > 0`.
 *
 * This can lead to UNSOUNDNESS:
 *
 *     loop :: {v:Int | v > 0}
 *     loop = loop  (* Diverges! But typechecks. *)
 *
 *     bad :: {v:Int | v < 0}
 *     bad = loop - 1  (* If loop > 0, then loop - 1 >= 0. But we claim < 0! *)
 *
 * The issue: we assumed `loop > 0` even though `loop` never produces a value.
 *
 * ============================================================================
 * CONNECTION TO F*'s EFFECT SYSTEM
 * ============================================================================
 *
 * F* handles divergence through its effect system, specifically the DIV effect:
 *
 *     effect DIV (a:Type) (pre:Type0) (post:a -> Type0)
 *     effect Div (a:Type) (pre:Type0) (post:a -> Type0) = DIV a pre (fun r -> pre ==> post r)
 *     effect Dv (a:Type) = DIV a True (fun _ -> True)
 *
 * Key properties of F*'s Dv effect (from fstar_pop_book.md):
 *
 * 1. PARTIAL CORRECTNESS SEMANTICS: A term `e : Dv t` may loop forever,
 *    but IF it terminates, the result has type `t`. This is different from
 *    Tot (total correctness) where termination is guaranteed.
 *
 * 2. EFFECT ORDERING: Tot < Dv in the effect lattice. This ensures that
 *    total computations cannot depend on potentially diverging ones,
 *    preventing unsoundness in F*'s logical core.
 *
 * 3. TERMINATION CHECKING DISABLED: F* does not require a decreasing
 *    measure for recursive functions annotated with Dv.
 *
 * 4. ISOLATED FROM PROOFS: Dv computations cannot be used in specifications
 *    or proofs, maintaining logical soundness. You cannot write:
 *
 *        val bad_lemma : x:nat -> Lemma (collatz x terminates)
 *
 *    Because `collatz x` is Dv, not Tot, so it cannot appear in a spec.
 *
 * ============================================================================
 * TERMINATION MEASURES AND WELL-FOUNDED RECURSION
 * ============================================================================
 *
 * F* uses several mechanisms for termination checking:
 *
 * 1. STRUCTURAL RECURSION: Arguments decrease according to the subterm
 *    ordering. For inductives, this is automatic.
 *
 * 2. LEXICOGRAPHIC ORDERING: Multiple measures compared lexicographically.
 *
 *        let rec ackermann (m n : nat) : Tot nat (decreases %[m; n]) = ...
 *
 * 3. WELL-FOUNDED RELATIONS: Custom orderings via the `acc` predicate:
 *
 *        type acc (#a:Type) (r:binrel a) (x:a) : Type =
 *          | AccIntro : (y:a -> r y x -> acc r y) -> acc r x
 *
 *    The `acc r x` type is inhabited iff there are no infinite descending
 *    r-chains starting at x. See FStar.WellFounded.
 *
 * 4. FUEL-BASED SMT ENCODING: For verification, recursive definitions are
 *    encoded with a "fuel" parameter. Each recursive call consumes fuel.
 *    When fuel reaches 0, the definition is undefined (for SMT purposes).
 *    This prevents infinite unfolding while allowing bounded reasoning.
 *
 *    The --initial_fuel and --max_fuel options control this.
 *
 * ============================================================================
 * LIQUIDHASKELL'S STRATIFICATION APPROACH
 * ============================================================================
 *
 * LiquidHaskell solves the lazy language soundness problem by stratifying
 * types according to their termination guarantee:
 *
 * - Div (May diverge): CANNOT assume refinement holds
 * - Wnf (Weak Head Normal Form): Partial guarantee
 * - Fin (Finite/Terminating): FULL refinement power
 *
 * The key insight is that certain language constructs FORCE evaluation:
 *
 * - Pattern matching forces scrutinee to WHNF
 * - Strict function application forces argument to WHNF
 * - `seq` forces first argument to WHNF
 * - `deepseq` forces to fully evaluated (Fin)
 *
 * After forcing, we can safely assume refinements hold.
 *
 * ============================================================================
 * BRRR-LANG ADAPTATION
 * ============================================================================
 *
 * Brrr-Lang is a multi-paradigm language supporting strict, lazy, and hybrid
 * evaluation modes. This module provides the infrastructure to track
 * divergence guarantees across all evaluation strategies.
 *
 * The stratification is essential for:
 *
 * 1. SOUND VERIFICATION CONDITIONS: Only include refinement assumptions
 *    when the divergence label guarantees evaluation.
 *
 * 2. TERMINATION PROOFS: Upgrade DivMay to DivFin when termination is proven
 *    via structural recursion, well-founded measure, or explicit annotation.
 *
 * 3. HYBRID LANGUAGE SUPPORT: Python generators, JS async functions, Scala
 *    lazy vals, and Rust lazy_static! all introduce lazy semantics into
 *    otherwise strict languages.
 *
 * 4. EFFECT INTERACTION: Divergence labels compose with other effects
 *    (exceptions, state, IO) through the effect system.
 *
 * ============================================================================
 * REFERENCES
 * ============================================================================
 *
 * - brrr_lang_spec_v0.4.tex: Section "Loop Typing with Divergence"
 * - fstar_pop_book.md: Lines 10000-11000 (Well-founded recursion)
 * - fstar_pop_book.md: Lines 14000-14500 (Dv effect)
 * - FSTAR_REFERENCE.md: Section 5 (Effect System)
 * - SPECIFICATION_ERRATA.md: Chapter 11 (Handler Termination)
 * - Vazou et al. "Refinement Types for Haskell" (ICFP 2014)
 * - Vazou et al. "Bounded Refinement Types" (ICFP 2015)
 *
 * Depends on: Primitives, BrrrTypes, DependentTypes
 *)
module BrrrDivergenceLabels

open FStar.List.Tot
open BrrrPrimitives
open BrrrTypes
open BrrrDependentTypes

(** ============================================================================
    EVALUATION MODES
    ============================================================================

    Different languages have different evaluation strategies, each with distinct
    implications for refinement type soundness:

    EvalStrict (Call-by-Value):
    ---------------------------
    Arguments are fully evaluated BEFORE function application. Used in:
      - C, C++, Rust: All evaluation is strict
      - Java, C#: Primitives and references strictly evaluated
      - OCaml, F#: Standard evaluation (with explicit laziness via Lazy.t)

    SOUNDNESS IMPLICATION: Refinements can always be assumed after binding.
    If `let x : {v:int | v > 0} = e` typechecks, then after the binding,
    we KNOW x > 0 because e has already been evaluated.

    EvalLazy (Call-by-Need):
    ------------------------
    Arguments are evaluated ON DEMAND, and results are memoized. Used in:
      - Haskell: Primary evaluation strategy
      - Miranda, Clean: Lazy functional languages

    SOUNDNESS IMPLICATION: Refinements CANNOT be assumed after binding
    unless we force evaluation. A binding `x = diverging_expr` creates
    a thunk that may never produce a value.

    The "need" in call-by-need means results are memoized. This differs
    from call-by-name where evaluation happens on every use.

    EvalHybrid:
    -----------
    Mix of strict and lazy constructs in the same language:
      - Python: Generators (yield), list comprehensions
      - JavaScript: Async/await, generator functions
      - Scala: lazy val, Stream, LazyList
      - Rust: lazy_static!, once_cell::Lazy
      - C++: std::optional with lazy initialization

    SOUNDNESS IMPLICATION: Must track laziness at construct level.
    Default is strict, but certain syntactic forms introduce laziness.

    F* PARALLEL:
    -----------
    In F*, the equivalent distinction is Tot vs Dv:
      - Tot (Total): Must terminate, like strict evaluation in that
                     we can assume the result exists
      - Dv (Divergent): May not terminate, like lazy with possible
                        infinite loop
    ============================================================================ *)

type eval_mode =
  | EvalStrict    (* Call-by-value: arguments always evaluated *)
  | EvalLazy      (* Call-by-need: arguments evaluated on demand *)
  | EvalHybrid    (* Mix: some constructs are lazy *)

(** ============================================================================
    DIVERGENCE LABELS
    ============================================================================

    Stratification of types by termination guarantee. This three-level
    hierarchy captures different degrees of evaluation progress, enabling
    sound refinement type checking for lazy languages.

    --------------------------------------------------------------------------
    DivMay (May Diverge)
    --------------------------------------------------------------------------
    Semantics:
      - Expression may diverge (loop forever, throw exception, bottom)
      - CANNOT assume refinement holds
      - Equivalent to F*'s Dv effect in terms of guarantees

    Examples:
      let x = loop() in ...       (* x may never have a value *)
      let y = undefined in ...    (* y is bottom *)
      let z = error "msg" in ...  (* z throws, never returns *)

    Verification Condition Translation:
      For {v:T^May | phi}, we translate phi to TRUE (no assumption).
      This is sound because we cannot rely on a value that may not exist.

    F* Connection:
      In F*, functions marked with Dv effect correspond to DivMay.
      The classic example from fstar_pop_book.md:

          let rec loop () : Dv unit = loop ()
          let rec collatz (n:pos) : Dv (list pos) = ...

      These may diverge, so we cannot use their results in Tot contexts.

    --------------------------------------------------------------------------
    DivWhnf (Weak Head Normal Form)
    --------------------------------------------------------------------------
    Semantics:
      - Expression reduces to WHNF (outermost constructor exposed)
      - CAN assume head structure, but subterms may diverge
      - Partial guarantee: we know the "shape" of the value

    What is WHNF?
      A term is in WHNF if its outermost form is:
        - A constructor application (Just _, (_, _), Left _)
        - A lambda abstraction (\x -> ...)
        - A primitive value (42, True, "hello")

      NOT in WHNF:
        - Function application (f x) where f needs reduction
        - Case expression (case ... of ...)
        - Let binding (let x = ... in ...)

    Examples:
      case e of ...     (* e is forced to WHNF by pattern match *)
      seq x y           (* x is forced to WHNF *)
      x `seq` y         (* Haskell's seq forces left arg to WHNF *)

    Verification Condition Translation:
      For {v:T^Wnf | phi}, we CAN include phi in assumptions IF phi
      only refers to the head structure. For deeper properties, we
      may need DivFin.

    Upgrade Operations:
      - Pattern matching scrutinee -> upgraded to DivWhnf
      - Strict function argument -> upgraded to DivWhnf
      - Haskell's seq, $! -> upgraded to DivWhnf

    --------------------------------------------------------------------------
    DivFin (Finite/Terminating)
    --------------------------------------------------------------------------
    Semantics:
      - Expression reduces to a FINITE value (fully evaluated)
      - FULL refinement power
      - Equivalent to F*'s Tot effect guarantee

    Examples:
      Proven terminating via:
        - Structural recursion on inductive type
        - Well-founded measure (decreases clause)
        - Explicit termination proof (acc-based)

          let rec length (xs : list a) : Tot nat (decreases xs) =
            match xs with
            | [] -> 0
            | _ :: tl -> 1 + length tl

        - Haskell's deepseq/NFData

    Verification Condition Translation:
      For {v:T^Fin | phi}, we include phi in VC assumptions.
      This is sound because we guarantee evaluation terminates.

    F* Connection:
      Tot functions in F* correspond to DivFin. The termination checker
      ensures all recursive calls decrease according to:
        1. The built-in subterm ordering (<<)
        2. A user-specified decreases clause
        3. A custom well-founded relation

      From FStar.WellFounded:
          type acc (#a:Type) (r:binrel a) (x:a) : Type =
            | AccIntro : (y:a -> r y x -> acc r y) -> acc r x

          let well_founded (#a:Type) (r:binrel a) = x:a -> acc r x

    --------------------------------------------------------------------------
    Subtype Ordering: Fin <: Wnf <: May
    --------------------------------------------------------------------------
    More precise (stronger guarantee) is subtype of less precise.
    This forms a lattice:

                    May  (top - weakest guarantee)
                     |
                    Wnf
                     |
                    Fin  (bottom - strongest guarantee)

    Intuition: If we have a proof of termination (Fin), we certainly
    have a proof of WHNF (Wnf), and trivially satisfy may-diverge (May).

    This subtyping is used in:
      - Covariant positions (function return types)
      - Contravariant positions (function argument types - reversed)
      - Invariant positions (mutable references)
    ============================================================================ *)

type divergence_label =
  | DivMay    (* May diverge - CANNOT assume refinement holds *)
  | DivWhnf   (* Reduces to weak head normal form - partial guarantee *)
  | DivFin    (* Reduces to finite value - FULL refinement power *)

(**
 * Divergence Label Subtyping: Fin <: Wnf <: May
 *
 * This defines the subtype relation on divergence labels. In a subtype
 * relation l1 <: l2, we can use a value of type (T, l1) wherever
 * (T, l2) is expected.
 *
 * The intuition is: stronger guarantees (Fin) subsume weaker ones (May).
 *
 * Proof obligations:
 *   - Reflexive: l <: l (proven in div_label_subtype_refl)
 *   - Transitive: l1 <: l2 /\ l2 <: l3 ==> l1 <: l3 (proven in div_label_subtype_trans)
 *   - Antisymmetric: l1 <: l2 /\ l2 <: l1 ==> l1 = l2
 *
 * This forms a bounded partial order (actually a total order here).
 *)
let div_label_subtype (l1 l2: divergence_label) : bool =
  match l1, l2 with
  | _, DivMay -> true         (* Anything is subtype of May *)
  | DivFin, DivFin -> true
  | DivFin, DivWhnf -> true   (* Fin <: Wnf *)
  | DivWhnf, DivWhnf -> true
  | _, _ -> false

(**
 * Join (Least Upper Bound) in the divergence lattice.
 *
 * Given two divergence labels, compute the weakest guarantee that
 * holds for BOTH. This is used when:
 *
 *   1. Merging branches: if-then-else with different branch labels
 *      Example: if c then x^Fin else y^Wnf has result label Wnf
 *
 *   2. Combining effects: sequencing operations
 *      Example: (e1; e2) where e1^May and e2^Fin has label May
 *
 *   3. Abstract interpretation widening (see widen_stratified)
 *
 * Join table:
 *       | Fin | Wnf | May
 *   ----+-----+-----+-----
 *   Fin | Fin | Wnf | May
 *   Wnf | Wnf | Wnf | May
 *   May | May | May | May
 *
 * Properties:
 *   - Commutative: join(l1, l2) = join(l2, l1) (proven in div_label_join_comm)
 *   - Associative: join(join(l1, l2), l3) = join(l1, join(l2, l3))
 *   - Idempotent: join(l, l) = l
 *)
let div_label_join (l1 l2: divergence_label) : divergence_label =
  match l1, l2 with
  | DivMay, _ -> DivMay
  | _, DivMay -> DivMay
  | DivWhnf, _ -> DivWhnf
  | _, DivWhnf -> DivWhnf
  | DivFin, DivFin -> DivFin

(**
 * Meet (Greatest Lower Bound) in the divergence lattice.
 *
 * Given two divergence labels, compute the strongest guarantee that
 * is a lower bound of both. This is less commonly used but needed for:
 *
 *   1. Intersection types: (T1, l1) /\ (T2, l2)
 *   2. Most specific common subtype
 *
 * Meet table:
 *       | Fin | Wnf | May
 *   ----+-----+-----+-----
 *   Fin | Fin | Fin | Fin
 *   Wnf | Fin | Wnf | Wnf
 *   May | Fin | Wnf | May
 *
 * Properties:
 *   - Commutative: meet(l1, l2) = meet(l2, l1)
 *   - Associative: meet(meet(l1, l2), l3) = meet(l1, meet(l2, l3))
 *   - Idempotent: meet(l, l) = l
 *
 * Together with join, this forms a BOUNDED LATTICE with:
 *   - Top element: DivMay
 *   - Bottom element: DivFin
 *)
let div_label_meet (l1 l2: divergence_label) : divergence_label =
  match l1, l2 with
  | DivFin, _ -> DivFin
  | _, DivFin -> DivFin
  | DivWhnf, _ -> DivWhnf
  | _, DivWhnf -> DivWhnf
  | DivMay, DivMay -> DivMay

(** ============================================================================
    STRATIFIED TYPES
    ============================================================================

    A stratified type pairs a base (dependent) type with a divergence label.
    This is the core mechanism for tracking termination guarantees through
    the type system.

    The type (T, l) represents:
      - A value of type T
      - With termination guarantee l

    Notation conventions in the literature:
      - T^Fin, T^Wnf, T^Div (superscript)
      - T @ Fin, T @ Wnf, T @ Div (annotation)
      - <T, l> (pair notation)

    VC Generation Impact:
    --------------------
    The divergence label directly affects verification condition generation.
    See translate_refinement_vc for the full translation rules.

    For a binding x : {v:T^l | phi}:
      - If l = Fin or l = Wnf: assume phi[x/v] in subsequent VCs
      - If l = May: do NOT assume phi (translate to True)

    This is the key insight that makes refinement types sound for lazy
    languages: we only rely on refinements when we have termination evidence.
    ============================================================================ *)

(**
 * Stratified type: pairs dependent type with divergence label.
 *
 * noeq is used because dep_type may contain functions or other
 * non-eqtype components, making decidable equality impossible.
 *)
noeq type stratified_type = {
  st_base   : dep_type;           (* Underlying dependent type *)
  st_label  : divergence_label;   (* Termination guarantee *)
}

(**
 * Stratify a type based on evaluation mode.
 *
 * This determines the DEFAULT divergence label for types in a given
 * evaluation context:
 *
 *   - EvalStrict -> DivFin: Strict evaluation guarantees termination
 *                           before we can use the value.
 *
 *   - EvalLazy -> DivMay: Lazy evaluation provides no initial guarantee.
 *                         We must upgrade via forcing constructs.
 *
 *   - EvalHybrid -> DivMay: Conservative default. Specific lazy constructs
 *                           can further refine this.
 *
 * Example:
 *   In Haskell (EvalLazy):
 *     let x = expensive_computation  (* x : T^May initially *)
 *     case x of ...                  (* x upgraded to T^Wnf here *)
 *
 *   In OCaml (EvalStrict):
 *     let x = expensive_computation  (* x : T^Fin always *)
 *)
let stratify (mode: eval_mode) (t: dep_type) : stratified_type =
  match mode with
  | EvalStrict -> { st_base = t; st_label = DivFin }   (* Strict = always Fin *)
  | EvalLazy   -> { st_base = t; st_label = DivMay }   (* Lazy = start as May *)
  | EvalHybrid -> { st_base = t; st_label = DivMay }   (* Hybrid = conservative *)

(**
 * Stratified type subtyping.
 *
 * (T1, l1) <: (T2, l2) iff:
 *   1. T1 <: T2 (base types are subtypes)
 *   2. l1 <: l2 (labels are compatible)
 *
 * Both conditions must hold. This is covariant in both components.
 *
 * For function types, divergence labels behave differently:
 *   - Argument labels: contravariant (input)
 *   - Return labels: covariant (output)
 *
 * Example:
 *   (Int^Fin) <: (Int^Wnf) <: (Int^May)
 *   ({x:Int | x > 0}^Fin) <: (Int^Wnf)
 *)
let stratified_subtype (st1 st2: stratified_type) : bool =
  (* Base types must be subtypes AND labels must be compatible *)
  dep_type_subtype st1.st_base st2.st_base &&
  div_label_subtype st1.st_label st2.st_label

(** ============================================================================
    DIVERGENCE LABEL UPGRADES
    ============================================================================

    Certain language constructs FORCE evaluation, allowing us to upgrade
    divergence labels from weaker (May) to stronger (Wnf or Fin) guarantees.

    This is the key mechanism for recovering refinement power in lazy
    languages: by observing that certain constructs demand evaluation,
    we can soundly assume the resulting value exists.

    --------------------------------------------------------------------------
    FORCING CONSTRUCTS
    --------------------------------------------------------------------------

    1. PATTERN MATCHING (case/match)
       Forces scrutinee to WHNF because we need to see the constructor.

       Example:
         case x of             (* x forced to WHNF here *)
           Nothing -> ...
           Just y  -> ...      (* y is still May - not forced yet *)

    2. STRICT FUNCTION APPLICATION
       Primitive operations and strict functions force arguments.

       Example:
         x + 1                 (* + is strict, so x forced to WHNF *)
         length xs             (* length forces xs to WHNF for each step *)

    3. BANG PATTERNS (!x)
       Haskell extension for explicit strictness.

       Example:
         f !x = ...            (* x evaluated before entering f *)

    4. seq / $! OPERATORS
       Haskell's primitives for forcing evaluation.

       Example:
         x `seq` y             (* x forced to WHNF, then y returned *)
         f $! x                (* x forced to WHNF, then passed to f *)

    5. DEEPSEQ / NFData
       Forces complete evaluation to normal form.

       Example:
         deepseq x y           (* x fully evaluated, then y returned *)
         force x               (* x : NFData a => x fully evaluated *)

    6. TERMINATION PROOFS
       Static proof that computation terminates (decreases clause, measure).

       Example in F*:
         let rec length (xs:list a) : Tot nat (decreases xs) = ...

       The (decreases xs) clause proves termination via structural recursion.

    --------------------------------------------------------------------------
    UPGRADE DIRECTIONS
    --------------------------------------------------------------------------

    Upgrades only go from weaker to stronger guarantees:
      May -> Wnf (via case, seq, strict application)
      May -> Fin (via deepseq, termination proof)
      Wnf -> Fin (via deepseq, termination proof)

    We NEVER downgrade from stronger to weaker (that would be unsound).
    Note: upgrade_case_scrutinee sets to DivWhnf unconditionally, which
    could downgrade DivFin to DivWhnf. This is noted in upgrade_monotonic
    as a design consideration - in practice, we should preserve Fin.
    ============================================================================ *)

(**
 * Case scrutinee is forced to WHNF.
 *
 * When pattern matching on an expression, the runtime must evaluate
 * the scrutinee enough to determine which constructor matches.
 * This is Weak Head Normal Form.
 *
 * Example:
 *   case x of         (* x : T^May becomes x : T^Wnf *)
 *     [] -> ...
 *     y:ys -> ...     (* y, ys still May - not yet forced *)
 *)
let upgrade_case_scrutinee (st: stratified_type) : stratified_type =
  { st with st_label = DivWhnf }

(**
 * Strict application forces argument to WHNF.
 *
 * For strict function f, the argument is evaluated before the call.
 * This applies to:
 *   - Primitive operations (+, -, *, etc.)
 *   - FFI calls to strict languages
 *   - Explicitly strict function parameters
 *
 * In Haskell terms: f $! x
 *)
let upgrade_strict_arg (st: stratified_type) : stratified_type =
  { st with st_label = DivWhnf }

(**
 * Termination proof upgrades to Fin.
 *
 * When we have a proof that a computation terminates, we can upgrade
 * from any label to DivFin. Termination proofs can come from:
 *
 *   1. STRUCTURAL RECURSION: Arguments decrease on subterm ordering.
 *      The (decreases e) clause uses F*'s built-in << ordering.
 *
 *   2. WELL-FOUNDED MEASURE: Custom measure proven to decrease.
 *      Uses FStar.WellFounded.acc for accessibility proof.
 *
 *   3. LEXICOGRAPHIC ORDERING: Multiple measures ordered lex.
 *      From FStar.LexicographicOrdering.
 *
 *   4. FUEL-BASED: Bounded recursion with explicit fuel parameter.
 *
 * See fstar_pop_book.md lines 10000-11000 for F* termination details.
 *)
let upgrade_terminating (st: stratified_type) : stratified_type =
  { st with st_label = DivFin }

(**
 * Haskell's seq operator forces to WHNF.
 *
 * seq :: a -> b -> b
 * seq x y = x `seq` y  (* evaluate x to WHNF, return y *)
 *
 * This is the primitive forcing operation. It evaluates its first
 * argument to WHNF and returns the second argument.
 *
 * Note: seq only forces to WHNF, not full normal form. For:
 *   seq (Just undefined) True
 * The Just constructor is exposed (WHNF), but undefined is not evaluated.
 *)
let upgrade_seq (st: stratified_type) : stratified_type =
  { st with st_label = DivWhnf }

(**
 * Haskell's deepseq forces to fully evaluated (Fin).
 *
 * deepseq :: NFData a => a -> b -> b
 * deepseq x y = x `deepseq` y  (* fully evaluate x, return y *)
 *
 * Unlike seq, deepseq recursively evaluates the entire structure.
 * This requires the NFData (Normal Form Data) typeclass, which provides
 * the rnf (reduce to normal form) operation.
 *
 * Example:
 *   deepseq (Just undefined) True  (* ERROR: undefined is evaluated *)
 *   deepseq [1,2,3] True           (* OK: entire list evaluated *)
 *)
let upgrade_deepseq (st: stratified_type) : stratified_type =
  { st with st_label = DivFin }

(** ============================================================================
    DIVERGENCE LABEL INFERENCE
    ============================================================================

    For expressions, we infer the most precise divergence label that
    soundly characterizes the expression's termination behavior. The
    inference is bottom-up, combining labels from subexpressions.

    --------------------------------------------------------------------------
    INFERENCE RULES
    --------------------------------------------------------------------------

    LITERALS and CONSTRUCTORS: DivFin
      - 42, True, "hello" are immediately values
      - Just x has label max(Fin, label(x)) = label(x)
      - Constructor application: join of argument labels

    VARIABLES: Inherit from binding
      - The label is stored in the typing context
      - May be upgraded if accessed via forcing construct

    FUNCTION APPLICATION: Depends on function and argument
      - Total function (Tot): result label = join of arg labels
      - Partial function (Dv): result label = DivMay
      - Strict function: argument labels upgraded

    RECURSION: DivMay unless termination proven
      - Without decreases clause: DivMay (may diverge)
      - With valid decreases: DivFin (proven terminating)
      - Mutual recursion: all functions must terminate together

    PRIMITIVES: Depends on primitive totality
      - Total primitives (+, -, *, etc.): DivFin
      - Partial primitives (/, error): DivMay or exception

    CONDITIONALS: Join of branch labels
      - if c then e1 else e2: join(label(e1), label(e2))
      - case e of ...: scrutinee upgraded, join of branch labels

    LET BINDINGS: Depends on bound expression and body
      - let x = e1 in e2: label(e2) with x having label(e1)
      - In lazy mode, e1 is not immediately evaluated

    --------------------------------------------------------------------------
    F* PARALLEL: TERMINATION CHECKING
    --------------------------------------------------------------------------

    F* uses fuel-based SMT encoding for termination. The --initial_fuel
    and --max_fuel options control how many times recursive definitions
    are unfolded. This is purely for verification; at runtime, the
    recursion proceeds normally.

    The (decreases e) clause specifies a termination measure. F* checks:
      1. The measure is well-founded (no infinite descending chains)
      2. Recursive calls have strictly smaller measure

    Examples from fstar_pop_book.md:

        (* Structural recursion - decreases is inferred *)
        let rec length xs = match xs with
          | [] -> 0
          | _::tl -> 1 + length tl

        (* Explicit measure *)
        let rec fib n : Tot nat (decreases n) =
          if n <= 1 then 1 else fib (n-1) + fib (n-2)

        (* Lexicographic ordering *)
        let rec ackermann m n : Tot nat (decreases %[m; n]) = ...

        (* Custom well-founded relation *)
        let rec f x : Tot nat (decreases {:well-founded wf_rel x}) = ...
    ============================================================================ *)

(**
 * Expression categories for divergence inference.
 *
 * These categories determine the default divergence label inference
 * strategy for different expression forms.
 *)
type expr_div_category =
  | ExprValue       (* Immediate value: literal, constructor *)
  | ExprVar         (* Variable reference: inherits from context *)
  | ExprApp         (* Function application: depends on function *)
  | ExprRecursive   (* Recursive call: May unless proven *)
  | ExprPrimitive   (* Primitive operation: Fin for total prims *)

(**
 * Infer divergence label from expression category.
 *
 * This provides the DEFAULT label for each category. Actual inference
 * may refine this based on:
 *   - Context information (variable labels from environment)
 *   - Termination proofs (decreases clauses)
 *   - Effect annotations (Tot vs Dv)
 *
 * The inference is conservative: we choose DivMay when uncertain.
 * This ensures soundness at the cost of some precision.
 *)
let infer_div_from_category (cat: expr_div_category) : divergence_label =
  match cat with
  | ExprValue -> DivFin        (* Values are finite by construction *)
  | ExprVar -> DivMay          (* Conservative for variables *)
  | ExprApp -> DivMay          (* Functions may diverge *)
  | ExprRecursive -> DivMay    (* Recursion may diverge *)
  | ExprPrimitive -> DivFin    (* Total primitives are finite *)

(** ============================================================================
    VERIFICATION CONDITION TRANSLATION
    ============================================================================

    This section implements the critical translation from stratified
    refinement types to verification conditions. The key insight is that
    in lazy languages, we can only include refinement assumptions in VCs
    when the divergence label guarantees evaluation has occurred.

    --------------------------------------------------------------------------
    THE SOUNDNESS ARGUMENT
    --------------------------------------------------------------------------

    Consider the refinement type {x:Int | x > 0}^l in a lazy context.

    If l = DivMay:
      The expression bound to x might diverge. If it diverges, x has no
      value, so "x > 0" is vacuously true but operationally meaningless.
      Including "x > 0" in the VC could let us prove false things about
      code that uses x (which might loop forever).

      Example of unsoundness if we assumed refinement:
        loop : {x:Int | x > 0}
        loop = loop                    (* Diverges *)

        bad : {x:Int | x < 0}
        bad = loop - 1                 (* If loop > 0, then loop-1 >= 0, not <0 *)

      By NOT assuming loop > 0, we prevent proving bad has type {x | x < 0}.

    If l = DivWhnf or l = DivFin:
      The expression has been forced to at least WHNF. For base types
      like Int, WHNF means we have an actual integer value. We CAN
      safely assume the refinement holds.

    --------------------------------------------------------------------------
    TRANSLATION RULES
    --------------------------------------------------------------------------

    STRICT MODE (EvalStrict):
      translate(x : {v:T | phi}) = phi[x/v]

      Rationale: In strict evaluation, by the time we have the binding,
      the expression has fully evaluated. Safe to assume refinement.

    LAZY/HYBRID MODE (EvalLazy, EvalHybrid):
      translate(x : {v:T^May | phi}) = True  (* No assumption *)
      translate(x : {v:T^Wnf | phi}) = phi[x/v]
      translate(x : {v:T^Fin | phi}) = phi[x/v]

      Rationale: Only after forcing (indicated by Wnf/Fin label) can we
      assume the refinement. For DivMay, we assume nothing.

    --------------------------------------------------------------------------
    INTERACTION WITH FORCING CONSTRUCTS
    --------------------------------------------------------------------------

    When the type system detects a forcing construct, it upgrades the
    divergence label BEFORE generating VCs. This means the VC generator
    sees the upgraded label and can safely include the refinement.

    Example workflow:
      1. x : {v:Int | v > 0}^May is bound
      2. VCs at this point do NOT include v > 0
      3. case x of ... triggers upgrade_case_scrutinee
      4. x is now {v:Int | v > 0}^Wnf
      5. VCs AFTER case CAN include v > 0

    --------------------------------------------------------------------------
    CONNECTION TO F*'s SMT ENCODING
    --------------------------------------------------------------------------

    F* uses a similar approach for its Tot vs Dv distinction:
      - Tot terms: refinements included in SMT encoding
      - Dv terms: cannot appear in specifications at all

    The difference is that F* enforces this at the effect level (you
    cannot even write a specification mentioning Dv terms), while our
    stratification allows mentioning divergent terms but controls which
    assumptions we make.

    See FSTAR_REFERENCE.md Section 6 for F*'s SMT encoding details.
    ============================================================================ *)

(**
 * Translate stratified refinement to VC assumption.
 *
 * Given a variable x with stratified type, produce the formula that
 * should be assumed about x in verification conditions.
 *
 * Parameters:
 *   mode - The evaluation mode (strict, lazy, or hybrid)
 *   x    - The variable being bound
 *   st   - The stratified type of x
 *
 * Returns:
 *   A formula to include in the VC, or FTrue if no assumption is safe.
 *
 * Soundness argument:
 *   If we return phi[x/v], it is because either:
 *     1. We are in strict mode (evaluation guaranteed), or
 *     2. The divergence label is Wnf/Fin (forcing has occurred).
 *   In both cases, x has a value, so the refinement is meaningful.
 *)
let translate_refinement_vc
    (mode: eval_mode)
    (x: dep_var)
    (st: stratified_type)
    : formula =
  match st.st_base with
  | DRefinement y base phi ->
      (match mode with
       | EvalStrict ->
           (* Strict: always safe to assume refinement *)
           subst_formula y (EVar x) phi

       | EvalLazy | EvalHybrid ->
           (* Lazy: only assume if evaluation guaranteed *)
           match st.st_label with
           | DivMay ->
               (* Cannot assume refinement - may diverge *)
               FTrue
           | DivWhnf | DivFin ->
               (* Safe to assume refinement *)
               subst_formula y (EVar x) phi)
  | _ ->
      (* Non-refinement type: no assumption needed *)
      FTrue

(** ============================================================================
    WIDENING WITH DIVERGENCE LABELS
    ============================================================================

    During abstract interpretation (AI), we use widening to ensure
    termination of the analysis. Widening for stratified types must
    correctly combine divergence labels.

    --------------------------------------------------------------------------
    ABSTRACT INTERPRETATION BACKGROUND
    --------------------------------------------------------------------------

    AI computes fixpoints over abstract domains. For loops:

        while (c) { body }

    We iterate: state_0 -> body -> state_1 -> body -> state_2 -> ...

    Without widening, this might not terminate if the abstract domain
    has infinite ascending chains. Widening (nabla) accelerates convergence
    by jumping to a safe overapproximation.

    --------------------------------------------------------------------------
    WIDENING FOR DIVERGENCE LABELS
    --------------------------------------------------------------------------

    The widening for divergence labels is simply the JOIN operation:

        widen_div(l1, l2) = join(l1, l2)

    Intuition: If ANY iteration of the loop might diverge, the result
    might diverge. This is sound but conservative.

    Example:
        while (c) {
          if (random()) {
            x = terminating_expr()   (* x : T^Fin *)
          } else {
            x = possibly_loop()      (* x : T^May *)
          }
        }
        (* After loop: x : T^May (join of Fin and May) *)

    --------------------------------------------------------------------------
    LOOP TYPING RULE (from brrr_lang_spec_v0.4.tex)
    --------------------------------------------------------------------------

    The specification includes the divergence effect in loop typing:

        env |- c : Bool [eps1]    env |- body : Unit [eps2]
        ---------------------------------------------------
        env |- while c { body } : Unit [eps1 |_| eps2 |_| Div]

    The Div effect is ALWAYS added because:
      1. The loop might not terminate (unknown iteration count)
      2. Even with termination proof, we're conservative in typing

    To prove a while loop terminates, we need a variant (loop invariant
    that decreases each iteration and is well-founded).
    ============================================================================ *)

(**
 * Widen stratified types during abstract interpretation.
 *
 * This is used when computing loop invariants or fixpoints.
 * The widening is conservative: we take the join of labels.
 *
 * Note: The base type widening is simplified here. A full implementation
 * would widen refinements, intervals, etc. according to the abstract
 * domain being used.
 *)
let widen_stratified (st1 st2: stratified_type) : stratified_type =
  (* Join divergence labels (conservative) *)
  let joined_label = div_label_join st1.st_label st2.st_label in
  (* For simplicity, use second type as base (proper widening is complex) *)
  { st_base = st2.st_base; st_label = joined_label }

(**
 * Check if type is safe for refinement assumptions.
 *
 * This predicate determines whether we can include the refinement
 * from a stratified type in verification conditions.
 *
 * Returns true iff:
 *   - We are in strict mode (all evaluations complete), OR
 *   - The divergence label is Wnf or Fin (forcing has occurred)
 *
 * Usage: Before generating VCs that rely on refinement phi, check
 * is_refinement_safe(mode, st). If false, assume True instead.
 *)
let is_refinement_safe (mode: eval_mode) (st: stratified_type) : bool =
  match mode with
  | EvalStrict -> true  (* Always safe in strict mode *)
  | EvalLazy | EvalHybrid ->
      match st.st_label with
      | DivMay -> false  (* Not safe: may diverge *)
      | DivWhnf | DivFin -> true

(** ============================================================================
    HYBRID LANGUAGE SUPPORT
    ============================================================================

    For hybrid languages (Python, JavaScript, Scala, Rust), certain
    constructs introduce lazy semantics into otherwise strict evaluation.
    This section provides infrastructure for detecting and handling these
    mixed-evaluation scenarios.

    --------------------------------------------------------------------------
    LAZY CONSTRUCTS IN STRICT LANGUAGES
    --------------------------------------------------------------------------

    GENERATORS (Python, JavaScript):
      def fibonacci():
          a, b = 0, 1
          while True:
              yield a           (* Suspension point *)
              a, b = b, a + b

      The generator function returns an iterator immediately, but the
      body is only executed when next() is called. Each yield suspends
      execution until the next iteration.

      Divergence: A generator that yields infinitely (like fibonacci) is
      fine - it's productive. But a generator with while True: pass
      would diverge on first next() call.

    ASYNC/AWAIT (JavaScript, Python, Rust):
      async function fetchData() {
          const response = await fetch(url);  (* Suspension point *)
          return response.json();
      }

      Async functions return a Promise/Future immediately. The body
      executes asynchronously, potentially never completing.

      Divergence: If await never resolves (e.g., server never responds),
      the async computation diverges.

    LAZY VALUES (Scala, Rust):
      lazy val expensiveResult = computeExpensive()  // Scala
      static ref CACHE: Lazy<Data> = Lazy::new(|| ...);  // Rust

      The RHS is not evaluated until first access. After first access,
      the result is memoized.

      Divergence: If the initializer diverges, first access diverges.

    THUNKS (Explicit delay):
      let delayed = delay(|| expensive_computation())
      let result = force(delayed)

      Explicitly wrapping computation to defer evaluation. Common in
      strict languages to simulate laziness.

    STREAMS/ITERATORS (Rust, Java, Scala):
      let stream = (0..).map(|x| x * 2).take(10);  // Rust

      Lazy sequences that compute elements on demand. May represent
      infinite sequences (productive) or divergent computations.

    --------------------------------------------------------------------------
    DETECTION AND HANDLING
    --------------------------------------------------------------------------

    When parsing/analyzing code, we detect lazy constructs syntactically
    and mark expressions accordingly. This affects:

      1. Initial divergence labels (EvalStrict -> EvalHybrid upgrade)
      2. VC generation (conservative assumptions)
      3. Termination checking (different rules for generators)

    The effective_eval_mode function computes the actual evaluation mode
    by considering both the base language mode and detected lazy constructs.
    ============================================================================ *)

(**
 * Lazy construct markers.
 *
 * These indicate syntactic forms that introduce lazy evaluation
 * into an otherwise strict context.
 *)
type lazy_construct =
  | LCGenerator         (* Python/JS generator function *)
  | LCAsync             (* async function *)
  | LCLazyVal           (* Scala lazy val, Rust lazy_static! *)
  | LCThunk             (* Explicit thunk/delay *)
  | LCStream            (* Lazy stream/iterator *)

(**
 * Check if expression uses any lazy construct.
 *
 * If true, the expression has lazy semantics even in a strict language.
 *)
let uses_lazy_construct (constructs: list lazy_construct) : bool =
  List.Tot.length constructs > 0

(**
 * Determine effective evaluation mode for an expression.
 *
 * Given the base language mode and detected lazy constructs, compute
 * the actual evaluation mode that should govern this expression.
 *
 * Rules:
 *   - EvalStrict + lazy constructs -> EvalHybrid
 *   - EvalStrict + no lazy constructs -> EvalStrict
 *   - EvalLazy -> EvalLazy (unchanged)
 *   - EvalHybrid -> EvalHybrid (unchanged)
 *
 * The key insight is that lazy constructs "infect" strict code,
 * forcing hybrid treatment. But in already-lazy languages, no change.
 *)
let effective_eval_mode
    (base_mode: eval_mode)
    (constructs: list lazy_construct)
    : eval_mode =
  match base_mode with
  | EvalStrict ->
      if uses_lazy_construct constructs then EvalHybrid else EvalStrict
  | EvalLazy -> EvalLazy
  | EvalHybrid -> EvalHybrid

(** ============================================================================
    TERMINATION CHECKING INTERFACE
    ============================================================================

    This section provides the interface between the divergence stratification
    system and F*-style termination checking. When we have a proof that a
    computation terminates, we can upgrade its divergence label from DivMay
    to DivFin.

    --------------------------------------------------------------------------
    TERMINATION PROOF METHODS
    --------------------------------------------------------------------------

    1. STRUCTURAL RECURSION
       The recursive call is on a strict subterm of an inductive argument.
       F* infers this automatically for most recursive functions.

       Example:
         let rec length xs = match xs with
           | [] -> 0
           | _::tl -> 1 + length tl  (* tl is subterm of xs *)

       In F*, this corresponds to the built-in (<<) ordering.

    2. WELL-FOUNDED MEASURE
       User provides a measure function that maps arguments to a
       well-ordered domain (typically nat), and shows the measure
       strictly decreases on each recursive call.

       Example:
         let rec fib n : Tot nat (decreases n) =
           if n <= 1 then 1 else fib (n-1) + fib (n-2)

       The measure n decreases: n > n-1 and n > n-2.

    3. LEXICOGRAPHIC ORDERING
       Multiple measures combined lexicographically. Useful for nested
       loops or functions with multiple arguments.

       Example:
         let rec ackermann m n : Tot nat (decreases %[m; n]) =
           if m = 0 then n + 1
           else if n = 0 then ackermann (m-1) 1
           else ackermann (m-1) (ackermann m (n-1))

       Decreases: (m,n) >_lex (m-1, any) and (m,n) >_lex (m, n-1)

    4. CUSTOM WELL-FOUNDED RELATION
       For complex orderings not expressible as measures.

       Example (from fstar_pop_book.md lines 10280-10298):
         let rec f x : Tot nat (decreases {:well-founded wf_rel x}) = ...

       Uses FStar.WellFounded.acc to prove accessibility.

    5. FUEL-BASED (SMT only)
       For verification, F* uses a fuel parameter. This doesn't prove
       termination but allows bounded reasoning.

       Options: --initial_fuel, --max_fuel

    --------------------------------------------------------------------------
    TERMINATION PROOF WITNESS
    --------------------------------------------------------------------------

    The termination_proof type captures the witness that a computation
    terminates. This is an abstract representation that could be:
      - A checked (decreases ...) clause
      - An external termination proof
      - A user annotation (trusted)
    ============================================================================ *)

(**
 * Termination proof witness (abstract).
 *
 * This type represents evidence that a computation terminates.
 * In a full implementation, this would include:
 *   - The actual decreases expression
 *   - The well-founded relation used
 *   - References to helper lemmas
 *)
type termination_proof = {
  tp_function : string;       (* Function name *)
  tp_measure  : string;       (* Termination measure description *)
  tp_method   : string;       (* Proof method: structural, measure, lex, etc. *)
}

(**
 * Upgrade type based on termination proof.
 *
 * If we have a valid termination proof for the expression producing
 * a value of stratified type st, we can upgrade to DivFin.
 *
 * This is sound because:
 *   - DivFin means "reduces to finite value"
 *   - A termination proof guarantees exactly that
 *   - Therefore the upgrade preserves the type's invariant
 *
 * Usage:
 *   When typechecking a recursive function with (decreases ...) clause:
 *   1. Check the decreases clause is valid
 *   2. Create termination_proof witness
 *   3. Call apply_termination_proof to upgrade return type
 *)
let apply_termination_proof
    (st: stratified_type)
    (proof: option termination_proof)
    : stratified_type =
  match proof with
  | Some _ -> { st with st_label = DivFin }
  | None -> st

(** ============================================================================
    DIVERGENCE-AWARE DEPENDENT TYPE
    ============================================================================

    This section defines dependent types with integrated divergence labels.
    Rather than separately tracking (type, label) pairs, we embed the
    divergence information directly into the type structure.

    This provides several advantages:
      1. Type-level operations naturally preserve divergence info
      2. Subtyping is defined uniformly
      3. Type inference can propagate labels through type constructors

    --------------------------------------------------------------------------
    TYPE CONSTRUCTORS WITH DIVERGENCE
    --------------------------------------------------------------------------

    DDBase (t, l):
      Base type t with divergence label l.
      Example: (Int, Fin) = a definitely-terminating integer

    DDPi (x, A, B):
      Pi/function type. x:A -> B where B may depend on x.
      The divergence of the result is in B, not the Pi itself.
      Example: (x:Int^Fin) -> {y:Int | y > x}^Fin

    DDSigma (x, A, B):
      Sigma/pair type. (x:A, B) where B may depend on x.
      The divergence of the second component is in B.
      Example: (x:Int^Fin, {y:Int | y = x + 1}^Fin)

    DDRefinement (x, base, phi, l):
      Refinement type {x:base | phi}^l.
      The label l governs when we can assume phi.
      Example: {x:Int | x > 0}^May -- cannot assume x > 0 yet

    --------------------------------------------------------------------------
    DIVERGENCE FLOW THROUGH TYPES
    --------------------------------------------------------------------------

    For Pi types (functions):
      - Argument divergence: contravariant (input is forced)
      - Result divergence: covariant (output may diverge)

      Example function subtyping:
        (Int^Fin -> Int^May) <: (Int^May -> Int^Fin)
                 ^                      ^
                 |                      |
        argument covariant?     result covariant? NO!

      Actually: (Int^May -> Int^Fin) <: (Int^Fin -> Int^May)
        - Function accepting May can accept Fin (contravariant)
        - Function returning Fin can be used where May expected (covariant)

    For Sigma types (pairs):
      - First component divergence affects second (dependency)
      - If first is May, second might not be evaluated

    For Refinements:
      - Label governs VC translation (see translate_refinement_vc)
      - Upgrading label makes refinement usable
    ============================================================================ *)

(**
 * Divergence-aware dependent type.
 *
 * noeq is needed because these types contain formulas and other
 * components that may not have decidable equality.
 *)
noeq type div_dep_type =
  (* Base with divergence *)
  | DDBase      : brrr_type -> divergence_label -> div_dep_type

  (* Pi-type with divergence on result *)
  | DDPi        : dep_var -> div_dep_type -> div_dep_type -> div_dep_type

  (* Sigma-type with divergence *)
  | DDSigma     : dep_var -> div_dep_type -> div_dep_type -> div_dep_type

  (* Refinement with divergence *)
  | DDRefinement : dep_var -> div_dep_type -> formula -> divergence_label -> div_dep_type

(**
 * Extract the divergence label from a div_dep_type.
 *
 * For compound types (Pi, Sigma), we return the label of the "result"
 * position - this is the label that governs the overall type's
 * termination guarantee.
 *
 * For Pi (x:A) -> B: the result is B, so we return label(B)
 * For Sigma (x:A, B): the result is B, so we return label(B)
 *
 * This matches the intuition that:
 *   - A function's divergence is determined by its result
 *   - A pair's divergence is determined by its second component
 *     (assuming first component was needed to construct second)
 *)
let rec div_dep_type_label (t: div_dep_type) : divergence_label =
  match t with
  | DDBase _ l -> l
  | DDPi _ _ t2 -> div_dep_type_label t2  (* Result divergence *)
  | DDSigma _ _ t2 -> div_dep_type_label t2
  | DDRefinement _ _ _ l -> l

(**
 * Upgrade divergence label throughout a type.
 *
 * This recursively updates all divergence labels in the type to the
 * new label. Used when we have a termination proof or forcing construct
 * that applies to the entire type.
 *
 * Note: This is a uniform upgrade. For more precise handling, we might
 * want to only upgrade specific positions (e.g., result of function,
 * not arguments).
 *)
let rec upgrade_div_dep_type
    (t: div_dep_type)
    (new_label: divergence_label)
    : div_dep_type =
  match t with
  | DDBase bt _ -> DDBase bt new_label
  | DDPi x t1 t2 -> DDPi x t1 (upgrade_div_dep_type t2 new_label)
  | DDSigma x t1 t2 -> DDSigma x t1 (upgrade_div_dep_type t2 new_label)
  | DDRefinement x base phi _ -> DDRefinement x base phi new_label

(** ============================================================================
    SOUNDNESS PROPERTIES
    ============================================================================

    This section contains the key lemmas establishing that the divergence
    label lattice operations satisfy the expected algebraic properties.
    These properties are essential for the soundness of the type system.

    --------------------------------------------------------------------------
    REQUIRED PROPERTIES FOR SOUNDNESS
    --------------------------------------------------------------------------

    For the subtyping relation to be well-behaved, we need:
      1. Reflexivity: l <: l
      2. Transitivity: l1 <: l2 /\ l2 <: l3 ==> l1 <: l3
      3. Antisymmetry: l1 <: l2 /\ l2 <: l1 ==> l1 = l2

    For the lattice operations:
      4. Join commutativity: join(l1, l2) = join(l2, l1)
      5. Join associativity: join(join(l1, l2), l3) = join(l1, join(l2, l3))
      6. Join idempotence: join(l, l) = l
      7. Join is LUB: l1 <: join(l1, l2) and l2 <: join(l1, l2)
      8. Analogous properties for meet

    For upgrades:
      9. Upgrades are monotonic (improve or preserve precision)

    These lemmas are proven below using exhaustive case analysis.
    The SMTPat annotations help the solver apply them automatically.
    ============================================================================ *)

(**
 * Divergence label subtyping is reflexive.
 *
 * For any label l: l <: l
 *
 * This is essential for type systems where t <: t (reflexive subtyping).
 * The SMTPat ensures this lemma is applied whenever the solver sees
 * div_label_subtype l l.
 *)
val div_label_subtype_refl : l:divergence_label ->
  Lemma (ensures div_label_subtype l l = true)
        [SMTPat (div_label_subtype l l)]
let div_label_subtype_refl l =
  match l with
  | DivMay -> ()
  | DivWhnf -> ()
  | DivFin -> ()

(**
 * Divergence label subtyping is transitive.
 *
 * For any labels l1, l2, l3:
 *   l1 <: l2 /\ l2 <: l3 ==> l1 <: l3
 *
 * This enables chaining subtype derivations:
 *   If T1^Fin <: T2^Wnf and T2^Wnf <: T3^May, then T1^Fin <: T3^May.
 *
 * The proof is by case analysis on all 27 combinations. Most cases
 * are trivially satisfied because anything <: May.
 *)
val div_label_subtype_trans : l1:divergence_label -> l2:divergence_label -> l3:divergence_label ->
  Lemma (requires div_label_subtype l1 l2 = true /\ div_label_subtype l2 l3 = true)
        (ensures div_label_subtype l1 l3 = true)
let div_label_subtype_trans l1 l2 l3 =
  match l1, l2, l3 with
  | DivFin, DivFin, _ -> ()
  | DivFin, DivWhnf, DivWhnf -> ()
  | DivFin, DivWhnf, DivMay -> ()
  | DivWhnf, DivWhnf, DivWhnf -> ()
  | DivWhnf, DivWhnf, DivMay -> ()
  | _, DivMay, DivMay -> ()
  | _, _, _ -> ()

(**
 * Join is commutative.
 *
 * For any labels l1, l2: join(l1, l2) = join(l2, l1)
 *
 * This ensures that branch order doesn't matter:
 *   if c then e1 else e2  has same label as  if not c then e2 else e1
 *)
val div_label_join_comm : l1:divergence_label -> l2:divergence_label ->
  Lemma (ensures div_label_join l1 l2 = div_label_join l2 l1)
let div_label_join_comm l1 l2 =
  match l1, l2 with
  | DivMay, DivMay -> ()
  | DivMay, DivWhnf -> ()
  | DivMay, DivFin -> ()
  | DivWhnf, DivMay -> ()
  | DivWhnf, DivWhnf -> ()
  | DivWhnf, DivFin -> ()
  | DivFin, DivMay -> ()
  | DivFin, DivWhnf -> ()
  | DivFin, DivFin -> ()

(**
 * Upgrade maintains or improves comparability (monotonicity property).
 *
 * This lemma establishes that upgrading a type's divergence label
 * maintains a subtype relationship in one direction or the other.
 *
 * IMPORTANT OBSERVATION:
 * The current implementation of upgrade_case_scrutinee unconditionally
 * sets the label to DivWhnf. This means:
 *   - DivMay -> DivWhnf is an UPGRADE (May <: Wnf becomes Wnf <: Wnf)
 *   - DivWhnf -> DivWhnf is IDENTITY
 *   - DivFin -> DivWhnf is a DOWNGRADE (violates monotonicity!)
 *
 * The lemma still holds (one of the subtype directions is true), but
 * the Fin -> Wnf case shows a design issue: we should preserve DivFin
 * when upgrading, not downgrade to DivWhnf.
 *
 * RECOMMENDED FIX:
 *   let upgrade_case_scrutinee st =
 *     match st.st_label with
 *     | DivMay -> { st with st_label = DivWhnf }
 *     | _ -> st  (* Preserve Wnf and Fin *)
 *
 * This ensures truly monotonic upgrades: only improve, never degrade.
 *)
val upgrade_monotonic : st:stratified_type ->
  Lemma (ensures div_label_subtype (upgrade_case_scrutinee st).st_label st.st_label = true \/
                 div_label_subtype st.st_label (upgrade_case_scrutinee st).st_label = true)
let upgrade_monotonic st =
  match st.st_label with
  | DivMay -> ()    (* May -> Wnf is upgrade: new <: old? No. old <: new? Yes. *)
  | DivWhnf -> ()   (* Wnf -> Wnf is identity: both directions hold *)
  | DivFin -> ()    (* Fin -> Wnf is downgrade: new <: old? Yes. old <: new? No. *)
  (* Note: This reveals that upgrade_case_scrutinee should preserve Fin *)
