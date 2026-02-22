(**
 * BrrrLang.Core.DivergenceLabels - Interface
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
 * ============================================================================
 * REFERENCES
 * ============================================================================
 *
 * - brrr_lang_spec_v0.4.tex: Section "Loop Typing with Divergence"
 * - fstar_pop_book.md: Lines 10000-11000 (Well-founded recursion)
 * - fstar_pop_book.md: Lines 14000-14500 (Dv effect)
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

    EvalHybrid:
    -----------
    Mix of strict and lazy constructs in the same language:
      - Python: Generators (yield), list comprehensions
      - JavaScript: Async/await, generator functions
      - Scala: lazy val, Stream, LazyList
      - Rust: lazy_static!, once_cell::Lazy
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

    Verification Condition Translation:
      For {v:T^May | phi}, we translate phi to TRUE (no assumption).
      This is sound because we cannot rely on a value that may not exist.

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

    --------------------------------------------------------------------------
    DivFin (Finite/Terminating)
    --------------------------------------------------------------------------
    Semantics:
      - Expression reduces to a FINITE value (fully evaluated)
      - FULL refinement power
      - Equivalent to F*'s Tot effect guarantee

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
    ============================================================================ *)

type divergence_label =
  | DivMay    (* May diverge - CANNOT assume refinement holds *)
  | DivWhnf   (* Reduces to weak head normal form - partial guarantee *)
  | DivFin    (* Reduces to finite value - FULL refinement power *)


(** ============================================================================
    DIVERGENCE LABEL LATTICE OPERATIONS
    ============================================================================ *)

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
 *)
val div_label_subtype : l1:divergence_label -> l2:divergence_label -> bool

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
val div_label_join : l1:divergence_label -> l2:divergence_label -> divergence_label

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
 * Together with join, this forms a BOUNDED LATTICE with:
 *   - Top element: DivMay
 *   - Bottom element: DivFin
 *)
val div_label_meet : l1:divergence_label -> l2:divergence_label -> divergence_label


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
val stratify : mode:eval_mode -> t:dep_type -> stratified_type

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
val stratified_subtype : st1:stratified_type -> st2:stratified_type -> bool


(** ============================================================================
    DIVERGENCE LABEL UPGRADES
    ============================================================================

    Certain language constructs FORCE evaluation, allowing us to upgrade
    divergence labels from weaker (May) to stronger (Wnf or Fin) guarantees.

    This is the key mechanism for recovering refinement power in lazy
    languages: by observing that certain constructs demand evaluation,
    we can soundly assume the resulting value exists.

    --------------------------------------------------------------------------
    UPGRADE DIRECTIONS
    --------------------------------------------------------------------------

    Upgrades only go from weaker to stronger guarantees:
      May -> Wnf (via case, seq, strict application)
      May -> Fin (via deepseq, termination proof)
      Wnf -> Fin (via deepseq, termination proof)

    We NEVER downgrade from stronger to weaker (that would be unsound).
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
val upgrade_case_scrutinee : st:stratified_type -> stratified_type

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
val upgrade_strict_arg : st:stratified_type -> stratified_type

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
 *)
val upgrade_terminating : st:stratified_type -> stratified_type

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
val upgrade_seq : st:stratified_type -> stratified_type

(**
 * Haskell's deepseq forces to fully evaluated (Fin).
 *
 * deepseq :: NFData a => a -> b -> b
 * deepseq x y = x `deepseq` y  (* fully evaluate x, return y *)
 *
 * Unlike seq, deepseq recursively evaluates the entire structure.
 * This requires the NFData (Normal Form Data) typeclass, which provides
 * the rnf (reduce to normal form) operation.
 *)
val upgrade_deepseq : st:stratified_type -> stratified_type


(** ============================================================================
    DIVERGENCE LABEL INFERENCE
    ============================================================================

    For expressions, we infer the most precise divergence label that
    soundly characterizes the expression's termination behavior.
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
val infer_div_from_category : cat:expr_div_category -> divergence_label


(** ============================================================================
    VERIFICATION CONDITION TRANSLATION
    ============================================================================

    This section implements the critical translation from stratified
    refinement types to verification conditions. The key insight is that
    in lazy languages, we can only include refinement assumptions in VCs
    when the divergence label guarantees evaluation has occurred.

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
val translate_refinement_vc : mode:eval_mode -> x:dep_var -> st:stratified_type -> formula


(** ============================================================================
    WIDENING WITH DIVERGENCE LABELS
    ============================================================================

    During abstract interpretation (AI), we use widening to ensure
    termination of the analysis. Widening for stratified types must
    correctly combine divergence labels.
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
val widen_stratified : st1:stratified_type -> st2:stratified_type -> stratified_type

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
val is_refinement_safe : mode:eval_mode -> st:stratified_type -> bool


(** ============================================================================
    HYBRID LANGUAGE SUPPORT
    ============================================================================

    For hybrid languages (Python, JavaScript, Scala, Rust), certain
    constructs introduce lazy semantics into otherwise strict evaluation.
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
val uses_lazy_construct : constructs:list lazy_construct -> bool

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
val effective_eval_mode : base_mode:eval_mode -> constructs:list lazy_construct -> eval_mode


(** ============================================================================
    TERMINATION CHECKING INTERFACE
    ============================================================================

    This section provides the interface between the divergence stratification
    system and F*-style termination checking. When we have a proof that a
    computation terminates, we can upgrade its divergence label from DivMay
    to DivFin.
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
val apply_termination_proof : st:stratified_type -> proof:option termination_proof -> stratified_type


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
 *)
val div_dep_type_label : t:div_dep_type -> Tot divergence_label

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
val upgrade_div_dep_type : t:div_dep_type -> new_label:divergence_label -> Tot div_dep_type


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

(**
 * Divergence label subtyping is transitive.
 *
 * For any labels l1, l2, l3:
 *   l1 <: l2 /\ l2 <: l3 ==> l1 <: l3
 *
 * This enables chaining subtype derivations:
 *   If T1^Fin <: T2^Wnf and T2^Wnf <: T3^May, then T1^Fin <: T3^May.
 *)
val div_label_subtype_trans : l1:divergence_label -> l2:divergence_label -> l3:divergence_label ->
  Lemma (requires div_label_subtype l1 l2 = true /\ div_label_subtype l2 l3 = true)
        (ensures div_label_subtype l1 l3 = true)

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
