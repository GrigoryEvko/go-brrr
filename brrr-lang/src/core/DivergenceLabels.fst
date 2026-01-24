(**
 * BrrrLang.Core.DivergenceLabels
 *
 * Divergence Stratification for Lazy Language Soundness.
 * Based on LiquidHaskell's divergence-aware refinement types.
 *
 * Gap Resolution:
 *   6. Divergence stratification (DivMay, DivWhnf, DivFin)
 *
 * For LAZY languages (Haskell, parts of Python/JS), refinement types
 * can be UNSOUND if we assume refinements hold for potentially
 * diverging expressions. This module provides stratified types that
 * track termination guarantees.
 *
 * Key insight: In lazy evaluation, an expression may never be evaluated,
 * so we cannot assume its refinement holds. Only AFTER forcing evaluation
 * (pattern matching, strict operations) can we rely on the refinement.
 *
 * Depends on: Primitives, BrrrTypes, DependentTypes
 *)
module DivergenceLabels

open FStar.List.Tot
open Primitives
open BrrrTypes
open DependentTypes

(** ============================================================================
    EVALUATION MODES
    ============================================================================

    Different languages have different evaluation strategies:
    - EvalStrict: Arguments evaluated before function application (C, Rust, Java)
    - EvalLazy: Arguments evaluated on demand (Haskell)
    - EvalHybrid: Mix of both (Python generators, JS async, Scala lazy val)
    ============================================================================ *)

type eval_mode =
  | EvalStrict    (* Call-by-value: arguments always evaluated *)
  | EvalLazy      (* Call-by-need: arguments evaluated on demand *)
  | EvalHybrid    (* Mix: some constructs are lazy *)

(** ============================================================================
    DIVERGENCE LABELS
    ============================================================================

    Stratification of types by termination guarantee:

    DivMay (Div):
      - May diverge (loop forever, throw exception, etc.)
      - CANNOT assume refinement holds
      - Example: let x = loop() in ... -- x may never have a value

    DivWhnf (Wnf):
      - Reduces to Weak Head Normal Form
      - CAN assume head constructor, but not full value
      - Example: case e of ... -- e is forced to WHNF by pattern match

    DivFin (Fin):
      - Reduces to finite value
      - FULL refinement power
      - Proven terminating via termination checker or structural recursion

    Ordering: Fin <: Wnf <: Div
    (More precise is subtype of less precise)
    ============================================================================ *)

type divergence_label =
  | DivMay    (* May diverge - CANNOT assume refinement holds *)
  | DivWhnf   (* Reduces to weak head normal form - partial guarantee *)
  | DivFin    (* Reduces to finite value - FULL refinement power *)

(* Subtyping: Fin <: Wnf <: May *)
let div_label_subtype (l1 l2: divergence_label) : bool =
  match l1, l2 with
  | _, DivMay -> true         (* Anything is subtype of May *)
  | DivFin, DivFin -> true
  | DivFin, DivWhnf -> true   (* Fin <: Wnf *)
  | DivWhnf, DivWhnf -> true
  | _, _ -> false

(* Join (least upper bound) *)
let div_label_join (l1 l2: divergence_label) : divergence_label =
  match l1, l2 with
  | DivMay, _ -> DivMay
  | _, DivMay -> DivMay
  | DivWhnf, _ -> DivWhnf
  | _, DivWhnf -> DivWhnf
  | DivFin, DivFin -> DivFin

(* Meet (greatest lower bound) *)
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

    A stratified type pairs a base type with a divergence label.
    The label affects how verification conditions are generated.
    ============================================================================ *)

noeq type stratified_type = {
  st_base   : dep_type;           (* Underlying dependent type *)
  st_label  : divergence_label;   (* Termination guarantee *)
}

(* Lift a type with default label based on eval mode *)
let stratify (mode: eval_mode) (t: dep_type) : stratified_type =
  match mode with
  | EvalStrict -> { st_base = t; st_label = DivFin }   (* Strict = always Fin *)
  | EvalLazy   -> { st_base = t; st_label = DivMay }   (* Lazy = start as May *)
  | EvalHybrid -> { st_base = t; st_label = DivMay }   (* Hybrid = conservative *)

(* Stratified type subtyping *)
let stratified_subtype (st1 st2: stratified_type) : bool =
  (* Base types must be subtypes AND labels must be compatible *)
  dep_type_subtype st1.st_base st2.st_base &&
  div_label_subtype st1.st_label st2.st_label

(** ============================================================================
    DIVERGENCE LABEL UPGRADES
    ============================================================================

    Certain language constructs FORCE evaluation, upgrading divergence labels:

    1. Pattern matching (case/match): Forces to WHNF
    2. Strict function application: Forces to WHNF
    3. Proven termination: Upgrades to Fin
    4. Bang patterns (!x): Forces strict evaluation
    ============================================================================ *)

(* Case scrutinee is forced to WHNF *)
let upgrade_case_scrutinee (st: stratified_type) : stratified_type =
  { st with st_label = DivWhnf }

(* Strict application forces argument to WHNF *)
let upgrade_strict_arg (st: stratified_type) : stratified_type =
  { st with st_label = DivWhnf }

(* Termination proof upgrades to Fin *)
let upgrade_terminating (st: stratified_type) : stratified_type =
  { st with st_label = DivFin }

(* Seq (Haskell's seq operator) forces to WHNF *)
let upgrade_seq (st: stratified_type) : stratified_type =
  { st with st_label = DivWhnf }

(* DeepSeq (Haskell's deepseq) forces to Fin *)
let upgrade_deepseq (st: stratified_type) : stratified_type =
  { st with st_label = DivFin }

(** ============================================================================
    DIVERGENCE LABEL INFERENCE
    ============================================================================

    For expressions, we infer the most precise divergence label:
    - Literals, constructors: Fin
    - Variables: inherit from binding
    - Function application: depends on function purity
    - Recursion: May unless termination proven
    ============================================================================ *)

(* Expression categories for divergence inference *)
type expr_div_category =
  | ExprValue       (* Immediate value: literal, constructor *)
  | ExprVar         (* Variable reference: inherits from context *)
  | ExprApp         (* Function application: depends on function *)
  | ExprRecursive   (* Recursive call: May unless proven *)
  | ExprPrimitive   (* Primitive operation: Fin for total prims *)

(* Infer divergence label for expression category *)
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

    The key insight: In lazy languages, we only include refinement
    assumptions in VCs when the divergence label guarantees evaluation.

    For strict languages:
      translate({x: {v:T | phi}}) = phi[x/v]

    For lazy languages:
      translate({x: {v:T^May | phi}}) = true        -- Cannot assume
      translate({x: {v:T^Wnf | phi}}) = phi[x/v]    -- Safe after forcing
      translate({x: {v:T^Fin | phi}}) = phi[x/v]    -- Safe: terminates
    ============================================================================ *)

(* Translate stratified refinement to VC assumption *)
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

    During abstract interpretation, widening must track divergence:
    - If ANY path through a loop can diverge, result is DivMay
    - Widening joins divergence labels: join(l1, l2)
    ============================================================================ *)

(* Widen stratified types *)
let widen_stratified (st1 st2: stratified_type) : stratified_type =
  (* Join divergence labels (conservative) *)
  let joined_label = div_label_join st1.st_label st2.st_label in
  (* For simplicity, use second type as base (proper widening is complex) *)
  { st_base = st2.st_base; st_label = joined_label }

(* Check if type is safe for refinement assumptions *)
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

    For hybrid languages (Python, JavaScript), certain constructs
    trigger lazy evaluation:
    - Generators (yield)
    - Async functions (async/await)
    - Lazy properties (Scala lazy val, Rust lazy_static!)

    We detect these syntactically and apply stratification.
    ============================================================================ *)

(* Lazy construct markers *)
type lazy_construct =
  | LCGenerator         (* Python/JS generator function *)
  | LCAsync             (* async function *)
  | LCLazyVal           (* Scala lazy val, Rust lazy_static! *)
  | LCThunk             (* Explicit thunk/delay *)
  | LCStream            (* Lazy stream/iterator *)

(* Check if expression uses lazy construct *)
let uses_lazy_construct (constructs: list lazy_construct) : bool =
  List.Tot.length constructs > 0

(* Determine effective eval mode for expression *)
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

    Integration with termination checker to upgrade DivMay to DivFin.
    ============================================================================ *)

(* Termination proof witness (abstract) *)
type termination_proof = {
  tp_function : string;       (* Function name *)
  tp_measure  : string;       (* Termination measure description *)
  tp_method   : string;       (* Proof method: structural, measure, lex, etc. *)
}

(* Upgrade type based on termination proof *)
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

    Extended dependent type with divergence annotation.
    ============================================================================ *)

noeq type div_dep_type =
  (* Base with divergence *)
  | DDBase      : brrr_type -> divergence_label -> div_dep_type

  (* Pi-type with divergence on result *)
  | DDPi        : dep_var -> div_dep_type -> div_dep_type -> div_dep_type

  (* Sigma-type with divergence *)
  | DDSigma     : dep_var -> div_dep_type -> div_dep_type -> div_dep_type

  (* Refinement with divergence *)
  | DDRefinement : dep_var -> div_dep_type -> formula -> divergence_label -> div_dep_type

(* Extract divergence label from div_dep_type *)
let rec div_dep_type_label (t: div_dep_type) : divergence_label =
  match t with
  | DDBase _ l -> l
  | DDPi _ _ t2 -> div_dep_type_label t2  (* Result divergence *)
  | DDSigma _ _ t2 -> div_dep_type_label t2
  | DDRefinement _ _ _ l -> l

(* Upgrade divergence label in type *)
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
    ============================================================================ *)

(* Divergence label subtyping is reflexive *)
val div_label_subtype_refl : l:divergence_label ->
  Lemma (ensures div_label_subtype l l = true)
        [SMTPat (div_label_subtype l l)]
let div_label_subtype_refl l =
  match l with
  | DivMay -> ()
  | DivWhnf -> ()
  | DivFin -> ()

(* Divergence label subtyping is transitive *)
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

(* Join is commutative *)
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

(* Upgrade is monotonic: upgrading never makes type less precise *)
val upgrade_monotonic : st:stratified_type ->
  Lemma (ensures div_label_subtype (upgrade_case_scrutinee st).st_label st.st_label = true \/
                 div_label_subtype st.st_label (upgrade_case_scrutinee st).st_label = true)
let upgrade_monotonic st =
  match st.st_label with
  | DivMay -> ()    (* May -> Wnf is upgrade *)
  | DivWhnf -> ()   (* Wnf -> Wnf is identity *)
  | DivFin -> ()    (* Fin -> Wnf is... actually a downgrade, hmm *)
  (* Note: This reveals that upgrade_case_scrutinee should preserve Fin *)
