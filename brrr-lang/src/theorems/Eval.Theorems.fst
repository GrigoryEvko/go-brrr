(**
 * Eval.Theorems - Formal Theorems for Evaluation Semantics
 *
 * This module contains theorems about the big-step operational semantics
 * defined in Eval.fst. These theorems are identified in AXIOMS_REPORT_v2.md
 * as provable statements (not axioms).
 *
 * Theorems included:
 * - T-1.6: eval_let_binding - Let binding evaluation correctness
 * - T-3.3: eval_preserves_valid_locs - Evaluation preserves heap location validity
 * - T-4.2: eval_closed_env_irrelevant - Closed expressions ignore environment
 *
 * Proof Status: All theorems currently use admit() as placeholders.
 * Full proofs require structural induction over expressions.
 *
 * References:
 * - brrr_lang_spec_v0.4.tex Part I (Foundations)
 * - AXIOMS_REPORT_v2.md Section: PART III: THEOREMS TO PROVE
 *)
module Eval.Theorems

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open Primitives
open Modes
open Effects
open Utils
open BrrrTypes
open Expressions
open Values
open Eval
open FStar.List.Tot

(** ============================================================================
    THEOREM T-1.6: LET BINDING EVALUATION CORRECTNESS
    ============================================================================

    Report ID: T-1.6
    Location: Eval.fst:2332
    Priority: 1 (Low-Hanging Fruit)
    Effort Estimate: 1-2 hours

    Statement: Let binding evaluation is correct - evaluating (let p = e1 in e2)
    where e1 evaluates to v1 is equivalent to evaluating e2 in an environment
    extended with the pattern bindings from matching p against v1.

    Proof Strategy:
    1. Evaluate e1 to get value v1 and state st1
    2. Show match_pattern on PatVar x with v1 produces Some [(x, v1)]
    3. Show extend_many with this singleton list is equivalent to extend x v1
    4. Conclude evaluation of body in extended env produces correct result

    Key Insight: For simple variable patterns (PatVar x), match_pattern
    always succeeds with the singleton binding [(x, v)]. This simplifies
    the proof considerably compared to complex patterns.
    ============================================================================ *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"

(** Helper lemma: PatVar always matches and binds the value.

    This captures the fundamental property that variable patterns
    are irrefutable - they always match any value. *)
val patvar_always_matches : x:var_id -> v:value ->
    Lemma (ensures match_pattern (locate_dummy (PatVar x)) v == Some [(x, v)])
    [SMTPat (match_pattern (locate_dummy (PatVar x)) v)]

let patvar_always_matches x v =
  (* By definition of match_pattern for PatVar case *)
  ()


(** Helper lemma: extend_many with singleton is equivalent to extend.

    This relates the batch environment extension used in match_pattern
    binding application to the single-variable extend operation. *)
val extend_many_singleton : x:var_id -> v:value -> e:env ->
    Lemma (ensures extend_many [(x, v)] e == extend x v e)
    [SMTPat (extend_many [(x, v)] e)]

let extend_many_singleton x v e =
  (* By definition: extend_many [(x,v)] e = [(x,v)] @ e = (x,v) :: e = extend x v e *)
  ()


(** T-1.6: Let Binding Evaluation Correctness

    For a simple let binding (let x = e1 in e2), if e1 evaluates to v1,
    then the entire let expression evaluates to the same result as e2
    evaluated in an environment where x is bound to v1.

    Formal Statement:
    Given:
      - fuel >= 3 (enough for outer let + inner evaluations)
      - eval_expr (fuel-1) e1 st produces (ROk v1, st1)
    Then:
      - eval_expr fuel (ELet (PatVar x) None e1 e2) st produces result r
      - r == fst (eval_expr (fuel-1) e2 { st1 with es_env = extend x v1 st1.es_env })

    This theorem establishes the semantic equivalence between let binding
    and explicit substitution/environment extension.
*)
val eval_let_binding_correct :
    fuel:nat ->
    x:var_id ->
    e1:expr ->
    e2:expr ->
    st:eval_state ->
    v1:value ->
    Lemma
      (requires
        fuel >= 3 /\
        fst (eval_expr (fuel - 1) e1 st) == ROk v1)
      (ensures (
        let (_, st1) = eval_expr (fuel - 1) e1 st in
        let st_bound = { st1 with es_env = extend x v1 st1.es_env } in
        let p = locate_dummy (PatVar x) in
        let let_expr = mk_expr_dummy (ELet p None e1 e2) in
        let (r, _) = eval_expr fuel let_expr st in
        r == fst (eval_expr (fuel - 1) e2 st_bound)))

let eval_let_binding_correct fuel x e1 e2 st v1 =
  (* Proof outline:

     1. By definition, eval_expr fuel (ELet p None e1 e2) st:
        - First evaluates e1 with (fuel-1), getting (ROk v1, st1)
        - Then calls match_pattern p v1
        - For PatVar x, this returns Some [(x, v1)]
        - Extends st1.es_env with [(x, v1)] = extend x v1 st1.es_env
        - Evaluates e2 in the extended environment

     2. By patvar_always_matches: match_pattern (PatVar x) v1 = Some [(x, v1)]

     3. By extend_many_singleton: extend_many [(x, v1)] env = extend x v1 env

     4. Therefore the result matches eval_expr (fuel-1) e2 st_bound

     Full proof requires unwinding eval_expr definition for ELet case
     and showing each step preserves the claimed equality.
  *)
  admit ()

#pop-options


(** ============================================================================
    THEOREM T-3.3: EVALUATION PRESERVES VALID LOCATIONS
    ============================================================================

    Report ID: T-3.3
    Location: Eval.fst:2249
    Priority: 3 (Substantial Effort)
    Effort Estimate: 3-5 hours

    Statement: If a heap location is valid (readable) before evaluation,
    it remains valid after evaluation. In other words, evaluation never
    deallocates heap locations.

    Proof Strategy:
    1. Prove alloc only adds new locations (never overwrites)
    2. Prove write only updates existing locations (never removes)
    3. Show by structural induction that all evaluation cases preserve
       existing locations while potentially adding new ones

    Key Insight: The heap grows monotonically during evaluation.
    This is a fundamental memory safety property.

    Dependencies:
    - Heap operation specifications from Values.fst:
      - alloc_fresh: alloc returns fresh location
      - write_updates/write_preserves: write is localized
      - No dealloc in normal evaluation (only in drop/cleanup)
    ============================================================================ *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** Helper lemma: Heap allocation preserves existing locations.

    When we allocate a new value on the heap, all previously valid
    locations remain valid and retain their values. *)
val alloc_preserves_valid : v:value -> h:heap -> l:loc ->
    Lemma
      (requires Some? (read l h))
      (ensures (let (_, h') = alloc v h in Some? (read l h')))
    [SMTPat (alloc v h); SMTPat (read l h)]

let alloc_preserves_valid v h l =
  (* By alloc_preserves from Values.fst:
     alloc prepends a new (fresh_loc, v) pair to the heap.
     Since fresh_loc != l (by freshness), read l h' = read l h.
     Therefore Some? (read l h) ==> Some? (read l h'). *)
  let (new_l, h') = alloc v h in
  if new_l = l then
    (* Contradiction: new_l is fresh, so read new_l h = None
       But we require Some? (read l h), and l = new_l would mean
       Some? (read new_l h) = Some? None = false. Contradiction. *)
    ()
  else
    (* new_l <> l, so by alloc_preserves: read l h' = read l h *)
    ()


(** Helper lemma: Heap write preserves other locations.

    When we write to a location, all other locations remain valid
    and retain their values. *)
val write_preserves_valid : l_write:loc -> v:value -> h:heap -> l:loc ->
    Lemma
      (requires Some? (read l h) /\ l <> l_write)
      (ensures Some? (read l (write l_write v h)))
    [SMTPat (write l_write v h); SMTPat (read l h)]

let write_preserves_valid l_write v h l =
  (* By write_preserves from Values.fst:
     write l_write v h updates only location l_write.
     For l <> l_write, read l (write l_write v h) = read l h.
     Therefore Some? (read l h) ==> Some? (read l (write l_write v h)). *)
  ()


(** T-3.3: Evaluation Preserves Valid Locations

    If a heap location l is valid (readable) in the initial state,
    then l remains valid in the final state after evaluation,
    regardless of what the expression does.

    Formal Statement:
    Given:
      - A heap location l that is valid: Some? (read l st.es_heap)
    Then:
      - After evaluation: Some? (read l st'.es_heap)
        where (_, st') = eval_expr fuel e st

    This theorem establishes heap monotonicity: the set of valid
    heap locations only grows during evaluation.

    Proof requires structural induction on expressions, showing
    that each expression form either:
    - Leaves the heap unchanged
    - Adds new locations via alloc (preserving existing)
    - Updates existing locations via write (preserving validity)
*)
val eval_preserves_valid_locs_thm :
    fuel:nat ->
    e:expr ->
    st:eval_state ->
    l:loc ->
    Lemma
      (requires Some? (read l st.es_heap))
      (ensures (
        let (_, st') = eval_expr fuel e st in
        Some? (read l st'.es_heap)))

let eval_preserves_valid_locs_thm fuel e st l =
  (* Proof outline (structural induction on e):

     Base cases:
     - ELit: heap unchanged, trivially preserves
     - EVar: heap unchanged, trivially preserves
     - EGlobal: heap unchanged, trivially preserves

     Allocation cases (ERef, EBox, EArray creation):
     - By alloc_preserves_valid, existing locations preserved

     Write cases (EAssign, field update):
     - By write_preserves_valid, other locations preserved
     - The written location itself remains valid (just updated)

     Compound cases (ELet, EIf, ECall, etc.):
     - By induction hypothesis on subexpressions
     - Heap changes are composition of preserving operations

     The full proof requires ~200-300 lines of case analysis
     following the structure of eval_expr.
  *)
  admit ()

#pop-options


(** ============================================================================
    THEOREM T-4.2: CLOSED EXPRESSIONS IGNORE ENVIRONMENT
    ============================================================================

    Report ID: T-4.2
    Location: Eval.fst:2188
    Priority: 4 (High Effort)
    Effort Estimate: 4-6 hours

    Statement: For closed expressions (no free variables), evaluation
    depends only on the heap, closure store, and globals - not on the
    local environment.

    Proof Strategy:
    1. Define closedness: free_vars e == []
    2. Show by structural induction that variable lookups only occur
       for variables in free_vars
    3. Conclude that if free_vars is empty, es_env is never consulted
    4. Therefore different environments produce identical results

    Key Insight: Variable references in closed terms are either:
    - Global variables (from es_globals)
    - Closure-captured variables (from closure environments)
    Neither depends on the local environment es_env.

    Applications:
    - Modular reasoning: can evaluate closed subexpressions in any context
    - Optimization: closed functions can be hoisted/memoized
    - Verification: simplifies reasoning about scope
    ============================================================================ *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** Predicate: Expression has no free variables.

    Wraps the is_closed function from Eval.fst for theorem statements. *)
let closed (e: expr) : Type0 = is_closed e = true


(** Helper lemma: Lookup is only performed for free variables.

    If variable x is looked up during evaluation, then x must be
    in the free variables of the expression. Contrapositive: if
    x is not free, it is never looked up. *)
val lookup_only_free : fuel:nat -> e:expr -> st:eval_state -> x:var_id ->
    Lemma
      (requires not (List.Tot.mem x (free_vars e)))
      (ensures (
        (* If we change only the binding for x, result is unchanged *)
        forall (v:value).
          let st' = { st with es_env = extend x v st.es_env } in
          fst (eval_expr fuel e st') == fst (eval_expr fuel e st)))

let lookup_only_free fuel e st x =
  (* Proof outline:
     By structural induction on e.

     Key cases:
     - EVar y: If y is not free, then y <> x (by precondition x not free).
               But EVar y means y IS free in e. So y <> x, and extending
               with x doesn't affect lookup of y.

     - ELet (PatVar y) _ e1 e2: y is bound in e2, so free_vars includes
               free_vars(e1) and free_vars(e2) minus y.
               By IH on e1 and e2.

     - ELambda params body: params are bound in body.
               Free vars of lambda are free_vars(body) minus params.
               By IH on body.

     This is a standard property of variable binding and
     would follow from a substitution lemma.
  *)
  admit ()


(** T-4.2: Closed Expression Environment Irrelevance

    For closed expressions, the local environment does not affect
    evaluation. Two states with different local environments but
    identical heap, closures, globals, handlers, and methods
    produce identical evaluation results.

    Formal Statement:
    Given:
      - e is closed: is_closed e = true (equivalently: free_vars e = [])
      - st1 and st2 agree on: heap, closures, globals, handlers, methods
      - st1 and st2 may differ on: es_env (local environment)
    Then:
      - fst (eval_expr fuel e st1) == fst (eval_expr fuel e st2)

    This theorem is fundamental for modular reasoning: we can analyze
    closed subexpressions without knowing the surrounding context.
*)
val eval_closed_env_irrelevant_thm :
    fuel:nat ->
    e:expr ->
    st1:eval_state ->
    st2:eval_state ->
    Lemma
      (requires
        is_closed e /\
        st1.es_heap == st2.es_heap /\
        st1.es_closures == st2.es_closures /\
        st1.es_globals == st2.es_globals /\
        st1.es_handlers == st2.es_handlers /\
        st1.es_methods == st2.es_methods)
      (ensures
        fst (eval_expr fuel e st1) == fst (eval_expr fuel e st2))

let eval_closed_env_irrelevant_thm fuel e st1 st2 =
  (* Proof outline:

     Since free_vars e = [], the expression e contains no references
     to variables that would be looked up in es_env.

     All variable references in e are one of:
     1. Bound by an enclosing binder (let, lambda, match, for)
        - These are resolved from the environment extensions made
          during evaluation, not from the initial es_env

     2. Global variables
        - Resolved from es_globals, which is equal in st1 and st2

     3. Closure-captured variables
        - Resolved from the closure's captured environment,
          stored in es_closures, which is equal in st1 and st2

     By structural induction on e:

     Base cases:
     - ELit: No environment access, result is literal value
     - EVar x: Impossible! x would be in free_vars e = [], contradiction
     - EGlobal g: Uses es_globals, equal in st1 and st2

     Inductive cases (ELet, ELambda, ECall, etc.):
     - By IH, closed subexpressions produce equal results
     - New bindings affect both st1 and st2 equally
     - Therefore compound results are equal

     The key insight is that eval_expr only consults es_env when
     evaluating EVar, and EVar of free variable x means x is in
     free_vars, contradicting the closedness assumption.

     Full proof requires ~300-400 lines following eval_expr structure.
  *)
  admit ()

#pop-options


(** ============================================================================
    ADDITIONAL SUPPORTING LEMMAS
    ============================================================================

    These lemmas support the main theorems and may be useful for
    other evaluation-related proofs.
    ============================================================================ *)

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"

(** Closed expression characterization: no variables are free.

    This relates the boolean is_closed predicate to a more semantic
    characterization using list membership. *)
val closed_means_no_free_vars : e:expr ->
    Lemma (ensures is_closed e <==> (forall x. not (List.Tot.mem x (free_vars e))))

let closed_means_no_free_vars e =
  (* is_closed e = Nil? (free_vars e)
     Nil? l <==> (forall x. not (mem x l))
     Therefore is_closed e <==> (forall x. not (mem x (free_vars e))) *)
  ()


(** Free variables are closed under subexpression.

    If x is free in a subexpression and not shadowed, it's free in
    the containing expression. This is used in the induction. *)
val free_vars_subexpr : e:expr -> x:var_id ->
    Lemma
      (requires List.Tot.mem x (free_vars e))
      (ensures not (is_closed e))

let free_vars_subexpr e x =
  (* If x is in free_vars e, then free_vars e is non-empty,
     so Nil? (free_vars e) = false, so is_closed e = false. *)
  ()


(** Heap growth lemma: evaluation may only add locations.

    The set of valid heap locations after evaluation is a superset
    of the valid locations before evaluation. *)
val heap_grows : fuel:nat -> e:expr -> st:eval_state ->
    Lemma (ensures (
      let (_, st') = eval_expr fuel e st in
      forall (l:loc). Some? (read l st.es_heap) ==> Some? (read l st'.es_heap)))

let heap_grows fuel e st =
  (* This follows from eval_preserves_valid_locs_thm.
     For any l with Some? (read l st.es_heap), we have
     Some? (read l st'.es_heap) by that theorem. *)
  Classical.forall_intro (eval_preserves_valid_locs_thm fuel e st)

#pop-options


(** ============================================================================
    THEOREM VERIFICATION STATUS
    ============================================================================

    Status of each theorem:

    T-1.6 (eval_let_binding_correct):
      - Status: ADMIT (placeholder)
      - Dependencies: patvar_always_matches, extend_many_singleton
      - Estimated effort: 1-2 hours
      - Key challenge: Unwinding eval_expr for ELet case

    T-3.3 (eval_preserves_valid_locs_thm):
      - Status: ADMIT (placeholder)
      - Dependencies: alloc_preserves_valid, write_preserves_valid
      - Estimated effort: 3-5 hours
      - Key challenge: ~30 cases in structural induction

    T-4.2 (eval_closed_env_irrelevant_thm):
      - Status: ADMIT (placeholder)
      - Dependencies: lookup_only_free, closed_means_no_free_vars
      - Estimated effort: 4-6 hours
      - Key challenge: Showing EVar is never reached for closed e

    Total estimated effort: 8-13 hours for full verification
    ============================================================================ *)
