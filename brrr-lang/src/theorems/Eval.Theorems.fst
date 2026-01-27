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

#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"

(** Helper lemma: PatVar always matches and binds the value.

    This captures the fundamental property that variable patterns
    are irrefutable - they always match any value.

    Delegates to match_pattern_patvar from Values.fsti which has the
    SMTPat trigger for automatic application. *)
val patvar_always_matches : x:var_id -> v:value ->
    Lemma (ensures match_pattern (locate_dummy (PatVar x)) v == Some [(x, v)])
    [SMTPat (match_pattern (locate_dummy (PatVar x)) v)]

let patvar_always_matches x v =
  (* Delegate to the lemma from Values.fst *)
  match_pattern_patvar x v


(** Helper lemma: extend_many with singleton is equivalent to extend.

    This relates the batch environment extension used in match_pattern
    binding application to the single-variable extend operation.

    NOTE: Uses Values.extend_many_singleton which has the SMTPat trigger. *)
val extend_many_singleton_thm : x:var_id -> v:value -> e:env ->
    Lemma (ensures Values.extend_many [(x, v)] e == extend x v e)
    [SMTPat (Values.extend_many [(x, v)] e)]

let extend_many_singleton_thm x v e =
  (* Delegate to Values.extend_many_singleton *)
  Values.extend_many_singleton x v e


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
  (* This theorem has the same statement as eval_let_binding from Eval.fsti.
     The proof is provided in Eval.fst with direct access to the definitions.
     We simply invoke that lemma here. *)
  eval_let_binding fuel x e1 e2 st v1

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

(** Helper lemma: Any write operation keeps locations valid.

    After writing to any location l_write:
    - If l = l_write: read l returns Some (the new value)
    - If l <> l_write: read l is unchanged

    In both cases, if l was valid before (or l = l_write), l is valid after. *)
val write_keeps_valid : l_write:loc -> v:value -> h:heap -> l:loc ->
    Lemma
      (requires Some? (read l h) \/ l = l_write)
      (ensures Some? (read l (write l_write v h)))

let write_keeps_valid l_write v h l =
  if l = l_write then
    (* By write_updates: read l_write (write l_write v h) == Some v *)
    write_updates l_write v h
  else
    (* By write_preserves: read l (write l_write v h) == read l h *)
    write_preserves l_write v h l

let alloc_preserves_valid v h l =
  (* Proof:
     1. Let (l_new, h') = alloc v h
     2. By alloc_fresh: read l_new h == None
     3. But precondition: Some? (read l h), so read l h <> None
     4. Therefore l <> l_new
     5. By alloc_preserves: read l h' == read l h
     6. Therefore Some? (read l h')
  *)
  let (l_new, h') = alloc v h in
  (* By alloc_fresh, read l_new h == None (triggered by SMTPat) *)
  alloc_fresh v h;
  (* Since Some? (read l h) but read l_new h == None, we have l <> l_new *)
  assert (l <> l_new);
  (* By alloc_preserves, since l <> l_new, read l h' == read l h *)
  alloc_preserves v h l;
  (* Therefore Some? (read l h') since Some? (read l h) *)
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
  (* Proof:
     By write_preserves from Values.fst (triggered by SMTPat):
     - Precondition: l <> l_write
     - write_preserves establishes: read l (write l_write v h) == read l h
     - Since Some? (read l h), we have Some? (read l (write l_write v h))
  *)
  write_preserves l_write v h l


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
  (* The full proof is implemented in Eval.fst via structural induction.
     We invoke that proof here. *)
  eval_preserves_valid_locs fuel e st l

#pop-options


(** ----------------------------------------------------------------------------
    COROLLARY: HEAP MONOTONICITY (HEAP ONLY GROWS)
    ----------------------------------------------------------------------------

    This is a direct consequence of T-3.3. The set of valid heap locations
    only grows during evaluation - no location ever becomes invalid.

    This property is crucial for:
    - Memory safety reasoning
    - Proving absence of dangling references
    - Establishing that borrows remain valid during evaluation
    --------------------------------------------------------------------------- *)

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** Predicate: All locations valid in h1 are also valid in h2.
    This captures "heap monotonicity" or "heap grows". *)
let heap_extends (h1 h2: heap) : Type0 =
  forall (l: loc). Some? (read l h1) ==> Some? (read l h2)

(** Corollary: Evaluation only extends the heap (never shrinks it).

    If h1 is the initial heap and h2 is the final heap after evaluation,
    then every location valid in h1 is also valid in h2. *)
val eval_heap_monotone :
    fuel:nat ->
    e:expr ->
    st:eval_state ->
    Lemma (ensures heap_extends st.es_heap (snd (eval_expr fuel e st)).es_heap)

let eval_heap_monotone fuel e st =
  (* Prove the forall by introducing it with a proof function *)
  let aux (l: loc) : Lemma (Some? (read l st.es_heap) ==> Some? (read l (snd (eval_expr fuel e st)).es_heap)) =
    if Some? (read l st.es_heap) then
      eval_preserves_valid_locs fuel e st l
    else ()
  in
  FStar.Classical.forall_intro aux

(** Alternative form: Valid locations form a subset that only grows. *)
val valid_locs_subset_after_eval :
    fuel:nat ->
    e:expr ->
    st:eval_state ->
    l:loc ->
    Lemma
      (requires Some? (read l st.es_heap))
      (ensures Some? (read l (snd (eval_expr fuel e st)).es_heap))
    [SMTPat (eval_expr fuel e st); SMTPat (read l st.es_heap)]

let valid_locs_subset_after_eval fuel e st l =
  eval_preserves_valid_locs_thm fuel e st l

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
  (* The full proof is implemented in Eval.fst via structural induction.

     Proof Strategy (see Eval.fst for implementation):
     ================================================

     1. Define environment agreement predicate:
        envs_agree_on vars env1 env2 :=
          forall x. mem x vars ==> lookup x env1 == lookup x env2

     2. Prove generalized lemma (eval_env_irrelevant):
        If states agree except on es_env, and environments agree on
        free_vars(e), then evaluation produces the same result.

     3. For closed expressions (free_vars e = []):
        Environments trivially agree on empty set of variables,
        so the result follows from the generalized lemma.

     Key Cases in Structural Induction:
     - EVar x: x is in free_vars(e), so lookup x env1 == lookup x env2
     - ELit: No environment access, identical results
     - ELet p _ e1 e2: By IH on e1, get same value. Extend both envs
       with same bindings. By IH on e2, get same result.
     - ELambda: Creates closure capturing current env. Returns same
       closure ID since closure stores are equal.

     The proof handles ~50 expression cases following eval_expr structure.
     Some cases use admit() where detailed state tracking is required.
  *)
  eval_closed_env_irrelevant fuel e st1 st2

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
     Therefore is_closed e <==> (forall x. not (mem x (free_vars e)))

     NOTE: Requires access to free_vars definition and list membership properties.
     This is a supporting lemma for T-4.2, not the main T-1.6 theorem. *)
  admit ()


(** Free variables are closed under subexpression.

    If x is free in a subexpression and not shadowed, it's free in
    the containing expression. This is used in the induction. *)
val free_vars_subexpr : e:expr -> x:var_id ->
    Lemma
      (requires List.Tot.mem x (free_vars e))
      (ensures not (is_closed e))

let free_vars_subexpr e x =
  (* If x is in free_vars e, then free_vars e is non-empty,
     so Nil? (free_vars e) = false, so is_closed e = false.

     NOTE: Supporting lemma for T-4.2. *)
  admit ()


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
     Some? (read l st'.es_heap) by that theorem.

     NOTE: Requires eval_preserves_valid_locs_thm (T-3.3) to be proven first. *)
  admit ()

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
