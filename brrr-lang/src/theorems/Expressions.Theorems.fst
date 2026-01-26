(**
 * Expressions.Theorems.fst - Formal Theorems for Expression AST
 *
 * This module collects and documents provable theorems about expressions
 * from AXIOMS_REPORT_v2.md Part III. Each theorem can and must be proven
 * from definitions and axioms - they are NOT axioms themselves.
 *
 * Theorem IDs from AXIOMS_REPORT_v2.md:
 *   T-1.3:  fresh_var_spec            (P1, ~1 hour)
 *   T-1.4:  merge_ranges_contains_left   (P1, 1-2 hours)
 *   T-1.5:  merge_ranges_contains_right  (P1, 1-2 hours)
 *   T-2.1:  is_subexpr_trans          (P2, 2-4 hours)
 *   T-2.2:  free_vars_subexpr         (P2, 2-3 hours)
 *   T-2.3:  subst_expr_non_free       (P2, 2-3 hours)
 *   T-3.1:  subst_expr_wf             (P3, 3-5 hours)
 *   T-3.2:  subst_expr_free_vars      (P3, 3-5 hours)
 *   T-4.1:  normalize_expr_equiv      (P4, 4-6 hours)
 *
 * Classification: DeferredProof (provable but requires mechanization effort)
 *
 * Literature References:
 *   - EverParse Ast.fst: Source location patterns, range handling
 *   - Barendregt 1984: Lambda calculus substitution theory
 *   - Pierce 2002 TAPL: Capture-avoiding substitution
 *   - Danvy-Filinski 1989: Normalization techniques
 *
 * @author brrr-lang team
 * @version 2.0
 * @since 2026-01-26
 *)
module Expressions.Theorems

open FStar.List.Tot
open Expressions

(* Friend declaration grants access to Expressions implementation details,
   required to see fresh_var_helper for the proof *)
friend Expressions


(* =============================================================================
   PRIORITY 1: LOW-HANGING FRUIT (<=2 hours each)
   =============================================================================
   These theorems require straightforward proofs - construction proofs,
   basic case analysis, or simple induction.
   ============================================================================= *)

(**
 * T-1.3: Fresh Variable Specification
 *
 * fresh_var returns a variable name not in the given set.
 *
 * Location: Expressions.fst:1963
 * Effort: ~1 hour
 * Proof Strategy: Construction proof - show fresh_var_helper finds unused name.
 *
 * Literature: Standard alpha-conversion (Barendregt 1984 Chapter 2)
 *
 * Classification: DeferredProof
 *)

(**
 * Helper lemma: fresh_var_helper returns a variable not in avoid.
 *
 * Proof by structural recursion following fresh_var_helper's definition.
 * The function only returns 'candidate' in the else branch where
 * mem candidate avoid = false, so by construction the result is fresh.
 *)
let rec fresh_var_helper_not_in_avoid (base: var_id) (avoid: list var_id) (counter: nat)
    : Lemma (ensures not (mem (fresh_var_helper base avoid counter) avoid)) =
  let candidate = base ^ "_" ^ string_of_int counter in
  if mem candidate avoid then
    (* Recursive case: candidate is in avoid, so fresh_var_helper recurses.
       By IH, fresh_var_helper base avoid (counter + 1) is not in avoid. *)
    fresh_var_helper_not_in_avoid base avoid (counter + 1)
  else
    (* Base case: candidate is not in avoid, so fresh_var_helper returns candidate.
       The postcondition 'not (mem candidate avoid)' follows directly from
       the else condition 'mem candidate avoid = false'. *)
    ()

val theorem_fresh_var_spec : base:var_id -> avoid:list var_id ->
  Lemma (ensures not (mem (fresh_var base avoid) avoid))

let theorem_fresh_var_spec base avoid =
  (* Proof by case analysis on whether base is in avoid:
     - Case 1: base not in avoid => fresh_var returns base, trivially fresh
     - Case 2: base in avoid => fresh_var calls fresh_var_helper, use helper lemma *)
  if mem base avoid then
    (* fresh_var base avoid = fresh_var_helper base avoid 0
       Apply helper lemma to show result is not in avoid *)
    fresh_var_helper_not_in_avoid base avoid 0
  else
    (* fresh_var base avoid = base
       The postcondition 'not (mem base avoid)' follows from else condition *)
    ()


(**
 * T-1.4: Merge Ranges Contains Left
 *
 * The merged range contains the left input range.
 *
 * Location: Expressions.fst:215
 * Effort: 1-2 hours
 * Proof Strategy: Case analysis on position ordering.
 *
 * Literature: EverParse Ast.fst range handling patterns
 *
 * Classification: DeferredProof
 *)
val theorem_merge_ranges_contains_left : r1:range -> r2:range ->
  Lemma (ensures range_within r1 (merge_ranges r1 r2) = true)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 300"

let theorem_merge_ranges_contains_left r1 r2 =
  (*
   * Proof of: range_within r1 (merge_ranges r1 r2) = true
   *
   * The merge_ranges function computes:
   *   - If files differ: returns r1 unchanged
   *   - If files match: (min(s1,s2), max(e1,e2)) by (line, col) ordering
   *
   * For range_within to be true, we need:
   *   pos_within s1 merged /\ pos_within e1 merged
   *)
  let (s1, e1) = r1 in
  let (s2, e2) = r2 in
  let merged = merge_ranges r1 r2 in
  let (ms, me) = merged in

  (* Case analysis: different files vs same file *)
  if s1.pos_filename <> s2.pos_filename then begin
    (* Different files => merged = r1 *)
    (* range_within r1 r1 is reflexive for any range *)
    assert (merged == r1);
    (* pos_within s1 (s1, e1): filename matches, s1 >= s1, and s1 <= e1 (for valid range) *)
    (* pos_within e1 (s1, e1): e1 >= s1 (for valid range), and e1 <= e1 *)
    ()
  end
  else begin
    (* Same file => merged = (start_pos, end_pos) where:
       start_pos = min(s1, s2) by line then col
       end_pos = max(e1, e2) by line then col *)

    (* Key observations:
       - ms is either s1 or s2 (whichever is smaller)
       - me is either e1 or e2 (whichever is larger)
       - Since s1, s2 have same filename, ms.filename = s1.filename
       - Since e1, e2 have same filename, me.filename = s1.filename *)

    (* For pos_within s1 (ms, me):
       1. s1.filename = ms.filename: ms is s1 or s2, same file
       2. s1 >= ms: ms is min(s1,s2), so ms <= s1
       3. s1 <= me: For valid input ranges, s1 <= e1.
                    me = max(e1,e2) >= e1 >= s1 *)

    (* For pos_within e1 (ms, me):
       1. e1.filename = ms.filename: same file
       2. e1 >= ms: For valid ranges, s1 <= e1, and ms = min(s1,s2) <= s1 <= e1
       3. e1 <= me: me = max(e1,e2) >= e1 *)

    (* F* SMT solver handles the case analysis on position orderings *)
    ()
  end

#pop-options


(**
 * T-1.5: Merge Ranges Contains Right
 *
 * The merged range contains the right input range.
 *
 * Location: Expressions.fst:220
 * Effort: 1-2 hours
 * Proof Strategy: Case analysis on position ordering (symmetric to T-1.4).
 *
 * Literature: EverParse Ast.fst range handling patterns
 *
 * Classification: DeferredProof
 *)
val theorem_merge_ranges_contains_right : r1:range -> r2:range ->
  Lemma (ensures range_within r2 (merge_ranges r1 r2) = true)

let theorem_merge_ranges_contains_right r1 r2 =
  (* DeferredProof: Position case analysis (symmetric argument)
     - Same reasoning as T-1.4 but for r2
     - merge_ranges takes min of start positions
     - merge_ranges takes max of end positions
     - Therefore r2 is within the merged range
     - Estimated effort: 1-2 hours *)
  admit ()


(* =============================================================================
   PRIORITY 2: MEDIUM EFFORT (2-6 hours each)
   =============================================================================
   These theorems require more careful reasoning - induction with auxiliary
   lemmas, multiple case splits, or reasoning about list operations.
   ============================================================================= *)

(**
 * T-2.1: Subexpression Transitivity
 *
 * The is_subexpr relation is transitive: if e1 is a subexpression of e2,
 * and e2 is a subexpression of e3, then e1 is a subexpression of e3.
 *
 * Location: Expressions.fst:1780
 * Effort: 2-4 hours
 * Proof Strategy: Induction on e3 with existsb lemmas.
 *
 * Literature: Standard subterm relation properties (TAPL Chapter 3)
 *
 * Classification: DeferredProof
 *)
val theorem_is_subexpr_trans : e1:expr -> e2:expr -> e3:expr ->
  Lemma (requires is_subexpr e1 e2 = true /\ is_subexpr e2 e3 = true)
        (ensures is_subexpr e1 e3 = true)

let theorem_is_subexpr_trans e1 e2 e3 =
  (* DeferredProof: Induction on e3
     - Base case: e2 = e3 implies e1 subexpr of e3 directly
     - Inductive case: e2 is immediate subexpr of some e3', apply IH
     - Requires auxiliary lemma about existsb
     - Key insight: immediate_subexprs produces smaller expressions
     - Estimated effort: 2-4 hours *)
  admit ()


(**
 * T-2.2: Free Variables in Subexpression
 *
 * Subexpressions have a subset of free variables (modulo parent bindings).
 * If sub is an immediate subexpression of parent, then every free variable
 * in sub is either free in parent or bound by parent.
 *
 * Location: Expressions.fst:1944
 * Effort: 2-3 hours
 * Proof Strategy: Case analysis on parent structure.
 *
 * Literature: Barendregt 1984 Variable Convention, TAPL Chapter 5
 *
 * Classification: DeferredProof
 *)
val theorem_free_vars_subexpr : sub:expr -> parent:expr ->
  Lemma (requires is_immediate_subexpr sub parent = true)
        (ensures forall v. mem v (free_vars sub) ==>
                          mem v (free_vars parent) \/
                          mem v (parent_binds parent))

let theorem_free_vars_subexpr sub parent =
  (* DeferredProof: Case analysis on parent structure
     - For non-binding forms (EUnary, EBinary, EIf, etc.):
       free_vars concatenates subexpr free_vars, so v in free_vars sub
       implies v in free_vars parent
     - For binding forms (ELet, ELambda, EFor, etc.):
       bound variables are filtered out but appear in parent_binds
     - Requires careful handling of each expression constructor
     - Estimated effort: 2-3 hours *)
  admit ()


(**
 * T-2.3: Substitution for Non-Free Variable
 *
 * Substituting for a variable that is not free in the target expression
 * is the identity operation.
 *
 * Location: Expressions.fst:2117
 * Effort: 2-3 hours
 * Proof Strategy: Structural induction on target.
 *
 * Literature: Barendregt 1984 Lemma 2.1.7, TAPL Lemma 6.2.3
 *
 * Classification: DeferredProof
 *)
val theorem_subst_expr_non_free : var:var_id -> replacement:expr -> target:expr ->
  Lemma (requires not (is_free_in var target))
        (ensures expr_eq (subst_expr var replacement target) target = true)

let theorem_subst_expr_non_free var replacement target =
  (* DeferredProof: Structural induction on target
     - Base case EVar x: x <> var (since var not free), so no change
     - Base case ELit: no variables, trivially equal
     - Inductive case EUnary, EBinary, etc.: apply IH to subexpressions
     - Key insight: var not free in target implies var not free in subexprs
       (unless re-bound, but then substitution stops)
     - Estimated effort: 2-3 hours *)
  admit ()


(* =============================================================================
   PRIORITY 3: SUBSTANTIAL EFFORT (3-8 hours each)
   =============================================================================
   These theorems require careful treatment of binding structure and
   potentially complex case analysis.
   ============================================================================= *)

(**
 * T-3.1: Substitution Preserves Well-Formedness
 *
 * If both the target expression and replacement expression are well-formed,
 * then the result of substitution is also well-formed.
 *
 * Location: Expressions.fst:2103
 * Effort: 3-5 hours
 * Proof Strategy: Structural induction with careful binding analysis.
 *
 * Literature: Barendregt 1984 Theorem 2.1.16, TAPL Chapter 6
 *
 * Classification: DeferredProof
 *)
val theorem_subst_expr_wf : var:var_id -> replacement:expr -> target:expr ->
  Lemma (requires expr_wf target = true /\ expr_wf replacement = true)
        (ensures expr_wf (subst_expr var replacement target) = true)

let theorem_subst_expr_wf var replacement target =
  (* DeferredProof: Structural induction on target
     - Base cases (EVar, ELit): result is either replacement (wf by hyp)
       or unchanged target (wf by hyp)
     - For binding forms: capture avoidance may rename, but renaming
       preserves well-formedness (need auxiliary lemma)
     - For non-binding forms: apply IH to subexpressions
     - Key insight: fresh_var produces valid identifiers
     - Estimated effort: 3-5 hours *)
  admit ()


(**
 * T-3.2: Substitution Free Variables
 *
 * After substituting var with replacement in target, the free variables
 * of the result are: free vars of target (minus var) union free vars of
 * replacement (if var was free in target).
 *
 * Location: Expressions.fst:2111
 * Effort: 3-5 hours
 * Proof Strategy: Structural induction with set reasoning.
 *
 * Literature: Barendregt 1984 Lemma 2.1.10, TAPL Lemma 6.2.4
 *
 * Classification: DeferredProof
 *)
val theorem_subst_expr_free_vars : var:var_id -> replacement:expr -> target:expr ->
  Lemma (ensures
    (forall v. mem v (free_vars (subst_expr var replacement target)) ==>
               (v <> var /\ mem v (free_vars target)) \/
               mem v (free_vars replacement)))

let theorem_subst_expr_free_vars var replacement target =
  (* DeferredProof: Structural induction on target
     - Base case EVar x:
       * If x = var: result is replacement, so fv = fv(replacement)
       * If x <> var: result is EVar x, so fv = {x}, and x in fv(target)
     - For binding forms with capture avoidance:
       * Fresh variables don't appear in free_vars(replacement)
       * Renaming doesn't change free variable membership
     - For non-binding forms: union of IH results
     - Requires careful set membership reasoning
     - Estimated effort: 3-5 hours *)
  admit ()


(* =============================================================================
   PRIORITY 4: HIGH EFFORT (4-16 hours each)
   =============================================================================
   These theorems require semantic reasoning about expression equivalence.
   ============================================================================= *)

(**
 * T-4.1: Normalization Preserves Semantics
 *
 * Normalization produces an alpha-equivalent expression. The normalized
 * form has the same meaning as the original expression.
 *
 * Location: Expressions.fst:2276
 * Effort: 4-6 hours
 * Proof Strategy: Show each normalization step preserves alpha-equivalence.
 *
 * Literature:
 *   - Danvy-Filinski 1989: Abstracting Control
 *   - Barendregt 1984: Alpha-conversion theory
 *
 * Classification: DeferredProof
 *)
val theorem_normalize_expr_equiv : e:expr ->
  Lemma (ensures expr_alpha_eq e (normalize_expr e) = true)

let theorem_normalize_expr_equiv e =
  (* DeferredProof: Show each normalization step preserves semantics
     - Block flattening: EBlock [e] ~= e (trivial by block semantics)
     - Nested block flattening: preserves evaluation order
     - Sequence normalization: ESeq (ESeq a b) c ~= ESeq a (ESeq b c)
       (by associativity of sequencing)
     - Key insight: normalization only restructures, doesn't change meaning
     - Requires defining evaluation semantics or using alpha-equivalence
     - Current expr_alpha_eq is simplified (= expr_eq), full proof needs
       proper alpha-equivalence with De Bruijn indices
     - Estimated effort: 4-6 hours *)
  admit ()


(* =============================================================================
   ADDITIONAL THEOREMS (Supplementary, from Expressions.fsti)
   =============================================================================
   These theorems are declared in the interface and should also be proven.
   ============================================================================= *)

(**
 * Normalization is Idempotent
 *
 * Applying normalization twice yields the same result as applying it once.
 * This is a standard property of normal forms.
 *
 * Location: Expressions.fst:2281
 * Effort: 2-3 hours
 * Proof Strategy: Show normalize_expr returns a fixed point.
 *
 * Classification: DeferredProof
 *)
val theorem_normalize_expr_idempotent : e:expr ->
  Lemma (ensures expr_eq (normalize_expr e) (normalize_expr (normalize_expr e)) = true)

let theorem_normalize_expr_idempotent e =
  (* DeferredProof: Show normalized expressions are already normal
     - Blocks are already flattened (no nested EBlock)
     - Sequences are in canonical form
     - Other constructs unchanged by normalization
     - Estimated effort: 2-3 hours *)
  admit ()


(**
 * Expression Equality Reflexivity
 *
 * Every expression is structurally equal to itself.
 *
 * Location: Expressions.fst (expr_eq_refl)
 * Effort: <1 hour
 * Proof Strategy: Structural induction (straightforward).
 *
 * Classification: DeferredProof
 *)
val theorem_expr_eq_refl : e:expr ->
  Lemma (ensures expr_eq e e = true)

let theorem_expr_eq_refl e =
  (* DeferredProof: Structural induction
     - Each constructor case: recursively equal to itself
     - Straightforward by definition of expr_eq
     - Estimated effort: <1 hour *)
  admit ()


(**
 * Expression Equality Symmetry
 *
 * If e1 equals e2, then e2 equals e1.
 *
 * Location: Expressions.fst (expr_eq_sym)
 * Effort: <1 hour
 * Proof Strategy: Structural induction (straightforward).
 *
 * Classification: DeferredProof
 *)
val theorem_expr_eq_sym : e1:expr -> e2:expr ->
  Lemma (requires expr_eq e1 e2 = true)
        (ensures expr_eq e2 e1 = true)

let theorem_expr_eq_sym e1 e2 =
  (* DeferredProof: Structural induction
     - expr_eq compares structure, which is symmetric
     - Each constructor case matches symmetrically
     - Estimated effort: <1 hour *)
  admit ()


(**
 * Expression Equality Transitivity
 *
 * If e1 equals e2 and e2 equals e3, then e1 equals e3.
 *
 * Location: Expressions.fst (expr_eq_trans)
 * Effort: 1-2 hours
 * Proof Strategy: Structural induction.
 *
 * Classification: DeferredProof
 *)
val theorem_expr_eq_trans : e1:expr -> e2:expr -> e3:expr ->
  Lemma (requires expr_eq e1 e2 = true /\ expr_eq e2 e3 = true)
        (ensures expr_eq e1 e3 = true)

let theorem_expr_eq_trans e1 e2 e3 =
  (* DeferredProof: Structural induction
     - If e1 = e2 structurally and e2 = e3 structurally, then e1 = e3
     - Each constructor case: matching constructors with IH on subterms
     - Estimated effort: 1-2 hours *)
  admit ()


(* =============================================================================
   THEOREM SUMMARY
   =============================================================================

   Priority 1 (Low-Hanging Fruit, <=2h each):
     T-1.3: theorem_fresh_var_spec            - 1 hour
     T-1.4: theorem_merge_ranges_contains_left   - 1-2 hours
     T-1.5: theorem_merge_ranges_contains_right  - 1-2 hours

   Priority 2 (Medium Effort, 2-6h each):
     T-2.1: theorem_is_subexpr_trans          - 2-4 hours
     T-2.2: theorem_free_vars_subexpr         - 2-3 hours
     T-2.3: theorem_subst_expr_non_free       - 2-3 hours

   Priority 3 (Substantial Effort, 3-8h each):
     T-3.1: theorem_subst_expr_wf             - 3-5 hours
     T-3.2: theorem_subst_expr_free_vars      - 3-5 hours

   Priority 4 (High Effort, 4-16h each):
     T-4.1: theorem_normalize_expr_equiv      - 4-6 hours

   Supplementary:
     theorem_normalize_expr_idempotent        - 2-3 hours
     theorem_expr_eq_refl                     - <1 hour
     theorem_expr_eq_sym                      - <1 hour
     theorem_expr_eq_trans                    - 1-2 hours

   TOTAL ESTIMATED EFFORT: 22-39 hours

   All proofs use admit() - this module documents the theorems and their
   proof strategies. Actual mechanization is deferred.

   ============================================================================= *)
