(**
 * BrrrLang.Theorems - Master Index Interface
 *
 * SINGLE SOURCE OF TRUTH for all theorems in brrr-lang.
 *
 * This module declares properties that CAN AND MUST BE PROVEN from
 * definitions and axioms. Unlike BrrrAxioms.fsti, these are statements
 * where formal proofs exist (or can be constructed).
 *
 * Organization:
 *   - Priority 0 (P0_Done):       Already proven in F*
 *   - Priority 1 (P1_Easy):       Low-hanging fruit (<=2 hours)
 *   - Priority 2 (P2_Medium):     Medium effort (2-6 hours)
 *   - Priority 3 (P3_Substantial): Substantial effort (3-8 hours)
 *   - Priority 4 (P4_High):       High effort (4-16 hours)
 *   - Priority 5 (P5_Research):   Research-grade (8-80 hours)
 *
 * Categories:
 *   - Expressions:  Substitution, free vars, normalization
 *   - Taint:        Soundness, completeness of taint analysis
 *   - Eval:         Preservation, environment properties
 *   - Modes:        Linear exclusivity, context validity
 *   - Sessions:     Progress, fidelity, projection
 *   - Primitives:   Division, overflow, wrapping
 *   - Security:     Noninterference, blame, parametricity
 *   - Memory:       Frame rule, DRF-SC, thin-air
 *   - FFI:          Boundaries, conversion
 *   - Analysis:     CFG, points-to soundness
 *
 * NO CORE MODULE IMPORTS - avoids circular dependencies.
 * Uses polymorphic signatures instantiated by client modules.
 *
 * PROOF TECHNIQUE REFERENCES:
 *   - fstar_pop_book.md lines 9001-11000: Proof fundamentals, induction
 *   - fstar_pop_book.md lines 14500-16500: Tactics and automation
 *   - FSTAR_REFERENCE.md Section 7: Tactics system
 *   - FSTAR_REFERENCE.md Section 13: Proof patterns
 *   - FSTAR_REFERENCE.md Section 20: Tactic recipes
 *
 * SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md):
 *   - Chapter 1: Integer arithmetic needs valid_input precondition
 *   - Chapter 2: Mode context join needs extended_modes_compatible
 *   - Chapter 3: Alpha equivalence must use normalization-based definition
 *   - Chapter 4: Range merge needs same_file precondition
 *   - Chapter 5: Honda 2008 session types - use corrected association relation
 *
 * References: AXIOMS_REPORT_v2.md for full details.
 *
 * Version: 1.0
 * Generated: 2026-01-26
 *)
module BrrrTheorems

open FStar.List.Tot


(* ============================================================================
   CLASSIFICATION TYPES
   ============================================================================ *)

(** Theorem proof status - current state of mechanization *)
type theorem_status =
  | Proven      (* Fully mechanized proof exists in F* *)
  | Admitted    (* Proof exists in literature, admitted in F* for now *)
  | InProgress  (* Actively being proven *)

(** Priority classification - based on effort and dependencies *)
type priority =
  | P0_Done        (* Already proven or trivial *)
  | P1_Easy        (* Low-hanging fruit: <=2 hours *)
  | P2_Medium      (* Medium effort: 2-6 hours *)
  | P3_Substantial (* Substantial effort: 3-8 hours *)
  | P4_High        (* High effort: 4-16 hours *)
  | P5_Research    (* Research-grade: 8-80 hours, may need literature port *)

(** Category classification - domain of the theorem *)
type theorem_category =
  | CatExpressions  (* Substitution, free vars, normalization *)
  | CatTaint        (* Taint analysis soundness/completeness *)
  | CatEval         (* Evaluation preservation *)
  | CatModes        (* Linear/affine mode system *)
  | CatSessions     (* Session types, MPST *)
  | CatPrimitives   (* Primitive operations *)
  | CatSecurity     (* IFC, noninterference *)
  | CatMemory       (* Separation logic, memory models *)
  | CatFFI          (* Cross-language boundaries *)
  | CatAnalysis     (* Static analysis infrastructure *)
  | CatModules      (* Module system *)
  | CatEffects      (* Effect handlers *)
  | CatTypes        (* Type system metatheory *)


(* ============================================================================
   SUMMARY STATISTICS
   ============================================================================

   TOTAL THEOREMS: 53

   BY PRIORITY:
   +----------+-------+----------------------+
   | Priority | Count | Total Effort (hours) |
   +----------+-------+----------------------+
   | P0 Done  |   7   | 0 (already proven)   |
   | P1 Easy  |   6   | 6-11                 |
   | P2 Medium|  10   | 22-35                |
   | P3 Subst.|   7   | 24-47                |
   | P4 High  |   9   | 40-86                |
   | P5 Rsrch.|  14   | 200-520              |
   +----------+-------+----------------------+
   | TOTAL    |  53   | 292-699              |
   +----------+-------+----------------------+

   BY CATEGORY:
   +-------------+-------+----------------------------------------+
   | Category    | Count | Notes                                  |
   +-------------+-------+----------------------------------------+
   | Expressions |  10   | Substitution, free vars, normalization |
   | Modes       |   3   | Linear exclusivity, context validity   |
   | Primitives  |   4   | Division, overflow, wrapping           |
   | Eval        |   4   | Preservation, environment              |
   | Modules     |   2   | Dependencies, imports                  |
   | Taint       |   5   | Soundness, completeness                |
   | Effects     |   1   | Handler termination                    |
   | Sessions    |   8   | Progress, fidelity, projection         |
   | FFI         |   4   | Boundaries, conversion                 |
   | Security    |   3   | Noninterference, blame, parametricity  |
   | Memory      |   4   | Frame, DRF-SC, thin-air, bi-abduction  |
   | Analysis    |   3   | CFG, stack filtering, Qilin            |
   | Types       |   2   | Occurrence typing, type checking       |
   +-------------+-------+----------------------------------------+

   ============================================================================ *)


(* ============================================================================
   PRIORITY 0: CRITICAL INFRASTRUCTURE (Already Proven)
   ============================================================================
   These theorems are already mechanized in the codebase or trivially follow
   from definitions. No additional work required.
   ============================================================================ *)

(* ----------------------------------------------------------------------------
   T-0.1: Dual Involution
   ---------------------------------------------------------------------------- *)
(** ID: T-0.1
    Statement: dual(dual(S)) = S for all session types S
    Category: Sessions
    Location: BrrrSessionTypes.fst:413-423
    Effort: 0 (proven)
    Status: PROVEN
    Literature: Honda et al. 2008

    PROOF TECHNIQUE: Structural induction on session type constructors.

    The dual function swaps send/recv, and recursively duals branches.
    Each constructor case is straightforward:
    - SEnd: dual(dual(SEnd)) = dual(SEnd) = SEnd
    - SSend t S: dual(dual(SSend t S)) = dual(SRecv t (dual S)) = SSend t (dual(dual S))
                 By IH on S, dual(dual S) = S, so result is SSend t S
    - SRecv t S: Symmetric to SSend
    - SChoice/SOffer: Swap and recurse, IH applies to each branch

    F* PROOF PATTERN:
    ```fstar
    let rec dual_involution_proof (s: session_type)
        : Lemma (ensures dual (dual s) == s) (decreases s) =
      match s with
      | SEnd -> ()
      | SSend t s' -> dual_involution_proof s'
      | SRecv t s' -> dual_involution_proof s'
      | SChoice branches -> FStar.Classical.forall_intro (fun b -> dual_involution_proof b)
      | SOffer branches -> FStar.Classical.forall_intro (fun b -> dual_involution_proof b)
    ```

    SMT HINTS: #set-options "--fuel 1 --ifuel 1" is sufficient.
*)
val dual_involution : #a:Type -> (dual: a -> a) ->
  Lemma (ensures True)  (* Actual: forall s. dual (dual s) == s *)

val dual_involution_priority : unit -> Tot priority
val dual_involution_status : unit -> Tot theorem_status
val dual_involution_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-0.2: Session Equality Reflexivity
   ---------------------------------------------------------------------------- *)
(** ID: T-0.2
    Statement: session_eq S S = true
    Category: Sessions
    Location: BrrrSessionTypes.fst:502+
    Effort: 0 (proven)
    Status: PROVEN
    Proof: Definitional - equality is reflexive *)
val session_eq_reflexive : unit ->
  Lemma (ensures True)  (* Actual: forall s. session_eq s s == true *)

val session_eq_reflexive_priority : unit -> Tot priority
val session_eq_reflexive_status : unit -> Tot theorem_status
val session_eq_reflexive_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-0.3: Dual Communication Safety
   ---------------------------------------------------------------------------- *)
(** ID: T-0.3
    Statement: dual S is communication-safe if S is
    Category: Sessions
    Location: BrrrSessionTypes.fsti:1047-1049
    Effort: 0 (proven)
    Status: PROVEN
    Literature: Honda et al. 2008 *)
val dual_comm_safe : unit ->
  Lemma (ensures True)  (* Actual: comm_safe s ==> comm_safe (dual s) *)

val dual_comm_safe_priority : unit -> Tot priority
val dual_comm_safe_status : unit -> Tot theorem_status
val dual_comm_safe_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-0.4: Well-Formed Has Progress
   ---------------------------------------------------------------------------- *)
(** ID: T-0.4
    Statement: Well-formed processes don't get stuck
    Category: Sessions
    Location: BrrrSessionTypes.fsti:1064-1067
    Effort: 0 (proven)
    Status: PROVEN
    Literature: Honda et al. 2008 Theorem 5.12 *)
val wf_has_progress : unit ->
  Lemma (ensures True)  (* Actual: wf p ==> p == PEnd \/ exists p'. step p p' *)

val wf_has_progress_priority : unit -> Tot priority
val wf_has_progress_status : unit -> Tot theorem_status
val wf_has_progress_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-0.5: Well-Formed Implies Projectable
   ---------------------------------------------------------------------------- *)
(** ID: T-0.5
    Statement: Well-formed global types can be projected
    Category: Sessions
    Location: BrrrMultipartySession.fst:1283-1286
    Effort: 0 (proven)
    Status: PROVEN
    Literature: Honda et al. 2008, Scalas & Yoshida 2019 (corrections) *)
val wf_implies_projectable : unit ->
  Lemma (ensures True)  (* Actual: wf_global g ==> forall p. Some? (project g p) *)

val wf_implies_projectable_priority : unit -> Tot priority
val wf_implies_projectable_status : unit -> Tot theorem_status
val wf_implies_projectable_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-0.6: Deadlock Freedom
   ---------------------------------------------------------------------------- *)
(** ID: T-0.6
    Statement: Well-typed sessions are deadlock-free
    Category: Sessions
    Location: BrrrMultipartySession.fst:1302-1305
    Effort: 0 (proven)
    Status: PROVEN
    Literature: Honda et al. 2008 Corollary 5.14 *)
val deadlock_freedom : unit ->
  Lemma (ensures True)  (* Actual: typed delta p ==> deadlock_free p *)

val deadlock_freedom_priority : unit -> Tot priority
val deadlock_freedom_status : unit -> Tot theorem_status
val deadlock_freedom_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-0.7: Linear Exclusivity
   ---------------------------------------------------------------------------- *)
(** ID: T-0.7
    Statement: split_ctx produces exclusive contexts for linear vars
    Category: Modes
    Location: BrrrModes.fst:466-485
    Effort: 0 (proven by construction)
    Status: PROVEN
    Proof: Follows from split_ctx definition *)
val linear_exclusivity : unit ->
  Lemma (ensures True)
  (* Actual: linear x ctx ==> (x in fst (split_ctx ctx)) xor (x in snd (split_ctx ctx)) *)

val linear_exclusivity_priority : unit -> Tot priority
val linear_exclusivity_status : unit -> Tot theorem_status
val linear_exclusivity_category : unit -> Tot theorem_category


(* ============================================================================
   END OF PRIORITY 0: 7 theorems (all proven)
   ============================================================================ *)


(* ============================================================================
   PRIORITY 1: LOW-HANGING FRUIT (<=2 hours each)
   ============================================================================
   Simple proofs using basic induction, set theory, or case analysis.
   Good starting points for theorem proving practice.
   ============================================================================ *)

(* ----------------------------------------------------------------------------
   T-1.1: Taint Set Union Subset Left
   ---------------------------------------------------------------------------- *)
(** ID: T-1.1
    Statement: A is a subset of A union B
    Category: Taint
    Location: BrrrTaintEffects.fst:656
    Effort: 30 minutes
    Status: ADMITTED
    Literature: Basic set theory

    PROOF TECHNIQUE: Direct application of union definition.

    The union operation is defined as:
      mem t (union a b) <==> mem t a \/ mem t b

    PROOF STRATEGY (from fstar_pop_book.md lines 15181-15195):
    Use FStar.Classical.forall_intro to introduce the universal quantifier,
    then the implication follows from the left disjunct of union definition.

    (* TODO: Implement using this pattern:
       #push-options "--fuel 0 --ifuel 0"
       let taint_set_union_subset_left_impl (a b: taint_set) (t: taint)
           : Lemma (requires mem t a) (ensures mem t (union a b)) =
         (* Union definition gives: mem t (union a b) <==> mem t a \/ mem t b *)
         (* Since mem t a is true, the disjunction holds *)
         ()
       #pop-options
    *)
*)
val taint_set_union_subset_left : unit ->
  Lemma (ensures True)
  (* Actual: forall t. t `mem` a ==> t `mem` (union a b) *)

val taint_set_union_subset_left_priority : unit -> Tot priority
val taint_set_union_subset_left_status : unit -> Tot theorem_status
val taint_set_union_subset_left_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-1.2: Filter Produces Nonempty
   ---------------------------------------------------------------------------- *)
(** ID: T-1.2
    Statement: If filter finds an element, result is nonempty
    Category: Taint
    Location: BrrrTaintEffects.fst:782
    Effort: 1 hour
    Status: ADMITTED

    PROOF TECHNIQUE: List induction with case split on head element.

    Base case: l = [] contradicts x `mem` l (empty list has no members)
    Inductive case: l = h::t
      - If h = x and f x, then filter keeps h, so length > 0
      - If h <> x or not (f h), recurse on t (x must be in t by mem definition)

    INDUCTION PATTERN (from fstar_pop_book.md lines 15168-15173):
    ```fstar
    let rec filter_nonempty (#a:Type) (f: a -> bool) (l: list a) (x: a)
        : Lemma (requires f x /\ mem x l) (ensures length (filter f l) > 0)
              (decreases l) =
      match l with
      | [] -> ()  (* Contradiction: x cannot be in empty list *)
      | h::t ->
        if f h then () (* h passes filter, so result has at least h *)
        else filter_nonempty f t x (* x must be in t since h <> x or not (f h) *)
    ```

    (* TODO: Need helper lemma: mem x (h::t) /\ h <> x ==> mem x t
       This follows from FStar.List.Tot.Properties.mem_cons *)
*)
val filter_produces_nonempty : #a:Type -> (f: a -> bool) -> (l: list a) -> (x: a) ->
  Lemma (requires True)  (* Actual: f x /\ x `mem` l *)
        (ensures True)   (* Actual: length (filter f l) > 0 *)

val filter_produces_nonempty_priority : unit -> Tot priority
val filter_produces_nonempty_status : unit -> Tot theorem_status
val filter_produces_nonempty_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-1.3: Fresh Variable Specification
   ---------------------------------------------------------------------------- *)
(** ID: T-1.3
    Statement: fresh_var returns variable not in given set
    Category: Expressions
    Location: BrrrExpressions.fst:1963
    Effort: 1 hour
    Status: ADMITTED
    Proof: Construction - fresh_var generates name by incrementing counter *)
val fresh_var_spec : unit ->
  Lemma (ensures True)
  (* Actual: not (fresh_var vars `mem` vars) *)

val fresh_var_spec_priority : unit -> Tot priority
val fresh_var_spec_status : unit -> Tot theorem_status
val fresh_var_spec_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-1.4: Merge Ranges Contains Left
   ---------------------------------------------------------------------------- *)
(** ID: T-1.4
    Statement: Merged range contains left input
    Category: Expressions
    Location: BrrrExpressions.fst:215
    Effort: 1-2 hours
    Status: ADMITTED

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 4):
    ============================================================
    Requires same_file precondition - ranges must be from same source file.
    Merging ranges from different files produces undefined results.

    CORRECTED STATEMENT:
      same_file r1 r2 ==> contains (merge_ranges r1 r2) r1

    PROOF TECHNIQUE: Position case analysis on start/end line/column.
    Uses min/max for start/end positions.

    (* TODO: Add same_file precondition per errata Chapter 4 *)
*)
val merge_ranges_contains_left : unit ->
  Lemma (ensures True)
  (* Actual: same_file r1 r2 ==> contains (merge_ranges r1 r2) r1 *)

val merge_ranges_contains_left_priority : unit -> Tot priority
val merge_ranges_contains_left_status : unit -> Tot theorem_status
val merge_ranges_contains_left_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-1.5: Merge Ranges Contains Right
   ---------------------------------------------------------------------------- *)
(** ID: T-1.5
    Statement: Merged range contains right input
    Category: Expressions
    Location: BrrrExpressions.fst:220
    Effort: 1-2 hours
    Status: ADMITTED

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 4):
    ============================================================
    Same as T-1.4 - requires same_file precondition.

    CORRECTED STATEMENT:
      same_file r1 r2 ==> contains (merge_ranges r1 r2) r2

    (* TODO: Add same_file precondition per errata Chapter 4 *)
*)
val merge_ranges_contains_right : unit ->
  Lemma (ensures True)
  (* Actual: same_file r1 r2 ==> contains (merge_ranges r1 r2) r2 *)

val merge_ranges_contains_right_priority : unit -> Tot priority
val merge_ranges_contains_right_status : unit -> Tot theorem_status
val merge_ranges_contains_right_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-1.6: Eval Let Binding
   ---------------------------------------------------------------------------- *)
(** ID: T-1.6
    Statement: Let binding evaluation is correct
    Category: Eval
    Location: BrrrEval.fst:2332
    Effort: 1-2 hours
    Status: ADMITTED
    Proof: match_pattern correctness + substitution lemma *)
val eval_let_binding : unit ->
  Lemma (ensures True)
  (* Actual: eval (ELet p (ELit v) e) st == eval (subst_pattern p v e) st *)

val eval_let_binding_priority : unit -> Tot priority
val eval_let_binding_status : unit -> Tot theorem_status
val eval_let_binding_category : unit -> Tot theorem_category


(* ============================================================================
   END OF PRIORITY 1: 6 theorems (6-11 hours total)
   ============================================================================ *)


(* ============================================================================
   PRIORITY 2: MEDIUM EFFORT (2-6 hours each)
   ============================================================================
   Require more complex induction schemes or careful case analysis.
   May need helper lemmas from other modules.
   ============================================================================ *)

(* ----------------------------------------------------------------------------
   T-2.1: Subexpression Transitivity
   ---------------------------------------------------------------------------- *)
(** ID: T-2.1
    Statement: is_subexpr is transitive
    Category: Expressions
    Location: BrrrExpressions.fst:1780
    Effort: 2-4 hours
    Status: ADMITTED
    Proof: Induction with existsb lemma - chain of containment *)
val is_subexpr_trans : unit ->
  Lemma (ensures True)
  (* Actual: is_subexpr e1 e2 /\ is_subexpr e2 e3 ==> is_subexpr e1 e3 *)

val is_subexpr_trans_priority : unit -> Tot priority
val is_subexpr_trans_status : unit -> Tot theorem_status
val is_subexpr_trans_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-2.2: Free Variables in Subexpression
   ---------------------------------------------------------------------------- *)
(** ID: T-2.2
    Statement: Subexpressions have subset of free variables
    Category: Expressions
    Location: BrrrExpressions.fst:1944
    Effort: 2-3 hours
    Status: ADMITTED
    Proof: Case analysis on parent expression form *)
val free_vars_subexpr : unit ->
  Lemma (ensures True)
  (* Actual: is_subexpr sub e ==> free_vars sub `subset` free_vars e *)

val free_vars_subexpr_priority : unit -> Tot priority
val free_vars_subexpr_status : unit -> Tot theorem_status
val free_vars_subexpr_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-2.3: Substitution Non-Free
   ---------------------------------------------------------------------------- *)
(** ID: T-2.3
    Statement: Substituting for non-free variable is identity
    Category: Expressions
    Location: BrrrExpressions.fst:2117
    Effort: 2-3 hours
    Status: ADMITTED
    Proof: Structural induction - var case is key *)
val subst_expr_non_free : unit ->
  Lemma (ensures True)
  (* Actual: not (x `mem` free_vars e) ==> subst x v e == e *)

val subst_expr_non_free_priority : unit -> Tot priority
val subst_expr_non_free_status : unit -> Tot theorem_status
val subst_expr_non_free_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-2.4: Split Ensures Exclusivity
   ---------------------------------------------------------------------------- *)
(** ID: T-2.4
    Statement: Context splitting preserves linear exclusivity
    Category: Modes
    Location: BrrrModes.fst:469
    Effort: 2-3 hours
    Status: ADMITTED
    Proof: for_all/map interaction on split operation *)
val split_ensures_exclusivity : unit ->
  Lemma (ensures True)
  (* Actual: linear_exclusive (fst (split_ctx ctx)) (snd (split_ctx ctx)) *)

val split_ensures_exclusivity_priority : unit -> Tot priority
val split_ensures_exclusivity_status : unit -> Tot theorem_status
val split_ensures_exclusivity_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-2.5: Valid Context Linear Mode
   ---------------------------------------------------------------------------- *)
(** ID: T-2.5
    Statement: Valid contexts have linear modes only for linear types
    Category: Modes
    Location: BrrrModes.fst:499
    Effort: 2-3 hours
    Status: ADMITTED
    Proof: Same infrastructure as T-2.4 *)
val valid_ctx_linear_mode : unit ->
  Lemma (ensures True)
  (* Actual: valid_ctx ctx /\ lookup x ctx = Some (t, MLinear) ==> is_linear_type t *)

val valid_ctx_linear_mode_priority : unit -> Tot priority
val valid_ctx_linear_mode_status : unit -> Tot theorem_status
val valid_ctx_linear_mode_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-2.6: Join Preserves Valid
   ---------------------------------------------------------------------------- *)
(** ID: T-2.6
    Statement: Context join preserves validity
    Category: Modes
    Location: BrrrModes.fst:523
    Effort: 2-3 hours
    Status: ADMITTED

    PROOF TECHNIQUE: Show mode_join preserves allowed modes for each extended mode.

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 2):
    The original theorem statement is INCOMPLETE. Join only preserves validity
    when extended modes are compatible. Add precondition:
      extended_modes_compatible ctx1 ctx2

    For each variable x in both contexts:
    - If ext_mode(x) = EMLinear: allowed modes are {0, 1}
      - mode_join 0 0 = 0 (valid)
      - mode_join 0 1 = 1 (valid)
      - mode_join 1 0 = 1 (valid)
      - mode_join 1 1 = omega (INVALID for linear!)
      - But linear_exclusive prevents 1+1 case
    - If ext_mode(x) = EMAffine: allowed modes are {0, 1, omega} - all results valid
    - If ext_mode(x) = EMUnrestricted: all results valid

    (* TODO: Add extended_modes_compatible precondition per errata:
       #push-options "--fuel 1 --ifuel 1"
       let join_preserves_valid_impl (ctx1 ctx2: mode_ctx)
           : Lemma (requires valid_mode_ctx ctx1 /\ valid_mode_ctx ctx2 /\
                            linear_exclusive ctx1 ctx2 /\
                            extended_modes_compatible ctx1 ctx2)
                   (ensures valid_mode_ctx (join_ctx ctx1 ctx2)) =
         (* For each binding (x, m, em) in result:
            - m = mode_join (lookup ctx1 x) (lookup ctx2 x)
            - em is same in both contexts (by extended_modes_compatible)
            - Show m `in` allowed(em) *)
         FStar.Classical.forall_intro (fun x ->
           mode_join_allowed_lemma ctx1 ctx2 x
         )
       #pop-options
    *)

    DEPENDENCY: Requires mode_join_linear_closed lemma from BrrrModes.fst
*)
val join_preserves_valid : unit ->
  Lemma (ensures True)
  (* Actual: valid_ctx ctx1 /\ valid_ctx ctx2 ==> valid_ctx (join_ctx ctx1 ctx2) *)

val join_preserves_valid_priority : unit -> Tot priority
val join_preserves_valid_status : unit -> Tot theorem_status
val join_preserves_valid_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-2.7: Normalize Expression Idempotent
   ---------------------------------------------------------------------------- *)
(** ID: T-2.7
    Statement: Normalization is idempotent
    Category: Expressions
    Location: BrrrExpressions.fst:2281
    Effort: 2-3 hours
    Status: ADMITTED

    PROOF TECHNIQUE: Show normalize produces expressions in normal form,
    and normal forms are fixed points.

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 3):
    This theorem is CRITICAL for alpha equivalence. The original definition
    of expr_alpha_eq was structurally flawed (just structural equality).

    CORRECTED DEFINITION:
      expr_alpha_eq e1 e2 = expr_eq (normalize e1) (normalize e2)

    With this definition, normalize_expr_equiv becomes TRIVIAL:
      normalize_expr_equiv e =
        expr_alpha_eq e (normalize e)
        = expr_eq (normalize e) (normalize (normalize e))  (* By def *)
        = expr_eq (normalize e) (normalize e)              (* By idempotence *)
        = true                                              (* Reflexivity *)

    PROOF STRATEGY:
    Define predicate is_normalized(e) that characterizes normal forms:
    - No nested blocks: not (EBlock [EBlock _])
    - No singleton blocks: not (EBlock [e])
    - No redundant lets: not (ELet x e (EVar x))
    - Bound vars canonically renamed (optional for stricter normal form)

    Show: normalize e produces is_normalized result
    Show: is_normalized e ==> normalize e == e

    (* TODO: Implement with normal form predicate:
       let is_normalized (e: expr) : bool = ...

       #push-options "--fuel 2 --ifuel 1"
       let rec normalize_produces_normalized (e: expr)
           : Lemma (ensures is_normalized (normalize e)) (decreases e) =
         match e with
         | EBlock stmts -> normalize_block_produces_normalized stmts
         | ELet p v body ->
           normalize_produces_normalized v;
           normalize_produces_normalized body;
           (* Check for identity let elimination *)
           ...
         | _ -> ()

       let rec normalized_is_fixed_point (e: expr)
           : Lemma (requires is_normalized e)
                   (ensures normalize e == e) (decreases e) = ...
       #pop-options
    *)

    DEPENDENCIES: Helper lemmas for each normalization rule
*)
val normalize_expr_idempotent : unit ->
  Lemma (ensures True)
  (* Actual: normalize (normalize e) == normalize e *)

val normalize_expr_idempotent_priority : unit -> Tot priority
val normalize_expr_idempotent_status : unit -> Tot theorem_status
val normalize_expr_idempotent_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-2.8: Collect Source Taints Sound
   ---------------------------------------------------------------------------- *)
(** ID: T-2.8
    Statement: Source taint collection is sound
    Category: Taint
    Location: BrrrTaintEffects.fst:836
    Effort: 2-3 hours
    Status: ADMITTED
    Proof: Induction on expression - all source nodes captured *)
val collect_source_taints_sound : unit ->
  Lemma (ensures True)
  (* Actual: is_taint_source e t ==> t `mem` collect_source_taints e env *)

val collect_source_taints_sound_priority : unit -> Tot priority
val collect_source_taints_sound_status : unit -> Tot theorem_status
val collect_source_taints_sound_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-2.9: Propagate Through Row Sound
   ---------------------------------------------------------------------------- *)
(** ID: T-2.9
    Statement: Taint propagation through rows is sound
    Category: Taint
    Location: BrrrTaintEffects.fst:881
    Effort: 2 hours
    Status: ADMITTED
    Proof: Use sec_label_leq_trans for lattice ordering *)
val propagate_through_row_sound : unit ->
  Lemma (ensures True)
  (* Actual: actual_flow row ==> flow `leq` propagate row taint *)

val propagate_through_row_sound_priority : unit -> Tot priority
val propagate_through_row_sound_status : unit -> Tot theorem_status
val propagate_through_row_sound_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-2.10: Mod Identity
   ---------------------------------------------------------------------------- *)
(** ID: T-2.10
    Statement: x % n = x when 0 <= x < n
    Category: Primitives
    Location: BrrrPrimitives.fst:1348
    Effort: 2-4 hours
    Status: ADMITTED
    Proof: Signed range identity - definition of modulo *)
val mod_identity : unit ->
  Lemma (ensures True)
  (* Actual: 0 <= x /\ x < n ==> x % n == x *)

val mod_identity_priority : unit -> Tot priority
val mod_identity_status : unit -> Tot theorem_status
val mod_identity_category : unit -> Tot theorem_category


(* ============================================================================
   END OF PRIORITY 2: 10 theorems (22-35 hours total)
   ============================================================================ *)


(* ============================================================================
   PRIORITY 3: SUBSTANTIAL EFFORT (3-8 hours each)
   ============================================================================
   Complex structural inductions, heap reasoning, or multi-step proofs.
   May require significant helper infrastructure.
   ============================================================================ *)

(* ----------------------------------------------------------------------------
   T-3.1: Substitution Well-Formed
   ---------------------------------------------------------------------------- *)
(** ID: T-3.1
    Statement: Substitution preserves well-formedness
    Category: Expressions
    Location: BrrrExpressions.fst:2103
    Effort: 3-5 hours
    Status: ADMITTED

    PROOF TECHNIQUE: Structural induction on expression e.

    This is a FOUNDATIONAL lemma used throughout the type system.
    Substitution is capture-avoiding by construction.

    WELL-FORMEDNESS CRITERIA (wf_expr):
    - All variable references are bound
    - All types are well-kinded
    - All branches in match are exhaustive
    - No dangling references

    INDUCTION CASES:
    - EVar y: If y = x, result is v (wf by hypothesis)
              If y <> x, result is EVar y (wf unchanged)
    - ELam y t body: If y = x, no substitution in body (x is shadowed)
                     If y <> x, recurse on body (y stays bound)
    - EApp f arg: IH on f and arg, combine
    - ELet p rhs body: Substitute in rhs, check pattern bindings
    - ... (each expression form)

    KEY INSIGHT: Capture-avoiding substitution ensures no free variables
    become accidentally bound. Fresh variable generation (T-1.3) is used
    when necessary to avoid capture.

    (* TODO: Implement with structural induction:
       #push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
       let rec subst_expr_wf_impl (x: var) (v: expr) (e: expr)
           : Lemma (requires wf_expr e /\ wf_expr v)
                   (ensures wf_expr (subst_expr x v e))
                   (decreases e) =
         match e with
         | EVar y -> if y = x then () else ()
         | ELam y t body ->
           if y = x then ()  (* x shadowed, no subst *)
           else if mem y (free_vars v) then
             (* Need capture-avoiding: rename y to fresh *)
             let y' = fresh_var (free_vars v `union` free_vars body) in
             let body' = subst_expr y (EVar y') body in
             subst_expr_wf_impl x v body'
           else
             subst_expr_wf_impl x v body
         | EApp f arg ->
           subst_expr_wf_impl x v f;
           subst_expr_wf_impl x v arg
         | ...
       #pop-options
    *)

    DEPENDENCIES: T-1.3 (fresh_var_spec), free_vars correctness
    SMT HINTS: May need --fuel 2 for nested lambdas
*)
val subst_expr_wf : unit ->
  Lemma (ensures True)
  (* Actual: wf_expr e /\ wf_expr v ==> wf_expr (subst x v e) *)

val subst_expr_wf_priority : unit -> Tot priority
val subst_expr_wf_status : unit -> Tot theorem_status
val subst_expr_wf_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-3.2: Substitution Free Variables
   ---------------------------------------------------------------------------- *)
(** ID: T-3.2
    Statement: Free variables after substitution
    Category: Expressions
    Location: BrrrExpressions.fst:2111
    Effort: 3-5 hours
    Status: ADMITTED

    PROOF TECHNIQUE: Structural induction on expression e.

    This is a FOUNDATIONAL lemma for reasoning about variable scoping.
    It characterizes exactly which variables are free after substitution.

    STATEMENT (more precisely):
    free_vars (subst x v e) =
      (free_vars e \ {x}) U (if x in free_vars e then free_vars v else {})

    INTUITION:
    - x is removed from free vars (it gets replaced by v)
    - If x was actually free in e, we add free vars of v (now exposed)
    - If x wasn't free in e, substitution is no-op, free vars unchanged

    INDUCTION CASES:
    - EVar y:
      * If y = x: subst x v (EVar x) = v, free_vars = free_vars v
        ({x} \ {x}) U free_vars v = {} U free_vars v = free_vars v (correct)
      * If y <> x: subst x v (EVar y) = EVar y, free_vars = {y}
        ({y} \ {x}) U {} = {y} (correct since x not in {y})

    - ELam y t body:
      * If y = x: x is shadowed, subst x v (ELam x t body) = ELam x t body
        free_vars = free_vars body \ {x} (no change)
      * If y <> x: subst x v (ELam y t body) = ELam y t (subst x v body)
        Apply IH to body, adjust for y binding

    - EApp f arg: Combine IH results with union

    - ELet: Similar to ELam, pattern may bind x

    (* TODO: Implement with careful set operations:
       #push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
       let rec subst_expr_free_vars_impl (x: var) (v: expr) (e: expr)
           : Lemma (ensures
               free_vars (subst_expr x v e) ==
               (free_vars e `remove` x) `union`
               (if mem x (free_vars e) then free_vars v else empty))
               (decreases e) =
         match e with
         | EVar y ->
           if y = x then
             (* subst x v (EVar x) = v *)
             assert (free_vars v == (singleton x `remove` x) `union` free_vars v)
           else
             (* subst x v (EVar y) = EVar y, x not in {y} *)
             assert (singleton y == (singleton y `remove` x) `union` empty)

         | ELam y t body ->
           if y = x then
             (* x shadowed *)
             ()
           else begin
             subst_expr_free_vars_impl x v body;
             (* Combine with lambda's binding of y *)
             set_remove_union_lemma x y (free_vars body)
           end

         | EApp f arg ->
           subst_expr_free_vars_impl x v f;
           subst_expr_free_vars_impl x v arg;
           (* Combine with union *)
           set_union_remove_distrib_lemma x (free_vars f) (free_vars arg)

         | ...
       #pop-options

       (* Helper: set operations distribute over remove/union *)
       let set_remove_union_distrib_lemma (x: var) (s1 s2: set var)
           : Lemma (ensures (s1 `union` s2) `remove` x ==
                           (s1 `remove` x) `union` (s2 `remove` x)) = ...
    *)

    DEPENDENCIES: Set operation lemmas, T-3.1 (subst_expr_wf)
    SMT HINTS: #set-options "--fuel 2" may be needed for nested cases
*)
val subst_expr_free_vars : unit ->
  Lemma (ensures True)
  (* Actual: free_vars (subst x v e) ==
             (free_vars e `remove` x) `union`
             (if x `mem` free_vars e then free_vars v else empty) *)

val subst_expr_free_vars_priority : unit -> Tot priority
val subst_expr_free_vars_status : unit -> Tot theorem_status
val subst_expr_free_vars_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-3.3: Eval Preserves Valid Locations
   ---------------------------------------------------------------------------- *)
(** ID: T-3.3
    Statement: Evaluation preserves location validity
    Category: Eval
    Location: BrrrEval.fst:2249
    Effort: 3-5 hours
    Status: ADMITTED
    Proof: Heap helper lemmas for allocation/deallocation *)
val eval_preserves_valid_locs : unit ->
  Lemma (ensures True)
  (* Actual: valid_locs st ==> valid_locs (snd (eval_expr fuel e st)) *)

val eval_preserves_valid_locs_priority : unit -> Tot priority
val eval_preserves_valid_locs_status : unit -> Tot theorem_status
val eval_preserves_valid_locs_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-3.4: Import Preserves Types
   ---------------------------------------------------------------------------- *)
(** ID: T-3.4
    Statement: Module imports preserve type kinds
    Category: Modules
    Location: BrrrModuleSystem.fst:4357
    Effort: 3-4 hours
    Status: ADMITTED
    Proof: Kind monotonicity through module graph *)
val import_preserves_types : unit ->
  Lemma (ensures True)
  (* Actual: imports m1 m2 /\ exports m2 name ==> type_of m1 name == type_of m2 name *)

val import_preserves_types_priority : unit -> Tot priority
val import_preserves_types_status : unit -> Tot theorem_status
val import_preserves_types_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-3.5: Detect Violations Strict Complete
   ---------------------------------------------------------------------------- *)
(** ID: T-3.5
    Statement: Strict violation detection is complete
    Category: Taint
    Location: BrrrTaintEffects.fst:926
    Effort: 3-4 hours
    Status: ADMITTED
    Proof: Complex induction on CPG structure *)
val detect_violations_strict_complete : unit ->
  Lemma (ensures True)
  (* Actual: actual_violation cpg policy v ==> v `mem` detect_violations_strict cpg policy *)

val detect_violations_strict_complete_priority : unit -> Tot priority
val detect_violations_strict_complete_status : unit -> Tot theorem_status
val detect_violations_strict_complete_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-3.6: Neg Wrap Involutive
   ---------------------------------------------------------------------------- *)
(** ID: T-3.6
    Statement: Wrapped negation is involutive
    Category: Primitives
    Location: BrrrPrimitives.fst:1306
    Effort: 3-5 hours
    Status: ADMITTED
    Proof: op_At_Percent lemmas for modular arithmetic *)
val neg_wrap_involutive : unit ->
  Lemma (ensures True)
  (* Actual: neg_wrap (neg_wrap x) == x *)

val neg_wrap_involutive_priority : unit -> Tot priority
val neg_wrap_involutive_status : unit -> Tot theorem_status
val neg_wrap_involutive_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-3.7: Handler Termination (Conditional)
   ---------------------------------------------------------------------------- *)
(** ID: T-3.7
    Statement: If operations terminate AND continuation is linear, THEN handler terminates
    Category: Effects
    Location: BrrrEffects.fst (implicit)
    Effort: 4-8 hours
    Status: ADMITTED
    Literature: Plotkin-Pretnar 2009 Section 8
    Proof: Structural induction on well-founded effect signatures *)
val handler_termination_conditional : unit ->
  Lemma (ensures True)
  (* Actual: all_terminate ops /\ linear_continuation h ==> terminates (handle h) *)

val handler_termination_conditional_priority : unit -> Tot priority
val handler_termination_conditional_status : unit -> Tot theorem_status
val handler_termination_conditional_category : unit -> Tot theorem_category


(* ============================================================================
   END OF PRIORITY 3: 7 theorems (24-47 hours total)
   ============================================================================ *)


(* ============================================================================
   PRIORITY 4: HIGH EFFORT (4-16 hours each)
   ============================================================================
   Require substantial mechanization, possibly porting from other proof
   assistants or careful graph/domain theory reasoning.
   ============================================================================ *)

(* ----------------------------------------------------------------------------
   T-4.1: Normalize Expression Equivalence
   ---------------------------------------------------------------------------- *)
(** ID: T-4.1
    Statement: Normalization preserves semantics
    Category: Expressions
    Location: BrrrExpressions.fst:2276
    Effort: 4-6 hours
    Status: ADMITTED

    PROOF TECHNIQUE: Show each normalization rule preserves evaluation.

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 3):
    With the CORRECTED definition of alpha equivalence (normalization-based),
    this theorem becomes much simpler to state and prove.

    NORMALIZATION RULES AND THEIR SEMANTIC PRESERVATION:

    1. BLOCK FLATTENING: { { e } } --> e
       eval (EBlock [EBlock [e]]) st
       = eval (EBlock [e]) st           (* by eval_block *)
       = eval e st                       (* by eval_block *)

    2. SINGLETON UNWRAPPING: { e } --> e
       eval (EBlock [e]) st = eval e st  (* by definition *)

    3. IDENTITY LET ELIMINATION: let x = e in x --> e
       eval (ELet x e (EVar x)) st
       = let v = eval e st in
         eval (EVar x) (extend st x v)  (* by eval_let *)
       = let v = eval e st in v          (* by eval_var *)
       = eval e st                        (* simplify *)

    4. BOUND VARIABLE RENAMING (for alpha equivalence):
       If y is fresh, let x = e1 in e2 --> let y = e1 in e2[y/x]
       Semantically identical (just renaming)

    (* TODO: Prove each normalization rule preserves semantics:
       #push-options "--fuel 2 --ifuel 1 --z3rlimit 50"

       let block_flatten_preserves (e: expr) (st: state)
           : Lemma (ensures eval (EBlock [EBlock [e]]) st == eval e st) =
         ()  (* Should follow from eval_block definition *)

       let singleton_unwrap_preserves (e: expr) (st: state)
           : Lemma (ensures eval (EBlock [e]) st == eval e st) =
         ()

       let identity_let_preserves (x: var) (e: expr) (st: state)
           : Lemma (ensures eval (ELet x e (EVar x)) st == eval e st) =
         let v = eval e st in
         assert (eval (EVar x) (extend st x v) == v)

       let rec normalize_expr_equiv_impl (e: expr) (st: state)
           : Lemma (ensures eval e st == eval (normalize_expr e) st)
                   (decreases e) =
         match e with
         | EBlock stmts -> normalize_block_equiv stmts st
         | ELet x rhs body ->
           normalize_expr_equiv_impl rhs st;
           (* Check if identity let *)
           if is_identity_let x body then
             identity_let_preserves x rhs st
           else
             normalize_expr_equiv_impl body (extend st x (eval rhs st))
         | _ -> ()
       #pop-options
    *)

    DEPENDENCIES: T-2.7 (normalize_expr_idempotent), eval definition
*)
val normalize_expr_equiv : unit ->
  Lemma (ensures True)
  (* Actual: eval e st == eval (normalize e) st *)

val normalize_expr_equiv_priority : unit -> Tot priority
val normalize_expr_equiv_status : unit -> Tot theorem_status
val normalize_expr_equiv_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-4.2: Eval Closed Environment Irrelevant
   ---------------------------------------------------------------------------- *)
(** ID: T-4.2
    Statement: Closed expressions ignore environment
    Category: Eval
    Location: BrrrEval.fst:2188
    Effort: 4-6 hours
    Status: ADMITTED
    Proof: Structural induction - no free vars = no env lookup *)
val eval_closed_env_irrelevant : unit ->
  Lemma (ensures True)
  (* Actual: closed e ==> eval_with_env e env1 st == eval_with_env e env2 st *)

val eval_closed_env_irrelevant_priority : unit -> Tot priority
val eval_closed_env_irrelevant_status : unit -> Tot theorem_status
val eval_closed_env_irrelevant_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-4.3: Division Checked Correct
   ---------------------------------------------------------------------------- *)
(** ID: T-4.3
    Statement: Checked division is correct
    Category: Primitives
    Location: BrrrPrimitives.fst:426
    Effort: 4-6 hours
    Status: ADMITTED

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 1):
    ============================================================
    CRITICAL: The original theorem statement is INCOMPLETE.
    Division is only correct when inputs are in the representable range.

    ORIGINAL (incorrect for all inputs):
      y <> 0 ==> div_checked x y == Some (x / y)

    CORRECTED (with valid_input precondition):
      valid_input it x /\ valid_input it y /\ y <> 0 ==>
      div_checked it x y == Some (x / y)

    where valid_input it n = n in representable_range(it)

    EDGE CASES requiring precondition:
    - Unsigned division with negative inputs (undefined in unsigned)
    - Signed division where dividend is MIN_INT and divisor is -1 (overflow)
    - Inputs outside the range of the target type

    PROOF TECHNIQUE (fstar_pop_book.md lines 15200-15250):
    Case analysis on integer type signedness and input ranges.
    Reference HACL* Lib.IntTypes for verified integer operations.

    (* TODO: Add valid_input precondition per errata Chapter 1 *)
*)
val div_checked_correct : unit ->
  Lemma (ensures True)
  (* Actual: valid_input it x /\ valid_input it y /\ y <> 0 ==>
             div_checked it x y == Some (x / y) *)

val div_checked_correct_priority : unit -> Tot priority
val div_checked_correct_status : unit -> Tot theorem_status
val div_checked_correct_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-4.4: Int Division Result Spec
   ---------------------------------------------------------------------------- *)
(** ID: T-4.4
    Statement: Integer division result specification
    Category: Primitives
    Location: BrrrPrimitives.fst:467
    Effort: 4-6 hours
    Status: ADMITTED

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 1):
    ============================================================
    Like T-4.3, requires valid_input precondition for full correctness.

    CORRECTED STATEMENT:
      valid_input w x /\ valid_input w y /\
      y <> 0 /\ not (x == int_min w /\ y == -1) ==>
      in_range w (v x / v y)

    The MIN_INT / -1 case is special: mathematical result is MAX_INT + 1,
    which overflows for two's complement representation.

    PROOF TECHNIQUE: Uses FStar.Math.Lemmas for modular arithmetic.
    See fstar_pop_book.md lines 15200-15250 for arithmetic proof patterns.

    (* TODO: Add valid_input precondition per errata Chapter 1 *)
*)
val int_div_result_spec : unit ->
  Lemma (ensures True)
  (* Actual: valid_input w x /\ valid_input w y /\
             y <> 0 /\ not (x == int_min w /\ y == -1) ==>
             in_range w (v x / v y) *)

val int_div_result_spec_priority : unit -> Tot priority
val int_div_result_spec_status : unit -> Tot theorem_status
val int_div_result_spec_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-4.5: Module Dependencies Acyclic
   ---------------------------------------------------------------------------- *)
(** ID: T-4.5
    Statement: Module dependency graph is acyclic
    Category: Modules
    Location: BrrrModuleSystem.fst:4290
    Effort: 4-6 hours
    Status: ADMITTED
    Proof: Graph theory - topological order exists iff acyclic *)
val module_deps_acyclic : unit ->
  Lemma (ensures True)
  (* Actual: well_formed_modules modules ==> acyclic (build_dep_graph modules) *)

val module_deps_acyclic_priority : unit -> Tot priority
val module_deps_acyclic_status : unit -> Tot theorem_status
val module_deps_acyclic_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-4.6: Coherence Decidability
   ---------------------------------------------------------------------------- *)
(** ID: T-4.6
    Statement: Session type coherence is decidable
    Category: Sessions
    Location: BrrrMultipartySession.fst
    Effort: 4-8 hours
    Status: ADMITTED
    Literature: Honda 2008 + Tirore 2025 (Coq template)

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 5):
    ============================================================
    CRITICAL: Original Honda 2008 definition of "coherence" via projection
    was INCOMPLETE for recursive types. Problems discovered:

    1. PROJECTABILITY: The merging condition for recursive types was
       too restrictive, rejecting valid protocols.

    2. ASSOCIATION RELATION: Yoshida & Hou 2024 introduced a top-down
       approach using "association relation" that correctly handles
       recursive types with subtyping.

    CORRECTED DEFINITION (Yoshida & Hou 2024):
    A global type G is coherent if:
    - G is projectable onto all participants
    - The local projections are pairwise compatible (can communicate)
    - The association relation between G and local types is well-founded

    PROOF TECHNIQUE: Constructive decidability via projection algorithm.

    The projection algorithm is:
    1. Structurally recurse on global type G
    2. For each participant p, compute local projection G|_p
    3. If projection fails (merge conflict), G is not coherent
    4. If all projections succeed, check pairwise compatibility

    DECIDABILITY follows from:
    - Global types are finite (no infinite depth)
    - Projection is a structural recursion
    - Merging is decidable (finite branching)
    - Compatibility check is decidable

    (* TODO: Implement constructive decidability proof:
       #push-options "--fuel 1 --ifuel 2 --z3rlimit 100"

       type coherence_result =
         | IsCoherent of (p:participant -> local_type)  (* witness: projections *)
         | NotCoherent of string                         (* reason for failure *)

       let rec check_coherence (g: global_type) : Tot coherence_result (decreases g) =
         (* Get all participants *)
         let participants = participants_of g in
         (* Try to project onto each *)
         let projections = map (fun p -> (p, project g p)) participants in
         (* Check if any projection failed *)
         match find (fun (_, r) -> None? r) projections with
         | Some (p, _) -> NotCoherent ("Cannot project onto " ^ show p)
         | None ->
           (* All projections succeeded, check compatibility *)
           let local_types = map (fun (p, Some l) -> (p, l)) projections in
           if pairwise_compatible local_types then
             IsCoherent (fun p -> lookup local_types p)
           else
             NotCoherent "Local types not pairwise compatible"

       let coherence_decidable_impl (g: global_type)
           : Lemma (ensures decidable (coherent g)) =
         match check_coherence g with
         | IsCoherent witness -> (* coherent g is true *)
         | NotCoherent reason -> (* coherent g is false *)
       #pop-options
    *)

    DEPENDENCIES: T-0.5 (wf_implies_projectable), projection algorithm
    NOTE: Use Yoshida & Hou 2024 formulation for correctness
*)
val coherence_decidable : unit ->
  Lemma (ensures True)
  (* Actual: decidable (coherent g) *)

val coherence_decidable_priority : unit -> Tot priority
val coherence_decidable_status : unit -> Tot theorem_status
val coherence_decidable_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-4.7: Protocol Projection Preservation
   ---------------------------------------------------------------------------- *)
(** ID: T-4.7
    Statement: Projection preserves protocol semantics
    Category: Sessions
    Location: BrrrMultipartySession.fst
    Effort: 4-8 hours
    Status: ADMITTED
    Literature: Honda 2008 + Tirore 2025, corrected by Yoshida & Hou 2024

    PROJECTION PRESERVATION THEOREM:
    If a global trace is valid for global type G, then the restricted trace
    for participant p is valid for G's projection onto p.

    This is THE key theorem connecting global and local session types.

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 5):
    ============================================================
    The original Honda 2008 proof had issues with recursive types.
    Yoshida & Hou 2024 provide a corrected proof using:

    1. ASSOCIATION RELATION: Instead of direct structural correspondence,
       use a relation that accounts for subtyping and internal choices.

    2. TOP-DOWN APPROACH: Start from global type, show local projections
       simulate global behavior (vs bottom-up composition).

    STATEMENT (more precisely):
    forall G, trace, p.
      valid_global_trace G trace ==>
      valid_local_trace (project G p) (restrict trace p)

    where:
    - restrict trace p = filter (involves_participant p) trace
    - involves_participant p action = sender(action) = p \/ receiver(action) = p

    PROOF TECHNIQUE: Simulation via association relation.

    Define association relation ~_A between global and local configurations:
    - (G, S_1, ..., S_n) ~_A if G associates with all S_i
    - Association is defined coinductively for recursive types

    Show: If (G, S_1, ..., S_n) ~_A and G --> G' via action a,
          then S_p --> S_p' (for involved p) and (G', S_1', ..., S_n') ~_A

    (* TODO: Port from Yoshida & Hou 2024 or Tirore 2025.
       Key definitions needed:

       (* Association relation *)
       let rec associated (g: global_type) (p: participant) (s: local_type)
           : Tot bool (decreases g) = ...

       (* Global trace validity *)
       let rec valid_global_trace (g: global_type) (trace: list action)
           : Tot bool (decreases trace) = ...

       (* Local trace validity *)
       let rec valid_local_trace (s: local_type) (trace: list action)
           : Tot bool (decreases trace) = ...

       (* Main theorem *)
       #push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
       let rec projection_preserves_semantics_impl
           (g: global_type) (trace: list action) (p: participant)
           : Lemma (requires valid_global_trace g trace)
                   (ensures valid_local_trace (project g p) (restrict trace p))
                   (decreases trace) =
         match trace with
         | [] -> ()
         | a::rest ->
           (* Show a is valid for projection *)
           if involves_participant p a then
             action_valid_for_projection g p a;
             projection_preserves_semantics_impl (global_step g a) rest p
           else
             (* p not involved, trace unchanged locally *)
             projection_preserves_semantics_impl (global_step g a) rest p
       #pop-options
    *)

    DEPENDENCIES: T-0.5 (wf_implies_projectable), T-4.6 (coherence_decidable)
    NOTE: Use Yoshida & Hou 2024 Theorems 1, 2 for correct formulation
*)
val projection_preserves_semantics : unit ->
  Lemma (ensures True)
  (* Actual: global_trace g trace ==> local_trace (project g p) (restrict trace p) *)

val projection_preserves_semantics_priority : unit -> Tot priority
val projection_preserves_semantics_status : unit -> Tot theorem_status
val projection_preserves_semantics_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-4.8: Stack Filtering Correctness
   ---------------------------------------------------------------------------- *)
(** ID: T-4.8
    Statement: IFDS stack filtering doesn't lose facts
    Category: Analysis
    Location: synthesis_part12.tex:1938-1945
    Effort: 4-8 hours
    Status: ADMITTED
    Literature: Horwitz 1990
    Proof: Given call graph completeness (Axiom A.14) *)
val stack_filtering_correct : unit ->
  Lemma (ensures True)
  (* Actual: complete_call_graph cg ==> (loc `in` filtered ==> loc `in` concrete_pts) *)

val stack_filtering_correct_priority : unit -> Tot priority
val stack_filtering_correct_status : unit -> Tot theorem_status
val stack_filtering_correct_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-4.9: Qilin Algorithm Soundness
   ---------------------------------------------------------------------------- *)
(** ID: T-4.9
    Statement: Qilin points-to analysis is sound
    Category: Analysis
    Location: synthesis_part13.tex:737-754
    Effort: 4-8 hours
    Status: ADMITTED
    Literature: Tan 2022
    Proof: Given call graph correctness *)
val qilin_sound : unit ->
  Lemma (ensures True)
  (* Actual: sound_call_graph cg ==> (may_alias p q ==> overlap (qilin_pts p) (qilin_pts q)) *)

val qilin_sound_priority : unit -> Tot priority
val qilin_sound_status : unit -> Tot theorem_status
val qilin_sound_category : unit -> Tot theorem_category


(* ============================================================================
   END OF PRIORITY 4: 9 theorems (40-86 hours total)
   ============================================================================ *)


(* ============================================================================
   PRIORITY 5: RESEARCH-GRADE (8-80 hours each)
   ============================================================================
   Major theorems requiring significant research effort:
   - Porting from existing Coq/Agda/Isabelle proofs
   - Novel proof development following literature
   - Large mechanization efforts (potentially thousands of lines)
   ============================================================================ *)

(* ----------------------------------------------------------------------------
   T-5.1: Session Progress
   ---------------------------------------------------------------------------- *)
(** ID: T-5.1
    Statement: Well-typed sessions make progress
    Category: Sessions
    Location: BrrrSessionTypes.fst (theorem statement)
    Effort: 8-16 hours
    Status: ADMITTED
    Literature: Honda 2008 Theorem 5.12 + Tirore 2025 (Coq mechanization)

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 5):
    ============================================================
    IMPORTANT: Original Honda et al. 2008 proofs had FLAWS discovered by
    Scalas & Yoshida 2019. The problems involve:

    1. PROJECTABILITY: Original definition was too restrictive for recursive types.
       - Fix: Use "association relation" (Yoshida & Hou 2024)

    2. SUBJECT REDUCTION: Process can CHOOSE which typing context reduction
       to follow due to subtyping. Original proof assumed determinism.
       - Fix: Use Theorem 5.4 from Scalas & Yoshida 2019 (corrected)

    3. TYPE SAFETY: Bottom-up approach (Scalas 2019) or top-down approach
       (Yoshida & Hou 2024) both provide correct proofs.

    PROOF TECHNIQUE: Structural induction on typing derivation.

    The proof proceeds by case analysis on the process form:
    - PEnd: Trivially satisfies p == PEnd
    - PSend c v P: Session type must be !T.S
      - By typing, c has session type !T.S
      - Can perform send action (progress)
    - PRecv c x P: Session type must be ?T.S
      - By typing, c has session type ?T.S
      - Either message available (can receive) or blocked waiting (rely on dual)
    - PChoice/PBranch: Similar reasoning with choice types

    KEY INSIGHT: Deadlock freedom (T-0.6) is a corollary of this theorem.

    (* TODO: Port from Tirore 2025 Coq mechanization.
       Key files in Coq development:
       - theories/sessions/Progress.v (main theorem)
       - theories/sessions/SubjectReduction.v (helper)
       - theories/sessions/Typing.v (typing rules)

       F* proof sketch:
       #push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
       let rec session_progress_impl (delta: typing_context) (p: process)
           : Lemma (requires typed delta p)
                   (ensures p == PEnd \/ (exists p'. step p p'))
                   (decreases p) =
         match p with
         | PEnd -> ()
         | PSend c v p' ->
           let s = lookup_session delta c in
           assert (SSend? s);  (* By typing *)
           (* send action is always enabled *)
           ()
         | PRecv c x p' ->
           let s = lookup_session delta c in
           assert (SRecv? s);  (* By typing *)
           (* Need to show message will arrive - use deadlock freedom *)
           deadlock_freedom ();
           ()
         | ...
       #pop-options
    *)

    DEPENDENCIES: T-0.6 (deadlock_freedom), subject_reduction lemma
    PORTING EFFORT: ~16 hours to port 2K lines from Coq
*)
val session_progress : unit ->
  Lemma (ensures True)
  (* Actual: typed delta p ==> p == PEnd \/ (exists p'. step p p') *)

val session_progress_priority : unit -> Tot priority
val session_progress_status : unit -> Tot theorem_status
val session_progress_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.2: Session Fidelity
   ---------------------------------------------------------------------------- *)
(** ID: T-5.2
    Statement: Well-typed processes follow their session types
    Category: Sessions
    Location: BrrrSessionTypes.fst (theorem statement)
    Effort: 8-16 hours
    Status: ADMITTED
    Literature: Honda 2008 Corollary 5.6 + Tirore 2025
               Scalas & Yoshida 2019 Theorem 5.4 (corrected)

    SESSION FIDELITY (Type Safety for Session Types):
    Well-typed processes produce communication traces that conform
    to their declared session types.

    SPECIFICATION ERRATA (see SPECIFICATION_ERRATA.md Chapter 5):
    ============================================================
    CRITICAL: The original Honda 2008 proof has a subtle bug in
    subject reduction due to SUBTYPING.

    ORIGINAL CLAIM: Typing context reduction is unique
    ACTUAL: Process can CHOOSE which typing context reduction to follow

    EXAMPLE:
    If S1 <: S2 and process P is typed with S1, then P can behave
    according to S2's protocol (since S1 is more specific).

    CORRECTED STATEMENT (Scalas & Yoshida 2019 Theorem 5.4):
    If typed delta P and P -->* P', then there exists delta' such that
    delta -->* delta' and typed delta' P'.

    The key is the EXISTENTIAL quantifier over typing context reduction.

    PROOF TECHNIQUE: Subject reduction + trace semantics.

    1. SUBJECT REDUCTION: If typed delta P and P --> P',
       then exists delta'. delta --> delta' and typed delta' P'

    2. TRACE CONFORMANCE: Build trace from P's execution,
       show each action matches session type expectation

    The proof uses a simulation argument between process transitions
    and session type transitions.

    (* TODO: Port from Tirore 2025 Coq or implement directly.
       Key insight: Use the CORRECTED subject reduction from
       Scalas & Yoshida 2019, not the original Honda 2008.

       F* proof structure:
       #push-options "--fuel 2 --ifuel 2 --z3rlimit 150"

       (* Subject reduction - the key lemma *)
       let rec subject_reduction (delta: typing_ctx) (p p': process)
           : Lemma (requires typed delta p /\ step p p')
                   (ensures exists delta'. ctx_step delta delta' /\ typed delta' p')
                   (decreases p) = ...

       (* Trace conformance *)
       let rec session_fidelity_impl (p: process) (s: session_type) (trace: list action)
           : Lemma (requires typed_session p s /\ execution_trace p trace)
                   (ensures conforms trace s)
                   (decreases trace) =
         match trace with
         | [] -> ()  (* Empty trace trivially conforms *)
         | a::rest ->
           (* a is action taken by p *)
           subject_reduction ...;  (* p --> p' *)
           (* Session type s must allow a *)
           session_type_allows_action s a;
           (* Recurse on rest of trace with updated session type *)
           session_fidelity_impl p' (session_step s a) rest
       #pop-options
    *)

    DEPENDENCIES: T-5.1 (session_progress), subject_reduction lemma
    PORTING EFFORT: ~16 hours from Tirore 2025
*)
val session_fidelity : unit ->
  Lemma (ensures True)
  (* Actual: typed_session p s ==> (execution_trace p trace ==> conforms trace s) *)

val session_fidelity_priority : unit -> Tot priority
val session_fidelity_status : unit -> Tot theorem_status
val session_fidelity_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.3: Convertibility Soundness
   ---------------------------------------------------------------------------- *)
(** ID: T-5.3
    Statement: Cross-language type convertibility is sound
    Category: FFI
    Location: synthesis_part11.tex:732-738
    Effort: 8-16 hours
    Status: ADMITTED
    Literature: Patterson 2022 Lemma 3.1 (PLDI) *)
val convertibility_sound : unit ->
  Lemma (ensures True)
  (* Actual: convertible tau_A tau_B /\ realizes source_lang tau_A v
             ==> realizes target_lang tau_B (convert v) *)

val convertibility_sound_priority : unit -> Tot priority
val convertibility_sound_status : unit -> Tot theorem_status
val convertibility_sound_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.4: Matthews-Findler Boundary Soundness
   ---------------------------------------------------------------------------- *)
(** ID: T-5.4
    Statement: Multi-language boundary terms are type-sound
    Category: FFI
    Location: synthesis_part13.tex
    Effort: 8-16 hours
    Status: ADMITTED
    Literature: Matthews-Findler 2007 Theorems 1-6 *)
val boundary_soundness : unit ->
  Lemma (ensures True)
  (* Actual: typed_multi e tau ==> e -->* v \/ e -->* Error \/ diverges e *)

val boundary_soundness_priority : unit -> Tot priority
val boundary_soundness_status : unit -> Tot theorem_status
val boundary_soundness_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.5: Noninterference
   ---------------------------------------------------------------------------- *)
(** ID: T-5.5
    Statement: Well-typed programs satisfy noninterference
    Category: Security
    Location: BrrrInformationFlow.fst (theorem statement)
    Effort: 40-80 hours
    Status: ADMITTED
    Literature: Volpano 1996, Sabelfeld & Myers 2003 (survey)

    THEOREM STATEMENT (Termination-Insensitive Noninterference):
    If a program is well-typed under the information flow type system,
    then for any two states s1, s2 that agree on LOW-labeled values,
    the resulting states (if both terminate) also agree on LOW values.

    Formally:
      typed_IFC Low e ==>
      (low_equiv s1 s2 /\ terminates e s1 /\ terminates e s2
       ==> low_equiv (eval e s1) (eval e s2))

    PROOF TECHNIQUE: Logical relations / simulation argument.

    The proof proceeds by induction on the typing derivation:

    1. T-VAR (x : tau^L): Reading low variable preserves low-equivalence
    2. T-CONST: Constants are same in both executions
    3. T-OP: Operations on low values produce same results
    4. T-IF (pc = Low): Both executions take same branch (condition is low)
    5. T-IF (pc = High): Both branches must produce low-equivalent results
       - This is where "implicit flow" is controlled
    6. T-ASSIGN (x : tau^L): Can only assign when pc = Low
       - Prevents assignment inside high branches
    7. T-SEQ, T-LET: Compose IH applications

    KEY INSIGHT: The pc (program counter) label tracks implicit flows.
    When branching on HIGH data, pc becomes HIGH, preventing LOW assignments.

    TERMINATION SENSITIVITY NOTE:
    This theorem is TERMINATION-INSENSITIVE. A high-security adversary
    can learn 1 bit per observation by causing divergence. For full security,
    use termination-sensitive noninterference (harder to prove, ~2x effort).

    (* TODO: Port from existing F* or Coq developments.
       Potential sources:
       - Barthe et al. 2004 "Secure Information Flow by Self-Composition"
       - FlowCaml implementation (OCaml type system)

       F* proof structure:
       #push-options "--fuel 0 --ifuel 0 --z3rlimit 200"
       let rec noninterference_impl (pc: sec_level) (e: expr) (s1 s2: state)
           : Lemma (requires typed_IFC pc e /\ low_equiv s1 s2 /\
                            terminates e s1 /\ terminates e s2)
                   (ensures low_equiv (eval e s1) (eval e s2))
                   (decreases e) =
         match e with
         | EVar x ->
           if label_of x = Low then
             (* Both states have same value for low vars *)
             ()
           else
             (* High var, result doesn't affect low equivalence *)
             ()
         | EIf cond then_ else_ ->
           if label_of_expr cond = Low then
             (* Same branch in both executions *)
             noninterference_impl pc (if eval_cond cond s1 then then_ else else_) s1 s2
           else
             (* Different branches possible, but pc is now High *)
             noninterference_impl High then_ s1 s2;
             noninterference_impl High else_ s1 s2;
             (* Both produce low-equivalent results since pc=High *)
             ()
         | ...
       #pop-options
    *)

    DEPENDENCIES: low_equiv_trans, label_of_expr soundness
    PORTING EFFORT: ~40-80 hours depending on complexity of expression language
*)
val noninterference : unit ->
  Lemma (ensures True)
  (* Actual: typed_IFC pc e ==>
             (low_equiv s1 s2 /\ terminates e s1 /\ terminates e s2
              ==> low_equiv (eval e s1) (eval e s2)) *)

val noninterference_priority : unit -> Tot priority
val noninterference_status : unit -> Tot theorem_status
val noninterference_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.6: Blame Soundness
   ---------------------------------------------------------------------------- *)
(** ID: T-5.6
    Statement: Blame correctly identifies contract violators
    Category: Security
    Location: BrrrContracts.fst (theorem statement)
    Effort: 16-32 hours
    Status: ADMITTED
    Literature: Wadler-Findler 2009 *)
val blame_soundness : unit ->
  Lemma (ensures True)
  (* Actual: blame (check e contract) = Some party ==> party violates contract *)

val blame_soundness_priority : unit -> Tot priority
val blame_soundness_status : unit -> Tot theorem_status
val blame_soundness_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.7: Parametricity (Abstraction Theorem)
   ---------------------------------------------------------------------------- *)
(** ID: T-5.7
    Statement: Related inputs produce related outputs
    Category: Security
    Location: BrrrTypeChecker.fst (theorem statement)
    Effort: 16-32 hours
    Status: ADMITTED
    Literature: Reynolds 1983, Bernardy 2010 (Agda mechanization) *)
val parametricity : unit ->
  Lemma (ensures True)
  (* Actual: (f: forall a. a -> a) ==> forall a (x:a). f x == x *)

val parametricity_priority : unit -> Tot priority
val parametricity_status : unit -> Tot theorem_status
val parametricity_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.8: Occurrence Typing Soundness
   ---------------------------------------------------------------------------- *)
(** ID: T-5.8
    Statement: Type narrowing after predicates is sound
    Category: Types
    Location: BrrrTypeChecker.fst
    Effort: 8-16 hours
    Status: ADMITTED
    Literature: Tobin-Hochstadt 2008 (Isabelle/HOL mechanization) *)
val occurrence_typing_sound : unit ->
  Lemma (ensures True)
  (* Actual: typeof e = Union [T1; T2] /\ pred filters T1
             ==> typeof (refine e pred) = T1 *)

val occurrence_typing_sound_priority : unit -> Tot priority
val occurrence_typing_sound_status : unit -> Tot theorem_status
val occurrence_typing_sound_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.9: Round-Trip Preservation
   ---------------------------------------------------------------------------- *)
(** ID: T-5.9
    Statement: parse -> IR -> pretty-print preserves semantics
    Category: FFI
    Location: synthesis_part13.tex:209-211
    Effort: 40-80 hours (per language)
    Status: ADMITTED
    Literature: CompCert-style proof *)
val round_trip_preservation : unit ->
  Lemma (ensures True)
  (* Actual: eval (parse source) == eval (parse (pretty_print (to_ir (parse source)))) *)

val round_trip_preservation_priority : unit -> Tot priority
val round_trip_preservation_status : unit -> Tot theorem_status
val round_trip_preservation_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.10: Control Flow Modeling
   ---------------------------------------------------------------------------- *)
(** ID: T-5.10
    Statement: CFG correctly models all control flow constructs
    Category: Analysis
    Location: synthesis_part13.tex:212-213
    Effort: 8-16 hours
    Status: ADMITTED
    Proof: Show implementation matches language spec *)
val cfg_complete : unit ->
  Lemma (ensures True)
  (* Actual: cfg = build_cfg program ==>
             (execution_path program path ==> cfg_path cfg path) *)

val cfg_complete_priority : unit -> Tot priority
val cfg_complete_status : unit -> Tot theorem_status
val cfg_complete_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.11: DRF-SC Theorem
   ---------------------------------------------------------------------------- *)
(** ID: T-5.11
    Statement: Data-race-free programs have SC semantics
    Category: Memory
    Location: Concurrency.fst (theorem statement)
    Effort: 20-40 hours
    Status: ADMITTED
    Literature: Boehm-Adve 2008 Theorem 7.1, Promising 2.0 (30K Coq)

    DRF-SC THEOREM (Data-Race-Freedom implies Sequential Consistency):
    If a program has no data races under sequentially consistent semantics,
    then all executions under the relaxed memory model are sequentially consistent.

    This is THE fundamental theorem for reasoning about concurrent programs.
    It allows programmers to reason about well-synchronized code as if
    memory operations execute in program order.

    DEFINITIONS:
    - Data race: Two conflicting accesses to same location, at least one write,
      not ordered by happens-before
    - Sequential consistency: All threads see same interleaving of operations
    - Happens-before: Transitive closure of program order + synchronization

    PROOF TECHNIQUE: Show that relaxed executions of DRF programs
    are equivalent to some SC execution.

    Key insight: If program is DRF, relaxed reorderings don't change
    observable behavior because there are no races to observe them.

    EXISTING MECHANIZATIONS:
    - Promising Semantics 2.0 (Kang, Lee, et al.): 30,000 lines Coq
      https://github.com/snu-sf/promising-coq-2.0
    - CompCert memory model: Different approach, simpler but less general

    (* TODO: Port from Promising 2.0 Coq development.
       Key files:
       - src/promising/DRFSC.v (main theorem)
       - src/promising/Configuration.v (execution model)
       - src/promising/Memory.v (memory model)

       Alternative: Use simpler TSO model if full relaxed not needed.

       F* proof would require:
       1. Define memory model (timestamps, views, promises)
       2. Define happens-before relation
       3. Define data-race-free predicate
       4. Define SC-equivalent predicate
       5. Prove: DRF(P) ==> forall exec. valid_exec(P, exec) ==> SC_equiv(exec)

       This is a MAJOR undertaking. Consider:
       - Using F*'s Steel library which has related proofs
       - Axiomatizing DRF-SC and proving local properties instead
    *)

    DEPENDENCIES: Memory model definitions, happens-before relation
    PORTING EFFORT: 20-40 hours, may need simplifications
*)
val drf_sc : unit ->
  Lemma (ensures True)
  (* Actual: data_race_free program ==> all_executions_sc program *)

val drf_sc_priority : unit -> Tot priority
val drf_sc_status : unit -> Tot theorem_status
val drf_sc_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.12: Frame Rule Soundness
   ---------------------------------------------------------------------------- *)
(** ID: T-5.12
    Statement: {P} C {Q} and C doesn't modify R implies {P * R} C {Q * R}
    Category: Memory
    Location: BrrrSeparationLogic.fst (theorem statement)
    Effort: 8-16 hours
    Status: ADMITTED
    Literature: Reynolds 2002, Iris (Coq mechanized)

    THE FRAME RULE (Separation Logic):
    The frame rule allows local reasoning about heap-manipulating programs.
    If we know {P} C {Q} (C transforms P to Q), and C doesn't touch
    the footprint of R, then {P * R} C {Q * R} (R is preserved).

    SEPARATING CONJUNCTION (star):
    P * R means heap can be split into disjoint parts satisfying P and R.
    This is THE key innovation of separation logic.

    PROOF TECHNIQUE: Semantic argument using heap decomposition.

    Given:
    - hoare_triple P C Q: forall h. P h ==> exists h'. eval C h = h' /\ Q h'
    - frame_safe C R: C doesn't read/write locations in footprint(R)

    Show:
    - hoare_triple (P * R) C (Q * R)

    Proof:
    1. Assume heap h satisfies (P * R)
    2. Decompose: h = h_p + h_r where P(h_p) and R(h_r)
    3. By frame_safe, C only accesses h_p
    4. By {P} C {Q}, running C on h_p produces h_p' with Q(h_p')
    5. Result heap is h_p' + h_r
    6. Since R(h_r) unchanged, we have (Q * R)(h_p' + h_r)

    EXISTING MECHANIZATIONS:
    - Iris (Coq): 40,000+ lines, very general (step-indexed, higher-order)
    - VST (Coq): Verified Software Toolchain, uses CompCert
    - F* Steel: Built into F*, may be able to leverage

    (* TODO: Use F* Steel library or implement from scratch.
       Steel approach:
       - Steel.Effect provides separation logic primitives
       - Steel.FramingLemma may already have this

       From-scratch approach:
       #push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
       let frame_rule_sound_impl (p q r: heap_prop) (c: command)
           : Lemma (requires hoare_triple p c q /\ frame_safe c r)
                   (ensures hoare_triple (star p r) c (star q r)) =
         (* Introduce arbitrary heap satisfying P * R *)
         FStar.Classical.forall_intro (fun h ->
           FStar.Classical.move_requires (fun (pf: (star p r) h) ->
             (* Decompose h into h_p, h_r *)
             let h_p, h_r = decompose h pf in
             (* Apply original triple to h_p *)
             let h_p' = eval c h_p in
             (* R is preserved since frame_safe *)
             (* Combine h_p' + h_r *)
             compose_star_lemma h_p' h_r q r
           ) ()
         )
       #pop-options
    *)

    DEPENDENCIES: Heap decomposition lemmas, footprint definition
*)
val frame_rule_sound : unit ->
  Lemma (ensures True)
  (* Actual: hoare_triple p c q /\ frame_safe c r
             ==> hoare_triple (p * r) c (q * r) *)

val frame_rule_sound_priority : unit -> Tot priority
val frame_rule_sound_status : unit -> Tot theorem_status
val frame_rule_sound_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.13: No Thin-Air Values
   ---------------------------------------------------------------------------- *)
(** ID: T-5.13
    Statement: Memory model prevents thin-air reads
    Category: Memory
    Location: Concurrency.fst (theorem statement)
    Effort: 20-40 hours
    Status: ADMITTED
    Literature: Kang 2017, Lee 2020 (Promising 2.0 - 30K Coq) *)
val no_thin_air : unit ->
  Lemma (ensures True)
  (* Actual: valid_execution execution ==> no_oota_reads execution *)

val no_thin_air_priority : unit -> Tot priority
val no_thin_air_status : unit -> Tot theorem_status
val no_thin_air_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-5.14: Bi-Abduction Soundness
   ---------------------------------------------------------------------------- *)
(** ID: T-5.14
    Statement: Bi-abduction computes correct frames
    Category: Memory
    Location: BrrrSeparationLogic.fst (theorem statement)
    Effort: 8-16 hours
    Status: ADMITTED
    Literature: Calcagno 2009 Theorems 4, 5, 9 *)
val biabduction_sound : unit ->
  Lemma (ensures True)
  (* Actual: biabduct pre post = (anti_frame, frame) ==>
             (pre * anti_frame) -* post /\ frame * pre |- post *)

val biabduction_sound_priority : unit -> Tot priority
val biabduction_sound_status : unit -> Tot theorem_status
val biabduction_sound_category : unit -> Tot theorem_category


(* ============================================================================
   END OF PRIORITY 5: 14 theorems (200-520 hours total)
   ============================================================================ *)


(* ============================================================================
   HELPER FUNCTIONS
   ============================================================================ *)

(** Get all theorems as a list for programmatic access *)
val list_all_theorems : unit -> Tot (list string)

(** Get theorems by priority *)
val list_theorems_by_priority : priority -> Tot (list string)

(** Get theorems by category *)
val list_theorems_by_category : theorem_category -> Tot (list string)

(** Count theorems by status *)
val count_proven : unit -> Tot nat
val count_admitted : unit -> Tot nat
val count_in_progress : unit -> Tot nat

(** Effort estimation *)
val total_effort_hours_min : unit -> Tot nat  (* Lower bound: 292 hours *)
val total_effort_hours_max : unit -> Tot nat  (* Upper bound: 699 hours *)


(* ============================================================================
   GRAND TOTAL: 53 THEOREMS
   ============================================================================

   +----------+-------+----------------------+
   | Priority | Count | Total Effort (hours) |
   +----------+-------+----------------------+
   | P0 Done  |   7   | 0 (already proven)   |
   | P1 Easy  |   6   | 6-11                 |
   | P2 Medium|  10   | 22-35                |
   | P3 Subst.|   7   | 24-47                |
   | P4 High  |   9   | 40-86                |
   | P5 Rsrch.|  14   | 200-520              |
   +----------+-------+----------------------+
   | TOTAL    |  53   | 292-699              |
   +----------+-------+----------------------+

   KEY DEPENDENCIES:
   - P1/P2 theorems are independent, can be parallelized
   - P3/P4 may require P1/P2 helper lemmas
   - P5 theorems often require porting from Coq/Agda/Isabelle

   CRITICAL PATH:
   1. Complete P1 (enables P2/P3)
   2. Session theorems (T-5.1, T-5.2) enable protocol verification
   3. Memory theorems (T-5.11, T-5.12, T-5.13) enable low-level reasoning
   4. Security theorems (T-5.5) enable IFC verification

   SUGGESTED PROOF ORDER:
   1. T-1.1 through T-1.6 (warmup, learn infrastructure)
   2. T-2.1 through T-2.10 (build helper library)
   3. T-3.1, T-3.2 (substitution - heavily used)
   4. T-4.6, T-4.7 (session types - core feature)
   5. T-5.1, T-5.2 (session progress/fidelity - flagship theorems)
   6. T-5.5, T-5.12 (security/memory - key guarantees)

   See AXIOMS_REPORT_v2.md for full justifications and literature references.

   ============================================================================ *)
