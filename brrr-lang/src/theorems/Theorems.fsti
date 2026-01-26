(**
 * BrrrLang.Theorems - Master Index Interface
 *
 * SINGLE SOURCE OF TRUTH for all theorems in brrr-lang.
 *
 * This module declares properties that CAN AND MUST BE PROVEN from
 * definitions and axioms. Unlike Axioms.fsti, these are statements
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
 * References: AXIOMS_REPORT_v2.md for full details.
 *
 * Version: 1.0
 * Generated: 2026-01-26
 *)
module Theorems

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
    Location: SessionTypes.fst:413-423
    Effort: 0 (proven)
    Status: PROVEN
    Literature: Honda et al. 2008
    Proof: Structural induction on session types *)
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
    Location: SessionTypes.fst:502+
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
    Location: SessionTypes.fsti:1047-1049
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
    Location: SessionTypes.fsti:1064-1067
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
    Location: MultipartySession.fst:1283-1286
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
    Location: MultipartySession.fst:1302-1305
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
    Location: Modes.fst:466-485
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
    Location: TaintEffects.fst:656
    Effort: 30 minutes
    Status: ADMITTED
    Literature: Basic set theory
    Proof: For all t in A, t in (A union B) by definition of union *)
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
    Location: TaintEffects.fst:782
    Effort: 1 hour
    Status: ADMITTED
    Proof: List induction - if f x /\ x in l, then filter produces >= 1 element *)
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
    Location: Expressions.fst:1963
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
    Location: Expressions.fst:215
    Effort: 1-2 hours
    Status: ADMITTED
    Proof: Position case analysis on start/end coordinates *)
val merge_ranges_contains_left : unit ->
  Lemma (ensures True)
  (* Actual: contains (merge_ranges r1 r2) r1 *)

val merge_ranges_contains_left_priority : unit -> Tot priority
val merge_ranges_contains_left_status : unit -> Tot theorem_status
val merge_ranges_contains_left_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-1.5: Merge Ranges Contains Right
   ---------------------------------------------------------------------------- *)
(** ID: T-1.5
    Statement: Merged range contains right input
    Category: Expressions
    Location: Expressions.fst:220
    Effort: 1-2 hours
    Status: ADMITTED
    Proof: Position case analysis (same as T-1.4) *)
val merge_ranges_contains_right : unit ->
  Lemma (ensures True)
  (* Actual: contains (merge_ranges r1 r2) r2 *)

val merge_ranges_contains_right_priority : unit -> Tot priority
val merge_ranges_contains_right_status : unit -> Tot theorem_status
val merge_ranges_contains_right_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-1.6: Eval Let Binding
   ---------------------------------------------------------------------------- *)
(** ID: T-1.6
    Statement: Let binding evaluation is correct
    Category: Eval
    Location: Eval.fst:2332
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
    Location: Expressions.fst:1780
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
    Location: Expressions.fst:1944
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
    Location: Expressions.fst:2117
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
    Location: Modes.fst:469
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
    Location: Modes.fst:499
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
    Location: Modes.fst:523
    Effort: 2-3 hours
    Status: ADMITTED
    Proof: Use mode_join_linear_closed lemma *)
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
    Location: Expressions.fst:2281
    Effort: 2-3 hours
    Status: ADMITTED
    Proof: Structural analysis - normalize produces normal form *)
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
    Location: TaintEffects.fst:836
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
    Location: TaintEffects.fst:881
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
    Location: Primitives.fst:1348
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
    Location: Expressions.fst:2103
    Effort: 3-5 hours
    Status: ADMITTED
    Proof: Structural induction on expression forms *)
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
    Location: Expressions.fst:2111
    Effort: 3-5 hours
    Status: ADMITTED
    Proof: Structural induction with careful variable tracking *)
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
    Location: Eval.fst:2249
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
    Location: ModuleSystem.fst:4357
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
    Location: TaintEffects.fst:926
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
    Location: Primitives.fst:1306
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
    Location: Effects.fst (implicit)
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
    Location: Expressions.fst:2276
    Effort: 4-6 hours
    Status: ADMITTED
    Proof: Alpha equivalence preservation through normalization *)
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
    Location: Eval.fst:2188
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
    Location: Primitives.fst:426
    Effort: 4-6 hours
    Status: ADMITTED
    Proof: Complex case analysis on division edge cases *)
val div_checked_correct : unit ->
  Lemma (ensures True)
  (* Actual: y <> 0 ==> div_checked x y == Some (x / y) *)

val div_checked_correct_priority : unit -> Tot priority
val div_checked_correct_status : unit -> Tot theorem_status
val div_checked_correct_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-4.4: Int Division Result Spec
   ---------------------------------------------------------------------------- *)
(** ID: T-4.4
    Statement: Integer division result specification
    Category: Primitives
    Location: Primitives.fst:467
    Effort: 4-6 hours
    Status: ADMITTED
    Proof: Complex case analysis (same infrastructure as T-4.3) *)
val int_div_result_spec : unit ->
  Lemma (ensures True)
  (* Actual: y <> 0 /\ not (x == min_int /\ y == -1) ==> in_range w (v x / v y) *)

val int_div_result_spec_priority : unit -> Tot priority
val int_div_result_spec_status : unit -> Tot theorem_status
val int_div_result_spec_category : unit -> Tot theorem_category


(* ----------------------------------------------------------------------------
   T-4.5: Module Dependencies Acyclic
   ---------------------------------------------------------------------------- *)
(** ID: T-4.5
    Statement: Module dependency graph is acyclic
    Category: Modules
    Location: ModuleSystem.fst:4290
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
    Location: MultipartySession.fst
    Effort: 4-8 hours
    Status: ADMITTED
    Literature: Honda 2008 + Tirore 2025 (Coq template)
    CAVEAT: Original Honda 2008 proofs had flaws (Scalas & Yoshida 2019).
            Use corrected formulation with association relation (Yoshida & Hou 2024).
    Proof: Constructive - projection algorithm terminates *)
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
    Location: MultipartySession.fst
    Effort: 4-8 hours
    Status: ADMITTED
    Literature: Honda 2008 + Tirore 2025, corrected by Yoshida & Hou 2024
    NOTE: Corrected proof uses association relation with subtyping.
    Proof: Simulation relation via association (Theorems 1, 2 in Yoshida & Hou 2024) *)
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
    Location: SessionTypes.fst (theorem statement)
    Effort: 8-16 hours
    Status: ADMITTED
    Literature: Honda 2008 Theorem 5.12 + Tirore 2025 (Coq mechanization)
    IMPORTANT: Original proofs had flaws (Scalas & Yoshida 2019).
               Use bottom-up (Scalas 2019) or top-down (Yoshida & Hou 2024).
    Proof: Port from Tirore 2025's 16K lines of Coq *)
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
    Location: SessionTypes.fst (theorem statement)
    Effort: 8-16 hours
    Status: ADMITTED
    Literature: Honda 2008 Corollary 5.6 + Tirore 2025
               Scalas & Yoshida 2019 Theorem 5.4 (corrected)
    NOTE: Process CHOOSES which typing context reduction to follow (due to subtyping).
    Proof: Port from Tirore 2025 *)
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
    Location: InformationFlow.fst (theorem statement)
    Effort: 40-80 hours
    Status: ADMITTED
    Literature: Volpano 1996 *)
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
    Location: Contracts.fst (theorem statement)
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
    Location: TypeChecker.fst (theorem statement)
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
    Location: TypeChecker.fst
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
    Literature: Boehm-Adve 2008 Theorem 7.1, Promising 2.0 (30K Coq) *)
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
    Location: SeparationLogic.fst (theorem statement)
    Effort: 8-16 hours
    Status: ADMITTED
    Literature: Reynolds 2002, Iris (Coq mechanized) *)
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
    Location: SeparationLogic.fst (theorem statement)
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
