(**
 * TaintAnalysis.Theorems
 *
 * Formal theorems for taint analysis soundness and completeness.
 * These theorems establish the security guarantees of the taint tracking system.
 *
 * THEOREM IDENTIFIERS (from AXIOMS_REPORT_v2.md):
 *   T-1.1: taint_set_union_subset_left - Basic set theory for taint union
 *   T-1.2: filter_produces_element_nonempty - List filter produces nonempty result
 *   T-2.8: collect_source_taints_sound - Source taint collection is sound
 *   T-2.9: propagate_through_row_sound - Taint propagation through effect rows is sound
 *   T-3.5: detect_violations_strict_complete - Strict violation detection is complete
 *
 * LITERATURE REFERENCES:
 *   - Livshits & Lam 2005: "Finding Security Vulnerabilities in Java Applications
 *     with Static Analysis" - foundational taint analysis
 *   - Tripp et al. 2009: "TAJ: Effective Taint Analysis of Web Applications" -
 *     precision/soundness tradeoffs
 *   - Arzt et al. 2014: "FlowDroid: Precise Context, Flow, Field, Object-sensitive
 *     and Lifecycle-aware Taint Analysis for Android Apps"
 *
 * Depends on: TaintAnalysis, TaintEffects, SecurityTypes, Effects
 *)
module TaintAnalysis.Theorems

(* Z3 configuration for theorem proofs *)
#set-options "--z3rlimit 100 --fuel 1 --ifuel 1"

open FStar.List.Tot
open FStar.Classical

(* Import core modules - order matters for F* dependency resolution *)
open Primitives
open Modes
open BrrrTypes
open Effects
open SecurityTypes
open TaintEffects

(** ============================================================================
    THEOREM T-1.1: TAINT SET UNION SUBSET LEFT
    ============================================================================

    Statement: For any taint sets A and B, A is a subset of (A union B).
    Formula:   forall ts1 ts2. taint_set_subset ts1 (taint_set_union ts1 ts2) = true

    This is a fundamental set-theoretic property that underlies the soundness
    of taint propagation. When we join taints from multiple sources, all
    original taints are preserved.

    Effort: 30 minutes
    Priority: P1 (Low-hanging fruit)
    Proof Strategy: Structural induction on ts1 with taint_in_set lemmas

    Literature: Basic set theory; used implicitly in all taint analysis papers.

    NOTE: This theorem is also stated in TaintEffects.fst:649-656 with an admit().
    ============================================================================ *)

(**
 * T-1.1: The left operand of taint_set_union is a subset of the result.
 *
 * This theorem is mathematically trivial but requires careful handling of
 * the recursive taint_set definitions in F*. The proof proceeds by induction
 * on the first list, showing that each element in ts1 appears in the union.
 *
 * SOUNDNESS IMPLICATION: When taints flow through a computation that joins
 * multiple data sources, no taint from the original sources is lost.
 *)
val theorem_t1_1_taint_set_union_subset_left : ts1:taint_set -> ts2:taint_set ->
  Lemma (ensures taint_set_subset ts1 (taint_set_union ts1 ts2) = true)
        (decreases ts1)

(* Implementation: Direct application of taint_set_union_subset_left from SecurityTypes.
 *
 * This theorem is now proven directly in SecurityTypes.fst where access to the
 * internal definitions of taint_set_subset and taint_set_union is available.
 * We simply re-export the proof here as the named theorem.
 *)
let theorem_t1_1_taint_set_union_subset_left ts1 ts2 =
  (* The proof is provided by taint_set_union_subset_left in SecurityTypes *)
  taint_set_union_subset_left ts1 ts2


(** ============================================================================
    THEOREM T-1.2: FILTER PRODUCES ELEMENT NONEMPTY
    ============================================================================

    Statement: If a predicate holds for some element in a list and that element
               is in the list, then filtering by that predicate produces a
               non-empty result.
    Formula:   f x = true /\ x `mem` l ==> length (filter f l) > 0

    This theorem is used in violation detection to show that when a taint kind
    is both in the required-absent set and in the input taints, the filter
    that finds violating taints produces at least one result.

    Effort: 1 hour
    Priority: P1 (Low-hanging fruit)
    Proof Strategy: List induction, tracking the witness element

    Literature: Standard list theory; critical for taint violation soundness.

    NOTE: This theorem is also stated in TaintEffects.fst:763-782 with an admit().
    ============================================================================ *)

(**
 * T-1.2: If an element satisfies the filter predicate and is in the list,
 *        the filtered result is non-empty.
 *
 * Applied to taint analysis: When checking if input taints violate sink
 * requirements, we filter required_absent by (fun k -> taint_in_set k input).
 * If some k is both required to be absent AND present in input, the filter
 * finds at least one violation.
 *
 * COMPLETENESS IMPLICATION: All true taint violations are detected.
 *)
val theorem_t1_2_filter_produces_element_nonempty :
  k:taint_kind ->
  required_absent:taint_set ->
  input_taints:taint_set ->
  Lemma (requires taint_in_set k required_absent = true /\
                  taint_in_set k input_taints = true)
        (ensures List.Tot.length
                   (List.Tot.filter (fun k' -> taint_in_set k' input_taints) required_absent) > 0)
        (decreases required_absent)

(* Implementation: Induction on required_absent, tracking witness k *)
let rec theorem_t1_2_filter_produces_element_nonempty k required_absent input_taints =
  (* Proof sketch:
   * Base case: required_absent = [] contradicts k `taint_in_set` required_absent
   * Inductive case: required_absent = k' :: rest
   *   Case 1: k = k' (by taint_kind_eq)
   *     - taint_in_set k input_taints = true (given)
   *     - So taint_in_set k' input_taints = true (k = k')
   *     - filter keeps k', result is non-empty
   *   Case 2: k <> k'
   *     - k must be in rest (since k in (k' :: rest) and k <> k')
   *     - By IH on rest, filter rest produces non-empty
   *     - filter (k' :: rest) includes filter rest, so still non-empty
   *
   * The key insight is that taint_kind_eq is used for membership, so we need
   * to show that the witness k (or an equivalent element) passes the filter.
   *)
  admit()  (* T-1.2: 1 hour estimated, requires taint_kind_eq congruence lemma *)


(** ============================================================================
    THEOREM T-2.8: COLLECT SOURCE TAINTS SOUND
    ============================================================================

    Statement: If an effect operation in a row is a source that introduces
               certain taints, those taints are included in collect_source_taints.
    Formula:   has_effect op row /\ effect_op_taint op = Some (TepSource ts)
               ==> taint_set_subset ts (collect_source_taints row)

    This theorem establishes that the source taint collection is SOUND:
    it captures all taints that could be introduced by effects in the row.
    The analysis may over-approximate (conservative) but never under-approximate.

    Effort: 2-3 hours
    Priority: P2 (Medium effort)
    Proof Strategy: Induction on effect_row structure

    Literature: Livshits & Lam 2005 Section 4 (Source identification);
                Arzt et al. 2014 (FlowDroid source/sink specifications)

    NOTE: This theorem is implemented in TaintEffects.fst:809-832 with partial proof.
    ============================================================================ *)

(**
 * T-2.8: Source taint collection is sound - all source taints are captured.
 *
 * The soundness property ensures that when analyzing an effect row:
 * 1. Concrete effects (RowExt) contribute their declared source taints
 * 2. Row variables (RowVar) conservatively return all_common_taints
 *
 * SOUNDNESS IMPLICATION: No source-introduced taint escapes detection.
 * May have false positives (conservative) but no false negatives.
 *)
val theorem_t2_8_collect_source_taints_sound :
  row:effect_row ->
  op:effect_op ->
  Lemma (requires has_effect op row /\
                  Some? (effect_op_taint op) /\
                  TepSource? (Some?.v (effect_op_taint op)))
        (ensures taint_set_subset
                   (TepSource?._0 (Some?.v (effect_op_taint op)))
                   (collect_source_taints row))

(* Implementation: Induction on effect_row *)
let rec theorem_t2_8_collect_source_taints_sound row op =
  (* Proof sketch:
   * Case RowEmpty:
   *   - has_effect op RowEmpty = false, contradiction
   *
   * Case RowVar v:
   *   - collect_source_taints (RowVar v) = all_common_taints
   *   - TepSource?._0 contains some subset of common taints
   *   - By definition, all_common_taints includes all standard taints
   *   - So any source taints are included (may need explicit subset proof)
   *
   * Case RowExt e rest:
   *   - If effect_op_eq e op:
   *     - op is the head effect, its taints are directly unioned
   *     - By taint_set_union_subset_left, they're in the result
   *   - Else:
   *     - op must be in rest (since has_effect op (RowExt e rest) and e <> op)
   *     - By IH, op's taints are in collect_source_taints rest
   *     - By taint_set_union properties, they're in the full result
   *
   * Key lemmas needed:
   *   - taint_set_union_subset_left (T-1.1)
   *   - has_effect transitivity through RowExt
   *)
  admit()  (* T-2.8: 2-3 hours, see TaintEffects.fst:819-832 for partial proof *)


(** ============================================================================
    THEOREM T-2.9: PROPAGATE THROUGH ROW SOUND
    ============================================================================

    Statement: Taint propagation through an effect row is sound - the output
               taint is at least as large as the input taint (taints accumulate,
               never disappear except through explicit sanitization).
    Formula:   PropOk? (propagate_through_row input row)
               ==> sec_label_leq input (PropOk?.v (propagate_through_row input row))

    This theorem establishes monotonicity of taint propagation: once data is
    tainted, it remains tainted unless explicitly sanitized. This is fundamental
    to the security guarantee of taint analysis.

    Effort: 2 hours
    Priority: P2 (Medium effort)
    Proof Strategy: Induction with sec_label_leq transitivity

    Literature: Denning 1977 (Information flow lattices - monotonicity);
                Livshits & Lam 2005 Section 5 (Taint propagation rules)

    NOTE: This theorem is implemented in TaintEffects.fst:852-878 with full proof.
    ============================================================================ *)

(**
 * T-2.9: Taint propagation through effect rows is monotonic (sound).
 *
 * The monotonicity property ensures:
 * 1. Source effects ADD taints (output >= input)
 * 2. Sink effects CHECK taints but don't remove them
 * 3. Row variables CONSERVATIVELY add all common taints
 * 4. Pure effects PRESERVE input taint unchanged
 *
 * SOUNDNESS IMPLICATION: Taint cannot silently disappear. Any tainted data
 * that reaches a sink was tainted when it entered the effect sequence.
 *)
val theorem_t2_9_propagate_through_row_sound :
  input_taint:sec_label ->
  row:effect_row ->
  Lemma (requires PropOk? (propagate_through_row input_taint row))
        (ensures (let PropOk out = propagate_through_row input_taint row in
                  sec_label_leq input_taint out))

(* Implementation: Induction on effect_row with transitivity *)
let rec theorem_t2_9_propagate_through_row_sound input_taint row =
  (* Proof sketch:
   * Case RowEmpty:
   *   - Returns PropOk input_taint
   *   - sec_label_leq input_taint input_taint by reflexivity
   *
   * Case RowVar v:
   *   - Returns PropOk (sec_label_join input_taint (sec_public_untrusted all_common_taints))
   *   - By sec_label_join_upper_l, input_taint <= join result
   *
   * Case RowExt op rest:
   *   - propagate_through_effect input_taint op = PropOk taint'
   *   - By propagate_through_effect_preserves_input: input_taint <= taint'
   *   - By IH on rest: taint' <= final_output
   *   - By sec_label_leq_trans: input_taint <= final_output
   *
   * Key lemmas needed:
   *   - propagate_through_effect_preserves_input (TaintEffects.fst:667-704)
   *   - sec_label_leq_refl, sec_label_leq_trans (SecurityTypes.fst)
   *   - sec_label_join_upper_l (SecurityTypes.fst)
   *)
  admit()  (* T-2.9: 2 hours, see TaintEffects.fst:859-878 for full proof *)


(** ============================================================================
    THEOREM T-3.5: DETECT VIOLATIONS STRICT COMPLETE
    ============================================================================

    Statement: In strict mode, if tainted data actually reaches a sink that
               rejects that taint, a violation is detected.
    Formula:   has_effect op row /\ effect_op_taint op = Some (TepSink reqs) /\
               taint_in_set k reqs /\ taint_in_set k input.taints
               ==> length (detect_violations_strict input row) > 0

    This theorem establishes COMPLETENESS of strict violation detection:
    all real violations are found. Combined with soundness of propagation,
    this gives the security guarantee that no unsafe data flow escapes detection.

    Effort: 3-4 hours
    Priority: P3 (Substantial effort)
    Proof Strategy: Complex induction with T-1.2

    Literature: Livshits & Lam 2005 Section 6 (Sink checking);
                Tripp et al. 2009 (Precision vs completeness tradeoffs)

    NOTE: This theorem is implemented in TaintEffects.fst:886-926 with full proof.
    ============================================================================ *)

(**
 * T-3.5: Strict violation detection is complete - all violations are found.
 *
 * In strict mode (detect_violations_strict):
 * 1. Known sink effects report violations when input is tainted with rejected kinds
 * 2. Row variables (unknown effects) report warnings when input is tainted
 * 3. Taint propagates correctly through intermediate effects
 *
 * COMPLETENESS IMPLICATION: If a real security violation exists (tainted data
 * reaches a sink that should reject it), strict mode WILL report it.
 *)
val theorem_t3_5_detect_violations_strict_complete :
  input_taint:sec_label ->
  row:effect_row ->
  op:effect_op ->
  k:taint_kind ->
  Lemma (requires has_effect op row /\
                  Some? (effect_op_taint op) /\
                  TepSink? (Some?.v (effect_op_taint op)) /\
                  taint_in_set k (TepSink?._0 (Some?.v (effect_op_taint op))) /\
                  taint_in_set k input_taint.taints)
        (ensures List.Tot.length (detect_violations_strict input_taint row) > 0)

(* Implementation: Complex induction with taint preservation *)
let rec theorem_t3_5_detect_violations_strict_complete input_taint row op k =
  (* Proof sketch:
   * Case RowEmpty:
   *   - has_effect op RowEmpty = false, contradiction
   *
   * Case RowVar v:
   *   - If input_taint.taints is non-empty (it is, since k is in it),
   *     strict mode reports a violation for the unknown effect
   *
   * Case RowExt e rest:
   *   - If effect_op_eq e op:
   *     - op is the head effect with sink requirement
   *     - k is in required_absent AND k is in input_taint.taints
   *     - By filter_produces_element_nonempty (T-1.2), filter produces >= 1 element
   *     - Violation is reported
   *   - Else:
   *     - op is in rest
   *     - Propagate taint through e: input_taint -> taint'
   *     - By propagate_through_effect_preserves_taint: k is still in taint'.taints
   *     - By IH on rest with taint': violations detected
   *
   * Key lemmas needed:
   *   - filter_produces_element_nonempty (T-1.2)
   *   - propagate_through_effect_preserves_taint (TaintEffects.fst:729-758)
   *   - has_effect decomposition
   *)
  admit()  (* T-3.5: 3-4 hours, see TaintEffects.fst:898-926 for full proof *)


(** ============================================================================
    AUXILIARY LEMMAS
    ============================================================================

    Helper lemmas that support the main theorems. These are either proven
    elsewhere or require additional infrastructure.
    ============================================================================ *)

(**
 * AUX-1: Taint kind membership is preserved through sec_label_join.
 *
 * Used by T-2.9 and T-3.5 to show that joining labels doesn't lose taints.
 * Proof: sec_label_join unions the taint sets, and union preserves membership.
 *)
val aux_taint_in_join_left : k:taint_kind -> l1:sec_label -> l2:sec_label ->
  Lemma (requires taint_in_set k l1.taints = true)
        (ensures taint_in_set k (sec_label_join l1 l2).taints = true)

let aux_taint_in_join_left k l1 l2 =
  (* sec_label_join l1 l2 has taints = taint_set_union l1.taints l2.taints *)
  (* By taint_set_union_includes_left, k is preserved *)
  taint_set_union_includes_left k l1.taints l2.taints

(**
 * AUX-2: Taint is preserved through single effect propagation.
 *
 * If propagation succeeds and k is in input, k is in output (for non-sanitize effects).
 * This is critical for T-3.5 completeness.
 *
 * NOTE: This lemma is implemented in TaintEffects.fst:729-758
 *)
val aux_propagate_effect_preserves_taint :
  k:taint_kind ->
  input:sec_label ->
  op:effect_op ->
  Lemma (requires PropOk? (propagate_through_effect input op) /\
                  taint_in_set k input.taints = true)
        (ensures (let PropOk out = propagate_through_effect input op in
                  taint_in_set k out.taints = true))

let aux_propagate_effect_preserves_taint k input op =
  (* Case analysis on effect_op_taint op *)
  (* None: returns input unchanged - k preserved *)
  (* TepSource: returns join(input, new) - k preserved by aux_taint_in_join_left *)
  (* TepSink: either error or returns input - k preserved *)
  (* TepPropagate: returns join(input, l) - k preserved by aux_taint_in_join_left *)
  admit()  (* See TaintEffects.fst:739-758 for implementation *)


(** ============================================================================
    THEOREM SUMMARY
    ============================================================================

    This module establishes the core security guarantees of taint analysis:

    SOUNDNESS (No False Negatives for Violations):
    - T-2.8: All source taints are collected
    - T-2.9: Taint propagation is monotonic (taints accumulate)
    - T-3.5: All violations are detected in strict mode

    SUPPORTING LEMMAS:
    - T-1.1: Set union preserves subsets (for taint accumulation)
    - T-1.2: Filter produces results when witness exists (for violation detection)

    PROOF STATUS:
    - All theorems have admit() placeholders in this file
    - Proof sketches provided for guidance
    - Some implementations exist in TaintEffects.fst
    - Estimated total effort: 8-12 hours for complete proofs

    DEPENDENCIES:
    - SecurityTypes.fst: sec_label_leq_trans, taint_set_subset_trans
    - TaintEffects.fst: collect_source_taints, propagate_through_row, detect_violations_strict
    - Effects.fst: has_effect, effect_op_eq

    SECURITY IMPLICATIONS:
    When these theorems are fully proven, the taint analysis provides:
    1. SOUND tracking: No taint escapes detection
    2. COMPLETE detection: All violations are found (in strict mode)
    3. MONOTONIC propagation: Once tainted, always tainted (unless sanitized)

    These properties together ensure that:
    - User input is properly tracked from sources
    - Tainted data is detected before reaching dangerous sinks
    - Security-sensitive operations reject tainted data
    ============================================================================ *)
