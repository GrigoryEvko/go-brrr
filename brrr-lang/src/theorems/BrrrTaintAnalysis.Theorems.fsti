(**
 * BrrrTaintAnalysis.Theorems - Interface
 *
 * Public interface for taint analysis soundness and completeness theorems.
 * This module formally verifies the security properties of Brrr-Lang's
 * taint tracking system, establishing that:
 *
 *   (1) SOUNDNESS: No tainted data escapes detection (no false negatives)
 *   (2) COMPLETENESS: All actual violations are reported (in strict mode)
 *   (3) MONOTONICITY: Taints accumulate and never silently disappear
 *
 * THEOREM IDENTIFIERS (from AXIOMS_REPORT_v2.md):
 *   T-1.1: taint_set_union_subset_left - Basic set theory for taint union
 *   T-1.2: filter_produces_element_nonempty - List filter produces nonempty result
 *   T-2.8: collect_source_taints_sound - Source taint collection is sound
 *   T-2.9: propagate_through_row_sound - Taint propagation through effect rows is sound
 *   T-3.5: detect_violations_strict_complete - Strict violation detection is complete
 *
 * LITERATURE REFERENCES:
 *
 *   [Arzt 2014] Arzt, Rasthofer, Fritz, Bodden, Bartel, Klein, Le Traon,
 *     Octeau, McDaniel. "FlowDroid: Precise Context, Flow, Field, Object-
 *     sensitive and Lifecycle-aware Taint Analysis for Android Apps."
 *     PLDI 2014. DOI: 10.1145/2594291.2594299
 *     - FlowDroid achieves high precision through context-sensitivity
 *     - Key insight: lifecycle-awareness crucial for Android taint analysis
 *     - Brrr-Lang adapts their source/sink/sanitizer taxonomy
 *
 *   [Livshits 2005] Livshits, Lam. "Finding Security Vulnerabilities in Java
 *     Applications with Static Analysis." USENIX Security 2005.
 *     - Foundational work on static taint analysis for security
 *     - Introduced PQL (Program Query Language) for vulnerability patterns
 *     - Our taint_kind enumeration follows their vulnerability taxonomy
 *
 *   [Tripp 2009] Tripp, Pistoia, Fink, Sridharan, Weisman. "TAJ: Effective
 *     Taint Analysis of Web Applications." PLDI 2009.
 *     - Addresses soundness/completeness tradeoffs in taint analysis
 *     - Key: "thin slicing" for improved precision without soundness loss
 *
 *   [Denning 1976] Denning. "A Lattice Model of Secure Information Flow."
 *     CACM 19(5), 1976.
 *     - Theoretical foundation for information flow as lattice
 *     - Monotonicity property (T-2.9) directly derived from lattice semantics
 *
 * SOUNDNESS VS COMPLETENESS TRADEOFFS:
 *
 *   In static analysis, soundness and completeness are often in tension:
 *
 *   - SOUND analysis: Reports ALL actual vulnerabilities (no false negatives)
 *     Cost: May report false positives (phantom vulnerabilities)
 *     Property: If analysis says "safe", code is definitely safe
 *
 *   - COMPLETE analysis: Reports ONLY actual vulnerabilities (no false positives)
 *     Cost: May miss real vulnerabilities (false negatives)
 *     Property: If analysis says "vulnerable", code is definitely vulnerable
 *
 *   BRRR-LANG APPROACH:
 *   Our taint analysis is SOUND by design (T-2.8, T-2.9), meaning:
 *     - All source-introduced taints are tracked (no taint escapes)
 *     - Taints propagate conservatively (accumulate, never vanish)
 *     - Row variables (unknown effects) are treated as potentially dangerous
 *
 *   STRICT MODE (T-3.5) is COMPLETE for detected violations:
 *     - If tainted data reaches a rejecting sink, we WILL report it
 *     - No real violations slip through undetected
 *
 *   The combination gives us: Sound tracking + Complete detection = No false negatives
 *   Tradeoff: We may over-approximate taints (false positives) but never under-approximate
 *
 *   This matches FlowDroid's design philosophy: "It is better to err on the side
 *   of caution in security analysis" [Arzt 2014, Section 5.2]
 *
 * SPECIFICATION REFERENCES (brrr_lang_spec_v0.4.tex):
 *   - Section "Taint Analysis" (Ch. 28): Defines taint_kind, taint_status
 *   - Taint-Op rule: Taints join through binary operations (t1 | t2)
 *   - Taint-Call rule: Function calls propagate taints from arguments to result
 *   - Taint-Sink rule: Tainted data at sink generates ERROR
 *   - Sanitizer: Removes specific taint kind after validation
 *
 * Depends on: TaintEffects, SecurityTypes, Effects
 *)
module BrrrTaintAnalysis.Theorems

open FStar.List.Tot
open BrrrPrimitives
open BrrrModes
open BrrrTypes
open BrrrEffects
open BrrrSecurityTypes
open BrrrTaintEffects

(** ============================================================================
    THEOREM T-1.1: TAINT SET UNION SUBSET LEFT
    ============================================================================

    FORMAL STATEMENT:
      forall ts1 ts2. taint_set_subset ts1 (taint_set_union ts1 ts2) = true

    SPECIFICATION REFERENCE (brrr_lang_spec_v0.4.tex, Taint Analysis):
      The Taint-Op rule states: e1 | e2 : tau^{t1 | t2}
      This requires that t1 is contained in the joined taint (t1 | t2).

    PROOF TECHNIQUE:
      Structural induction on ts1 (list taint_kind).
      Base case: [] is trivially a subset of any set.
      Inductive case: For (k :: rest), show k is in union (by reflexivity),
        then apply IH to show rest is also a subset.

    SECURITY IMPLICATION:
      When multiple data sources are combined (e.g., string concatenation),
      taints from ALL sources are preserved in the result. This is fundamental
      to SOUNDNESS: no taint information is lost through data combination.

    LITERATURE:
      This is a standard set-theoretic property, used implicitly in all
      taint analysis papers. FlowDroid [Arzt 2014] represents taints as
      access paths which also satisfy this union-subset property.

    COMPLEXITY: O(|ts1| * |ts1 union ts2|) due to list-based set representation
    ============================================================================ *)

(**
 * T-1.1: The left operand of taint_set_union is a subset of the result.
 *
 * This foundational lemma ensures that joining taint sets never loses
 * information from either operand. It is critical for proving that
 * taint propagation is monotonic (taints only accumulate).
 *)
val theorem_t1_1_taint_set_union_subset_left :
  ts1:taint_set ->
  ts2:taint_set ->
  Lemma (ensures taint_set_subset ts1 (taint_set_union ts1 ts2) = true)
        (decreases ts1)

(** ============================================================================
    THEOREM T-1.2: FILTER PRODUCES ELEMENT NONEMPTY
    ============================================================================

    FORMAL STATEMENT:
      forall k required_absent input_taints.
        taint_in_set k required_absent = true /\
        taint_in_set k input_taints = true
        ==>
        length (filter (fun k' -> taint_in_set k' input_taints) required_absent) > 0

    INTUITION:
      If we have a witness element k that is:
        (a) in the "forbidden" set (required_absent), AND
        (b) in the actual input taints
      Then filtering the forbidden set by "is present in input" produces
      a non-empty result (at least k itself).

    SPECIFICATION REFERENCE (brrr_lang_spec_v0.4.tex, Taint-Sink rule):
      The Taint-Sink rule states that when tainted data reaches a sink
      that rejects that taint kind, an ERROR is generated. This theorem
      ensures we can DETECT such errors: if a violating taint exists,
      our filter-based detection finds at least one.

    PROOF TECHNIQUE:
      Structural induction on required_absent, tracking witness k.
      When we reach position where taint_kind_eq k hd = true, the filter
      keeps that element (since k is in input_taints implies hd is too,
      by the equivalence relation property of taint_kind_eq).

    SECURITY IMPLICATION:
      COMPLETENESS of violation detection. If a true violation exists
      (tainted data at a rejecting sink), we WILL find it. Combined with
      T-2.8 and T-2.9 (soundness), this gives us: NO FALSE NEGATIVES.

    LITERATURE:
      Tripp et al. [TAJ 2009] discuss the importance of complete violation
      detection: "Missing even one vulnerability can be catastrophic."
      FlowDroid [Arzt 2014] also guarantees completeness for detected sources.

    SMT LIMITATION NOTE:
      This proof requires reasoning about higher-order functions (filter
      with lambda predicates). F*'s SMT encoding has incomplete support
      for such patterns, requiring explicit induction rather than SMT-only.
      See SPECIFICATION_ERRATA.md Chapter 14 for details.
    ============================================================================ *)

(**
 * T-1.2: If an element satisfies the filter predicate and is in the list,
 * the filtered result is non-empty.
 *
 * Applied to taint analysis: When checking if input taints violate sink
 * requirements, we filter required_absent by membership in input_taints.
 * If some taint k is both required-absent AND present, the filter finds it.
 *
 * This is the key lemma for COMPLETENESS: all actual violations are detected.
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

(** ============================================================================
    THEOREM T-2.8: COLLECT SOURCE TAINTS SOUND
    ============================================================================

    FORMAL STATEMENT:
      forall row op.
        has_effect op row /\
        effect_op_taint op = Some (TepSource ts)
        ==>
        taint_set_subset ts (collect_source_taints row)

    INTUITION:
      If an effect operation in an effect row is a taint SOURCE that
      introduces certain taints, those taints appear in the result of
      collect_source_taints. The analysis captures ALL taints that
      could be introduced by effects in the row.

    SPECIFICATION REFERENCE (brrr_lang_spec_v0.4.tex, Taint Sources):
      "A source introduces tainted data: source_kind : () -> tau^{Tainted[kind]}"
      Examples: user input (TkUserInput), network data (TkNetwork), files (TkFileSystem)

      collect_source_taints aggregates all such source taints from an effect row,
      ensuring none are missed.

    PROOF TECHNIQUE:
      Structural induction on effect_row.
      - RowEmpty/RowVar/RowVarUnify: Precondition has_effect op row is false,
        so these cases are vacuously true.
      - RowExt e rest: Either op is at head (use T-1.1 for union subset),
        or op is in rest (use IH + helper lemma for subset preservation).

    SECURITY IMPLICATION:
      SOUNDNESS of source identification. If a function can introduce taint
      (e.g., reading user input), that taint IS tracked. No source-introduced
      taint escapes our analysis.

    LITERATURE:
      FlowDroid [Arzt 2014] Section 3.1 discusses source specifications:
      "Sources are defined as calls to specific API methods that return
      sensitive data." Our effect-based approach generalizes this to any
      effect that introduces taint.

      Livshits & Lam [2005] introduced the source/sink/derivation framework
      that we adapt here. Their "source descriptors" map to our TepSource.

    CONSERVATIVE APPROXIMATION:
      For row variables (unknown effects), we conservatively return
      all_common_taints, which may OVER-approximate. This maintains
      soundness at the cost of potential false positives.
    ============================================================================ *)

(**
 * T-2.8: Source taint collection is sound - all source taints are captured.
 *
 * When analyzing an effect row for source taints:
 * - Concrete source effects (RowExt) contribute their declared taints
 * - Row variables (RowVar) conservatively return all common taints
 *
 * SOUNDNESS: No source-introduced taint escapes detection.
 * COST: May have false positives from conservative row variable handling.
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

(** ============================================================================
    THEOREM T-2.9: PROPAGATE THROUGH ROW SOUND
    ============================================================================

    FORMAL STATEMENT:
      forall input_taint row.
        PropOk? (propagate_through_row input_taint row)
        ==>
        sec_label_leq input_taint (PropOk?.v (propagate_through_row input_taint row))

    INTUITION:
      Taint propagation is MONOTONIC: output taint is always at least as
      large as input taint. Taints accumulate through computation, they
      never silently disappear (except through explicit sanitization).

    SPECIFICATION REFERENCE (brrr_lang_spec_v0.4.tex, Taint Propagation):
      The Taint-Op rule: e1 | e2 : tau^{t1 | t2}
      The Taint-Call rule: f(e1,...,en) : sigma^{Tainted} if any ei is tainted

      Both rules show that taints JOIN (|), never MEET (&). The output
      is at least as tainted as any input.

    PROOF TECHNIQUE:
      Structural induction on effect_row.
      - RowEmpty: Returns input unchanged, use reflexivity of sec_label_leq.
      - RowVar: Returns join(input, all_common_taints), use join_upper_l.
      - RowExt e rest: Propagate through e, then recurse on rest.
        Use transitivity: input <= taint' <= output.

    SECURITY IMPLICATION:
      SOUNDNESS of taint tracking. Once data is tainted, it remains tainted
      through all computations. This is the MONOTONICITY property from
      Denning's lattice model [Denning 1976]: information can only flow
      "upward" in the security lattice.

    LITERATURE:
      [Denning 1976] formalized information flow as a lattice where:
        - Security labels form a partial order
        - Information flows from low to high (monotonically)
        - No "downward" flow is possible without explicit declassification

      FlowDroid [Arzt 2014] implements this as "taint propagation rules"
      (Section 3.2): "If a tainted value is used in a computation, the
      result is also tainted."

      Our sec_label_leq is the lattice ordering, and this theorem proves
      that propagate_through_row respects it.

    RELATION TO T-2.8:
      T-2.8 (source soundness) + T-2.9 (propagation soundness) together
      ensure end-to-end soundness: taints are correctly introduced at
      sources AND correctly propagated through all subsequent operations.
    ============================================================================ *)

(**
 * T-2.9: Taint propagation through effect rows is monotonic (sound).
 *
 * The monotonicity property ensures:
 * - Source effects ADD taints (output >= input)
 * - Sink effects CHECK but don't remove taints
 * - Row variables CONSERVATIVELY add all common taints
 * - Pure effects PRESERVE input unchanged
 *
 * SOUNDNESS: Tainted data cannot silently become untainted.
 *)
val theorem_t2_9_propagate_through_row_sound :
  input_taint:sec_label ->
  row:effect_row ->
  Lemma (requires PropOk? (propagate_through_row input_taint row))
        (ensures (let PropOk out = propagate_through_row input_taint row in
                  sec_label_leq input_taint out))
        (decreases row)

(** ============================================================================
    THEOREM T-3.5: DETECT VIOLATIONS STRICT COMPLETE
    ============================================================================

    FORMAL STATEMENT:
      forall input_taint row op k.
        has_effect op row /\                                     (* op is in row *)
        effect_op_taint op = Some (TepSink required_absent) /\   (* op is a sink *)
        taint_in_set k required_absent /\                        (* k must be absent *)
        taint_in_set k input_taint.taints                        (* but k is present! *)
        ==>
        length (detect_violations_strict input_taint row) > 0    (* violation detected *)

    INTUITION:
      If there is a REAL security violation (tainted data k reaching a sink
      that requires k to be absent), strict mode WILL detect and report it.
      No actual vulnerability slips through.

    SPECIFICATION REFERENCE (brrr_lang_spec_v0.4.tex, Taint-Sink rule):
      "Taint-Sink: If e : tau^{Tainted[kind]} and sink[kind], then ERROR"

      The error is generated when tainted data flows to a sink that
      should reject that taint kind. This theorem proves we DETECT all
      such errors, not just that they're erroneous.

    PROOF TECHNIQUE:
      Complex structural induction on effect_row, using T-1.2 as key lemma.

      - RowEmpty: Unreachable (has_effect is false)
      - RowVar: Strict mode reports violation when input is tainted
        (taint_in_set_implies_nonempty gives length > 0)
      - RowExt e rest:
        * If e = op (the sink): Use T-1.2 to show filter finds k
        * If e != op: Propagate taint through e, preserve k in taints
          (propagate_through_effect_preserves_taint), then apply IH

    SECURITY IMPLICATION:
      COMPLETENESS of violation detection in strict mode.

      Combined with T-2.8 (sound source tracking) and T-2.9 (sound propagation):
        - Taints are correctly introduced (T-2.8)
        - Taints correctly propagate (T-2.9)
        - Violations are all detected (T-3.5)
        => NO FALSE NEGATIVES: Every actual vulnerability is reported

    LITERATURE:
      FlowDroid [Arzt 2014] Section 5.2: "FlowDroid is designed to be
      sound, reporting all potential data flows... We also strive for
      precision to minimize false positives."

      Our strict mode prioritizes COMPLETENESS (no false negatives) over
      PRECISION (minimal false positives). This is the appropriate choice
      for security analysis where missing a vulnerability is worse than
      a false alarm.

      TAJ [Tripp 2009]: "In security analysis, false negatives (missed
      vulnerabilities) are unacceptable. False positives are merely
      inconvenient."

    STRICT VS PERMISSIVE MODE:
      - STRICT (this theorem): Complete. Reports ALL violations.
        May have false positives from row variable handling.
      - PERMISSIVE: Allows known effects to pass, only checks unknown.
        Fewer false positives, but may miss violations in known code.

      Choose based on your security requirements:
      - High security: Use strict mode, accept more false positives
      - Rapid development: Use permissive mode, accept risk of misses

    DEPENDENCY ON T-1.2:
      The proof relies critically on theorem_t1_2_filter_produces_element_nonempty.
      When we know k is in required_absent AND k is in input_taints, T-1.2
      guarantees the filter-based detection produces a non-empty result.
    ============================================================================ *)

(**
 * T-3.5: Strict violation detection is complete - all violations are found.
 *
 * In strict mode (detect_violations_strict):
 * - Known sink effects report violations when input contains rejected taints
 * - Row variables (unknown effects) report warnings when input is tainted
 * - Taint correctly propagates through intermediate effects
 *
 * COMPLETENESS: If a real violation exists, strict mode WILL report it.
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

(** ============================================================================
    AUXILIARY LEMMAS
    ============================================================================

    These lemmas support the main theorems by establishing properties about
    taint membership through various operations. They are critical for the
    inductive proofs of T-2.9 and T-3.5.

    DESIGN NOTE:
    The auxiliary lemmas are separated from the main theorems to:
    (1) Enable reuse across multiple proofs
    (2) Keep the main theorem proofs focused on high-level structure
    (3) Allow independent verification of foundational properties
    ============================================================================ *)

(**
 * AUX-1: Taint kind membership is preserved through sec_label_join.
 *
 * If taint k is in label l1, then k is in (sec_label_join l1 l2).
 * This follows from T-1.1 applied to the taint sets within sec_labels.
 *
 * USE IN T-2.9: When proving propagation soundness, we need to show
 * that joining labels (e.g., at source effects) preserves existing taints.
 *
 * USE IN T-3.5: When proving completeness, we need to show that the
 * witness taint k is preserved through intermediate propagation steps.
 *)
val aux_taint_in_join_left :
  k:taint_kind ->
  l1:sec_label ->
  l2:sec_label ->
  Lemma (requires taint_in_set k l1.taints = true)
        (ensures taint_in_set k (sec_label_join l1 l2).taints = true)

(**
 * AUX-2: Taint is preserved through single effect propagation.
 *
 * If propagation through effect op succeeds (PropOk) and k was in input,
 * then k is in output. This is the single-step version of T-2.9's
 * monotonicity property.
 *
 * PROOF BY CASE ANALYSIS on effect_op_taint op:
 * - None: Returns input unchanged, k trivially preserved
 * - TepSource: Returns join(input, new_taints), k preserved by AUX-1
 * - TepSink: Either error (excluded by PropOk) or returns input
 * - TepPropagate: Returns join(input, label), k preserved by AUX-1
 *
 * CRITICAL FOR T-3.5: This lemma allows the inductive case to "push"
 * the witness taint k through intermediate effects on the way to the sink.
 *)
val aux_propagate_effect_preserves_taint :
  k:taint_kind ->
  input:sec_label ->
  op:effect_op ->
  Lemma (requires PropOk? (propagate_through_effect input op) /\
                  taint_in_set k input.taints = true)
        (ensures (let PropOk out = propagate_through_effect input op in
                  taint_in_set k out.taints = true))
