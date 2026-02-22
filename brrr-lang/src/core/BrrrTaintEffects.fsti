(**
 * BrrrLang.Core.TaintEffects Interface
 *
 * Effect-based taint propagation for Brrr-Lang IR.
 * Connects the algebraic effect system with security/taint tracking.
 *
 * ============================================================================
 * THEORETICAL FOUNDATIONS
 * ============================================================================
 *
 * This module implements taint analysis as an EFFECT PHENOMENON rather than
 * a separate type annotation system. This approach unifies security analysis
 * with the broader effect system, following insights from:
 *
 *   - Livshits & Lam (2005): "Finding Security Vulnerabilities in Java
 *     Applications with Static Analysis" - pioneering static taint analysis
 *
 *   - Arzt et al. (2014): "FlowDroid: Precise Context, Flow, Field,
 *     Object-sensitive and Lifecycle-aware Taint Analysis for Android Apps"
 *     - interprocedural taint analysis with context sensitivity
 *
 *   - Plotkin & Power (2003): "Algebraic Operations and Generic Effects"
 *     - algebraic effect foundations
 *
 * ============================================================================
 * KEY INSIGHT: TAINT AS EFFECT
 * ============================================================================
 *
 * Traditional taint analysis treats taint as a TYPE ANNOTATION:
 *
 *     x : String^{tainted}    (* taint attached to type *)
 *
 * We instead express taint through the EFFECT SYSTEM:
 *
 *     read_user_input : Unit -> <EInput IOUserInput> String
 *
 * The effect <EInput IOUserInput> INTRODUCES taint. This has several benefits:
 *
 *   1. UNIFIED TRACKING: Taint propagation follows effect composition rules.
 *   2. HANDLER-BASED SANITIZATION: Effect handlers can remove taint effects.
 *   3. ROW POLYMORPHISM: Unknown effects enable sound approximation.
 *   4. EFFECT INFERENCE: Standard effect inference gives taint inference.
 *
 * Depends on: Effects, SecurityTypes, BrrrTypes
 *)
module BrrrTaintEffects

open FStar.List.Tot
open BrrrEffects
open BrrrSecurityTypes
open BrrrTypes

(** ============================================================================
    TAINT EFFECT PARAMETERS
    ============================================================================

    Classification of effect operations by their security role.

    TepSource(taints):   Effect INTRODUCES the specified taints
    TepSink(taints):     Effect REQUIRES ABSENCE of specified taints
    TepSanitize(taints): Effect REMOVES the specified taints
    TepPropagate(label): Effect CARRIES taint through without modification
    ============================================================================ *)

(** Taint effect parameters classify effect operations by security role *)
noeq type taint_eff_param =
  | TepSource    : taint_set -> taint_eff_param
  | TepSink      : taint_set -> taint_eff_param
  | TepSanitize  : taint_set -> taint_eff_param
  | TepPropagate : sec_label -> taint_eff_param

(** ============================================================================
    EFFECT-TO-TAINT MAPPING
    ============================================================================ *)

(**
 * Get taint implications of an effect operation.
 *
 * Returns Some(TepSource ts) if the effect introduces taints ts.
 * Returns Some(TepSink ts) if the effect requires absence of taints ts.
 * Returns None if the effect has no direct taint implications.
 *)
val effect_op_taint : op:effect_op -> option taint_eff_param

(** ============================================================================
    TAINTED EFFECT ROWS
    ============================================================================

    Pairs effect rows with taint information on input/output for precise
    tracking of how taint flows through computations.
    ============================================================================ *)

(**
 * A tainted effect row pairs effects with taint on input/output.
 *
 * Fields:
 *   effects   - The algebraic effect row
 *   taint_in  - Security label on values flowing INTO the computation
 *   taint_out - Security label on values flowing OUT of the computation
 *
 * INVARIANT: taint_out >= join(taint_in, source_taints(effects))
 *)
noeq type tainted_row = {
  effects : effect_row;
  taint_in : sec_label;
  taint_out : sec_label;
}

(** Pure computation has no effects and is untainted *)
val tainted_pure : tainted_row

(**
 * Join two tainted rows for sequential composition.
 *
 * The output taint is: join(r1.taint_out, join(r2.taint_out, r2.taint_in))
 * This ensures taint from r2's input effects is not lost.
 *)
val tainted_row_seq : r1:tainted_row -> r2:tainted_row -> tainted_row

(** Parallel composition of tainted rows *)
val tainted_row_par : r1:tainted_row -> r2:tainted_row -> tainted_row

(** ============================================================================
    TAINT FLOW THROUGH EFFECTS
    ============================================================================ *)

(** All common taint kinds - used for conservative approximation of RowVar *)
val all_common_taints : taint_set

(**
 * Collect all source taints from an effect row.
 *
 * SOUNDNESS: RowVar represents unknown effects that could potentially
 * introduce ANY taint. Returns all common taint kinds for row variables.
 *)
val collect_source_taints : row:effect_row -> taint_set

(**
 * Collect all sink requirements from an effect row.
 *
 * Returns empty set for RowVar (conservative for sinks).
 * Use collect_sink_requirements_complete for strict analysis.
 *)
val collect_sink_requirements : row:effect_row -> taint_set

(**
 * Complete sink requirements collection - for strict analysis mode.
 *
 * Returns ALL common taints for RowVar, ensuring no tainted data
 * can flow to unknown sinks.
 *)
val collect_sink_requirements_complete : row:effect_row -> taint_set

(** Compute output taint given input taint and effect row *)
val compute_output_taint : input_taint:sec_label -> row:effect_row -> sec_label

(** Check if effect row is safe given input taint *)
val check_effect_row_safe : input_taint:sec_label -> row:effect_row -> bool

(** ============================================================================
    SANITIZING EFFECT HANDLERS
    ============================================================================ *)

(**
 * Sanitizing handler specification.
 *
 * A sanitizing handler both handles effects AND removes taints.
 *
 * Fields:
 *   sh_handled - Effect row being handled (these effects are removed)
 *   sh_removes - Taint kinds being sanitized (these taints are removed)
 *)
noeq type sanitizing_handler = {
  sh_handled : effect_row;
  sh_removes : taint_set;
}

(**
 * Remove all effects from handled_row from target_row.
 *)
val remove_effects_from_row : handled_row:effect_row -> target_row:effect_row -> effect_row

(**
 * Apply sanitizing handler to a tainted row.
 *)
val apply_sanitizing_handler : h:sanitizing_handler -> r:tainted_row -> tainted_row

(** ============================================================================
    SECURITY-TYPED EFFECT SIGNATURES
    ============================================================================ *)

(** Security-annotated operation signature *)
noeq type sec_op_sig = {
  sos_name    : string;
  sos_arg     : sec_type;
  sos_ret     : sec_type;
  sos_role    : sec_role;
}

(** Security-annotated effect signature *)
noeq type sec_effect_sig = {
  ses_name       : string;
  ses_operations : list sec_op_sig;
}

(** ============================================================================
    COMMON SECURITY EFFECT PATTERNS
    ============================================================================ *)

(** User input effect: source of all common taints *)
val eff_user_input : effect_row

(** Network input effect: source of network-related taints *)
val eff_network_input : effect_row

(** Database output effect: sink that rejects SQL injection *)
val eff_database_output : db:string -> effect_row

(** File write effect: sink that rejects path traversal *)
val eff_file_write : path:string -> effect_row

(** Shell execution effect (unsafe): sink that rejects command injection *)
val eff_shell_exec : effect_row

(** ============================================================================
    TAINT PROPAGATION RULES
    ============================================================================ *)

(** Propagation rule result *)
noeq type propagation_result =
  | PropOk    : sec_label -> propagation_result
  | PropError : string -> propagation_result

(** Apply propagation for an effect operation *)
val propagate_through_effect : input_taint:sec_label -> op:effect_op -> propagation_result

(**
 * Propagate through an entire effect row.
 *
 * SOUNDNESS: For row variables, conservatively adds all common taints.
 *)
val propagate_through_row : input_taint:sec_label -> row:effect_row
    -> Tot propagation_result (decreases row)

(** ============================================================================
    FUNCTION TAINT ANALYSIS
    ============================================================================ *)

(** Helper: for_all2 - check predicate holds for all pairs *)
val for_all2 : #a:Type -> #b:Type -> f:(a -> b -> bool) -> xs:list a -> ys:list b -> bool

(** Compute the taint flow for a function call *)
val analyze_call_taint :
    func_summary:func_taint_summary ->
    arg_taints:list sec_label ->
    option sec_label

(** ============================================================================
    TAINT SUMMARY COMPUTATION
    ============================================================================ *)

(** Compute initial taint summary from function type *)
val compute_taint_summary :
    func_id:nat ->
    sf:sec_func_type ->
    func_taint_summary

(** Update taint summary based on effect analysis *)
val refine_taint_summary :
    summary:func_taint_summary ->
    effects:effect_row ->
    func_taint_summary

(** ============================================================================
    TAINT VIOLATION DETECTION
    ============================================================================ *)

(** Violation record *)
noeq type taint_violation = {
  tv_effect    : effect_op;
  tv_taints    : taint_set;
  tv_message   : string;
}

(**
 * Check for violations in an effect row.
 *
 * For row variables representing unknown effects, no violations are
 * reported (no false positives from unknown sinks).
 *)
val detect_violations :
    input_taint:sec_label ->
    row:effect_row ->
    Tot (list taint_violation) (decreases row)

(**
 * Strict violation detection - warns about row variables.
 *
 * Reports a potential violation when row variables are encountered
 * with tainted input.
 *)
val detect_violations_strict :
    input_taint:sec_label ->
    row:effect_row ->
    Tot (list taint_violation) (decreases row)

(** ============================================================================
    AUXILIARY LEMMAS FOR SOUNDNESS PROOFS
    ============================================================================ *)

(**
 * The left operand of taint_set_union is a subset of the result.
 *)
val taint_set_union_subset_left : ts1:taint_set -> ts2:taint_set ->
  Lemma (ensures taint_set_subset ts1 (taint_set_union ts1 ts2) = true)
        (decreases ts1)

(**
 * propagate_through_effect preserves input taint (output >= input).
 *)
val propagate_through_effect_preserves_input :
  input_taint:sec_label ->
  op:effect_op ->
  Lemma (requires PropOk? (propagate_through_effect input_taint op))
        (ensures (let PropOk out = propagate_through_effect input_taint op in
                  sec_label_leq input_taint out = true))

(**
 * Taint kind membership is preserved through sec_label_join.
 *)
val taint_in_join_left : k:taint_kind -> l1:sec_label -> l2:sec_label ->
  Lemma (requires taint_in_set k l1.taints = true)
        (ensures taint_in_set k (sec_label_join l1 l2).taints = true)

(**
 * Taint kind is preserved through propagate_through_effect.
 *)
val propagate_through_effect_preserves_taint :
  k:taint_kind ->
  input_taint:sec_label ->
  op:effect_op ->
  Lemma (requires PropOk? (propagate_through_effect input_taint op) /\
                  taint_in_set k input_taint.taints = true)
        (ensures (let PropOk out = propagate_through_effect input_taint op in
                  taint_in_set k out.taints = true))

(**
 * Helper: if a filter produces at least one element, list is non-empty.
 *)
val filter_produces_element_nonempty :
  k:taint_kind ->
  required_absent:taint_set ->
  input_taints:taint_set ->
  Lemma (requires taint_in_set k required_absent = true /\
                  taint_in_set k input_taints = true)
        (ensures List.Tot.length
                   (List.Tot.filter (fun k' -> taint_in_set k' input_taints) required_absent) > 0)
        (decreases required_absent)

(** ============================================================================
    SOUNDNESS LEMMAS
    ============================================================================ *)

(**
 * Soundness: If an effect op has a source taint, that taint is collected.
 *)
val collect_source_taints_sound :
  row:effect_row ->
  op:effect_op ->
  Lemma (requires has_effect op row /\
                  Some? (effect_op_taint op) /\
                  TepSource? (Some?.v (effect_op_taint op)))
        (ensures taint_set_subset
                   (TepSource?._0 (Some?.v (effect_op_taint op)))
                   (collect_source_taints row))

(**
 * Soundness: Row variables conservatively add all common taints.
 *)
val rowvar_conservative :
  v:string ->
  Lemma (ensures collect_source_taints (RowVar v) == all_common_taints)

(**
 * Soundness: Propagation through row adds source taints to output.
 *)
val propagate_through_row_sound :
  input_taint:sec_label ->
  row:effect_row ->
  Lemma (requires PropOk? (propagate_through_row input_taint row))
        (ensures (let PropOk out = propagate_through_row input_taint row in
                  sec_label_leq input_taint out))

(**
 * Completeness for strict mode: If tainted data reaches a sink, it's detected.
 *)
val detect_violations_strict_complete :
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
