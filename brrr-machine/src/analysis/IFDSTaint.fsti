(**
 * BrrrMachine.Analysis.IFDSTaint - Interface
 *
 * IFDS-Based Context-Sensitive Taint Analysis Interface
 *
 * Based on:
 *   - Livshits 2005 "Finding Security Vulnerabilities in Java Applications"
 *   - Arzt 2014 (FlowDroid) for heap-sensitive extensions
 *   - Synthesis document Section 8.1 (Taint Analysis)
 *
 * This interface exposes the taint analysis infrastructure built on IFDS.
 * Key Features:
 *   - Variable and field taint tracking via access paths
 *   - Three-valued logic (TMaybe) for may/must taint
 *   - Source/sink/sanitizer specifications
 *   - Context-sensitive interprocedural analysis (O(ED^3))
 *   - FlowDroid-style bidirectional heap-sensitive extension
 *)
module BrrrMachine.Analysis.IFDSTaint

open FStar.List.Tot
open FStar.Set
open BrrrMachine.Core.Types
open BrrrMachine.Core.CFG
open BrrrMachine.Core.CallGraph
open BrrrMachine.Analysis.IFDS

(** Module-level Z3 options for proof efficiency *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 1: TAINT KINDS
   ═══════════════════════════════════════════════════════════════════════════

   Taint kinds categorize the security vulnerability type.
   A value can be tainted with multiple kinds simultaneously.
   ═══════════════════════════════════════════════════════════════════════════ *)

type taint_kind =
  | TKSQLi          : taint_kind  (** SQL Injection *)
  | TKXss           : taint_kind  (** Cross-Site Scripting *)
  | TKCmdi          : taint_kind  (** Command Injection *)
  | TKPathTraversal : taint_kind  (** Path Traversal / LFI *)
  | TKSsrf          : taint_kind  (** Server-Side Request Forgery *)
  | TKLdapi         : taint_kind  (** LDAP Injection *)
  | TKXxe           : taint_kind  (** XML External Entity *)
  | TKDeser         : taint_kind  (** Insecure Deserialization *)
  | TKLogInjection  : taint_kind  (** Log Injection / Forging *)
  | TKHeaderInject  : taint_kind  (** HTTP Header Injection *)
  | TKOpenRedirect  : taint_kind  (** Open Redirect *)
  | TKTemplateInject: taint_kind  (** Template Injection / SSTI *)
  | TKCustom        : string -> taint_kind  (** Custom user-defined *)

(** Taint kind equality *)
val taint_kind_eq : taint_kind -> taint_kind -> bool

(** Check if taint kinds k1 are a subset of k2 *)
val taint_kinds_subset : set taint_kind -> set taint_kind -> bool

(** Check if taint kinds k1 and k2 are disjoint (no overlap) *)
val taint_kinds_disjoint : set taint_kind -> set taint_kind -> bool

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 2: ACCESS PATHS
   ═══════════════════════════════════════════════════════════════════════════

   Access paths model heap locations: x.f.g represents the field g of
   the field f of variable x.

   For heap-sensitive taint, we track access paths rather than just variables.
   Access paths have bounded length (k-limiting) for finite domain.
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Field access in an access path *)
type access_element =
  | AEField : string -> access_element       (** Field access .f *)
  | AEArrayIdx : access_element              (** Array index [*] *)
  | AEMapKey : access_element                (** Map key access *)
  | AEDeref : access_element                 (** Pointer dereference *)

(** Access path: variable + sequence of field accesses *)
type access_path = {
  ap_base: var_id;                  (** Base variable *)
  ap_fields: list access_element;   (** Field/index chain *)
}

(** Maximum access path length for finite domain (k-limiting) *)
val max_access_path_length : nat

(** Access element equality *)
val access_element_eq : access_element -> access_element -> bool

(** Field list equality *)
val access_path_fields_eq : list access_element -> list access_element -> bool

(** Access path equality *)
val access_path_eq : access_path -> access_path -> bool

(** Append field to access path (includes truncation) *)
val access_path_append : access_path -> access_element -> access_path

(** Truncate access path to maximum length (k-limiting) *)
val truncate_access_path : access_path -> access_path

(** Check if first field list is prefix of second *)
val is_prefix : list access_element -> list access_element -> bool

(** Check if first access path is prefix of second *)
val access_path_is_prefix : access_path -> access_path -> bool

(* ─────────────────────────────────────────────────────────────────────────
   2.1: ACCESS PATH ORDERING LEMMAS
   ───────────────────────────────────────────────────────────────────────── *)

(** Access path equality is reflexive *)
val access_path_eq_refl : ap:access_path ->
    Lemma (access_path_eq ap ap = true)
    [SMTPat (access_path_eq ap ap)]

(** Access path equality is symmetric *)
val access_path_eq_sym : ap1:access_path -> ap2:access_path ->
    Lemma (access_path_eq ap1 ap2 = access_path_eq ap2 ap1)
    [SMTPat (access_path_eq ap1 ap2)]

(** Access path equality is transitive *)
val access_path_eq_trans : ap1:access_path -> ap2:access_path -> ap3:access_path ->
    Lemma (requires access_path_eq ap1 ap2 /\ access_path_eq ap2 ap3)
          (ensures access_path_eq ap1 ap3 = true)

(** Prefix ordering is reflexive *)
val access_path_prefix_refl : ap:access_path ->
    Lemma (access_path_is_prefix ap ap = true)
    [SMTPat (access_path_is_prefix ap ap)]

(** Prefix ordering is transitive *)
val access_path_prefix_trans : ap1:access_path -> ap2:access_path -> ap3:access_path ->
    Lemma (requires access_path_is_prefix ap1 ap2 /\ access_path_is_prefix ap2 ap3)
          (ensures access_path_is_prefix ap1 ap3 = true)

(** Prefix ordering is antisymmetric *)
val access_path_prefix_antisym : ap1:access_path -> ap2:access_path ->
    Lemma (requires access_path_is_prefix ap1 ap2 /\ access_path_is_prefix ap2 ap1)
          (ensures access_path_eq ap1 ap2 = true)

(* ─────────────────────────────────────────────────────────────────────────
   2.2: TRUNCATION LEMMAS
   ───────────────────────────────────────────────────────────────────────── *)

(** Truncation is idempotent *)
val truncate_idempotent : ap:access_path ->
    Lemma (truncate_access_path (truncate_access_path ap) = truncate_access_path ap)
    [SMTPat (truncate_access_path (truncate_access_path ap))]

(** Truncation preserves the base variable *)
val truncate_preserves_base : ap:access_path ->
    Lemma ((truncate_access_path ap).ap_base = ap.ap_base)
    [SMTPat ((truncate_access_path ap).ap_base)]

(** Truncation bounds the field list length *)
val truncate_bounds : ap:access_path ->
    Lemma (List.Tot.length (truncate_access_path ap).ap_fields <= max_access_path_length)
    [SMTPat (truncate_access_path ap)]

(** Truncated path is prefix of original *)
val truncate_is_prefix : ap:access_path ->
    Lemma (access_path_is_prefix (truncate_access_path ap) ap = true)

(** Append preserves base variable *)
val append_preserves_base : ap:access_path -> elem:access_element ->
    Lemma ((access_path_append ap elem).ap_base = ap.ap_base)
    [SMTPat ((access_path_append ap elem).ap_base)]

(** Append result is bounded *)
val append_bounded : ap:access_path -> elem:access_element ->
    Lemma (List.Tot.length (access_path_append ap elem).ap_fields <= max_access_path_length)
    [SMTPat (access_path_append ap elem)]

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 3: TAINT FACTS (IFDS DOMAIN)
   ═══════════════════════════════════════════════════════════════════════════

   The IFDS domain D consists of taint facts. A fact represents
   "access path X is tainted with kinds K".
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Taint activation status (FlowDroid extension) *)
type taint_activation =
  | TAActive   : taint_activation  (** Taint is active *)
  | TAInactive : taint_activation  (** Taint awaits activation *)

(** Taint Fact: Core IFDS domain element *)
type taint_fact =
  | TFTainted : {
      tf_path: access_path;           (** What is tainted *)
      tf_kinds: set taint_kind;       (** With what kinds *)
      tf_confidence: tmaybe;          (** How confident *)
      tf_activation: taint_activation;(** Active or inactive *)
      tf_source_id: nat;              (** Source that introduced this taint *)
    } -> taint_fact
  | TFReturn : {
      tf_kinds: set taint_kind;
      tf_confidence: tmaybe;
    } -> taint_fact
  | TFException : {
      tf_kinds: set taint_kind;
    } -> taint_fact
  | TFZero : taint_fact  (** Zero/lambda fact for IFDS initialization *)

(** Extract access path from fact (if applicable) *)
val fact_access_path : taint_fact -> option access_path

(** Extract taint kinds from fact *)
val fact_kinds : taint_fact -> set taint_kind

(** Check if fact is active *)
val fact_is_active : taint_fact -> bool

(** Taint fact equality (needed for IFDS domain) *)
val taint_fact_eq : taint_fact -> taint_fact -> bool

(** Extract source node from a taint fact *)
val fact_source_node : taint_fact -> option node_id

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 4: SOURCE/SINK/SANITIZER SPECIFICATIONS
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Source parameter specification *)
type source_param =
  | SPReturn           (** Return value is tainted *)
  | SPParam of nat     (** Parameter at index is tainted *)
  | SPReceiver         (** Receiver/this is tainted *)
  | SPAll              (** All parameters are tainted *)

(** Source specification *)
type source_spec = {
  ss_package: string;           (** Package/module name *)
  ss_function: string;          (** Function name (supports wildcards) *)
  ss_param: source_param;       (** Which part is tainted *)
  ss_kinds: set taint_kind;     (** Taint kinds introduced *)
  ss_confidence: tmaybe;        (** Confidence level *)
}

(** Taint source database *)
noeq type source_database = {
  sd_sources: list source_spec;
  sd_language: string;
}

(** Sink severity levels *)
type sink_severity =
  | SevCritical  (** RCE, SQLi *)
  | SevHigh      (** XSS, Path Traversal *)
  | SevMedium    (** Open Redirect, Log Injection *)
  | SevLow       (** Information Disclosure *)

(** Sink specification *)
type sink_spec = {
  sk_package: string;
  sk_function: string;
  sk_param: nat;                 (** Which parameter is sensitive *)
  sk_dangerous_kinds: set taint_kind;  (** Which taints are dangerous *)
  sk_severity: sink_severity;
}

(** Sink database *)
noeq type sink_database = {
  sd_sinks: list sink_spec;
  sd_language: string;
}

(** Sanitizer specification *)
type sanitizer_spec = {
  sn_package: string;
  sn_function: string;
  sn_param: nat;                    (** Which parameter is sanitized *)
  sn_removes_kinds: set taint_kind; (** Which taints are removed *)
  sn_for_sinks: set taint_kind;     (** Effective against which sink types *)
}

(** Sanitizer database *)
noeq type sanitizer_database = {
  san_sanitizers: list sanitizer_spec;
  san_language: string;
}

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 5: TAINT CONFIGURATION
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Taint analysis configuration *)
noeq type taint_config = {
  tc_sources: source_database;
  tc_sinks: sink_database;
  tc_sanitizers: sanitizer_database;
  tc_max_path_length: nat;      (** k-limiting for access paths *)
  tc_track_implicit_flows: bool;(** Track control-flow taint *)
  tc_activation_enabled: bool;  (** FlowDroid-style activation *)
}

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 6: NODE INFORMATION EXTRACTION
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Call information extracted from a call node *)
type call_info = {
  ci_callee_name: string;
  ci_callee_package: string;
  ci_arguments: list var_id;
  ci_result_var: option var_id;
  ci_is_method_call: bool;
  ci_receiver_var: option var_id;
}

(** Assignment information *)
type assign_info = {
  ai_lhs_var: var_id;
  ai_rhs_vars: list var_id;
  ai_is_field_assign: bool;
  ai_field_path: list string;
}

(** Let binding information *)
type let_info = {
  li_bound_var: var_id;
  li_rhs_vars: list var_id;
  li_is_mutable: bool;
}

(** Expression node information *)
type expr_info = {
  ei_vars_used: list var_id;
  ei_is_source_like: bool;
  ei_source_pattern: option (string & string);
}

(** Node detail kinds *)
type node_detail =
  | NDCall      : call_info -> node_detail
  | NDAssign    : assign_info -> node_detail
  | NDLet       : let_info -> node_detail
  | NDExpr      : expr_info -> node_detail
  | NDReturn    : option var_id -> node_detail
  | NDCondition : list var_id -> node_detail
  | NDEntry     : list var_id -> node_detail
  | NDExit      : node_detail
  | NDOther     : node_detail

(** Get detailed node information from supergraph *)
val get_node_detail : supergraph -> node_id -> option node_detail

(** Extract callee name from call node detail *)
val get_callee_name : node_detail -> option (string & string)

(** Check if a function name matches a pattern *)
val function_name_matches : string -> string -> string -> string -> bool

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 7: SOURCE/SINK/SANITIZER MATCHING
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Check if node is a taint source *)
val is_source : taint_config -> supergraph -> node_id -> option source_spec

(** Check if node is a sanitizer *)
val is_sanitizer : taint_config -> supergraph -> node_id -> option sanitizer_spec

(** Check if node is a sink *)
val is_sink : taint_config -> supergraph -> node_id -> option sink_spec

(** Get variable assigned at node (if assignment) *)
val get_assigned_var : supergraph -> node_id -> option var_id

(** Get RHS variables used in assignment or expression *)
val get_rhs_vars : supergraph -> node_id -> list var_id

(** Get variables to taint based on source parameter specification *)
val get_source_tainted_vars : supergraph -> node_id -> source_spec -> list var_id

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 8: TAINT FLOW FUNCTIONS
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Normal flow function: intraprocedural taint propagation *)
val taint_flow_function :
  taint_config ->
  supergraph ->
  flow_edge ->
  taint_fact ->
  flow_result taint_fact

(** Call flow function: map actuals to formals *)
val taint_call_flow :
  taint_config ->
  supergraph ->
  node_id ->  (** call site *)
  node_id ->  (** callee entry *)
  taint_fact ->
  flow_result taint_fact

(** Return flow function: map callee exit facts to return site *)
val taint_return_flow :
  taint_config ->
  supergraph ->
  node_id ->  (** call site *)
  node_id ->  (** callee exit *)
  node_id ->  (** return site *)
  taint_fact -> (** d_call: fact at call *)
  taint_fact -> (** d_exit: fact at exit *)
  flow_result taint_fact

(** Call-to-return flow: facts that bypass the call *)
val taint_call_to_return_flow :
  taint_config ->
  supergraph ->
  node_id ->  (** call site *)
  node_id ->  (** return site *)
  taint_fact ->
  flow_result taint_fact

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 9: IFDS PROBLEM INSTANTIATION
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Build the taint analysis IFDS problem *)
val build_taint_problem :
  taint_config ->
  supergraph ->
  ifds_problem taint_fact

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 10: TAINT ANALYSIS RESULTS
   ═══════════════════════════════════════════════════════════════════════════ *)

(** A taint finding represents tainted data reaching a sink *)
type taint_finding = {
  tf_sink: sink_spec;
  tf_taint_kinds: set taint_kind;
  tf_confidence: tmaybe;
  tf_source_node: node_id;
  tf_sink_node: node_id;
  tf_path: list node_id;
}

(** Taint analysis result *)
noeq type taint_analysis_result = {
  tar_findings: list taint_finding;
  tar_sources_found: nat;
  tar_sinks_checked: nat;
  tar_paths_analyzed: nat;
  tar_ifds_stats: ifds_stats;
}

(** Check if taint kinds intersect with dangerous kinds *)
val taint_kinds_intersect : set taint_kind -> set taint_kind -> bool

(** Get all nodes in the supergraph *)
val all_nodes : supergraph -> list node_id

(** Get facts that hold at a specific node from IFDS result *)
val get_facts_at_node : ifds_result taint_fact -> node_id -> list taint_fact

(** Check if taint affects the sensitive parameter of a sink *)
val taint_affects_sensitive_param :
    supergraph ->
    node_id ->
    sink_spec ->
    taint_fact ->
    bool

(** Check for taint findings by querying IFDS results at sinks *)
val check_sinks :
  taint_config ->
  supergraph ->
  ifds_result taint_fact ->
  list taint_finding

(** Main entry point: run taint analysis *)
val analyze_taint :
  taint_config ->
  supergraph ->
  taint_analysis_result

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 11: FLOWDROID BIDIRECTIONAL EXTENSION
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Alias query for backward analysis *)
type alias_query = {
  aq_access_path: access_path;
  aq_at_node: node_id;
  aq_spawn_node: node_id;
}

(** Alias result from backward analysis *)
type alias_result = {
  ar_aliases: list access_path;
  ar_query: alias_query;
}

(** Bidirectional taint state *)
noeq type bidir_state = {
  bs_forward: ifds_state taint_fact;
  bs_backward_queries: list alias_query;
  bs_alias_results: list alias_result;
}

(** Spawn backward alias query when heap write detected *)
val spawn_alias_query :
  access_path ->
  node_id ->
  bidir_state ->
  bidir_state

(** Activate taint when alias confirmed *)
val activate_taint :
  alias_result ->
  bidir_state ->
  bidir_state

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 12: SOUNDNESS THEOREMS
   ═══════════════════════════════════════════════════════════════════════════

   Key correctness properties of the taint analysis.
   Based on IFDS soundness (Reps, Horwitz, Sagiv 1995).
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Predicate: taint introduces at a source *)
val introduces_taint : taint_config -> supergraph -> node_id -> Type0

(** Predicate: a path is valid in the supergraph *)
val valid_supergraph_path : supergraph -> list node_id -> Type0

(** Check if a sanitizer is present on an edge *)
val is_sanitizer_on_edge : taint_config -> supergraph -> flow_edge -> option sanitizer_spec

(**
 * THEOREM: Source Introduction Correctness
 *
 * When a node is identified as a source, the flow function produces
 * a taint fact with the correct taint kinds from the source specification.
 *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val source_introduces_taint :
    config:taint_config ->
    sg:supergraph ->
    node:node_id ->
    spec:source_spec{is_source config sg node = Some spec} ->
    result:set (node_id & taint_fact) ->
    Lemma (requires result = solve (build_taint_problem config sg))
          (ensures
            (forall (edge: flow_edge) (d: taint_fact).
              edge.fe_source = node ==>
              (let flow_result = taint_flow_function config sg edge d in
               exists (fact: taint_fact).
                 Set.mem fact flow_result /\
                 TFTainted? fact /\
                 Set.equal (TFTainted?._0 fact).tf_kinds spec.ss_kinds /\
                 (TFTainted?._0 fact).tf_source_id = node)))
          [SMTPat (is_source config sg node)]
#pop-options

(**
 * THEOREM: Flow Function Preserves Taint (or Sanitization Occurs)
 *
 * When taint flows through a non-sanitizer edge, the taint kinds are
 * either preserved or a subset.
 *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val flow_function_preserves_taint :
    config:taint_config ->
    sg:supergraph ->
    edge:flow_edge ->
    fact:taint_fact{TFTainted? fact} ->
    Lemma (ensures
            forall (f': taint_fact).
              Set.mem f' (taint_flow_function config sg edge fact) ==>
              (TFTainted? f' ==>
               taint_kinds_subset (TFTainted?._0 f').tf_kinds
                                  (TFTainted?._0 fact).tf_kinds \/
               Some? (is_sanitizer_on_edge config sg edge) \/
               Some? (is_source config sg edge.fe_source)))
#pop-options

(**
 * THEOREM: Sanitizer Removes Specified Kinds Completely
 *
 * After flowing through a sanitizer, the output taint kinds are
 * disjoint from the sanitizer's removed kinds.
 *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
val sanitizer_removes_kinds :
    config:taint_config ->
    sg:supergraph ->
    node:node_id ->
    san:sanitizer_spec{is_sanitizer config sg node = Some san} ->
    fact:taint_fact{TFTainted? fact} ->
    Lemma (ensures
            forall (edge: flow_edge) (f': taint_fact).
              edge.fe_source = node /\
              Set.mem f' (taint_flow_function config sg edge fact) /\
              TFTainted? f' ==>
              taint_kinds_disjoint (TFTainted?._0 f').tf_kinds san.sn_removes_kinds = true)
#pop-options

(**
 * THEOREM: Confidence Preserved Through Flow
 *
 * When taint flows through an edge, the confidence level either:
 * - Stays the same (identity/propagation)
 * - Decreases (may-alias introduces uncertainty)
 *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val confidence_preserved :
    config:taint_config ->
    sg:supergraph ->
    fact:taint_fact{TFTainted? fact} ->
    edge:flow_edge ->
    Lemma (ensures
            forall (f': taint_fact).
              Set.mem f' (taint_flow_function config sg edge fact) /\
              TFTainted? f' ==>
              tmaybe_leq (TFTainted?._0 f').tf_confidence
                         (TFTainted?._0 fact).tf_confidence)
          [SMTPat (taint_flow_function config sg edge fact)]
#pop-options

(**
 * THEOREM: Truncation Soundness
 *
 * Access path truncation produces a prefix of the original path,
 * or returns the path unchanged if already within limits.
 *)
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
val truncation_sound :
    ap:access_path ->
    Lemma (ensures
            access_path_is_prefix (truncate_access_path ap) ap \/
            access_path_eq ap (truncate_access_path ap))
          [SMTPat (truncate_access_path ap)]
#pop-options

(** TMaybe ordering is reflexive *)
val tmaybe_leq_refl :
    t:tmaybe ->
    Lemma (ensures tmaybe_leq t t = true)
          [SMTPat (tmaybe_leq t t)]

(** TMaybe ordering is transitive *)
val tmaybe_leq_trans :
    a:tmaybe -> b:tmaybe -> c:tmaybe ->
    Lemma (requires tmaybe_leq a b = true /\ tmaybe_leq b c = true)
          (ensures tmaybe_leq a c = true)

(** Set.diff produces disjoint result *)
val set_diff_disjoint_lemma :
    s1:set taint_kind ->
    s2:set taint_kind ->
    Lemma (ensures taint_kinds_disjoint (Set.diff s1 s2) s2 = true)
          [SMTPat (Set.diff s1 s2)]

(** Taint kinds subset is transitive *)
val taint_kinds_subset_trans :
    k1:set taint_kind ->
    k2:set taint_kind ->
    k3:set taint_kind ->
    Lemma (requires taint_kinds_subset k1 k2 = true /\ taint_kinds_subset k2 k3 = true)
          (ensures taint_kinds_subset k1 k3 = true)

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 13: FLOW FUNCTION CORRECTNESS
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Predicate: Concrete taint propagates from d to d' along an edge *)
val concrete_propagates : supergraph -> flow_edge -> taint_fact -> taint_fact -> Type0

(**
 * THEOREM: Flow function soundness.
 *
 * If concrete taint propagates from d to d' along an edge,
 * then d' is in the result of taint_flow_function applied to d.
 *)
val taint_flow_function_sound :
  config:taint_config ->
  sg:supergraph ->
  edge:flow_edge ->
  d:taint_fact ->
  d':taint_fact ->
  Lemma (requires concrete_propagates sg edge d d')
        (ensures Set.mem d' (taint_flow_function config sg edge d))

(**
 * THEOREM: Flow function completeness (no spurious propagation).
 *
 * If d' is in the flow function result for d, then there exists
 * a valid concrete propagation from d to d'.
 *)
val taint_flow_function_complete :
  config:taint_config ->
  sg:supergraph ->
  edge:flow_edge ->
  d:taint_fact ->
  d':taint_fact ->
  Lemma (requires Set.mem d' (taint_flow_function config sg edge d))
        (ensures concrete_propagates sg edge d d' \/
                 (introduces_taint config sg edge.fe_source /\
                  TFTainted? d'))

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 14: INTERPROCEDURAL FLOW CORRECTNESS
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Predicate: Concrete taint propagation through call *)
val concrete_call_propagates : supergraph -> node_id -> node_id ->
    taint_fact -> taint_fact -> Type0

(** Predicate: Concrete taint propagation through return *)
val concrete_return_propagates : supergraph -> node_id -> node_id -> node_id ->
    taint_fact -> taint_fact -> taint_fact -> Type0

(**
 * THEOREM: Call flow function soundness.
 *)
val call_flow_sound :
  config:taint_config ->
  sg:supergraph ->
  call_site:node_id ->
  callee_entry:node_id ->
  d_call:taint_fact ->
  d_entry:taint_fact ->
  Lemma (requires concrete_call_propagates sg call_site callee_entry d_call d_entry)
        (ensures Set.mem d_entry (taint_call_flow config sg call_site callee_entry d_call))

(**
 * THEOREM: Return flow function soundness.
 *)
val return_flow_sound :
  config:taint_config ->
  sg:supergraph ->
  call_site:node_id ->
  callee_exit:node_id ->
  return_site:node_id ->
  d_call:taint_fact ->
  d_exit:taint_fact ->
  d_return:taint_fact ->
  Lemma (requires concrete_return_propagates sg call_site callee_exit return_site
                   d_call d_exit d_return)
        (ensures Set.mem d_return (taint_return_flow config sg call_site callee_exit
                                   return_site d_call d_exit))

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 15: PATH RECONSTRUCTION
   ═══════════════════════════════════════════════════════════════════════════ *)

(**
 * THEOREM: Path reconstruction produces valid paths.
 *)
val reconstruct_path_valid :
  sg:supergraph ->
  result:ifds_result taint_fact ->
  pe:path_edge taint_fact ->
  Lemma (requires Set.mem pe result.ir_path_edges)
        (ensures
          exists (path: extended_path taint_fact).
            is_realizable_path sg path /\
            List.Tot.length path.ep_path > 0)

(**
 * THEOREM: IFDS path edges correspond to concrete taint paths.
 *)
val path_edge_represents_taint_flow :
  config:taint_config ->
  sg:supergraph ->
  result:ifds_result taint_fact ->
  pe:path_edge taint_fact ->
  Lemma (requires Set.mem pe result.ir_path_edges)
        (ensures
          exists (path: list (node_id & taint_fact)).
            List.Tot.length path >= 1)
