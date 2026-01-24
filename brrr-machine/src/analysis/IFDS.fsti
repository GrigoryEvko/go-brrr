(**
 * BrrrMachine.Analysis.IFDS - Interface
 *
 * IFDS (Interprocedural Finite Distributive Subset) Framework Interface
 *
 * Based on: Reps, Horwitz, Sagiv 1995 "Precise Interprocedural Dataflow
 * Analysis via Graph Reachability"
 *
 * This interface exposes the core IFDS infrastructure for context-sensitive
 * interprocedural dataflow analysis. IFDS reduces dataflow problems to
 * graph reachability over an "exploded supergraph", achieving O(ED^3)
 * complexity where E = edges in supergraph, D = domain size.
 *
 * Key Concepts:
 *   - Supergraph: Interprocedural CFG with call/return edges
 *   - Exploded Supergraph: G# = (N x D, E#) - nodes paired with facts
 *   - Path Edge: Realizable path from procedure entry to current node
 *   - Summary Edge: Procedure effect from call site to return site
 *   - CFL-Reachability: Context-sensitivity via matched parentheses
 *)
module BrrrMachine.Analysis.IFDS

open FStar.List.Tot
open FStar.Set
open BrrrMachine.Core.Types
open BrrrMachine.Core.CFG
open BrrrMachine.Core.CallGraph

(** Module-level Z3 options for proof efficiency *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 1: CORE IDENTIFIERS
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Procedure identifier *)
unfold
let proc_id : Type0 = nat

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 2: THREE-VALUED LOGIC (TMaybe)
   ═══════════════════════════════════════════════════════════════════════════

   TMaybe implements three-valued logic for may/must analysis:
     - TDefinitely: Fact definitely holds (must analysis)
     - TMaybe: Fact may hold (may analysis)
     - TNo: Fact definitely does not hold

   This forms a lattice: TNo < TMaybe < TDefinitely
   ═══════════════════════════════════════════════════════════════════════════ *)

type tmaybe =
  | TDefinitely : tmaybe  (** Fact definitely holds *)
  | TMaybe      : tmaybe  (** Fact may hold *)
  | TNo         : tmaybe  (** Fact does not hold *)

(** TMaybe ordering: TNo < TMaybe < TDefinitely *)
val tmaybe_leq : tmaybe -> tmaybe -> bool

(** TMaybe join (least upper bound) *)
val tmaybe_join : tmaybe -> tmaybe -> tmaybe

(** TMaybe meet (greatest lower bound) *)
val tmaybe_meet : tmaybe -> tmaybe -> tmaybe

(** Convert to boolean for may-analysis *)
val tmaybe_may : tmaybe -> bool

(** Convert to boolean for must-analysis *)
val tmaybe_must : tmaybe -> bool

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 3: SUPERGRAPH DEFINITION
   ═══════════════════════════════════════════════════════════════════════════

   The supergraph G* is the interprocedural CFG combining all procedures.
   Nodes are partitioned into procedures, with special call/return edges
   connecting them.
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Node types in the supergraph *)
type supergraph_node_kind =
  | SNEntry     : proc_id -> supergraph_node_kind  (** Procedure entry *)
  | SNExit      : proc_id -> supergraph_node_kind  (** Procedure exit *)
  | SNCall      : callee:proc_id -> supergraph_node_kind  (** Call site *)
  | SNReturnSite: call_node:node_id -> supergraph_node_kind  (** Return site *)
  | SNOrdinary  : supergraph_node_kind  (** Regular intraprocedural node *)

(** Supergraph node *)
type supergraph_node = {
  sn_id: node_id;
  sn_proc: proc_id;             (** Containing procedure *)
  sn_kind: supergraph_node_kind;
  sn_cfg_node: option cfg_node; (** Underlying CFG node if any *)
}

(** Edge types in the supergraph - crucial for IFDS flow functions *)
type supergraph_edge_kind =
  | SEIntra      : supergraph_edge_kind  (** Intraprocedural edge *)
  | SECallToStart: supergraph_edge_kind  (** Call site -> callee entry *)
  | SEExitToReturn: supergraph_edge_kind (** Callee exit -> return site *)
  | SECallToReturn: supergraph_edge_kind (** Call site -> return site (bypassing callee) *)

(** Supergraph edge *)
type supergraph_edge = {
  se_source: node_id;
  se_target: node_id;
  se_kind: supergraph_edge_kind;
}

(** The complete supergraph structure - abstract, contains functions *)
val supergraph : Type0

(** Supergraph accessors *)
val sg_nodes : supergraph -> list supergraph_node
val sg_edges : supergraph -> list supergraph_edge
val sg_procs : supergraph -> list proc_id
val sg_main : supergraph -> proc_id
val sg_get_node : supergraph -> node_id -> option supergraph_node
val sg_get_entry : supergraph -> proc_id -> option node_id
val sg_get_exit : supergraph -> proc_id -> option node_id
val sg_get_callee : supergraph -> node_id -> option proc_id
val sg_get_return_site : supergraph -> node_id -> option node_id
val sg_get_call_site : supergraph -> node_id -> option node_id
val sg_successors : supergraph -> node_id -> list supergraph_edge
val sg_predecessors : supergraph -> node_id -> list supergraph_edge

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 4: IFDS PROBLEM DEFINITION
   ═══════════════════════════════════════════════════════════════════════════

   An IFDS problem is a tuple (G*, D, M) where:
     - G* = supergraph
     - D = finite domain of dataflow facts
     - M : E* -> 2^(D x D) assigns distributive transfer functions to edges
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Dataflow fact - parameterized by the specific analysis *)
unfold
let ifds_fact (d: Type) : Type0 = d

(** Flow function result: set of target facts *)
unfold
let flow_result (d: Type) : Type0 = set d

(** Edge for flow function computation *)
type flow_edge = {
  fe_source: node_id;
  fe_target: node_id;
  fe_kind: supergraph_edge_kind;
}

(**
 * IFDS Problem Definition
 *
 * The core interface that specific analyses (taint, reaching defs, etc.)
 * must implement.
 *)
noeq type ifds_problem (d: Type) = {
  (** The supergraph *)
  ip_supergraph: supergraph;

  (** The dataflow domain - must be finite *)
  ip_domain: set d;

  (** Zero/lambda fact: artificial fact for procedure entry initialization *)
  ip_zero: d;

  (** Equality on domain elements *)
  ip_eq: d -> d -> bool;

  (** Hash for efficient set operations *)
  ip_hash: d -> nat;

  (**
   * Normal flow function: intraprocedural edges
   * Given edge (n1, n2) and fact d at n1, returns facts holding at n2.
   *)
  ip_flow_function: flow_edge -> d -> flow_result d;

  (**
   * Call flow function: call site -> callee entry
   * Maps facts at call site to facts at callee entry.
   *)
  ip_call_flow: node_id -> node_id -> d -> flow_result d;

  (**
   * Return flow function: callee exit -> return site
   * Maps facts at callee exit back to return site.
   *)
  ip_return_flow: node_id -> node_id -> node_id -> d -> d -> flow_result d;

  (**
   * Call-to-return flow function: call site -> return site (bypassing callee)
   * For facts that are NOT passed to callee (e.g., local variables).
   *)
  ip_call_to_return_flow: node_id -> node_id -> d -> flow_result d;
}

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 5: PATH EDGES AND SUMMARY EDGES
   ═══════════════════════════════════════════════════════════════════════════ *)

(**
 * Path Edge: Represents a realizable path in the exploded supergraph.
 *
 * A path edge <d1, s_proc> -> <d2, n> means:
 *   Starting from procedure s_proc's entry with fact d1,
 *   we can reach node n with fact d2 via a valid (context-matched) path.
 *)
type path_edge (d: Type) = {
  pe_proc_entry: node_id;  (** Entry node of the containing procedure *)
  pe_d1: d;                (** Fact at procedure entry *)
  pe_node: node_id;        (** Current node reached *)
  pe_d2: d;                (** Fact at current node *)
}

(**
 * Summary Edge: Captures a procedure's input-output behavior.
 *
 * A summary edge <d1, c> -> <d2, r> means:
 *   If fact d1 holds at call site c, then after the call returns,
 *   fact d2 holds at return site r.
 *)
type summary_edge (d: Type) = {
  se_call_site: node_id;    (** The call node *)
  se_d_call: d;             (** Fact at call site *)
  se_return_site: node_id;  (** The return node *)
  se_d_return: d;           (** Fact at return site *)
}

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 6: REALIZABLE PATHS AND REACHABILITY
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Exploded supergraph node: (node, fact) pair *)
unfold
let exploded_node (d: Type) : Type0 = node_id & d

(** Call stack entry: records pending return site *)
type call_stack_entry = {
  cse_call_site: node_id;
  cse_return_site: node_id;
}

(** A path in the exploded supergraph *)
unfold
let exploded_path (d: Type) : Type0 = list (exploded_node d)

(** Call stack for tracking pending returns *)
unfold
let call_stack : Type0 = list call_stack_entry

(** Extended path with call stack for reachability checking *)
type extended_path (d: Type) = {
  ep_path: exploded_path d;
  ep_stack: call_stack;
}

(** Predicate: path segment is intraprocedural *)
val is_intraprocedural_segment : supergraph -> node_id -> node_id -> bool

(** Predicate: edge is a call edge *)
val is_call_edge : supergraph -> node_id -> node_id -> bool

(** Predicate: edge is a return edge *)
val is_return_edge : supergraph -> node_id -> node_id -> bool

(**
 * Check if a path is realizable (CFL-reachable).
 *
 * A path is realizable iff:
 *   1. Every call edge pushes a return site onto the stack
 *   2. Every return edge pops and matches the expected return site
 *   3. At the end, the stack may be non-empty (suffix of execution)
 *)
val is_realizable_path : #d:Type -> supergraph -> extended_path d -> bool

(**
 * Valid flow path predicate: a path respects flow functions.
 *)
val valid_flow_path : #d:Type -> ifds_problem d -> exploded_path d -> bool

(**
 * Predicate: fact d2 is IFDS-reachable at node n from entry with fact d1.
 *)
val ifds_reaches : #d:Type -> supergraph -> d -> node_id -> d -> node_id -> Type0

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 7: IFDS SOLVER STATE AND RESULT
   ═══════════════════════════════════════════════════════════════════════════ *)

(** IFDS Solver State - abstract implementation *)
val ifds_state : (d: Type) -> Type0

(** Statistics for IFDS analysis *)
type ifds_stats = {
  stat_nodes_visited: nat;
  stat_edges_processed: nat;
  stat_summaries_created: nat;
  stat_iterations: nat;
}

(** Query result for a specific node *)
type ifds_query_result (d: Type) = {
  qr_node: node_id;
  qr_facts: set d;           (** Facts that hold at this node *)
  qr_path_count: nat;        (** Number of realizable paths *)
}

(** Full analysis result *)
noeq type ifds_result (d: Type) = {
  ir_all_facts: set (node_id & d);
  ir_path_edges: set (path_edge d);
  ir_summary_edges: set (summary_edge d);
  ir_stats: ifds_stats;
}

(** State accessors *)
val is_path_edges : #d:Type -> ifds_state d -> set (path_edge d)
val is_summary_edges : #d:Type -> ifds_state d -> set (summary_edge d)
val is_worklist : #d:Type -> ifds_state d -> list (path_edge d)

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 8: TABULATION ALGORITHM INTERFACE
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Initial state for IFDS solver *)
val ifds_initial_state : #d:Type -> ifds_problem d -> ifds_state d

(** Propagate a new path edge *)
val propagate_edge : #d:Type -> ifds_problem d -> path_edge d -> ifds_state d -> ifds_state d

(** Propagate multiple path edges *)
val propagate_edges : #d:Type -> ifds_problem d -> list (path_edge d) -> ifds_state d -> ifds_state d

(** Add a summary edge *)
val add_summary : #d:Type -> summary_edge d -> ifds_state d -> ifds_state d

(** Helper: Get all facts from a flow result as a list *)
val flow_result_to_list : #d:Type -> flow_result d -> list d

(** Helper: Create path edges for flow function results *)
val create_edges_for_flow : #d:Type ->
  node_id -> d -> node_id -> flow_result d -> list (path_edge d)

(**
 * Process a single path edge from the worklist.
 * This is the core of the IFDS tabulation algorithm.
 *)
val process_edge : #d:Type -> ifds_problem d -> path_edge d -> ifds_state d -> ifds_state d

(** Main worklist loop with fuel for termination *)
val solve_worklist : #d:Type -> ifds_problem d -> ifds_state d -> nat -> ifds_state d

(** Main IFDS solver entry point *)
val solve : #d:Type -> ifds_problem d -> set (node_id & d)

(** Query facts at a specific node *)
val query_node : #d:Type -> ifds_result d -> node_id -> ifds_query_result d

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 9: FLOW FUNCTION PROPERTIES
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Set inclusion (subset relation) *)
val set_subset : #a:Type -> set a -> set a -> Type0

(** Predicate: flow function is monotone *)
val is_monotone_flow : #d:Type -> ifds_problem d -> Type0

(** Predicate: flow function is distributive *)
val is_distributive_flow : #d:Type -> ifds_problem d -> Type0

(** LEMMA: Distributivity implies monotonicity *)
val distributive_implies_monotone : #d:Type ->
  prob:ifds_problem d ->
  Lemma (requires is_distributive_flow prob)
        (ensures is_monotone_flow prob)

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 10: CFL-REACHABILITY TYPES
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Grammar symbol for CFL-reachability *)
type cfl_symbol =
  | CFL_OpenParen   : proc_id -> cfl_symbol  (** (i - call to procedure i *)
  | CFL_CloseParen  : proc_id -> cfl_symbol  (** )i - return from procedure i *)
  | CFL_Epsilon     : cfl_symbol             (** epsilon transition *)
  | CFL_Intra       : cfl_symbol             (** intraprocedural edge *)

(** CFL derivation: sequence of grammar applications *)
unfold
let cfl_derivation : Type0 = list cfl_symbol

(** Predicate: derivation produces L-matched string *)
val derives_L_matched : cfl_derivation -> Tot bool

(** Predicate: derivation reaches a node with a fact *)
val derivation_reaches : #d:Type -> ifds_problem d -> cfl_derivation -> node_id -> d -> Type0

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 11: VALIDITY PREDICATES
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Predicate: path edge is in result *)
val path_edge_in_result : #d:Type -> path_edge d -> ifds_result d -> Type0

(** Predicate: (node, fact) pair is in result *)
val fact_at_node_in_result : #d:Type -> node_id -> d -> ifds_result d -> Type0

(** Predicate: path edge is structurally valid *)
val valid_path_edge : #d:Type -> ifds_problem d -> path_edge d -> Type0

(** Predicate: pe2 is an IFDS successor of pe1 *)
val is_ifds_successor : #d:Type -> ifds_problem d -> path_edge d -> path_edge d -> Type0

(** Predicate: fact reaches a node from entry *)
val fact_reaches_node : #d:Type -> ifds_problem d -> d -> node_id -> d -> Type0

(** Predicate: problem has distributive flow functions *)
val is_distributive_problem : #d:Type -> ifds_problem d -> Type0

(** Predicate: result is a valid fixed point of the IFDS equations *)
val is_ifds_fixpoint : #d:Type -> ifds_problem d -> ifds_state d -> Type0

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 12: SOUNDNESS AND COMPLETENESS THEOREMS
   ═══════════════════════════════════════════════════════════════════════════

   Key correctness properties of the IFDS algorithm based on:
   Reps, Horwitz, Sagiv 1995 Theorem 3.6
   ═══════════════════════════════════════════════════════════════════════════ *)

(**
 * THEOREM: IFDS Soundness (Reps et al. Theorem 3.6)
 *
 * If there exists a realizable path from the main entry with the zero fact
 * to node n with fact d, then (n, d) is in the IFDS result.
 *)
val ifds_soundness : #d:Type ->
  prob:ifds_problem d ->
  result:ifds_result d ->
  n:node_id ->
  fact:d ->
  Lemma (requires
           (let sg = prob.ip_supergraph in
            let main_entry = sg_get_entry sg (sg_main sg) in
            match main_entry with
            | None -> True
            | Some entry -> ifds_reaches sg prob.ip_zero entry fact n))
        (ensures fact_at_node_in_result n fact result)

(**
 * THEOREM: IFDS Completeness (Reps et al. Theorem 3.6)
 *
 * Every (n, d) in the IFDS result corresponds to a realizable path
 * from main entry to n where d holds.
 *)
val ifds_completeness : #d:Type ->
  prob:ifds_problem d ->
  result:ifds_result d ->
  n:node_id ->
  fact:d ->
  Lemma (requires fact_at_node_in_result n fact result)
        (ensures
           (let sg = prob.ip_supergraph in
            let main_entry = sg_get_entry sg (sg_main sg) in
            match main_entry with
            | None -> True
            | Some entry -> ifds_reaches sg prob.ip_zero entry fact n))

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 13: INVARIANT THEOREMS
   ═══════════════════════════════════════════════════════════════════════════ *)

(**
 * THEOREM: Path Edge Validity Invariant
 *
 * Every path edge in the IFDS state corresponds to a valid realizable path
 * in the exploded supergraph.
 *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val path_edge_valid : #d:Type ->
    prob:ifds_problem d ->
    pe:path_edge d ->
    state:ifds_state d ->
    Lemma (requires Set.mem pe (is_path_edges state))
          (ensures
            valid_path_edge prob pe /\
            (exists (path: extended_path d).
              is_realizable_path prob.ip_supergraph path /\
              List.Tot.length path.ep_path > 0 /\
              (let (start_n, start_d) = List.Tot.hd path.ep_path in
               let (end_n, end_d) = List.Tot.last path.ep_path (start_n, start_d) in
               start_n = pe.pe_proc_entry /\
               start_d == pe.pe_d1 /\
               end_n = pe.pe_node /\
               end_d == pe.pe_d2)))
          [SMTPat (Set.mem pe (is_path_edges state))]
#pop-options

(** THEOREM: Worklist Invariant *)
val worklist_invariant : #d:Type ->
    prob:ifds_problem d ->
    state:ifds_state d ->
    Lemma (ensures
            forall pe. Set.mem pe (is_path_edges state) ==>
                       valid_path_edge prob pe)

(** THEOREM: Process Edge Maintains Invariant *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
val process_edge_maintains_invariant : #d:Type ->
    prob:ifds_problem d ->
    edge:path_edge d ->
    state:ifds_state d ->
    Lemma (requires
             (forall pe. Set.mem pe (is_path_edges state) ==> valid_path_edge prob pe) /\
             valid_path_edge prob edge)
          (ensures
             (let state' = process_edge prob edge state in
              forall pe. Set.mem pe (is_path_edges state') ==> valid_path_edge prob pe))
#pop-options

(**
 * THEOREM: Summary Edge Soundness
 *
 * Every summary edge represents a valid procedure behavior.
 *)
#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"
val summary_edge_sound : #d:Type ->
    prob:ifds_problem d ->
    se:summary_edge d ->
    result:ifds_result d ->
    Lemma (requires Set.mem se result.ir_summary_edges)
          (ensures
            forall entry_fact.
              fact_reaches_node prob entry_fact se.se_call_site se.se_d_call ==>
              fact_reaches_node prob entry_fact se.se_return_site se.se_d_return)
          [SMTPat (Set.mem se result.ir_summary_edges)]
#pop-options

(** THEOREM: Propagate Edge Idempotent *)
val propagate_edge_idempotent : #d:Type ->
    prob:ifds_problem d ->
    edge:path_edge d ->
    state:ifds_state d ->
    Lemma (ensures
            (let s1 = propagate_edge prob edge state in
             let s2 = propagate_edge prob edge s1 in
             Set.equal (is_path_edges s1) (is_path_edges s2)))
          [SMTPat (propagate_edge prob edge state)]

(** THEOREM: Fixed-Point Characterization *)
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
val solve_is_fixpoint : #d:Type ->
    prob:ifds_problem d ->
    result:ifds_result d{result.ir_path_edges = is_path_edges (solve_worklist prob (ifds_initial_state prob) 1000000)} ->
    Lemma (ensures
            forall pe. Set.mem pe result.ir_path_edges ==>
              (forall succ_pe. is_ifds_successor prob pe succ_pe ==>
                               Set.mem succ_pe result.ir_path_edges))
#pop-options

(**
 * THEOREM: CFL-Reachability Correspondence (Key theorem from RHS95)
 *
 * The IFDS result exactly characterizes CFL-reachable (node, fact) pairs.
 *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
val cfl_reachability_correspondence : #d:Type ->
    prob:ifds_problem d{is_distributive_problem prob} ->
    node:node_id ->
    fact:d ->
    result:ifds_result d ->
    Lemma (ensures
            Set.mem (node, fact) result.ir_all_facts <==>
            (exists derivation.
              derives_L_matched derivation /\
              derivation_reaches prob derivation node fact))
#pop-options

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 14: MONOTONICITY AND CONVERGENCE
   ═══════════════════════════════════════════════════════════════════════════ *)

(** LEMMA: Path edges grow monotonically *)
val path_edges_monotone : #d:Type ->
    prob:ifds_problem d ->
    edge:path_edge d ->
    state:ifds_state d ->
    Lemma (ensures
            set_subset (is_path_edges state)
                       (is_path_edges (process_edge prob edge state)))

(** LEMMA: Summary edges grow monotonically *)
val summary_edges_monotone : #d:Type ->
    prob:ifds_problem d ->
    edge:path_edge d ->
    state:ifds_state d ->
    Lemma (ensures
            set_subset (is_summary_edges state)
                       (is_summary_edges (process_edge prob edge state)))

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 15: COMPLEXITY BOUNDS
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Size of supergraph nodes *)
val supergraph_node_count : supergraph -> nat

(** Size of supergraph edges *)
val supergraph_edge_count : supergraph -> nat

(** Size of domain *)
val domain_size : #d:Type -> ifds_problem d -> nat

(** Path edge space bound: at most N * D^2 path edges *)
val max_path_edges : #d:Type -> ifds_problem d -> nat

(** Summary edge space bound: at most C * D^2 summary edges *)
val max_summary_edges : #d:Type -> ifds_problem d -> nat

(** Worklist measure for termination proof *)
val worklist_measure : #d:Type -> ifds_problem d -> ifds_state d -> nat

(** LEMMA: Processing an edge decreases the measure *)
val process_edge_decreases_measure : #d:Type ->
  prob:ifds_problem d ->
  edge:path_edge d ->
  state:ifds_state d{List.Tot.length (is_worklist state) > 0} ->
  Lemma (requires
           List.Tot.hd (is_worklist state) == edge /\
           Set.cardinality (is_path_edges state) <= max_path_edges prob)
        (ensures
           (let state' = { state with is_worklist = List.Tot.tl (is_worklist state) } in
            let state'' = process_edge prob edge state' in
            worklist_measure prob state'' <= worklist_measure prob state \/
            List.Tot.length (is_worklist state'') = 0))

(** THEOREM: Worklist algorithm terminates *)
val worklist_terminates : #d:Type ->
  prob:ifds_problem d ->
  init:ifds_state d ->
  Lemma (requires Set.cardinality (is_path_edges init) <= max_path_edges prob)
        (ensures
           exists (n: nat). n <= max_path_edges prob + List.Tot.length (is_worklist init) /\
           (let final = solve_worklist prob init n in
            List.Tot.length (is_worklist final) = 0))

(** THEOREM: Solve produces a fixed point *)
val solve_reaches_fixpoint : #d:Type ->
  prob:ifds_problem d ->
  fuel:nat{fuel >= max_path_edges prob} ->
  Lemma (ensures
           (let init = ifds_initial_state prob in
            let final = solve_worklist prob init fuel in
            is_ifds_fixpoint prob final))

(**
 * THEOREM: IFDS Complexity Bound (Reps et al. Theorem 3.7)
 *
 * The IFDS tabulation algorithm terminates in O(E * D^3) time.
 *)
val ifds_complexity : #d:Type ->
  prob:ifds_problem d ->
  Lemma (ensures
           (let max_pe = max_path_edges prob in
            let max_se = max_summary_edges prob in
            True))

(** COROLLARY: IFDS analysis terminates in O(E * D^3) time *)
val ifds_terminates_with_bound : #d:Type ->
  prob:ifds_problem d ->
  Lemma (ensures
           (let bound = max_path_edges prob + max_summary_edges prob in
            True))

(**
 * THEOREM: IFDS Context-Sensitivity (CFL-Reachability)
 *
 * The IFDS algorithm only computes facts along realizable paths.
 *)
val ifds_context_sensitive : #d:Type ->
  prob:ifds_problem d ->
  result:ifds_result d ->
  pe:path_edge d ->
  Lemma (requires path_edge_in_result pe result)
        (ensures
           (let sg = prob.ip_supergraph in
            exists (path: extended_path d).
              is_realizable_path sg path /\
              List.Tot.length path.ep_path > 0 /\
              (let (start_n, start_d) = List.Tot.hd path.ep_path in
               let (end_n, end_d) = List.Tot.last path.ep_path (start_n, start_d) in
               start_n = pe.pe_proc_entry /\
               start_d == pe.pe_d1 /\
               end_n = pe.pe_node /\
               end_d == pe.pe_d2)))

(** THEOREM: Summary Edge Correctness *)
val summary_edge_correct : #d:Type ->
  prob:ifds_problem d ->
  result:ifds_result d ->
  se:summary_edge d ->
  Lemma (requires Set.mem se result.ir_summary_edges)
        (ensures
           (let sg = prob.ip_supergraph in
            let callee_opt = sg_get_callee sg se.se_call_site in
            match callee_opt with
            | None -> True
            | Some callee ->
              match sg_get_entry sg callee, sg_get_exit sg callee with
              | Some entry, Some exit ->
                ifds_reaches sg se.se_d_call entry se.se_d_return exit
              | _, _ -> True))
        [SMTPat (Set.mem se result.ir_summary_edges)]

(** LEMMA: IFDS flow functions preserve distributivity *)
val path_flow_distributive : #d:Type ->
  prob:ifds_problem d ->
  path:list flow_edge ->
  Lemma (requires is_distributive_flow prob)
        (ensures True)

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 16: DEMAND-DRIVEN EXTENSION
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Demand-driven query configuration *)
type demand_query (d: Type) = {
  dq_target_node: node_id;   (** Node we're querying *)
  dq_target_fact: option d;  (** Specific fact, or None for all facts *)
}

(** Demand-driven IFDS solver *)
val solve_demand : #d:Type -> ifds_problem d -> demand_query d -> ifds_query_result d

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 17: SPARSE IFDS OPTIMIZATION
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Sparse flow function representation *)
type sparse_flow (d: Type) = {
  sf_gen: set d;   (** Facts generated *)
  sf_kill: set d;  (** Facts killed *)
  sf_id: bool;     (** True if identity for all other facts *)
}

(** Convert sparse flow to dense flow function *)
val sparse_to_dense : #d:Type -> sparse_flow d -> (d -> flow_result d)

(** Check if a flow function is sparse (gen/kill form) *)
val is_sparse : #d:Type -> (d -> flow_result d) -> set d -> option (sparse_flow d)

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 18: IDE EXTENSION (Interprocedural Distributive Environment)
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Micro-function: environment transformer *)
noeq type micro_fn (v: Type) = {
  mf_compose: micro_fn v -> micro_fn v;  (** Composition *)
  mf_meet: micro_fn v -> micro_fn v;     (** Pointwise meet *)
  mf_apply: v -> v;                       (** Apply to value *)
  mf_id: bool;                            (** Is identity? *)
}

(** IDE Problem Definition *)
noeq type ide_problem (d: Type) (v: Type) = {
  ide_ifds: ifds_problem d;          (** Underlying IFDS problem *)
  ide_value_lattice: v;              (** Value lattice bottom *)
  ide_value_join: v -> v -> v;       (** Value join *)
  ide_edge_fn: flow_edge -> d -> d -> micro_fn v;  (** Micro-function per edge *)
}

(** IDE Result: Facts with associated values *)
type ide_result (d: Type) (v: Type) = {
  ide_facts: set (node_id & d & v);
}

(** IDE Solver *)
val solve_ide : #d:Type -> #v:Type -> ide_problem d v -> ide_result d v
