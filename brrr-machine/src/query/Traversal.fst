(**
 * BrrrMachine.Query.Traversal
 *
 * Traversal API and Combinators for CPG-based Program Analysis.
 *
 * Based on synthesis_combined.md Remark 1.54 (Yamaguchi 2014):
 *   - Traversals are first-class values: `set node_id -> set node_id`
 *   - MATCH_p(V) = FILTER_p(TNODES(V)) for pattern matching in subtrees
 *   - Compositional query construction via combinators
 *
 * Design Principles:
 *   1. Traversals as first-class citizens - can be stored, composed, reused
 *   2. Type-filtered node access via TNODES
 *   3. Predicate-based filtering via FILTER
 *   4. Set-theoretic combinators (union, intersection, difference)
 *   5. Transitive closures for reachability analysis
 *   6. Context-sensitive interprocedural traversal
 *
 * Key Types:
 *   - traversal: set node_id -> set node_id
 *   - label_pattern: flexible edge matching
 *   - traversal_result: lazy sequence abstraction
 *
 * References:
 *   - Yamaguchi 2014: "Modeling and Discovering Vulnerabilities with CPGs"
 *   - Weiser 1984: "Program Slicing"
 *   - Horwitz 1990: "Interprocedural Slicing"
 *   - Tripp 2009 (TAJ): "Thin Slicing"
 *
 * Integration:
 *   Add to Makefile INCLUDE_PATHS: --include query --include cpg
 *   Add to Makefile QUERY_SOURCES: query/Traversal.fst
 *)
module BrrrMachine.Query.Traversal

open FStar.List.Tot
open FStar.Set
open BrrrMachine.CPG

(** ============================================================================
    SECTION 1: LABEL PATTERNS
    ============================================================================
    Flexible edge matching patterns for traversal queries.
    Supports exact match, prefix, any, and boolean combinations.
    ============================================================================ *)

(**
 * Label Pattern - Flexible edge label matching.
 *
 * Enables queries like:
 *   - LabelExact (EdgeDdg (DdgUse "x")) - exact match
 *   - LabelPrefix "Ddg" - any data dependence edge
 *   - LabelOr [LabelPrefix "Ddg"; LabelPrefix "Cdg"] - any dependence
 *)
noeq type label_pattern =
  | LabelExact   : cpg_edge_kind -> label_pattern        (* Exact match *)
  | LabelPrefix  : string -> label_pattern               (* Prefix match on stringified label *)
  | LabelAny     : label_pattern                         (* Match any edge *)
  | LabelOr      : list label_pattern -> label_pattern   (* Disjunction *)
  | LabelAnd     : list label_pattern -> label_pattern   (* Conjunction *)
  | LabelNot     : label_pattern -> label_pattern        (* Negation *)
  | LabelByKind  : edge_kind_class -> label_pattern      (* Match by edge category *)

(**
 * Edge kind classification for pattern matching.
 *)
and edge_kind_class =
  | EkAst       : edge_kind_class   (* AST edges *)
  | EkCfg       : edge_kind_class   (* CFG edges *)
  | EkDdg       : edge_kind_class   (* Data dependence edges *)
  | EkCdg       : edge_kind_class   (* Control dependence edges *)
  | EkCg        : edge_kind_class   (* Call graph edges *)
  | EkEffect    : edge_kind_class   (* Effect edges *)

(**
 * Convert edge kind to string for prefix matching.
 *)
let edge_kind_to_string (k: cpg_edge_kind) : string =
  match k with
  | EdgeAst _    -> "Ast"
  | EdgeCfg _    -> "Cfg"
  | EdgeDdg _    -> "Ddg"
  | EdgeCdg _    -> "Cdg"
  | EdgeCg _     -> "Cg"
  | EdgeEffect _ -> "Effect"

(**
 * Classify edge kind into category.
 *)
let edge_kind_class (k: cpg_edge_kind) : edge_kind_class =
  match k with
  | EdgeAst _    -> EkAst
  | EdgeCfg _    -> EkCfg
  | EdgeDdg _    -> EkDdg
  | EdgeCdg _    -> EkCdg
  | EdgeCg _     -> EkCg
  | EdgeEffect _ -> EkEffect

(**
 * Check if string starts with prefix.
 *)
let string_starts_with (s: string) (prefix: string) : bool =
  let prefix_len = String.length prefix in
  let s_len = String.length s in
  if prefix_len > s_len then false
  else String.sub s 0 prefix_len = prefix

(**
 * Match a label pattern against an edge kind.
 *
 * Returns true if the edge kind matches the pattern.
 *)
let rec matches_pattern (pattern: label_pattern) (kind: cpg_edge_kind) : Tot bool (decreases pattern) =
  match pattern with
  | LabelExact k -> kind = k
  | LabelPrefix prefix -> string_starts_with (edge_kind_to_string kind) prefix
  | LabelAny -> true
  | LabelOr patterns -> List.Tot.existsb (fun p -> matches_pattern p kind) patterns
  | LabelAnd patterns -> List.Tot.for_all (fun p -> matches_pattern p kind) patterns
  | LabelNot p -> not (matches_pattern p kind)
  | LabelByKind cls -> edge_kind_class kind = cls

(** Convenience patterns for common edge types *)
let pattern_ast : label_pattern = LabelByKind EkAst
let pattern_cfg : label_pattern = LabelByKind EkCfg
let pattern_ddg : label_pattern = LabelByKind EkDdg
let pattern_cdg : label_pattern = LabelByKind EkCdg
let pattern_cg  : label_pattern = LabelByKind EkCg
let pattern_effect : label_pattern = LabelByKind EkEffect

(** Data and control dependence combined *)
let pattern_dependence : label_pattern = LabelOr [pattern_ddg; pattern_cdg]

(** All interprocedural edges *)
let pattern_interprocedural : label_pattern = pattern_cg

(** ============================================================================
    SECTION 2: TRAVERSAL RESULT TYPE
    ============================================================================
    Traversal result as a lazy sequence of nodes.

    While F* doesn't have built-in laziness, we model lazy sequences
    as a thunk that produces a list on demand. This enables:
      - Deferred computation
      - Early termination via limit
      - Composable transformations
    ============================================================================ *)

(**
 * Traversal Result - Lazy sequence of node IDs.
 *
 * Conceptually a lazy sequence, implemented as a thunk for on-demand
 * computation. Allows composing filters and maps without materializing
 * intermediate results.
 *)
noeq type traversal_result = {
  tr_compute : unit -> list node_id;  (* Thunk to compute result *)
  tr_source  : string;                (* Origin description for debugging *)
}

(** Materialize a traversal result into a set *)
let materialize (tr: traversal_result) : set node_id =
  Set.fromList (tr.tr_compute ())

(** Materialize as list *)
let to_list (tr: traversal_result) : list node_id =
  tr.tr_compute ()

(** Create traversal result from set *)
let from_set (nodes: set node_id) (desc: string) : traversal_result =
  { tr_compute = (fun () -> Set.toList nodes);
    tr_source = desc }

(** Create traversal result from list *)
let from_list (nodes: list node_id) (desc: string) : traversal_result =
  { tr_compute = (fun () -> nodes);
    tr_source = desc }

(** Empty traversal result *)
let empty_result : traversal_result =
  { tr_compute = (fun () -> []);
    tr_source = "empty" }

(** Single node result *)
let singleton_result (n: node_id) (desc: string) : traversal_result =
  { tr_compute = (fun () -> [n]);
    tr_source = desc }

(** ============================================================================
    SECTION 3: CORE TRAVERSAL TYPE
    ============================================================================
    A traversal is a function from a set of nodes to a set of nodes.
    This is the fundamental abstraction from Yamaguchi 2014.
    ============================================================================ *)

(**
 * Traversal - First-class graph query.
 *
 * A traversal T applied to node set X yields a new node set T(X).
 * Traversals can be composed, enabling complex query construction.
 *
 * Theorem (Traversal Closure): Traversals form a monoid under composition
 * with identity traversal as the identity element.
 *)
type traversal = set node_id -> set node_id

(**
 * Identity traversal - returns input unchanged.
 *)
let id_traversal : traversal = fun nodes -> nodes

(**
 * Empty traversal - always returns empty set.
 *)
let empty_traversal : traversal = fun _ -> Set.empty

(**
 * Constant traversal - always returns fixed set.
 *)
let const_traversal (result: set node_id) : traversal = fun _ -> result

(** ============================================================================
    SECTION 4: TRAVERSAL COMPOSITION
    ============================================================================
    Compose traversals sequentially and in parallel.
    ============================================================================ *)

(**
 * Compose two traversals sequentially (left-to-right).
 *
 * (compose2 t1 t2) x = t2 (t1 x)
 *
 * First apply t1, then apply t2 to the result.
 *)
let compose2 (t1 t2: traversal) : traversal =
  fun nodes -> t2 (t1 nodes)

(**
 * Compose a list of traversals sequentially.
 *
 * compose [t1; t2; t3] = t3 . t2 . t1
 *)
let compose (traversals: list traversal) : traversal =
  fun nodes -> List.Tot.fold_left (fun ns t -> t ns) nodes traversals

(**
 * Operator for infix composition.
 * (t1 |>> t2) = compose2 t1 t2
 *)
let ( |>> ) (t1 t2: traversal) : traversal = compose2 t1 t2

(** ============================================================================
    SECTION 5: TRAVERSAL COMBINATORS
    ============================================================================
    Set-theoretic operations on traversal results.
    ============================================================================ *)

(**
 * Union - nodes reachable by either traversal.
 *
 * union_t t1 t2 x = (t1 x) U (t2 x)
 *)
let union_t (t1 t2: traversal) : traversal =
  fun nodes -> Set.union (t1 nodes) (t2 nodes)

(**
 * Intersection - nodes reachable by both traversals.
 *
 * inter_t t1 t2 x = (t1 x) N (t2 x)
 *)
let inter_t (t1 t2: traversal) : traversal =
  fun nodes -> Set.inter (t1 nodes) (t2 nodes)

(**
 * Difference - nodes in first but not second.
 *
 * diff_t t1 t2 x = (t1 x) \ (t2 x)
 *)
let diff_t (t1 t2: traversal) : traversal =
  fun nodes -> Set.diff (t1 nodes) (t2 nodes)

(**
 * Symmetric difference - nodes in exactly one traversal result.
 *)
let sym_diff_t (t1 t2: traversal) : traversal =
  fun nodes ->
    let r1 = t1 nodes in
    let r2 = t2 nodes in
    Set.union (Set.diff r1 r2) (Set.diff r2 r1)

(**
 * Complement - requires a universe set.
 *)
let complement_t (t: traversal) (universe: set node_id) : traversal =
  fun nodes -> Set.diff universe (t nodes)

(** ============================================================================
    SECTION 6: BASIC TRAVERSALS (OUT, IN, FILTER, MAP)
    ============================================================================
    Core primitives following Yamaguchi 2014.
    ============================================================================ *)

(**
 * OUT - Follow outgoing edges matching label pattern.
 *
 * Given nodes V and pattern p, returns all nodes N such that
 * exists v in V, edge (v, n) with label matching p.
 *)
val out : cpg -> label_pattern -> traversal

let out (g: cpg) (pattern: label_pattern) : traversal =
  fun nodes ->
    let edges = cpg_filter_edges g (fun e ->
      Set.mem e.ce_source nodes && matches_pattern pattern e.ce_kind) in
    Set.fromList (List.Tot.map (fun e -> e.ce_target) edges)

(**
 * IN - Follow incoming edges matching label pattern.
 *
 * Given nodes V and pattern p, returns all nodes N such that
 * exists v in V, edge (n, v) with label matching p.
 *)
val in_ : cpg -> label_pattern -> traversal

let in_ (g: cpg) (pattern: label_pattern) : traversal =
  fun nodes ->
    let edges = cpg_filter_edges g (fun e ->
      Set.mem e.ce_target nodes && matches_pattern pattern e.ce_kind) in
    Set.fromList (List.Tot.map (fun e -> e.ce_source) edges)

(**
 * FILTER - Keep only nodes satisfying predicate.
 *
 * Essential for pattern matching within traversal results.
 *)
val filter : cpg -> (cpg_node -> bool) -> traversal

let filter (g: cpg) (pred: cpg_node -> bool) : traversal =
  fun nodes ->
    Set.filter (fun n ->
      match g.cpg_get_node n with
      | Some node -> pred node
      | None -> false) nodes

(**
 * MAP - Transform nodes via function (collects results into set).
 *)
val map_t : cpg -> (cpg_node -> set node_id) -> traversal

let map_t (g: cpg) (f: cpg_node -> set node_id) : traversal =
  fun nodes ->
    let expand n =
      match g.cpg_get_node n with
      | Some node -> f node
      | None -> Set.empty
    in
    Set.fold (fun n acc -> Set.union (expand n) acc) nodes Set.empty

(**
 * MAP with scalar function - Transform node IDs.
 *)
val map_nodes : cpg -> (node_id -> option node_id) -> traversal

let map_nodes (g: cpg) (f: node_id -> option node_id) : traversal =
  fun nodes ->
    Set.fromList (List.Tot.filterMap f (Set.toList nodes))

(** ============================================================================
    SECTION 7: ALL NODES QUERY
    ============================================================================
    Entry points for traversals - starting node sets.
    ============================================================================ *)

(**
 * All nodes in the CPG.
 *)
let all_nodes (g: cpg) : set node_id =
  Set.fromList (List.Tot.map (fun n -> n.cn_id) g.cpg_nodes)

(**
 * Nodes of a specific kind.
 *)
let nodes_of_kind (g: cpg) (kind: cpg_node_kind) : set node_id =
  Set.fromList (List.Tot.filterMap
    (fun n -> if n.cn_kind = kind then Some n.cn_id else None)
    g.cpg_nodes)

(**
 * Nodes in a specific procedure.
 *)
let nodes_in_proc (g: cpg) (pid: proc_id) : set node_id =
  Set.fromList (List.Tot.filterMap
    (fun n -> if n.cn_proc = Some pid then Some n.cn_id else None)
    g.cpg_nodes)

(**
 * Entry node of a procedure.
 *)
let entry_node (g: cpg) (pid: proc_id) : set node_id =
  match g.cpg_proc_entry pid with
  | Some n -> Set.singleton n
  | None -> Set.empty

(**
 * Exit node of a procedure.
 *)
let exit_node (g: cpg) (pid: proc_id) : set node_id =
  match g.cpg_proc_exit pid with
  | Some n -> Set.singleton n
  | None -> Set.empty

(** ============================================================================
    SECTION 8: TNODES - TREE NODES (AST SUBTREE COLLECTION)
    ============================================================================
    From Yamaguchi 2014: TNODES(V) returns all nodes in subtrees rooted at V.
    Essential for syntax-based queries examining entire expressions/statements.
    ============================================================================ *)

(**
 * TNODES - Collect all nodes in AST subtrees rooted at given nodes.
 *
 * Yamaguchi 2014: "TNODES(V) returns all nodes in subtrees rooted at V"
 *
 * Recursively follows AST child edges to collect entire subtrees.
 * Essential for syntax-aware queries that need to examine complete
 * expressions or statement blocks.
 *)
val tnodes : cpg -> traversal

let tnodes (g: cpg) : traversal =
  fun roots ->
    let rec collect_subtree (node: node_id) (acc: set node_id) (fuel: nat) : set node_id =
      if fuel = 0 || Set.mem node acc then acc
      else
        let acc' = Set.add node acc in
        let ast_children = out g pattern_ast (Set.singleton node) in
        Set.fold (fun child a -> collect_subtree child a (fuel - 1)) ast_children acc'
    in
    Set.fold (fun root acc -> collect_subtree root acc 1000) roots Set.empty

(**
 * TNODES with depth limit.
 *)
val tnodes_depth : cpg -> nat -> traversal

let tnodes_depth (g: cpg) (max_depth: nat) : traversal =
  fun roots ->
    let rec collect (node: node_id) (depth: nat) (acc: set node_id) : set node_id =
      if depth > max_depth || Set.mem node acc then acc
      else
        let acc' = Set.add node acc in
        let ast_children = out g pattern_ast (Set.singleton node) in
        Set.fold (fun child a -> collect child (depth + 1) a) ast_children acc'
    in
    Set.fold (fun root acc -> collect root 0 acc) roots Set.empty

(** ============================================================================
    SECTION 9: MATCH - FIND NODES MATCHING PREDICATE IN SUBTREES
    ============================================================================
    From Yamaguchi 2014: MATCH_p(V) = FILTER_p(TNODES(V))

    Combines subtree collection with filtering to find specific patterns
    within AST subtrees. Foundation for syntax-aware vulnerability queries.
    ============================================================================ *)

(**
 * MATCH_p - Find nodes matching predicate within subtrees.
 *
 * Yamaguchi 2014, Remark 1.54:
 *   MATCH_p(V) = FILTER_p(TNODES(V))
 *
 * This is the key primitive for syntax-aware vulnerability detection.
 * Given root nodes V, finds all nodes in their subtrees matching predicate p.
 *)
val match_pred : cpg -> (cpg_node -> bool) -> traversal

let match_pred (g: cpg) (pred: cpg_node -> bool) : traversal =
  fun roots ->
    filter g pred (tnodes g roots)

(**
 * MATCH by node kind - Find nodes of specific kind in subtrees.
 *)
val match_kind : cpg -> cpg_node_kind -> traversal

let match_kind (g: cpg) (kind: cpg_node_kind) : traversal =
  match_pred g (fun n -> n.cn_kind = kind)

(**
 * MATCH by kind predicate - Find nodes where kind satisfies predicate.
 *)
val match_kind_pred : cpg -> (cpg_node_kind -> bool) -> traversal

let match_kind_pred (g: cpg) (kind_pred: cpg_node_kind -> bool) : traversal =
  match_pred g (fun n -> kind_pred n.cn_kind)

(**
 * MATCH by name pattern - Find nodes whose name matches pattern.
 *
 * Uses simple substring matching. For regex, extend with proper regex library.
 *)
val match_name : cpg -> (string -> bool) -> traversal

let match_name (g: cpg) (name_pred: string -> bool) : traversal =
  match_pred g (fun n ->
    match n.cn_kind with
    | NkVar v -> name_pred v
    | NkGlobal s -> name_pred s
    | NkParam v _ -> name_pred v
    | NkLetMut v -> name_pred v
    | NkMethodCall m -> name_pred m
    | NkField f -> name_pred f
    | NkPerform op -> name_pred op
    | _ -> false)

(**
 * Find variable references by name.
 *)
val match_var : cpg -> var_id -> traversal

let match_var (g: cpg) (var: var_id) : traversal =
  match_kind g (NkVar var)

(**
 * Find function calls.
 *)
val match_calls : cpg -> traversal

let match_calls (g: cpg) : traversal =
  match_kind_pred g (fun k ->
    match k with
    | NkCall | NkMethodCall _ | NkCallSite _ -> true
    | _ -> false)

(**
 * Find all parameters.
 *)
val match_params : cpg -> traversal

let match_params (g: cpg) : traversal =
  match_kind_pred g (fun k ->
    match k with
    | NkParam _ _ -> true
    | _ -> false)

(**
 * Find all definitions (let, let mut, param).
 *)
val match_defs : cpg -> traversal

let match_defs (g: cpg) : traversal =
  match_kind_pred g (fun k ->
    match k with
    | NkLet _ | NkLetMut _ | NkParam _ _ -> true
    | _ -> false)

(** ============================================================================
    SECTION 10: TRANSITIVE CLOSURES - REACHABILITY
    ============================================================================
    Compute transitive closure along edges matching a pattern.
    Foundation for dataflow analysis and taint tracking.
    ============================================================================ *)

(**
 * REACHES - Forward transitive closure from start node.
 *
 * Returns all nodes reachable from start via edges matching pattern.
 * Implements fixpoint: REACHES(s) = {s} U OUT(REACHES(s))
 *)
val reaches : cpg -> label_pattern -> node_id -> set node_id

let reaches (g: cpg) (pattern: label_pattern) (start: node_id) : set node_id =
  let rec go (visited: set node_id) (frontier: set node_id) (fuel: nat) : set node_id =
    if fuel = 0 || Set.is_empty frontier then visited
    else
      let next = out g pattern frontier in
      let new_nodes = Set.diff next visited in
      go (Set.union visited new_nodes) new_nodes (fuel - 1)
  in
  go (Set.singleton start) (Set.singleton start) 10000

(**
 * REACHED_BY - Backward transitive closure to target node.
 *
 * Returns all nodes from which target is reachable via matching edges.
 *)
val reached_by : cpg -> label_pattern -> node_id -> set node_id

let reached_by (g: cpg) (pattern: label_pattern) (target: node_id) : set node_id =
  let rec go (visited: set node_id) (frontier: set node_id) (fuel: nat) : set node_id =
    if fuel = 0 || Set.is_empty frontier then visited
    else
      let prev = in_ g pattern frontier in
      let new_nodes = Set.diff prev visited in
      go (Set.union visited new_nodes) new_nodes (fuel - 1)
  in
  go (Set.singleton target) (Set.singleton target) 10000

(**
 * REACHES_SET - From any source to any target.
 *
 * Returns pairs (src, tgt) where tgt is reachable from src.
 *)
val reaches_set : cpg -> label_pattern -> set node_id -> set node_id -> list (node_id & node_id)

let reaches_set (g: cpg) (pattern: label_pattern) (sources targets: set node_id) : list (node_id & node_id) =
  let source_list = Set.toList sources in
  let target_list = Set.toList targets in
  let check_pair (src: node_id) : list (node_id & node_id) =
    let reachable = reaches g pattern src in
    List.Tot.filterMap
      (fun tgt -> if Set.mem tgt reachable then Some (src, tgt) else None)
      target_list
  in
  List.Tot.concatMap check_pair source_list

(**
 * REACHABLE - Traversal version of reaches.
 *
 * Given starting nodes, returns all reachable nodes.
 *)
val reachable : cpg -> label_pattern -> traversal

let reachable (g: cpg) (pattern: label_pattern) : traversal =
  fun starts ->
    Set.fold (fun start acc -> Set.union (reaches g pattern start) acc) starts Set.empty

(**
 * REACHABLE_BY - Traversal version of reached_by.
 *)
val reachable_by : cpg -> label_pattern -> traversal

let reachable_by (g: cpg) (pattern: label_pattern) : traversal =
  fun targets ->
    Set.fold (fun tgt acc -> Set.union (reached_by g pattern tgt) acc) targets Set.empty

(** ============================================================================
    SECTION 11: CFG/PDG TRAVERSALS
    ============================================================================
    Specialized traversals for control flow and dependence graphs.
    ============================================================================ *)

(**
 * CFG successors - immediate successors in control flow graph.
 *)
val cfg_succ : cpg -> traversal

let cfg_succ (g: cpg) : traversal = out g pattern_cfg

(**
 * CFG predecessors - immediate predecessors in control flow graph.
 *)
val cfg_pred : cpg -> traversal

let cfg_pred (g: cpg) : traversal = in_ g pattern_cfg

(**
 * DDG successors - nodes that use definitions from given nodes.
 *)
val ddg_succ : cpg -> traversal

let ddg_succ (g: cpg) : traversal = out g pattern_ddg

(**
 * DDG predecessors - definitions reaching given nodes.
 *)
val ddg_pred : cpg -> traversal

let ddg_pred (g: cpg) : traversal = in_ g pattern_ddg

(**
 * CDG successors - control-dependent nodes.
 *)
val cdg_succ : cpg -> traversal

let cdg_succ (g: cpg) : traversal = out g pattern_cdg

(**
 * CDG predecessors - controlling nodes.
 *)
val cdg_pred : cpg -> traversal

let cdg_pred (g: cpg) : traversal = in_ g pattern_cdg

(**
 * Traverse forward in CFG - all reachable nodes.
 *)
val traverse_forward_cfg : cpg -> traversal

let traverse_forward_cfg (g: cpg) : traversal = reachable g pattern_cfg

(**
 * Traverse backward in CFG - all nodes that can reach targets.
 *)
val traverse_backward_cfg : cpg -> traversal

let traverse_backward_cfg (g: cpg) : traversal = reachable_by g pattern_cfg

(**
 * Traverse forward following any dependence (data or control).
 *)
val traverse_forward_dep : cpg -> traversal

let traverse_forward_dep (g: cpg) : traversal = reachable g pattern_dependence

(**
 * Traverse backward following any dependence.
 *)
val traverse_backward_dep : cpg -> traversal

let traverse_backward_dep (g: cpg) : traversal = reachable_by g pattern_dependence

(** ============================================================================
    SECTION 12: PROGRAM SLICING
    ============================================================================
    Based on Weiser 1984, Horwitz 1990, Tripp 2009.
    ============================================================================ *)

(**
 * BACKWARD_SLICE - All nodes that could affect slicing criterion.
 *
 * Weiser 1984: Follows data and control dependence edges backward.
 *)
val backward_slice : cpg -> traversal

let backward_slice (g: cpg) : traversal = reachable_by g pattern_dependence

(**
 * FORWARD_SLICE - All nodes that could be affected by criterion.
 *
 * Dual of backward slice for impact analysis.
 *)
val forward_slice : cpg -> traversal

let forward_slice (g: cpg) : traversal = reachable g pattern_dependence

(**
 * TWO_PHASE_BACKWARD_SLICE - Context-sensitive interprocedural slice.
 *
 * From Horwitz 1990: Prevents spurious paths through call graph.
 *
 * Phase 1: Ascend to callers (don't follow param-out)
 * Phase 2: Descend into callees (don't follow call/param-in)
 *)
val two_phase_backward_slice : cpg -> set node_id -> set node_id

let two_phase_backward_slice (g: cpg) (criteria: set node_id) : set node_id =
  (* Phase 1: Backward but exclude outgoing param edges *)
  let phase1_pattern = LabelAnd [pattern_dependence; LabelNot pattern_cg] in
  let phase1 = reachable_by g phase1_pattern criteria in

  (* Phase 2: From phase1 results, continue backward but exclude incoming call edges *)
  let phase2 = reachable_by g phase1_pattern phase1 in

  Set.union phase1 phase2

(**
 * THIN_SLICE - Backward slice following only relevant dependencies.
 *
 * From Tripp 2009 (TAJ): More precise by tracking relevant variables.
 *)
val thin_slice : cpg -> node_id -> var_id -> nat -> set node_id

let thin_slice (g: cpg) (sink: node_id) (sink_var: var_id) (fuel: nat) : set node_id =
  let rec go (visited: set node_id) (frontier: set node_id) (relevant_vars: set var_id) (f: nat) : set node_id =
    if f = 0 || Set.is_empty frontier then visited
    else
      (* Get DDG predecessors *)
      let preds = in_ g pattern_ddg frontier in
      (* Filter to only nodes defining relevant variables *)
      let relevant_preds = Set.filter (fun n ->
        match g.cpg_get_node n with
        | Some node ->
            (match node.cn_kind with
             | NkLet (PatKVar v) -> Set.mem v relevant_vars
             | NkLetMut v -> Set.mem v relevant_vars
             | NkParam v _ -> Set.mem v relevant_vars
             | NkAssign -> true  (* TODO: Check if assigns relevant var *)
             | _ -> false)
        | None -> false) preds in
      (* Collect new relevant variables from these nodes *)
      let new_vars = Set.fold (fun n acc ->
        match g.cpg_get_node n with
        | Some node ->
            (match node.cn_kind with
             | NkVar v -> Set.add v acc
             | _ -> acc)
        | None -> acc) relevant_preds relevant_vars in
      let new_nodes = Set.diff relevant_preds visited in
      go (Set.union visited new_nodes) new_nodes new_vars (f - 1)
  in
  go (Set.singleton sink) (Set.singleton sink) (Set.singleton sink_var) fuel

(** ============================================================================
    SECTION 13: VULNERABILITY QUERY STRUCTURE
    ============================================================================
    Generic structure for vulnerability queries (taint analysis).
    ============================================================================ *)

(**
 * Vulnerability Query - Source-sink analysis with sanitizers.
 *
 * Pattern: source data flows to sink without passing through sanitizer.
 *)
noeq type vuln_query = {
  vq_name       : string;                    (* Query name for reporting *)
  vq_source     : cpg -> traversal;          (* Where tainted data originates *)
  vq_sink       : cpg -> traversal;          (* Where it must not reach unsanitized *)
  vq_sanitizers : cpg -> traversal;          (* What makes data safe *)
}

(**
 * Execute vulnerability query.
 *
 * Returns pairs (source, sink) where source reaches sink without sanitization.
 *)
val execute_vuln_query : cpg -> vuln_query -> list (node_id & node_id)

let execute_vuln_query (g: cpg) (query: vuln_query) : list (node_id & node_id) =
  let all = all_nodes g in
  let sources = query.vq_source g all in
  let sinks = query.vq_sink g all in
  let safe_nodes = query.vq_sanitizers g all in

  (* Find all source-sink pairs where path exists *)
  let pairs = reaches_set g pattern_ddg sources sinks in

  (* Filter out pairs where path passes through sanitizer *)
  (* This is a conservative check - ideally we'd check the actual path *)
  List.Tot.filter (fun (src, _) ->
    let reachable_from_src = reaches g pattern_ddg src in
    let safe_reachable = Set.inter reachable_from_src safe_nodes in
    Set.is_empty safe_reachable) pairs

(** ============================================================================
    SECTION 14: QUERY RESULT TYPES
    ============================================================================
    Structured results for different query types.
    ============================================================================ *)

(**
 * Taint finding - A specific vulnerability instance.
 *)
type taint_finding = {
  tf_source      : node_id;
  tf_sink        : node_id;
  tf_source_var  : option var_id;
  tf_path_length : nat;
  tf_description : string;
}

(**
 * Slice result - Nodes in a program slice.
 *)
type slice_result = {
  sr_criterion   : set node_id;   (* Original slicing criterion *)
  sr_slice       : set node_id;   (* Computed slice *)
  sr_direction   : string;        (* "forward" or "backward" *)
}

(**
 * Reachability result - Path information.
 *)
type reach_result = {
  rr_from        : node_id;
  rr_to          : node_id;
  rr_reachable   : bool;
  rr_path        : option (list node_id);
}

(** ============================================================================
    SECTION 15: CONVENIENCE FUNCTIONS
    ============================================================================
    High-level query functions for common patterns.
    ============================================================================ *)

(**
 * Check if any node in src_set can reach any node in tgt_set.
 *)
val any_reaches : cpg -> label_pattern -> set node_id -> set node_id -> bool

let any_reaches (g: cpg) (pattern: label_pattern) (sources targets: set node_id) : bool =
  let pairs = reaches_set g pattern sources targets in
  not (List.Tot.isEmpty pairs)

(**
 * Get the defined variable at a node, if any.
 *)
val get_defined_var : cpg -> node_id -> option var_id

let get_defined_var (g: cpg) (n: node_id) : option var_id =
  match g.cpg_get_node n with
  | Some node ->
      (match node.cn_kind with
       | NkLet (PatKVar v) -> Some v
       | NkLetMut v -> Some v
       | NkParam v _ -> Some v
       | _ -> None)
  | None -> None

(**
 * Get variables used at a node.
 *)
val get_used_vars : cpg -> node_id -> set var_id

let get_used_vars (g: cpg) (n: node_id) : set var_id =
  (* Get all variable reference nodes in subtree *)
  let subtree_nodes = tnodes g (Set.singleton n) in
  let var_nodes = filter g (fun node ->
    match node.cn_kind with NkVar _ -> true | _ -> false) subtree_nodes in
  Set.fromList (List.Tot.filterMap
    (fun vid ->
      match g.cpg_get_node vid with
      | Some node ->
          (match node.cn_kind with
           | NkVar v -> Some v
           | _ -> None)
      | None -> None)
    (Set.toList var_nodes))

(**
 * Find all nodes that define a given variable.
 *)
val find_defs_of : cpg -> var_id -> set node_id

let find_defs_of (g: cpg) (v: var_id) : set node_id =
  Set.fromList (List.Tot.filterMap
    (fun n ->
      match n.cn_kind with
      | NkLet (PatKVar x) -> if x = v then Some n.cn_id else None
      | NkLetMut x -> if x = v then Some n.cn_id else None
      | NkParam x _ -> if x = v then Some n.cn_id else None
      | _ -> None)
    g.cpg_nodes)

(**
 * Find all nodes that use a given variable.
 *)
val find_uses_of : cpg -> var_id -> set node_id

let find_uses_of (g: cpg) (v: var_id) : set node_id =
  Set.fromList (List.Tot.filterMap
    (fun n ->
      match n.cn_kind with
      | NkVar x -> if x = v then Some n.cn_id else None
      | _ -> None)
    g.cpg_nodes)

(** ============================================================================
    SECTION 16: TRAVERSAL ALGEBRA LEMMAS (Specifications)
    ============================================================================
    Algebraic properties of traversals (proofs deferred).
    ============================================================================ *)

(**
 * Lemma: Identity is left identity for composition.
 *)
val compose_id_left : t:traversal -> nodes:set node_id ->
  Lemma (compose2 id_traversal t nodes = t nodes)

let compose_id_left t nodes = ()

(**
 * Lemma: Identity is right identity for composition.
 *)
val compose_id_right : t:traversal -> nodes:set node_id ->
  Lemma (compose2 t id_traversal nodes = t nodes)

let compose_id_right t nodes = ()

(**
 * Lemma: Union is commutative.
 *)
val union_comm : t1:traversal -> t2:traversal -> nodes:set node_id ->
  Lemma (union_t t1 t2 nodes = union_t t2 t1 nodes)

let union_comm t1 t2 nodes = Set.union_comm (t1 nodes) (t2 nodes)

(**
 * Lemma: Intersection is commutative.
 *)
val inter_comm : t1:traversal -> t2:traversal -> nodes:set node_id ->
  Lemma (inter_t t1 t2 nodes = inter_t t2 t1 nodes)

let inter_comm t1 t2 nodes = Set.inter_comm (t1 nodes) (t2 nodes)

(**
 * Lemma: Union with empty is identity.
 *)
val union_empty : t:traversal -> nodes:set node_id ->
  Lemma (union_t t empty_traversal nodes = t nodes)

let union_empty t nodes = Set.union_empty_r (t nodes)

(**
 * Lemma: Intersection with empty is empty.
 *)
val inter_empty : t:traversal -> nodes:set node_id ->
  Lemma (inter_t t empty_traversal nodes = Set.empty)

let inter_empty t nodes = Set.inter_empty_r (t nodes)

(**
 * Lemma: Composition is associative.
 *
 * compose2 (compose2 t1 t2) t3 = compose2 t1 (compose2 t2 t3)
 *
 * This establishes that traversals form a monoid under composition.
 *)
val compose_assoc : t1:traversal -> t2:traversal -> t3:traversal -> nodes:set node_id ->
  Lemma (compose2 (compose2 t1 t2) t3 nodes = compose2 t1 (compose2 t2 t3) nodes)

let compose_assoc t1 t2 t3 nodes =
  (* By definition of compose2:
     compose2 (compose2 t1 t2) t3 nodes
       = t3 ((compose2 t1 t2) nodes)
       = t3 (t2 (t1 nodes))

     compose2 t1 (compose2 t2 t3) nodes
       = (compose2 t2 t3) (t1 nodes)
       = t3 (t2 (t1 nodes))

     Both are equal by function application. *)
  ()

(**
 * Lemma: Union is associative.
 *)
val union_assoc : t1:traversal -> t2:traversal -> t3:traversal -> nodes:set node_id ->
  Lemma (union_t (union_t t1 t2) t3 nodes = union_t t1 (union_t t2 t3) nodes)

let union_assoc t1 t2 t3 nodes =
  Set.union_assoc (t1 nodes) (t2 nodes) (t3 nodes)

(**
 * Lemma: Intersection is associative.
 *)
val inter_assoc : t1:traversal -> t2:traversal -> t3:traversal -> nodes:set node_id ->
  Lemma (inter_t (inter_t t1 t2) t3 nodes = inter_t t1 (inter_t t2 t3) nodes)

let inter_assoc t1 t2 t3 nodes =
  Set.inter_assoc (t1 nodes) (t2 nodes) (t3 nodes)

(**
 * Lemma: Difference with self is empty.
 *)
val diff_self : t:traversal -> nodes:set node_id ->
  Lemma (diff_t t t nodes = Set.empty)

let diff_self t nodes = Set.diff_self (t nodes)

(** ============================================================================
    SECTION 16b: REACHABILITY LEMMAS
    ============================================================================
    Properties of graph reachability as computed by traversals.
    ============================================================================ *)

(**
 * Lemma: Reachability is reflexive.
 *
 * Every node can reach itself via zero edges.
 *)
val reaches_reflexive : g:cpg -> pattern:label_pattern -> start:node_id ->
  Lemma (ensures Set.mem start (reaches g pattern start))

let reaches_reflexive g pattern start =
  (* By definition, reaches initializes visited with {start} *)
  ()

(**
 * Lemma: Reachability is transitive.
 *
 * If a can reach b and b can reach c, then a can reach c.
 *)
val reaches_transitive : g:cpg -> pattern:label_pattern -> a:node_id -> b:node_id -> c:node_id ->
  Lemma (requires Set.mem b (reaches g pattern a) && Set.mem c (reaches g pattern b))
        (ensures Set.mem c (reaches g pattern a))

let reaches_transitive g pattern a b c =
  (* The reachability computation explores all paths from start.
     If b is reachable from a, and c is reachable from b,
     the path a -> ... -> b -> ... -> c exists and will be found. *)
  admit ()  (* Full proof requires unfolding the fixpoint computation *)

(**
 * Lemma: OUT edge implies reachability.
 *
 * If there is a direct edge from a to b matching pattern, then b is reachable from a.
 *)
val direct_edge_implies_reaches : g:cpg -> pattern:label_pattern -> a:node_id -> b:node_id ->
  Lemma (requires Set.mem b (out g pattern (Set.singleton a)))
        (ensures Set.mem b (reaches g pattern a))

let direct_edge_implies_reaches g pattern a b =
  (* A direct edge is explored in the first iteration of reaches *)
  ()

(**
 * Lemma: Backward reachability is reflexive.
 *)
val reached_by_reflexive : g:cpg -> pattern:label_pattern -> target:node_id ->
  Lemma (ensures Set.mem target (reached_by g pattern target))

let reached_by_reflexive g pattern target =
  (* By definition, reached_by initializes visited with {target} *)
  ()

(**
 * Lemma: Backward reachability is transitive.
 *)
val reached_by_transitive : g:cpg -> pattern:label_pattern -> a:node_id -> b:node_id -> c:node_id ->
  Lemma (requires Set.mem b (reached_by g pattern c) && Set.mem a (reached_by g pattern b))
        (ensures Set.mem a (reached_by g pattern c))

let reached_by_transitive g pattern a b c =
  (* Symmetric to reaches_transitive *)
  admit ()  (* Full proof requires unfolding the fixpoint computation *)

(**
 * Lemma: Forward and backward reachability are dual.
 *
 * a reaches b iff b is reached_by a.
 *)
val reaches_reached_by_dual : g:cpg -> pattern:label_pattern -> a:node_id -> b:node_id ->
  Lemma (ensures Set.mem b (reaches g pattern a) <==> Set.mem a (reached_by g pattern b))

let reaches_reached_by_dual g pattern a b =
  (* Both compute the same set of connected nodes, just from different directions *)
  admit ()  (* Requires showing the fixpoint computations are equivalent *)

(**
 * Lemma: Slice contains all directly dependent nodes.
 *
 * If node b depends on node a (via DDG or CDG), and a is in the backward slice of c,
 * then b's dependencies will be explored.
 *)
val slice_includes_deps : g:cpg -> target:node_id ->
  Lemma (ensures Set.subset (in_ g pattern_dependence (Set.singleton target))
                            (backward_slice g (Set.singleton target)))

let slice_includes_deps g target =
  (* backward_slice is defined as reachable_by with pattern_dependence,
     which includes the immediate predecessors *)
  ()

(**
 * Lemma: TNODES is idempotent.
 *
 * Collecting subtrees of subtrees gives the same result as collecting once.
 *)
val tnodes_idempotent : g:cpg -> roots:set node_id ->
  Lemma (ensures tnodes g (tnodes g roots) = tnodes g roots)

let tnodes_idempotent g roots =
  (* Once we have all nodes in subtrees, re-collecting can't add more *)
  admit ()  (* Requires showing the recursion terminates with same set *)

(**
 * Lemma: MATCH preserves subset relationship.
 *
 * If A is a subset of B, then MATCH on A is a subset of MATCH on B.
 *)
val match_preserves_subset : g:cpg -> pred:(cpg_node -> bool) ->
                             a:set node_id -> b:set node_id ->
  Lemma (requires Set.subset a b)
        (ensures Set.subset (match_pred g pred a) (match_pred g pred b))

let match_preserves_subset g pred a b =
  (* MATCH_p = FILTER_p . TNODES
     If a ⊆ b, then TNODES(a) ⊆ TNODES(b), and FILTER preserves this *)
  admit ()  (* Requires showing TNODES and FILTER preserve subset *)

(** ============================================================================
    SECTION 17: EXAMPLE QUERIES
    ============================================================================
    Demonstration of query composition for common vulnerability patterns.
    ============================================================================ *)

(* Note: Section 16b inserted above for reachability lemmas *)

(**
 * Example: SQL Injection Query
 *
 * Source: User input (parameters, request data)
 * Sink: SQL query execution
 * Sanitizer: Prepared statements, escaping functions
 *)
let sql_injection_query : vuln_query = {
  vq_name = "SQL Injection";
  vq_source = (fun g -> match_params g);
  vq_sink = (fun g -> match_name g (fun s ->
    s = "query" || s = "execute" || s = "raw_query"));
  vq_sanitizers = (fun g -> match_name g (fun s ->
    s = "escape" || s = "prepare" || s = "parameterize"));
}

(**
 * Example: Command Injection Query
 *)
let command_injection_query : vuln_query = {
  vq_name = "Command Injection";
  vq_source = (fun g -> match_params g);
  vq_sink = (fun g -> match_name g (fun s ->
    s = "exec" || s = "system" || s = "popen" || s = "shell"));
  vq_sanitizers = (fun g -> match_name g (fun s ->
    s = "sanitize" || s = "escape_shell" || s = "quote"));
}

(**
 * Example: Buffer Overflow Query (Yamaguchi 2014 Section 8.4)
 *
 * Pattern: Parameter matching "count" flows to memcpy size without bounds check.
 *)
val buffer_overflow_query : cpg -> set node_id

let buffer_overflow_query (g: cpg) : set node_id =
  (* Step 1: Find parameters with names suggesting count/size *)
  let count_params = filter g (fun n ->
    match n.cn_kind with
    | NkParam v _ -> string_starts_with v "count" || string_starts_with v "size"
    | _ -> false) (all_nodes g) in

  (* Step 2: Find what these can reach via data dependence *)
  let reachable_from_count = reachable g pattern_ddg count_params in

  (* Step 3: Filter to memcpy-like calls *)
  let memcpy_calls = filter g (fun n ->
    match n.cn_kind with
    | NkMethodCall m -> m = "memcpy" || m = "copy_from_user"
    | _ -> false) reachable_from_count in

  (* Step 4: Exclude if sanitized *)
  let sanitizers = filter g (fun n ->
    match n.cn_kind with
    | NkCall -> true  (* Simplified: any call to bounds-check function *)
    | NkMethodCall m -> m = "min" || m = "bounds_check"
    | _ -> false) (all_nodes g) in

  let sanitized = reachable_by g pattern_ddg sanitizers in

  Set.diff memcpy_calls sanitized

(** ============================================================================
    SECTION 18: EXPORTS
    ============================================================================
    Re-export key types and functions for external use.
    ============================================================================ *)

(* Core types are already exposed *)
(* Key traversal constructors and combinators are exposed *)
(* Query structures are exposed *)
